use crate::state::{scan_folders, File, Files};
use std::collections::hash_map::HashMap;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{oneshot, RwLock};
use tower_lsp::lsp_types::{MessageType, SemanticTokens, Url};
use tower_lsp::Client;

#[derive(Default)]
pub(crate) struct State {
    pub(crate) disk_files: Files,
    pub(crate) open_files: HashMap<Url, File>,
    pub(crate) diagnostic_versions: HashMap<Url, i32>,
    pub(crate) semantic_tokens_cache: HashMap<Url, SemanticTokens>,
    pub(crate) disk_scan_generation: u64,
    /// Set to `true` once at least one workspace scan has finished
    /// populating `disk_files`. Until then, the typecheck snapshot may be
    /// missing most of the workspace, so the strict unresolved-identifier
    /// check has to stay disabled — otherwise every cross-file reference
    /// would fire as `Unresolved identifier` until the scan races in.
    pub(crate) workspace_scan_complete: bool,
    /// Per-URI generation counter for typecheck tasks. Incremented each time a
    /// new typecheck is scheduled so that stale in-flight workers can detect
    /// they have been superseded and bail out early.
    pub(crate) typecheck_generation: HashMap<Url, u64>,
    /// Per-URI cancellation token for the in-flight typecheck worker. When
    /// a new typecheck is scheduled, the previous token is flipped to
    /// cancelled so the doomed worker stops at the next definition
    /// boundary instead of running to completion.
    pub(crate) typecheck_cancel: HashMap<Url, crate::typecheck::CancellationToken>,
}

impl State {
    /// Bump the typecheck generation for `uri` and return the new value.
    pub(crate) fn next_typecheck_generation(&mut self, uri: &Url) -> u64 {
        let gen = self.typecheck_generation.entry(uri.clone()).or_insert(0);
        *gen += 1;
        *gen
    }

    /// Look up a file by URI, preferring open files over disk files.
    /// Disk files are lazily loaded + parsed on first access.
    pub(crate) fn get_file(&self, uri: &Url) -> Option<&File> {
        self.open_files
            .get(uri)
            .or_else(|| self.disk_files.get_file(uri))
    }

    /// Iterate every file (open + disk) once, with open files shadowing
    /// their disk counterparts. Disk files are lazily parsed on first
    /// touch via the per-slot `OnceLock`, so a workspace with 158 files
    /// only pays parse cost for the files actually iterated.
    pub(crate) fn all_files(&self) -> impl Iterator<Item = (&Url, &File)> {
        self.open_files.iter().chain(
            self.disk_files
                .all_files()
                .filter(|(uri, _)| !self.open_files.contains_key(uri)),
        )
    }
}

pub(crate) struct Backend {
    pub(crate) state: Arc<RwLock<State>>,
    pub(crate) client: Client,
}

pub(crate) const SAIL_KEYWORDS: &[&str] = &[
    "and",
    "as",
    "assert",
    "backwards",
    "bitfield",
    "by",
    "catch",
    "clause",
    "configuration",
    "constant",
    "constraint",
    "dec",
    "default",
    "do",
    "downto",
    "effect",
    "else",
    "end",
    "enum",
    "exit",
    "forall",
    "foreach",
    "forwards",
    "from",
    "function",
    "if",
    "impl",
    "in",
    "inc",
    "infix",
    "infixl",
    "infixr",
    "instantiation",
    "let",
    "mapping",
    "match",
    "mutual",
    "newtype",
    "outcome",
    "overload",
    "private",
    "pure",
    "ref",
    "register",
    "repeat",
    "return",
    "scattered",
    "sizeof",
    "struct",
    "termination_measure",
    "then",
    "throw",
    "to",
    "try",
    "type",
    "union",
    "until",
    "val",
    "var",
    "when",
    "while",
    "with",
];

pub(crate) const SAIL_BUILTINS: &[&str] = &[
    "Int",
    "Nat",
    "Type",
    "Order",
    "Bool",
    "true",
    "false",
    "undefined",
    "bitzero",
    "bitone",
];

const DIAGNOSTIC_DEBOUNCE_MS: u64 = 250;
const TYPECHECK_DEBOUNCE_MS: u64 = 250;
const TYPECHECK_MAX_SOURCE_BYTES: usize = 128 * 1024;
// Sail type inference still recurses much more deeply than the default async
// worker stack, and even exceeded rust-analyzer's 8 MiB worker size on large
// RISC-V model files. Use a larger dedicated stack until the checker is made
// more iterative.
const TYPECHECK_THREAD_STACK_SIZE: usize = 64 * 1024 * 1024;

pub(crate) fn should_schedule_typecheck(file: &File) -> bool {
    if std::env::var_os("SAIL_FORCE_TYPECHECK").is_some() {
        return true;
    }
    file.source.text().len() <= TYPECHECK_MAX_SOURCE_BYTES
}

impl Backend {
    pub fn new_with_client(client: Client) -> Self {
        Self {
            state: Arc::new(RwLock::new(State::default())),
            client,
        }
    }

    /// Helper for read-only handlers that need a file by URI.
    pub(crate) async fn with_file<F, R>(&self, uri: &Url, f: F) -> tower_lsp::jsonrpc::Result<Option<R>>
    where
        F: FnOnce(&State, &File) -> Option<R>,
    {
        let state = self.state.read().await;
        let Some(file) = state.get_file(uri) else {
            return Ok(None);
        };
        Ok(f(&state, file))
    }

    pub(crate) fn schedule_debounced_diagnostics(&self, uri: Url, version: i32) {
        let state = self.state.clone();
        let client = self.client.clone();
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_millis(DIAGNOSTIC_DEBOUNCE_MS)).await;
            let diagnostics = {
                let state_guard = state.read().await;
                if state_guard.diagnostic_versions.get(&uri).copied() != Some(version) {
                    return;
                }
                state_guard
                    .open_files
                    .get(&uri)
                    .map(|file| file.lsp_diagnostics())
            };
            if let Some(diagnostics) = diagnostics {
                client.publish_diagnostics(uri, diagnostics, None).await;
            }
        });
    }

    pub(crate) async fn schedule_workspace_scan(&self) {
        let (generation, folders) = {
            let mut state = self.state.write().await;
            state.disk_scan_generation += 1;
            (
                state.disk_scan_generation,
                state.disk_files.folders().clone(),
            )
        };

        let state = self.state.clone();
        let client = self.client.clone();
        tokio::spawn(async move {
            let files = match tokio::task::spawn_blocking(move || scan_folders(folders)).await {
                Ok(files) => files,
                Err(err) => {
                    client
                        .log_message(
                            MessageType::ERROR,
                            format!("workspace scan task failed: {err}"),
                        )
                        .await;
                    return;
                }
            };

            let (applied, refresh_uris): (bool, Vec<(Url, i32, File)>) = {
                let mut state_guard = state.write().await;
                if state_guard.disk_scan_generation != generation {
                    (false, Vec::new())
                } else {
                    state_guard.disk_files.update(files);
                    state_guard.workspace_scan_complete = true;
                    // Re-snapshot every open file so we can re-run their
                    // typecheck against the freshly populated workspace.
                    // Without this, files opened before the scan finished
                    // would keep showing the lenient pre-scan diagnostics
                    // (or, if the strict check ever ran, a flood of false
                    // "Unresolved identifier" errors).
                    let refresh = state_guard
                        .open_files
                        .iter()
                        .map(|(uri, file)| {
                            let version = state_guard
                                .diagnostic_versions
                                .get(uri)
                                .copied()
                                .unwrap_or(0);
                            (uri.clone(), version, file.clone())
                        })
                        .collect();
                    (true, refresh)
                }
            };

            if applied {
                client
                    .log_message(MessageType::INFO, "workspace scan completed")
                    .await;
            }

            // Schedule a fresh typecheck for every currently open file so
            // they immediately reflect the now-complete workspace context.
            if applied {
                for (uri, version, file) in refresh_uris {
                    spawn_debounced_typecheck(state.clone(), client.clone(), uri, version, file);
                }
            }
        });
    }

    pub(crate) fn schedule_debounced_typecheck(&self, uri: Url, version: i32, file: File) {
        spawn_debounced_typecheck(self.state.clone(), self.client.clone(), uri, version, file);
    }
}

pub(crate) fn spawn_debounced_typecheck(
    state: Arc<RwLock<State>>,
    client: Client,
    uri: Url,
    version: i32,
    file: File,
) {
    tokio::spawn(async move {
            // Bump the generation counter so any previously-spawned typecheck
            // for this URI knows it has been superseded, and install a fresh
            // cancellation token, cancelling the previous one so its in-flight
            // worker stops at the next definition boundary instead of running
            // to completion.
            let (generation, cancel) = {
                let mut state_guard = state.write().await;
                let generation = state_guard.next_typecheck_generation(&uri);
                let cancel = crate::typecheck::CancellationToken::new();
                if let Some(prev) =
                    state_guard.typecheck_cancel.insert(uri.clone(), cancel.clone())
                {
                    prev.cancel();
                }
                (generation, cancel)
            };

            tokio::time::sleep(Duration::from_millis(TYPECHECK_DEBOUNCE_MS)).await;

            // After the debounce sleep, check whether a newer typecheck was
            // scheduled (generation changed) or the document version moved on.
            {
                let state_guard = state.read().await;
                if state_guard.typecheck_generation.get(&uri).copied() != Some(generation) {
                    return;
                }
                if state_guard.diagnostic_versions.get(&uri).copied() != Some(version) {
                    return;
                }
            }

            // Snapshot all files (open + disk) so the worker thread can do
            // cross-file analysis without holding the state lock. Also
            // capture whether the disk scan has completed — until it has,
            // the snapshot may be missing most of the workspace, so the
            // strict unresolved-identifier check has to stay disabled.
            let (workspace_files, workspace_complete): (Vec<File>, bool) = {
                let state_guard = state.read().await;
                (
                    state_guard.all_files().map(|(_, f)| f.clone()).collect(),
                    state_guard.workspace_scan_complete,
                )
            };

            // Run typecheck AND workspace-aware semantic recompute in the
            // worker thread so they can both use the cross-file context.
            let (tx, rx) = oneshot::channel();
            let workspace_for_thread = workspace_files;
            let cancel_for_thread = cancel.clone();
            let spawn_result = std::thread::Builder::new()
                .name("sail-typecheck".to_string())
                .stack_size(TYPECHECK_THREAD_STACK_SIZE)
                .spawn(move || {
                    let mut file = file;
                    file.recompute_diagnostics_with_workspace(
                        &workspace_for_thread,
                        workspace_complete,
                        cancel_for_thread,
                    );
                    let _ = tx.send(file);
                });

            let updated_file = match spawn_result {
                Ok(_handle) => rx.await.ok(),
                Err(err) => {
                    client
                        .log_message(
                            MessageType::ERROR,
                            format!("failed to spawn typecheck worker: {err}"),
                        )
                        .await;
                    None
                }
            };

            // After typecheck completes, verify this task is still the latest
            // before committing the result into state. Also collect a list
            // of dependent open files whose typecheck should be refreshed:
            // any open file (other than this one) that referenced one of
            // F's top-level symbol names. This is the lightweight reverse-
            // dependency analogue of salsa's automatic invalidation.
            let (diagnostics, dependents): (Option<Vec<_>>, Vec<(Url, i32, File)>) = {
                let mut state_guard = state.write().await;
                if state_guard.typecheck_generation.get(&uri).copied() != Some(generation) {
                    return;
                }
                if state_guard.diagnostic_versions.get(&uri).copied() != Some(version) {
                    return;
                }
                let Some(file) = state_guard.open_files.get_mut(&uri) else {
                    return;
                };
                if let Some(updated) = updated_file {
                    *file = updated;
                }
                let diagnostics = Some(file.lsp_diagnostics());

                // Collect names of every top-level definition exported by
                // the file we just rechecked. These are the symbols whose
                // signatures might have changed shape.
                let exported_names: std::collections::HashSet<String> = file
                    .signature_index
                    .keys()
                    .cloned()
                    .chain(file.definitions.keys().cloned())
                    .collect();

                // Find every other open file that references one of those
                // names in its parsed symbol occurrences. Snapshot the
                // (uri, version, File) so we can hand them to the
                // background scheduler without holding the write lock.
                let dependents: Vec<(Url, i32, File)> = state_guard
                    .open_files
                    .iter()
                    .filter(|(other_uri, _)| **other_uri != uri)
                    .filter_map(|(other_uri, other_file)| {
                        let parsed = other_file.parsed()?;
                        let touches = parsed
                            .symbol_occurrences
                            .iter()
                            .any(|occ| exported_names.contains(&occ.name));
                        if touches {
                            let v = state_guard
                                .diagnostic_versions
                                .get(other_uri)
                                .copied()
                                .unwrap_or(0);
                            Some((other_uri.clone(), v, other_file.clone()))
                        } else {
                            None
                        }
                    })
                    .collect();

                (diagnostics, dependents)
            };

            if let Some(diagnostics) = diagnostics {
                client.publish_diagnostics(uri.clone(), diagnostics, None).await;
            }

            // Reschedule dependent open files. Each call goes through the
            // normal debounce + cancellation pipeline, so a rapid edit
            // burst on F won't generate a thundering herd — only the
            // latest reschedule for each dependent survives.
            for (dep_uri, dep_version, dep_file) in dependents {
                spawn_debounced_typecheck(state.clone(), client.clone(), dep_uri, dep_version, dep_file);
            }
        });
}
