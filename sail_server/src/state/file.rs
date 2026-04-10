use tower_lsp::lsp_types::{Diagnostic as LspDiagnostic, Position, TextDocumentContentChangeEvent};

use super::TextDocument;
use crate::diagnostics::{compute_parse_diagnostics, compute_semantic_diagnostics, Diagnostic};
use crate::symbols::{add_parsed_definitions, CallableSignature};
use chumsky::Parser;
use std::hash::{Hash, Hasher};
use std::{cmp::Ordering, collections::HashMap, sync::Arc, sync::Mutex};

/// Cheap content hash used to short-circuit `parse()` when the source text
/// hasn't changed since the last parse. This is the lightweight analogue
/// of salsa's input-revision tracking — repeated `did_change` events that
/// land on the same text (e.g. typing a character then undoing it) skip
/// the entire lex/parse/index pipeline.
fn content_hash(text: &str) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    text.hash(&mut hasher);
    hasher.finish()
}

fn best_parsed(
    core_ast: Option<&sail_parser::core_ast::SourceFile>,
) -> Option<sail_parser::ParsedFile> {
    core_ast.map(sail_parser::ParsedFile::from_core_ast)
}

/// Heavy per-file derived data is wrapped in `Arc<...>` so that
/// `File::clone()` becomes O(pointers) instead of O(file size). This makes
/// the workspace snapshot the typecheck worker thread builds essentially
/// free, regardless of how many files are in the workspace.
///
/// Mutations on these fields use `Arc::make_mut` (which clones in place if
/// the value is shared, no-op if uniquely owned) so the mutation pattern
/// stays local.
pub struct File {
    // The source code.
    pub source: TextDocument,

    // The parse result if any. Arc-wrapped for cheap cloning when passing to typecheck thread.
    pub tokens: Option<Arc<Vec<(sail_parser::Token, sail_parser::Span)>>>,

    // Lowered AST used for LSP analysis without depending on the upstream Sail binary.
    pub core_ast: Option<Arc<sail_parser::core_ast::SourceFile>>,

    // Cached semantic index derived from the best available parse.
    pub parsed: Option<Arc<sail_parser::ParsedFile>>,

    // Cached local type-check result inspired by Sail's type checker pipeline.
    pub type_check: Option<Arc<crate::typecheck::TypeCheckResult>>,

    // Go-to definition locations extracted from the file.
    pub definitions: Arc<HashMap<String, usize>>,

    // Cached callable signatures indexed by name for O(1) lookup.
    pub signature_index: Arc<HashMap<String, CallableSignature>>,

    // Cached per-file reference and implementation counts for code lenses.
    pub ref_counts: Arc<HashMap<String, usize>>,
    pub impl_counts: Arc<HashMap<String, usize>>,

    // Parse and semantic diagnostics that are available without type checking.
    base_diagnostics: Arc<Vec<Diagnostic>>,
    // Number of leading entries in `base_diagnostics` that are parse-only
    // (lex/syntax) diagnostics. Used by `recompute_diagnostics_with_workspace`
    // to replace just the trailing semantic diagnostics with workspace-aware
    // versions.
    parse_diagnostics_len: usize,

    // Cached LSP diagnostics to avoid repeated allocation.
    cached_lsp_diagnostics: Mutex<Option<Vec<LspDiagnostic>>>,

    // Disk-indexed files skip eager type checking to keep workspace scans shallow.
    eager_type_check: bool,

    /// Hash of the source text that produced the cached parse data above.
    /// `parse()` short-circuits when the live source text still hashes to
    /// this value — so a `did_change` whose net effect is a no-op (e.g.
    /// typing then undoing) doesn't burn a full lex/parse pass.
    content_hash: u64,
}

impl Clone for File {
    fn clone(&self) -> Self {
        // All Arc clones are pointer-bumps. The only "expensive" pieces are
        // the source TextDocument (which holds the buffer text) and the
        // diagnostic cache mutex contents.
        Self {
            source: self.source.clone(),
            tokens: self.tokens.clone(),
            core_ast: self.core_ast.clone(),
            parsed: self.parsed.clone(),
            type_check: self.type_check.clone(),
            definitions: self.definitions.clone(),
            signature_index: self.signature_index.clone(),
            ref_counts: self.ref_counts.clone(),
            impl_counts: self.impl_counts.clone(),
            base_diagnostics: self.base_diagnostics.clone(),
            parse_diagnostics_len: self.parse_diagnostics_len,
            cached_lsp_diagnostics: Mutex::new(
                self.cached_lsp_diagnostics.lock().unwrap().clone(),
            ),
            eager_type_check: self.eager_type_check,
            content_hash: self.content_hash,
        }
    }
}

impl File {
    #[cfg_attr(not(test), allow(dead_code))]
    pub fn new(source: String) -> Self {
        Self::new_with_type_check(source, true)
    }

    pub fn new_lazy(source: String) -> Self {
        Self::new_with_type_check(source, false)
    }

    fn new_with_type_check(source: String, eager_type_check: bool) -> Self {
        let mut f = Self {
            source: TextDocument::new(source),
            tokens: None,
            core_ast: None,
            parsed: None,
            type_check: None,
            definitions: Arc::new(HashMap::new()),
            signature_index: Arc::new(HashMap::new()),
            ref_counts: Arc::new(HashMap::new()),
            impl_counts: Arc::new(HashMap::new()),
            base_diagnostics: Arc::new(Vec::new()),
            parse_diagnostics_len: 0,
            cached_lsp_diagnostics: Mutex::new(None),
            eager_type_check,
            content_hash: 0,
        };
        f.parse();
        f
    }

    /// Test-only convenience: apply changes and reparse in one call.
    /// Production code (the `did_change` handler) splits this into
    /// `update_text` (under the state write lock) followed by `parse()`
    /// (off the lock) so other LSP requests aren't blocked while we lex.
    #[allow(dead_code)]
    pub fn update(&mut self, changes: Vec<TextDocumentContentChangeEvent>) {
        self.update_text(&changes);
        self.parse();
    }

    /// Apply text content changes without reparsing. The `did_change`
    /// handler uses this to keep the parse pass off the state write lock:
    /// it updates the source under the lock, then reparses a clone
    /// outside the lock and commits the result back.
    pub fn update_text(&mut self, changes: &[TextDocumentContentChangeEvent]) {
        for change in changes {
            self.source.update(change);
        }
    }

    pub fn parse(&mut self) {
        let text = self.source.text();
        let new_hash = content_hash(text);
        // Memoization: if the live source text is byte-identical to the
        // text we last parsed, all of the derived data on this `File` is
        // already correct. This catches typing+undo round-trips, ad-hoc
        // re-parses from `update()`, and (most importantly) lazy disk
        // file loads where the file content hasn't changed since the
        // workspace scan started. The hash check itself is one pass over
        // the text, which is still much cheaper than the full lex + AST
        // + index pipeline below.
        if self.content_hash != 0 && self.content_hash == new_hash {
            return;
        }
        self.content_hash = new_hash;
        *self.cached_lsp_diagnostics.lock().unwrap() = None;
        let result = sail_parser::lexer().parse(text);
        let lex_errors = result.errors().cloned().collect::<Vec<_>>();
        self.tokens = result.output().cloned().map(Arc::new);
        self.core_ast = self
            .tokens
            .as_deref()
            .and_then(|tokens| sail_parser::parse_core_source(tokens).into_output())
            .map(Arc::new);
        self.parsed = best_parsed(self.core_ast.as_deref()).map(Arc::new);
        self.type_check = self
            .eager_type_check
            .then(|| crate::typecheck::check_file(self))
            .flatten()
            .map(Arc::new);

        let mut definitions = HashMap::with_capacity(self.definitions.len());
        let parse_diagnostics = compute_parse_diagnostics(self, &lex_errors);

        if let Some(parsed) = self.parsed.as_deref() {
            add_parsed_definitions(parsed, &mut definitions);
        }

        self.definitions = Arc::new(definitions);
        self.signature_index = Arc::new(crate::symbols::build_signature_index(self));
        self.build_count_caches();
        // Record where parse diagnostics end and semantic diagnostics begin so
        // `recompute_diagnostics_with_workspace` can later append workspace-
        // aware semantic diagnostics without rerunning the parse pass. We
        // intentionally skip running single-file semantic diagnostics here:
        // the workspace-aware worker thread will compute them shortly and
        // its result strictly subsumes the local-only version. For files
        // that the worker never picks up (e.g. lazy disk files) callers can
        // still get single-file diagnostics by invoking
        // `compute_local_semantic_diagnostics` explicitly.
        self.parse_diagnostics_len = parse_diagnostics.len();
        if self.eager_type_check {
            // Eager-typecheck files (the unit-test path) don't go through
            // the debounced worker, so we have to run semantic diagnostics
            // inline to keep their behaviour identical to before.
            let mut diagnostics = parse_diagnostics;
            diagnostics.extend(compute_semantic_diagnostics(self));
            self.base_diagnostics = Arc::new(diagnostics);
        } else {
            self.base_diagnostics = Arc::new(parse_diagnostics);
        }
    }

    /// Force a single-file semantic diagnostic pass and store the result.
    /// Used by callers that need diagnostics outside the workspace-aware
    /// worker pipeline (e.g. lazy disk files surfaced via the document
    /// diagnostic LSP request before the workspace scan completes).
    #[allow(dead_code)]
    pub fn ensure_local_semantic_diagnostics(&mut self) {
        if self.parse_diagnostics_len < self.base_diagnostics.len() {
            // Already populated.
            return;
        }
        let semantic = compute_semantic_diagnostics(self);
        if semantic.is_empty() {
            return;
        }
        let diags = Arc::make_mut(&mut self.base_diagnostics);
        diags.extend(semantic);
        *self.cached_lsp_diagnostics.lock().unwrap() = None;
    }

    /// Re-run semantic diagnostics and typecheck with workspace context. Call
    /// this after `parse_and_check` once all files in the workspace have been
    /// parsed, so cross-file references can be resolved.
    ///
    /// `workspace_complete` should be `true` only when the caller is sure
    /// `all_files` represents the entire workspace. If it's `false`, the
    /// strict unresolved-identifier check is suppressed because we'd
    /// otherwise flag every cross-file reference when racing the disk scan.
    pub fn recompute_diagnostics_with_workspace<'a, I>(
        &mut self,
        all_files: I,
        workspace_complete: bool,
        cancel: crate::typecheck::CancellationToken,
    ) where
        I: IntoIterator<Item = &'a File> + Clone,
    {
        // Recompute typecheck with workspace env so cross-file types resolve.
        let new_type_check = crate::typecheck::check_file_with_workspace(
            self,
            all_files.clone(),
            workspace_complete,
            cancel,
        );

        // Recompute semantic diagnostics with cross-file enum member context.
        let semantic_diags =
            crate::diagnostics::semantic::compute_semantic_diagnostics_with_workspace(
                self, all_files,
            );

        // Replace just the semantic portion of base_diagnostics, preserving
        // the parse diagnostics produced earlier. `Arc::make_mut` clones
        // the inner Vec only if it's currently shared with a snapshot held
        // by another thread; in the common case (we own the only ref) it's
        // a no-op pointer hand-over.
        {
            let diags = Arc::make_mut(&mut self.base_diagnostics);
            diags.truncate(self.parse_diagnostics_len);
            diags.extend(semantic_diags);
        }

        *self.cached_lsp_diagnostics.lock().unwrap() = None;
        self.type_check = new_type_check.map(Arc::new);
    }

    fn build_count_caches(&mut self) {
        // Build into fresh maps and atomically swap so we never expose
        // half-rebuilt state to a concurrent reader holding a clone.
        let mut ref_counts: HashMap<String, usize> = HashMap::new();
        let mut impl_counts: HashMap<String, usize> = HashMap::new();
        if let Some(parsed) = self.parsed.as_deref() {
            for occurrence in &parsed.symbol_occurrences {
                if occurrence.role.is_some()
                    || occurrence.scope != Some(sail_parser::Scope::TopLevel)
                {
                    continue;
                }
                *ref_counts.entry(occurrence.name.clone()).or_insert(0) += 1;
            }
            for decl in &parsed.decls {
                if decl.role != sail_parser::DeclRole::Definition
                    || decl.scope != sail_parser::Scope::TopLevel
                {
                    continue;
                }
                if matches!(
                    decl.kind,
                    sail_parser::DeclKind::Function
                        | sail_parser::DeclKind::Mapping
                        | sail_parser::DeclKind::Overload
                ) {
                    *impl_counts.entry(decl.name.clone()).or_insert(0) += 1;
                }
            }
        }
        self.ref_counts = Arc::new(ref_counts);
        self.impl_counts = Arc::new(impl_counts);
    }

    /// Content hash of the source text the cached parse data was built
    /// from. Used by the workspace context cache to dedup aggregation
    /// passes across files whose content hasn't changed.
    pub fn content_hash(&self) -> u64 {
        self.content_hash
    }

    pub fn parsed(&self) -> Option<&sail_parser::ParsedFile> {
        self.parsed.as_deref()
    }

    pub fn core_ast(&self) -> Option<&sail_parser::core_ast::SourceFile> {
        self.core_ast.as_deref()
    }

    pub fn type_check(&self) -> Option<&crate::typecheck::TypeCheckResult> {
        self.type_check.as_deref()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub fn compute_type_check(&self) -> Option<crate::typecheck::TypeCheckResult> {
        crate::typecheck::check_file(self)
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub fn set_type_check(&mut self, type_check: Option<crate::typecheck::TypeCheckResult>) {
        *self.cached_lsp_diagnostics.lock().unwrap() = None;
        self.type_check = type_check.map(Arc::new);
    }

    pub fn lsp_diagnostics(&self) -> Vec<LspDiagnostic> {
        let mut cache = self.cached_lsp_diagnostics.lock().unwrap();
        if let Some(ref cached) = *cache {
            return cached.clone();
        }
        let diagnostics: Vec<LspDiagnostic> = self
            .base_diagnostics
            .iter()
            .chain(
                self.type_check
                    .as_deref()
                    .into_iter()
                    .flat_map(|type_check| type_check.diagnostics().iter()),
            )
            .map(|d| d.to_proto())
            .collect();
        *cache = Some(diagnostics.clone());
        diagnostics
    }

    fn token_at_offset(
        tokens: &[(sail_parser::Token, sail_parser::Span)],
        offset: usize,
    ) -> Option<&(sail_parser::Token, sail_parser::Span)> {
        let token = tokens.binary_search_by(|(_, span)| {
            if span.start <= offset && offset < span.end {
                Ordering::Equal
            } else if span.start > offset {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        });
        token.ok().map(|i| &tokens[i])
    }

    pub fn token_at(&self, position: Position) -> Option<&(sail_parser::Token, sail_parser::Span)> {
        let offset = self.source.offset_at(&position);
        let tokens = self.tokens.as_deref()?;

        // LSP cursors are often reported at token boundaries; try exact offset first,
        // then the preceding byte to keep identifier-based features stable.
        Self::token_at_offset(tokens, offset).or_else(|| {
            offset
                .checked_sub(1)
                .and_then(|prev| Self::token_at_offset(tokens, prev))
        })
    }
}

#[cfg(test)]
mod tests {
    use super::best_parsed;
    use chumsky::Parser;

    #[test]
    fn builds_parsed_from_core_ast() {
        let source = "val f : bits('n) -> bits('n)\nfunction f(x) = x\n";
        let tokens = sail_parser::lexer().parse(source).into_result().unwrap();
        let core_ast = sail_parser::parse_core_source(&tokens)
            .into_result()
            .unwrap();

        let parsed = best_parsed(Some(&core_ast)).expect("parsed");
        assert_eq!(parsed, sail_parser::ParsedFile::from_core_ast(&core_ast));
    }

    #[test]
    fn returns_none_without_core_ast() {
        assert!(best_parsed(None).is_none());
    }

    #[test]
    fn lazy_files_skip_eager_type_check() {
        let source = "function id(x) = x\n";
        let file = super::File::new_lazy(source.to_string());

        assert!(file.parsed().is_some());
        assert!(file.type_check().is_none());
    }

    #[test]
    fn lazy_type_check_results_extend_diagnostics() {
        let source = "function f(x : bits(32)) -> int = x\n";
        let mut file = super::File::new_lazy(source.to_string());

        assert!(file.lsp_diagnostics().iter().all(|diagnostic| diagnostic
            .code
            .as_ref()
            .map(|code| format!("{code:?}"))
            != Some("String(\"type-error\")".to_string())));

        let result = file.clone().compute_type_check();
        file.set_type_check(result);

        assert!(file.lsp_diagnostics().iter().any(|diagnostic| diagnostic
            .code
            .as_ref()
            .map(|code| format!("{code:?}"))
            == Some("String(\"type-error\")".to_string())));
    }
}
