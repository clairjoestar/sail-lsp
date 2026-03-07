use crate::analysis::{collect_callable_signatures, function_snippet};
use crate::file::File;
use std::collections::{BTreeMap, HashMap};
use tower_lsp::lsp_types::{CompletionItem, CompletionItemKind, InsertTextFormat, Url};

#[derive(Clone)]
struct CompletionCandidate {
    kind: CompletionItemKind,
    detail: Option<String>,
    snippet: Option<String>,
}

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'?' | b'\'' | b'~')
}

pub(crate) fn completion_prefix(text: &str, offset: usize) -> &str {
    let offset = offset.min(text.len());
    let bytes = text.as_bytes();
    let mut start = offset;

    while start > 0 && is_identifier_byte(bytes[start - 1]) {
        start -= 1;
    }

    &text[start..offset]
}

pub(crate) fn completion_trigger_characters() -> Vec<String> {
    vec![
        ".".to_string(),
        ":".to_string(),
        "(".to_string(),
        "_".to_string(),
        "?".to_string(),
        "~".to_string(),
        "'".to_string(),
    ]
}

fn completion_kind_priority(kind: &CompletionItemKind) -> u8 {
    match kind {
        &CompletionItemKind::KEYWORD => 8,
        &CompletionItemKind::FUNCTION => 7,
        &CompletionItemKind::METHOD => 6,
        &CompletionItemKind::ENUM => 5,
        &CompletionItemKind::CLASS => 4,
        &CompletionItemKind::CONSTANT => 3,
        &CompletionItemKind::TYPE_PARAMETER => 2,
        &CompletionItemKind::VARIABLE => 1,
        _ => 0,
    }
}

fn upsert_candidate(
    candidates: &mut BTreeMap<String, CompletionCandidate>,
    label: String,
    candidate: CompletionCandidate,
) {
    match candidates.get(&label) {
        Some(existing)
            if completion_kind_priority(&existing.kind)
                >= completion_kind_priority(&candidate.kind) => {}
        _ => {
            candidates.insert(label, candidate);
        }
    }
}

fn completion_score(label: &str, prefix: &str) -> u8 {
    if prefix.is_empty() {
        return 0;
    }
    if label == prefix {
        return 0;
    }
    if label.starts_with(prefix) {
        return 1;
    }
    2
}

pub(crate) fn build_completion_items<'a, I>(
    files: I,
    prefix: &str,
    keywords: &[&str],
    builtins: &[&str],
) -> Vec<CompletionItem>
where
    I: IntoIterator<Item = (&'a Url, &'a File)>,
{
    let all_files = files.into_iter().collect::<Vec<_>>();
    let prefix_lower = prefix.to_ascii_lowercase();

    let mut candidates: BTreeMap<String, CompletionCandidate> = BTreeMap::new();
    let mut call_signatures: HashMap<String, Vec<String>> = HashMap::new();
    for (_, candidate_file) in &all_files {
        for sig in collect_callable_signatures(candidate_file) {
            call_signatures.entry(sig.name).or_insert(sig.params);
        }
    }

    for keyword in keywords {
        upsert_candidate(
            &mut candidates,
            (*keyword).to_string(),
            CompletionCandidate {
                kind: CompletionItemKind::KEYWORD,
                detail: Some("keyword".to_string()),
                snippet: None,
            },
        );
    }

    for builtin in builtins {
        let kind = if builtin
            .chars()
            .next()
            .is_some_and(|ch| ch.is_ascii_uppercase())
        {
            CompletionItemKind::CLASS
        } else {
            CompletionItemKind::CONSTANT
        };
        upsert_candidate(
            &mut candidates,
            (*builtin).to_string(),
            CompletionCandidate {
                kind,
                detail: Some("builtin".to_string()),
                snippet: None,
            },
        );
    }

    for (_, candidate_file) in &all_files {
        if let Some(tokens) = candidate_file.tokens.as_ref() {
            for decl in sail_parser::parse_tokens(tokens).decls {
                if decl.scope != sail_parser::Scope::TopLevel {
                    continue;
                }
                let (name, kind, detail) = match decl.kind {
                    sail_parser::DeclKind::Function => (
                        decl.name,
                        CompletionItemKind::FUNCTION,
                        Some("function".to_string()),
                    ),
                    sail_parser::DeclKind::Value => (
                        decl.name,
                        CompletionItemKind::FUNCTION,
                        Some("value specification".to_string()),
                    ),
                    sail_parser::DeclKind::Mapping => (
                        decl.name,
                        CompletionItemKind::FUNCTION,
                        Some("mapping".to_string()),
                    ),
                    sail_parser::DeclKind::Overload => (
                        decl.name,
                        CompletionItemKind::FUNCTION,
                        Some("overload".to_string()),
                    ),
                    sail_parser::DeclKind::Type
                    | sail_parser::DeclKind::Struct
                    | sail_parser::DeclKind::Union
                    | sail_parser::DeclKind::Bitfield
                    | sail_parser::DeclKind::Newtype => (
                        decl.name,
                        CompletionItemKind::CLASS,
                        Some("type".to_string()),
                    ),
                    sail_parser::DeclKind::Enum => (
                        decl.name,
                        CompletionItemKind::ENUM,
                        Some("enum".to_string()),
                    ),
                    sail_parser::DeclKind::Register => (
                        decl.name,
                        CompletionItemKind::VARIABLE,
                        Some("register".to_string()),
                    ),
                    _ => continue,
                };
                let snippet = if matches!(
                    kind,
                    CompletionItemKind::FUNCTION | CompletionItemKind::METHOD
                ) {
                    call_signatures
                        .get(&name)
                        .map(|params| function_snippet(&name, params))
                } else {
                    None
                };
                upsert_candidate(
                    &mut candidates,
                    name,
                    CompletionCandidate {
                        kind,
                        detail,
                        snippet,
                    },
                );
            }

            for (token, _) in tokens {
                match token {
                    sail_parser::Token::Id(name) => {
                        upsert_candidate(
                            &mut candidates,
                            name.clone(),
                            CompletionCandidate {
                                kind: CompletionItemKind::VARIABLE,
                                detail: Some("identifier".to_string()),
                                snippet: None,
                            },
                        );
                    }
                    sail_parser::Token::TyVal(name) => {
                        upsert_candidate(
                            &mut candidates,
                            format!("'{}", name),
                            CompletionCandidate {
                                kind: CompletionItemKind::TYPE_PARAMETER,
                                detail: Some("type parameter".to_string()),
                                snippet: None,
                            },
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    let mut items = candidates
        .into_iter()
        .filter_map(|(label, candidate)| {
            let label_lower = label.to_ascii_lowercase();
            let score = completion_score(&label_lower, &prefix_lower);
            if score >= 2 {
                return None;
            }

            Some((score, completion_kind_priority(&candidate.kind), {
                let insert_text_format = if candidate.snippet.is_some() {
                    InsertTextFormat::SNIPPET
                } else {
                    InsertTextFormat::PLAIN_TEXT
                };
                let detail = candidate
                    .detail
                    .clone()
                    .unwrap_or_else(|| "symbol".to_string());
                let kind_name = format!("{:?}", candidate.kind);
                CompletionItem {
                    label: label.clone(),
                    kind: Some(candidate.kind),
                    detail: candidate.detail,
                    filter_text: Some(label.clone()),
                    insert_text: Some(candidate.snippet.unwrap_or(label)),
                    insert_text_format: Some(insert_text_format),
                    data: Some(serde_json::json!({
                        "source": "sail-lsp",
                        "kind": kind_name,
                        "detail": detail,
                    })),
                    ..CompletionItem::default()
                }
            }))
        })
        .collect::<Vec<_>>();

    items.sort_by(
        |(score_a, priority_a, item_a), (score_b, priority_b, item_b)| {
            score_a
                .cmp(score_b)
                .then_with(|| priority_b.cmp(priority_a))
                .then_with(|| item_a.label.cmp(&item_b.label))
        },
    );

    const MAX_COMPLETIONS: usize = 200;
    if items.len() > MAX_COMPLETIONS {
        items.truncate(MAX_COMPLETIONS);
    }

    items
        .into_iter()
        .enumerate()
        .map(|(index, (_, _, mut item))| {
            item.sort_text = Some(format!("{index:04}_{}", item.label.to_ascii_lowercase()));
            item
        })
        .collect()
}

pub(crate) fn resolve_completion_item(mut item: CompletionItem) -> CompletionItem {
    if let Some(data) = &item.data {
        let kind = data
            .get("kind")
            .and_then(|v| v.as_str())
            .unwrap_or("SYMBOL");
        let detail = data
            .get("detail")
            .and_then(|v| v.as_str())
            .unwrap_or("Sail symbol");
        let doc = format!("`{}`\n\n{}", item.label, detail);
        item.documentation = Some(tower_lsp::lsp_types::Documentation::String(format!(
            "[{kind}] {doc}"
        )));
    } else if item.documentation.is_none() {
        item.documentation = Some(tower_lsp::lsp_types::Documentation::String(format!(
            "`{}`\n\nSail completion item",
            item.label
        )));
    }
    item
}
