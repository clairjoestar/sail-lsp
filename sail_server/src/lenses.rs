use crate::analysis::{extract_symbol_decls, is_definition_at, token_symbol_key};
use crate::file::File;
use std::collections::HashMap;
use tower_lsp::lsp_types::{CodeLens, Range, SymbolKind, Url};

pub(crate) fn collect_reference_counts(files: &[(&Url, &File)]) -> HashMap<String, usize> {
    let mut counts = HashMap::<String, usize>::new();
    for (_, file) in files {
        let Some(tokens) = file.tokens.as_ref() else {
            continue;
        };
        for (token, span) in tokens {
            let Some(key) = token_symbol_key(token) else {
                continue;
            };
            if !key.starts_with('\'') && is_definition_at(file, &key, span.start) {
                continue;
            }
            *counts.entry(key).or_insert(0) += 1;
        }
    }
    counts
}

pub(crate) fn collect_implementation_counts(files: &[(&Url, &File)]) -> HashMap<String, usize> {
    let mut counts = HashMap::<String, usize>::new();
    for (_, file) in files {
        let Some(tokens) = file.tokens.as_ref() else {
            continue;
        };
        let mut i = 0usize;
        while i + 1 < tokens.len() {
            let (tok0, tok1) = (&tokens[i].0, &tokens[i + 1].0);
            let name = match (tok0, tok1) {
                (sail_parser::Token::KwFunction, sail_parser::Token::Id(n))
                | (sail_parser::Token::KwMapping, sail_parser::Token::Id(n))
                | (sail_parser::Token::KwOverload, sail_parser::Token::Id(n)) => Some(n.clone()),
                (sail_parser::Token::KwFunction, sail_parser::Token::KwClause)
                | (sail_parser::Token::KwMapping, sail_parser::Token::KwClause)
                    if i + 2 < tokens.len() =>
                {
                    match &tokens[i + 2].0 {
                        sail_parser::Token::Id(n) => Some(n.clone()),
                        _ => None,
                    }
                }
                _ => None,
            };
            if let Some(name) = name {
                *counts.entry(name).or_insert(0) += 1;
            }
            i += 1;
        }
    }
    counts
}

fn pluralize(count: usize, singular: &str, plural: &str) -> String {
    if count == 1 {
        format!("{count} {singular}")
    } else {
        format!("{count} {plural}")
    }
}

pub(crate) fn code_lens_title(data: &serde_json::Value) -> Option<String> {
    let kind = data.get("kind")?.as_str()?;
    let count = data
        .get("count")
        .and_then(|v| v.as_u64())
        .map(|n| n as usize)
        .unwrap_or(0);
    match kind {
        "refs" => Some(pluralize(count, "reference", "references")),
        "impls" => Some(pluralize(count, "implementation", "implementations")),
        _ => None,
    }
}

pub(crate) fn code_lenses_for_file(
    file: &File,
    ref_counts: &HashMap<String, usize>,
    impl_counts: &HashMap<String, usize>,
) -> Vec<CodeLens> {
    let mut out = Vec::new();

    for decl in extract_symbol_decls(file) {
        if decl.detail == "binding" || decl.kind == SymbolKind::ENUM_MEMBER {
            continue;
        }
        let range = Range::new(
            file.source.position_at(decl.offset),
            file.source.position_at(decl.offset + decl.name.len()),
        );
        let refs = ref_counts.get(&decl.name).copied().unwrap_or(0);
        out.push(CodeLens {
            range,
            command: None,
            data: Some(serde_json::json!({
                "kind": "refs",
                "name": decl.name,
                "count": refs
            })),
        });

        if decl.kind == SymbolKind::FUNCTION {
            let impls = impl_counts.get(&decl.name).copied().unwrap_or(0);
            out.push(CodeLens {
                range,
                command: None,
                data: Some(serde_json::json!({
                    "kind": "impls",
                    "name": decl.name,
                    "count": impls
                })),
            });
        }
    }

    out
}
