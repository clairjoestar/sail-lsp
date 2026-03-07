use crate::analysis::find_symbol_decl;
use crate::file::File;
use tower_lsp::lsp_types::{Hover, HoverContents, MarkupContent, MarkupKind, Url};

pub(crate) fn hover_for_symbol<'a, I>(
    files: I,
    current_uri: &Url,
    symbol_key: &str,
) -> Option<Hover>
where
    I: IntoIterator<Item = (&'a Url, &'a File)>,
{
    let mut definition: Option<(String, u32, u32, Option<String>)> = None;

    if !symbol_key.starts_with('\'') {
        for (candidate_uri, candidate_file) in files {
            if let Some(offset) = candidate_file.definitions.get(symbol_key).copied() {
                let pos = candidate_file.source.position_at(offset);
                let decl_line = find_symbol_decl(candidate_file, symbol_key)
                    .map(|decl| format!("{} {}", decl.detail, decl.name));
                definition = Some((
                    candidate_uri.path().to_string(),
                    pos.line + 1,
                    pos.character + 1,
                    decl_line,
                ));
                if candidate_uri == current_uri {
                    break;
                }
            }
        }
    }

    let mut lines = Vec::new();
    if let Some((path, line, character, decl_line)) = definition {
        if let Some(decl_line) = decl_line {
            lines.push(format!("```sail\n{}\n```", decl_line));
        } else {
            lines.push(format!("```sail\n{}\n```", symbol_key));
        }
        lines.push(format!("Defined at `{}`:{}:{}", path, line, character));
    } else {
        lines.push(format!("```sail\n{}\n```", symbol_key));
    }

    Some(Hover {
        contents: HoverContents::Markup(MarkupContent {
            kind: MarkupKind::Markdown,
            value: lines.join("\n\n"),
        }),
        range: None,
    })
}
