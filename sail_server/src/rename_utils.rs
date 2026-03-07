use tower_lsp::jsonrpc::Result;

fn is_identifier_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'?' | b'\'' | b'~')
}

fn is_valid_identifier_name(name: &str) -> bool {
    let mut chars = name.chars();
    let Some(first) = chars.next() else {
        return false;
    };
    if !(first.is_ascii_alphabetic() || first == '_') {
        return false;
    }
    chars.all(|ch| ch.is_ascii() && is_identifier_byte(ch as u8))
}

pub(crate) fn normalize_validated_rename(
    token: &sail_parser::Token,
    requested_name: &str,
    keywords: &[&str],
) -> Result<Option<String>> {
    let (base_name, quoted) = if let Some(stripped) = requested_name.strip_prefix('\'') {
        (stripped, true)
    } else {
        (requested_name, false)
    };
    if !is_valid_identifier_name(base_name) {
        return Err(tower_lsp::jsonrpc::Error::invalid_params(
            "new_name must be a valid identifier",
        ));
    }
    if keywords.iter().any(|kw| *kw == base_name) {
        return Err(tower_lsp::jsonrpc::Error::invalid_params(
            "new_name cannot be a Sail keyword",
        ));
    }

    match token {
        sail_parser::Token::TyVal(_) => {
            if quoted {
                Ok(Some(requested_name.to_string()))
            } else {
                Ok(Some(format!("'{base_name}")))
            }
        }
        _ if quoted => Err(tower_lsp::jsonrpc::Error::invalid_params(
            "type variable marker (') is only valid when renaming type variables",
        )),
        _ => Ok(Some(base_name.to_string())),
    }
}
