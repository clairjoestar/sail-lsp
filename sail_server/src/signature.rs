use crate::analysis::{find_call_at_position, find_callable_signature};
use crate::file::File;
use tower_lsp::lsp_types::{
    ParameterInformation, ParameterLabel, Position, SignatureHelp, SignatureInformation, Url,
};

pub(crate) fn signature_help_for_position<'a, I>(
    files: I,
    uri: &Url,
    file: &File,
    position: Position,
) -> Option<SignatureHelp>
where
    I: IntoIterator<Item = (&'a Url, &'a File)>,
{
    let (callee, arg_index) = find_call_at_position(file, position)?;
    let sig = find_callable_signature(files, uri, &callee)?;

    let active_parameter = arg_index
        .min(sig.params.len().saturating_sub(1))
        .try_into()
        .unwrap_or(0);

    let signature_information = SignatureInformation {
        label: sig.label,
        documentation: None,
        parameters: Some(
            sig.params
                .iter()
                .map(|param| ParameterInformation {
                    label: ParameterLabel::Simple(param.clone()),
                    documentation: None,
                })
                .collect(),
        ),
        active_parameter: Some(active_parameter),
    };

    Some(SignatureHelp {
        signatures: vec![signature_information],
        active_signature: Some(0),
        active_parameter: Some(active_parameter),
    })
}
