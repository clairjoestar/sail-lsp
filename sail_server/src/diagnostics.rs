use crate::file::File;
use std::collections::{hash_map::DefaultHasher, HashMap};
use std::hash::{Hash, Hasher};
use tower_lsp::lsp_types::{
    DocumentDiagnosticReport, DocumentDiagnosticReportResult, FullDocumentDiagnosticReport,
    RelatedFullDocumentDiagnosticReport, RelatedUnchangedDocumentDiagnosticReport,
    UnchangedDocumentDiagnosticReport, Url, WorkspaceDiagnosticReport,
    WorkspaceDiagnosticReportResult, WorkspaceDocumentDiagnosticReport,
    WorkspaceFullDocumentDiagnosticReport,
};

fn file_diagnostic_result_id(file: &File) -> String {
    let mut hasher = DefaultHasher::new();
    file.source.text().len().hash(&mut hasher);
    file.diagnostics.len().hash(&mut hasher);
    for diagnostic in &file.diagnostics {
        diagnostic.range.start.line.hash(&mut hasher);
        diagnostic.range.start.character.hash(&mut hasher);
        diagnostic.range.end.line.hash(&mut hasher);
        diagnostic.range.end.character.hash(&mut hasher);
        format!("{:?}", diagnostic.severity).hash(&mut hasher);
        diagnostic.code.hash(&mut hasher);
        diagnostic.source.hash(&mut hasher);
        diagnostic.message.hash(&mut hasher);
    }
    format!("{:x}", hasher.finish())
}

pub(crate) fn document_diagnostic_report_for_file(
    file: &File,
    previous_result_id: Option<&str>,
) -> DocumentDiagnosticReportResult {
    let result_id = file_diagnostic_result_id(file);
    if previous_result_id == Some(result_id.as_str()) {
        return DocumentDiagnosticReport::Unchanged(RelatedUnchangedDocumentDiagnosticReport {
            related_documents: None,
            unchanged_document_diagnostic_report: UnchangedDocumentDiagnosticReport { result_id },
        })
        .into();
    }

    DocumentDiagnosticReport::Full(RelatedFullDocumentDiagnosticReport {
        related_documents: None,
        full_document_diagnostic_report: FullDocumentDiagnosticReport {
            result_id: Some(result_id),
            items: file.diagnostics.clone(),
        },
    })
    .into()
}

pub(crate) fn workspace_diagnostic_report<'a, I>(
    files: I,
    versions: &HashMap<Url, i32>,
    previous_result_ids: &HashMap<Url, String>,
) -> WorkspaceDiagnosticReportResult
where
    I: IntoIterator<Item = (&'a Url, &'a File)>,
{
    let mut items = Vec::new();
    for (uri, file) in files {
        let result_id = file_diagnostic_result_id(file);
        let version = versions.get(uri).copied().map(i64::from);
        if previous_result_ids.get(uri).map(String::as_str) == Some(result_id.as_str()) {
            items.push(WorkspaceDocumentDiagnosticReport::Unchanged(
                tower_lsp::lsp_types::WorkspaceUnchangedDocumentDiagnosticReport {
                    uri: uri.clone(),
                    version,
                    unchanged_document_diagnostic_report: UnchangedDocumentDiagnosticReport {
                        result_id,
                    },
                },
            ));
        } else {
            items.push(WorkspaceDocumentDiagnosticReport::Full(
                WorkspaceFullDocumentDiagnosticReport {
                    uri: uri.clone(),
                    version,
                    full_document_diagnostic_report: FullDocumentDiagnosticReport {
                        result_id: Some(result_id),
                        items: file.diagnostics.clone(),
                    },
                },
            ));
        }
    }
    WorkspaceDiagnosticReport { items }.into()
}
