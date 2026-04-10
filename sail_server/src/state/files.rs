// Disk-resident file index. The workspace scan walks every project folder
// and discovers `.sail` files; the *contents* of those files are loaded
// and parsed lazily on first read so that opening a 158-file workspace
// like sail-riscv only pays for the files actually touched by the user.
//
// Each disk slot uses `OnceLock<File>` so that:
//   - reads are `&self` and return `Option<&File>` (no API churn)
//   - the parse only happens once per file even if multiple threads ask
//     for the same URI concurrently
//   - once loaded, the `File` lives at a stable address so callers can
//     hold borrows across the rest of the request without copying

use super::File;
use std::{
    collections::{HashMap, HashSet},
    fs,
    sync::OnceLock,
};
use tower_lsp::lsp_types::Url;
use walkdir::WalkDir;

struct DiskFileSlot {
    path: std::path::PathBuf,
    file: OnceLock<File>,
}

impl DiskFileSlot {
    fn loaded(file: File) -> Self {
        let cell = OnceLock::new();
        let _ = cell.set(file);
        Self {
            path: std::path::PathBuf::new(),
            file: cell,
        }
    }

    fn unloaded(path: std::path::PathBuf) -> Self {
        Self {
            path,
            file: OnceLock::new(),
        }
    }

    fn get(&self) -> Option<&File> {
        if self.file.get().is_none() {
            if let Some(f) = load_file_from_disk(&self.path) {
                // Best-effort: another thread may have raced ahead.
                let _ = self.file.set(f);
            }
        }
        self.file.get()
    }
}

#[derive(Default)]
pub struct Files {
    folders: HashSet<Url>,
    files: HashMap<Url, DiskFileSlot>,
}

/// Result of a workspace scan: just the list of discovered URI → path
/// pairs. Files are not read or parsed at this point.
pub fn scan_folders(folders: HashSet<Url>) -> HashMap<Url, std::path::PathBuf> {
    let mut out = HashMap::new();

    for folder in folders {
        if folder.scheme() != "file" {
            continue;
        }
        let Ok(folder_path) = folder.to_file_path() else {
            continue;
        };
        for entry in WalkDir::new(&folder_path) {
            let Ok(entry) = entry else {
                continue;
            };
            if !entry.file_type().is_file()
                || entry.path().extension() != Some("sail".as_ref())
            {
                continue;
            }
            let path = entry.path();
            let Some(path_str) = path.to_str() else {
                eprintln!("Error converting path to string: {}", path.display());
                continue;
            };
            let mut url = folder.clone();
            // TODO: hack around Windows paths + servo/rust-url#864.
            let mut path_windows = path_str.replace('\\', "/");
            if !path_windows.starts_with('/') {
                path_windows.insert(0, '/');
            }
            url.set_path(&path_windows);
            out.insert(url, path.to_path_buf());
        }
    }

    out
}

/// Read + parse a disk file on demand. Returns `None` on I/O error.
fn load_file_from_disk(path: &std::path::Path) -> Option<File> {
    match fs::read_to_string(path) {
        Ok(source) => Some(File::new_lazy(source)),
        Err(e) => {
            eprintln!("Error reading file {}: {:?}", path.display(), e);
            None
        }
    }
}

impl Files {
    pub fn add_folder(&mut self, folder: Url) {
        self.folders.insert(folder);
    }

    pub fn remove_folder(&mut self, folder: &Url) {
        self.folders.remove(folder);
    }

    pub fn add_file(&mut self, url: Url, file: File) {
        self.files.insert(url, DiskFileSlot::loaded(file));
    }

    pub fn remove_file(&mut self, url: &Url) {
        self.files.remove(url);
    }

    /// Iterator over every known disk file. Each `(&Url, &File)` pair
    /// triggers a lazy parse the first time it's accessed; subsequent
    /// iterations reuse the cached parse via `OnceLock`.
    pub fn all_files(&self) -> impl Iterator<Item = (&Url, &File)> {
        self.files
            .iter()
            .filter_map(|(uri, slot)| slot.get().map(|f| (uri, f)))
    }

    pub fn get_file(&self, url: &Url) -> Option<&File> {
        self.files.get(url)?.get()
    }

    /// Replace the disk file index with a fresh path-only inventory.
    /// Files are not read until they're touched via `get_file` or
    /// `all_files`.
    pub fn update(&mut self, paths: HashMap<Url, std::path::PathBuf>) {
        self.files = paths
            .into_iter()
            .map(|(url, path)| (url, DiskFileSlot::unloaded(path)))
            .collect();
    }

    pub fn folders(&self) -> &HashSet<Url> {
        &self.folders
    }
}
