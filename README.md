# sail-lsp

Standalone Sail language server for editor integrations (stdio LSP).

- Repo: https://github.com/TinyuengKwan/sail-lsp
- Zed extension: https://github.com/TinyuengKwan/sail-zed

## Build locally

```bash
cargo build -p sail_server --release
```

Binary:

- `target/release/sail_server`

## Release binaries (GitHub Actions)

This repo publishes prebuilt binaries when you push a tag matching `v*`.

Workflow:

- file: `.github/workflows/release.yml`
- trigger: `git tag vX.Y.Z && git push origin vX.Y.Z`
- release assets:
  - `sail-lsp-x86_64-unknown-linux-gnu`
  - `sail-lsp-x86_64-apple-darwin`
  - `sail-lsp-aarch64-apple-darwin`
  - `sail-lsp-x86_64-pc-windows-msvc.exe`

## LSP features

Implemented features include diagnostics, completion, hover, signature help,
rename, references, semantic tokens, code actions, code lenses, formatting,
call/type hierarchy, symbols, and file-rename handling.
