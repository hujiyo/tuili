# 本地检查：Rust 格式、clippy、测试。任一步失败，脚本以非零码退出。
# 用法：pwsh -NoProfile -File scripts/check.ps1
$ErrorActionPreference = 'Stop'

Set-Location (Split-Path -Parent $PSScriptRoot)

Write-Host '==> cargo fmt --check'
cargo fmt --check
if ($LASTEXITCODE -ne 0) {
    throw 'cargo fmt --check 未通过：先运行 cargo fmt'
}

Write-Host '==> cargo clippy --workspace --all-targets -- -D warnings'
cargo clippy --workspace --all-targets -- -D warnings
if ($LASTEXITCODE -ne 0) {
    throw 'cargo clippy 未通过：修掉警告，不要用 #[allow] 压掉'
}

Write-Host '==> cargo test --workspace'
cargo test --workspace
if ($LASTEXITCODE -ne 0) {
    throw 'cargo test 未通过'
}

Write-Host 'OK: fmt / clippy / test 全部通过' -ForegroundColor Green
