#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "$0")"
lake="${PM_FRAMEWORK_LAKE_BIN:-lake}"
"$lake" build
"$lake" env lean Audit.lean
