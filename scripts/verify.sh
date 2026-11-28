#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
python3 -m unittest discover -s tests
python3 verso/check_translation.py
for asset in composer reader study study-math workbook; do
  node --check "verso/static/$asset.js"
done
python3 scripts/check_workflow_locks.py
if [[ "${1:-}" == "--automation-only" ]]; then
  exit 0
fi
python3 verso/build_site.py
python3 verso/check_study.py
