#!/usr/bin/env bash
set -euo pipefail
echo 'Lean and Mathlib 4.35.0 are pinned in lean-toolchain and lakefile.lean.'
echo 'Resolving transitive package dependencies; this writes lake-manifest.json.'
lake update
lake exe cache get
lake build
lake env lean TPCV9/StatementAudit.lean | tee lean_axioms.txt
python3 scripts/check_axiom_report.py lean_axioms.txt
python3 scripts/verify_sources.py
echo 'IMPORTANT: git add lake-manifest.json and commit it for exact transitive version pinning.'
