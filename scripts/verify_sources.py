#!/usr/bin/env python3
"""Verify checksums of verbatim copied v9 and post-v9 sources."""
from pathlib import Path
import json
import hashlib
import sys

root = Path(__file__).resolve().parents[1]
expected = json.loads((root / 'provenance/SOURCE_SHA256.json').read_text())
problems = []
for item in expected['files']:
    file = root / item['path']
    if not file.is_file():
        problems.append('MISSING: ' + item['path'])
        continue
    actual = hashlib.sha256(file.read_bytes()).hexdigest()
    if actual != item['sha256']:
        problems.append('MISMATCH: ' + item['path'])
if problems:
    print(chr(10).join(problems))
    sys.exit(1)
print(f"Source integrity PASS: {len(expected['files'])} preserved files match original hashes.")
