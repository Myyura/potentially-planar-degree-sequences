#!/bin/sh
set -eu
root=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)

cd "$root/lean"
lake env lean --version
lake build SparseBoundary
lake env lean ../verification/Audit.lean

cd "$root/lean-eg"
lake build BoundaryCorollaries
lake env lean ../verification/AuditEG.lean
for module in AtlasEG BoundaryEG SparseInterior FullBoundary BoundaryCorollaries; do
  lake env leanchecker -v "$module"
done

cd "$root"
python3 verification/replay.py
