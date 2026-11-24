#!/bin/sh
set -eu
paper=$(CDPATH='' cd -- "$(dirname -- "$0")/.." && pwd)
cd "$paper/.."

lake build
lake build sparse-boundary/SparseBoundary wagnerBridge/WagnerBridge
lake env lean "$paper/Audit.lean"
lake env lean "$paper/recognition/Audit.lean"
lake env lean "$paper/planarity/Audit.lean"
lake env lean "$paper/verification/Audit.lean"
lake env lean "$paper/verification/AuditEG.lean"

lake env leanchecker -v AtlasEG BoundaryEG SparseInterior FullBoundary BoundaryCorollaries
lake env leanchecker -v HardnessResult StellationResult EliminationResult PrescriptionCost UnaryHardness \
  TargetLanguagesResult TargetLanguagesWire TargetStackedBridge WireOutput \
  ListingResult CatalogueResult CompactBoundaryPrefix RowRecognition IntervalCosts \
  IntervalExamples FixedTypeLanguage StackedTableResult StackedCensus MidpointResult \
  WorkedMidpoint TraceDeterminant KirchhoffInput DiamondDeterminant EncodingExamples \
  FiniteRowChecksAtlas QuadraticTransfer CompactBoundaryMarks RawVerifierResult RawVerifierOrbit
lake env leanchecker -v RecognizingPotentiallyPlanarDegreeSequences
python3 "$paper/verification/replay.py" "$@"
