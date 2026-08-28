/-
# Esa22Copy

Root module. Importing `Esa22Copy` must pull in the headline theorem, so that
`import Esa22Copy` and a bare `lake build` both compile *and expose* the result.

Keep this file a pure aggregation of area roots — put content in the modules.
-/

import Esa22Copy.Model.Theorem

/-
The running time in *word* operations, which needs a rate for the sample-set
implementation and so is a separate claim from the paper-facing ones.  The
running time in dictionary operations is `Model.Theorem.esa22CopyTime`.
-/
import Esa22Copy.Analysis.TimeBoundRam
