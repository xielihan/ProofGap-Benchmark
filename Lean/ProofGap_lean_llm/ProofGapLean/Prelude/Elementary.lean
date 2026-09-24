import ProofGapLean.Prelude.Core
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Data.Real.Sign
import Mathlib.Data.Real.Sqrt

/-! Elementary real functions used by the translated exercises. -/

/- `Real.cbrt` is not provided by this Mathlib release.  The translated
exercises only use it on nonnegative inputs, where real `rpow` is the intended
cube-root semantics. -/
noncomputable def Real.cbrt (x : ℝ) : ℝ :=
  Real.rpow x (1 / 3 : ℝ)
