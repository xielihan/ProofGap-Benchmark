import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1164

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := Real.log x / x
def raw2 (x : ℝ) : ℝ :=
  (-(1 / x) * x ^ 2 - 2 * x * (1 - Real.log x)) / x ^ 4
def raw3 (x : ℝ) : ℝ :=
  -((-(2 / x) * x ^ 3 - 3 * x ^ 2 * (3 - 2 * Real.log x)) / x ^ 6)
def raw4 (x : ℝ) : ℝ :=
  (-(6 / x) * x ^ 4 - 4 * x ^ 3 * (11 - 6 * Real.log x)) / x ^ 8
def raw5 (x : ℝ) : ℝ :=
  -((-(24 / x) * x ^ 5 - 5 * x ^ 4 * (50 - 24 * Real.log x)) / x ^ 10)

private theorem deriv_congr_of_pos {f g : ℝ → ℝ} {x : ℝ}
    (hx : 0 < x) (h : ∀ z, 0 < z → f z = g z) :
    deriv f x = deriv g x := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [Ioi_mem_nhds hx] with z hz
  exact h z hz

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = (1 - Real.log x) / x ^ 2 := by
  unfold y
  have h :=
    (Real.hasDerivAt_log hx.ne').div (hasDerivAt_id x) hx.ne'
  have hd :
      deriv (fun z : ℝ => Real.log z / z) x =
        (x⁻¹ * x - Real.log x) / x ^ 2 := by
    simpa only [id_eq, mul_one] using h.deriv
  calc
    deriv (fun z : ℝ => Real.log z / z) x =
        (x⁻¹ * x - Real.log x) / x ^ 2 := hd
    _ = (1 - Real.log x) / x ^ 2 := by
      simp [hx.ne']
theorem gap2 (x : ℝ) (hx : 0 < x) : nthDeriv 2 y x = raw2 x := by
  change deriv (deriv y) x = raw2 x
  calc
    deriv (deriv y) x =
        deriv (fun z : ℝ => (1 - Real.log z) / z ^ 2) x := by
      exact deriv_congr_of_pos hx (fun z hz => gap1 z hz)
    _ = raw2 x := by
      have h :=
        ((hasDerivAt_const x (1 : ℝ)).sub
          (Real.hasDerivAt_log hx.ne')).div
          ((hasDerivAt_id x).pow 2) (pow_ne_zero 2 hx.ne')
      convert h.deriv using 1 <;>
        dsimp [raw2] <;>
        field_simp [hx.ne'] <;>
        ring
theorem gap3 (x : ℝ) (hx : 0 < x) :
    raw2 x = -(3 - 2 * Real.log x) / x ^ 3 := by
  unfold raw2
  field_simp [hx.ne'] <;>
    ring
theorem gap4 (x : ℝ) (hx : 0 < x) :
    nthDeriv 2 y x = -(3 - 2 * Real.log x) / x ^ 3 := by
  calc
    nthDeriv 2 y x = raw2 x := gap2 x hx
    _ = -(3 - 2 * Real.log x) / x ^ 3 := gap3 x hx
theorem gap5 (x : ℝ) (hx : 0 < x) : nthDeriv 3 y x = raw3 x := by
  change deriv (nthDeriv 2 y) x = raw3 x
  calc
    deriv (nthDeriv 2 y) x =
        deriv (fun z : ℝ => -(3 - 2 * Real.log z) / z ^ 3) x := by
      exact deriv_congr_of_pos hx (fun z hz => gap4 z hz)
    _ = raw3 x := by
      have hnum :=
        ((hasDerivAt_const x (3 : ℝ)).sub
          ((hasDerivAt_const x (2 : ℝ)).mul
            (Real.hasDerivAt_log hx.ne'))).neg
      have h :=
        hnum.div ((hasDerivAt_id x).pow 3) (pow_ne_zero 3 hx.ne')
      convert h.deriv using 1 <;>
        dsimp [raw3] <;>
        field_simp [hx.ne'] <;>
        ring
theorem gap6 (x : ℝ) (hx : 0 < x) :
    raw3 x = (11 - 6 * Real.log x) / x ^ 4 := by
  unfold raw3
  field_simp [hx.ne'] <;>
    ring
theorem gap7 (x : ℝ) (hx : 0 < x) :
    nthDeriv 3 y x = (11 - 6 * Real.log x) / x ^ 4 := by
  calc
    nthDeriv 3 y x = raw3 x := gap5 x hx
    _ = (11 - 6 * Real.log x) / x ^ 4 := gap6 x hx
theorem gap8 (x : ℝ) (hx : 0 < x) : nthDeriv 4 y x = raw4 x := by
  change deriv (nthDeriv 3 y) x = raw4 x
  calc
    deriv (nthDeriv 3 y) x =
        deriv (fun z : ℝ => (11 - 6 * Real.log z) / z ^ 4) x := by
      exact deriv_congr_of_pos hx (fun z hz => gap7 z hz)
    _ = raw4 x := by
      have hnum :=
        (hasDerivAt_const x (11 : ℝ)).sub
          ((hasDerivAt_const x (6 : ℝ)).mul
            (Real.hasDerivAt_log hx.ne'))
      have h :=
        hnum.div ((hasDerivAt_id x).pow 4) (pow_ne_zero 4 hx.ne')
      convert h.deriv using 1 <;>
        dsimp [raw4] <;>
        field_simp [hx.ne'] <;>
        ring
theorem gap9 (x : ℝ) (hx : 0 < x) :
    raw4 x = -(50 - 24 * Real.log x) / x ^ 5 := by
  unfold raw4
  field_simp [hx.ne'] <;>
    ring
theorem gap10 (x : ℝ) (hx : 0 < x) :
    nthDeriv 4 y x = -(50 - 24 * Real.log x) / x ^ 5 := by
  calc
    nthDeriv 4 y x = raw4 x := gap8 x hx
    _ = -(50 - 24 * Real.log x) / x ^ 5 := gap9 x hx
theorem gap11 (x : ℝ) (hx : 0 < x) : nthDeriv 5 y x = raw5 x := by
  change deriv (nthDeriv 4 y) x = raw5 x
  calc
    deriv (nthDeriv 4 y) x =
        deriv (fun z : ℝ => -(50 - 24 * Real.log z) / z ^ 5) x := by
      exact deriv_congr_of_pos hx (fun z hz => gap10 z hz)
    _ = raw5 x := by
      have hnum :=
        ((hasDerivAt_const x (50 : ℝ)).sub
          ((hasDerivAt_const x (24 : ℝ)).mul
            (Real.hasDerivAt_log hx.ne'))).neg
      have h :=
        hnum.div ((hasDerivAt_id x).pow 5) (pow_ne_zero 5 hx.ne')
      convert h.deriv using 1 <;>
        dsimp [raw5] <;>
        field_simp [hx.ne'] <;>
        ring
theorem gap12 (x : ℝ) (hx : 0 < x) :
    raw5 x = (274 - 120 * Real.log x) / x ^ 6 := by
  unfold raw5
  field_simp [hx.ne'] <;>
    ring
theorem gap13 (x : ℝ) (hx : 0 < x) :
    nthDeriv 5 y x = (274 - 120 * Real.log x) / x ^ 6 := by
  calc
    nthDeriv 5 y x = raw5 x := gap11 x hx
    _ = (274 - 120 * Real.log x) / x ^ 6 := gap12 x hx

end

end ProofGap.Exercise1164
