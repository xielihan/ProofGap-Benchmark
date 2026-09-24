import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1163

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x * Real.log x

theorem gap1 (x : ℝ) (hx : 0 < x) :
    deriv y x = 1 + Real.log x := by
  unfold y
  convert
    ((hasDerivAt_id x).mul (Real.hasDerivAt_log hx.ne')).deriv
    using 1 <;>
      simp only [id_eq] <;>
      field_simp [hx.ne'] <;>
      ring

theorem gap2 (x : ℝ) (hx : 0 < x) :
    nthDeriv 2 y x = 1 / x := by
  change deriv (deriv y) x = 1 / x
  have heq :
      deriv y =ᶠ[nhds x] (fun z : ℝ => 1 + Real.log z) := by
    exact Filter.mem_of_superset (Ioi_mem_nhds hx)
      (fun z hz => gap1 z hz)
  rw [heq.deriv_eq]
  simpa [one_div] using
    ((hasDerivAt_const x (1 : ℝ)).add
      (Real.hasDerivAt_log hx.ne')).deriv

theorem gap3 (x : ℝ) (hx : 0 < x) :
    nthDeriv 5 y x =
      -((Nat.factorial 3 : ℕ) : ℝ) / x ^ 4 := by
  have hd3 : ∀ z : ℝ, 0 < z → nthDeriv 3 y z = -1 / z ^ 2 := by
    intro z hz
    change deriv (nthDeriv 2 y) z = _
    have heq :
        nthDeriv 2 y =ᶠ[nhds z] (fun t : ℝ => 1 / t) := by
      exact Filter.mem_of_superset (Ioi_mem_nhds hz)
        (fun t ht => gap2 t ht)
    rw [heq.deriv_eq]
    have hderiv :
        HasDerivAt (fun t : ℝ => 1 / t) (-1 / z ^ 2) z := by
      convert
        (hasDerivAt_const z (1 : ℝ)).div (hasDerivAt_id z) hz.ne'
        using 1 <;>
          simp only [id_eq, Pi.pow_apply] <;>
          field_simp [hz.ne'] <;>
          ring_nf
    exact hderiv.deriv
  have hd4 : ∀ z : ℝ, 0 < z → nthDeriv 4 y z = 2 / z ^ 3 := by
    intro z hz
    change deriv (nthDeriv 3 y) z = _
    have heq :
        nthDeriv 3 y =ᶠ[nhds z] (fun t : ℝ => -1 / t ^ 2) := by
      exact Filter.mem_of_superset (Ioi_mem_nhds hz)
        (fun t ht => hd3 t ht)
    rw [heq.deriv_eq]
    have hderiv :
        HasDerivAt (fun t : ℝ => -1 / t ^ 2) (2 / z ^ 3) z := by
      convert
        (hasDerivAt_const z (-1 : ℝ)).div
          ((hasDerivAt_id z).pow 2) (pow_ne_zero 2 hz.ne')
        using 1 <;>
          simp only [id_eq, Pi.pow_apply] <;>
          field_simp [hz.ne'] <;>
          ring_nf
    exact hderiv.deriv
  have hd5 : ∀ z : ℝ, 0 < z → nthDeriv 5 y z = -6 / z ^ 4 := by
    intro z hz
    change deriv (nthDeriv 4 y) z = _
    have heq :
        nthDeriv 4 y =ᶠ[nhds z] (fun t : ℝ => 2 / t ^ 3) := by
      exact Filter.mem_of_superset (Ioi_mem_nhds hz)
        (fun t ht => hd4 t ht)
    rw [heq.deriv_eq]
    have hderiv :
        HasDerivAt (fun t : ℝ => 2 / t ^ 3) (-6 / z ^ 4) z := by
      convert
        (hasDerivAt_const z (2 : ℝ)).div
          ((hasDerivAt_id z).pow 3) (pow_ne_zero 3 hz.ne')
        using 1 <;>
          simp only [id_eq, Pi.pow_apply] <;>
          field_simp [hz.ne'] <;>
          ring_nf
    exact hderiv.deriv
  simpa [Nat.factorial] using hd5 x hx

end

end ProofGap.Exercise1163
