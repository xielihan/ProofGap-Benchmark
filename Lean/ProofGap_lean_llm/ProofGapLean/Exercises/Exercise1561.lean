import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1561

noncomputable section

def perimeter (S x : ℝ) : ℝ := 2 * (x + S / x)

def IsMinimizerOn (u : ℝ → ℝ) (s : Set ℝ) (x₀ : ℝ) : Prop :=
  x₀ ∈ s ∧ ∀ x ∈ s, u x₀ ≤ u x

private theorem hasDerivAt_const_div_id_pg1561 (S x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun z : ℝ => S / z) (-S / x ^ 2) x := by
  convert (hasDerivAt_const x S).div (hasDerivAt_id x) hx using 1 <;>
    simp only [id_eq] <;> ring

theorem gap1 (S x : ℝ) :
    perimeter S x = 2 * (x + S / x) := by
  rfl

theorem gap2 (S x : ℝ) (hx : x ≠ 0) :
    deriv (perimeter S) x = 2 * (1 - S / x ^ 2) := by
  have hperim :
      HasDerivAt (perimeter S) (2 * (1 - S / x ^ 2)) x := by
    unfold perimeter
    convert (hasDerivAt_const x (2 : ℝ)).mul
      ((hasDerivAt_id x).add
        (hasDerivAt_const_div_id_pg1561 S x hx)) using 1 <;>
      (try simp only [id_eq]) <;>
      ring
  exact hperim.deriv

theorem gap3 (S x : ℝ) (hS : 0 < S) (hx : 0 < x)
    (hcrit : deriv (perimeter S) x = 0) :
    x = Real.sqrt S := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hcrit' := hcrit
  rw [gap2 S x hx0] at hcrit'
  field_simp [hx0] at hcrit'
  have hxsq : x ^ 2 = S := by
    nlinarith [hcrit']
  have hsqrtsq : (Real.sqrt S) ^ 2 = S :=
    Real.sq_sqrt (le_of_lt hS)
  have hsqrtnonneg : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
  nlinarith [hxsq, hsqrtsq, hsqrtnonneg, sq_nonneg (x - Real.sqrt S)]

theorem gap4 (S x : ℝ) (hx : x ≠ 0) :
    deriv (deriv (perimeter S)) x = 4 * S / x ^ 3 := by
  have htwodiv :
      HasDerivAt (fun z : ℝ => S / z / z) (-2 * S / x ^ 3) x := by
    convert (hasDerivAt_const_div_id_pg1561 S x hx).div
      (hasDerivAt_id x) hx using 1 <;>
      simp only [id_eq] <;>
      field_simp [hx] <;> ring
  have hformula :
      HasDerivAt (fun z : ℝ => 2 * (1 - S / z / z))
        (4 * S / x ^ 3) x := by
    convert (hasDerivAt_const x (2 : ℝ)).mul
      ((hasDerivAt_const x (1 : ℝ)).sub htwodiv) using 1 <;>
      field_simp [hx] <;> ring
  have heq :
      (fun z : ℝ => deriv (perimeter S) z) =ᶠ[nhds x]
        (fun z : ℝ => 2 * (1 - S / z / z)) := by
    filter_upwards [eventually_ne_nhds hx] with z hz
    calc
      deriv (perimeter S) z = 2 * (1 - S / z ^ 2) := gap2 S z hz
      _ = 2 * (1 - S / z / z) := by
        field_simp [hz]
        <;> ring
  calc
    deriv (deriv (perimeter S)) x =
        deriv (fun z : ℝ => 2 * (1 - S / z / z)) x := heq.deriv_eq
    _ = 4 * S / x ^ 3 := hformula.deriv

theorem gap5 (S : ℝ) (hS : 0 < S) :
    0 < deriv (deriv (perimeter S)) (Real.sqrt S) := by
  have hsqrtpos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  rw [gap4 S (Real.sqrt S) (ne_of_gt hsqrtpos)]
  positivity

theorem gap6 (S : ℝ) (hS : 0 < S) :
    IsMinimizerOn (perimeter S) (Set.Ioi 0) (Real.sqrt S) := by
  have hrpos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hrne : Real.sqrt S ≠ 0 := ne_of_gt hrpos
  have hrsq : (Real.sqrt S) ^ 2 = S :=
    Real.sq_sqrt (le_of_lt hS)
  constructor
  · exact hrpos
  · intro y hy
    have hyne : y ≠ 0 := ne_of_gt hy
    have hnonneg : 0 ≤ (y - Real.sqrt S) ^ 2 / y :=
      div_nonneg (sq_nonneg (y - Real.sqrt S)) (le_of_lt hy)
    have hid :
        y + S / y - 2 * Real.sqrt S =
          (y - Real.sqrt S) ^ 2 / y := by
      field_simp [hyne]
      nlinarith [hrsq]
    have hamgm : 2 * Real.sqrt S ≤ y + S / y := by
      nlinarith [hnonneg, hid]
    have hrdiv : S / Real.sqrt S = Real.sqrt S := by
      apply (div_eq_iff hrne).2
      nlinarith [hrsq]
    unfold perimeter
    rw [hrdiv]
    nlinarith [hamgm]

theorem gap7 (S y : ℝ) (hS : 0 < S) (hy : 0 < y) :
    perimeter S (Real.sqrt S) ≤ perimeter S y := by
  exact (gap6 S hS).2 y hy

theorem gap8 (S : ℝ) (hS : 0 < S) :
    ∃ x > 0, x = Real.sqrt S ∧
      ∀ y > 0, perimeter S x ≤ perimeter S y := by
  refine ⟨Real.sqrt S, Real.sqrt_pos.2 hS, rfl, ?_⟩
  intro y hy
  exact gap7 S y hS hy

end

end ProofGap.Exercise1561
