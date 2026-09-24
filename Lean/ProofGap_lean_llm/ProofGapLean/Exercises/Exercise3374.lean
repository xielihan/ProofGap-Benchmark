import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3374

noncomputable section

def powerEquation (y : ℝ → ℝ) (x : ℝ) : Prop :=
  Real.rpow x (y x) = Real.rpow (y x) x

def secondDeriv (y : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv y) x

def IsC2Branch (D : Set ℝ) (y : ℝ → ℝ) : Prop :=
  IsOpen D ∧ DifferentiableOn ℝ y D ∧
    DifferentiableOn ℝ (deriv y) D ∧
      (∀ x ∈ D, 0 < x ∧ 0 < y x ∧ x ≠ y x ∧ powerEquation y x) ∧
        ∀ x ∈ D, 1 - Real.log (y x) ≠ 0

theorem gap1 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      y x * Real.log x = x * Real.log (y x) := by
  intro x hx
  rcases h.2.2.2.1 x hx with ⟨hxpos, hypos, _, heq⟩
  unfold powerEquation at heq
  have hxdef :
      Real.rpow x (y x) = Real.exp (Real.log x * y x) := by
    exact Real.rpow_def_of_pos hxpos (y x)
  have hydef :
      Real.rpow (y x) x = Real.exp (Real.log (y x) * x) := by
    exact Real.rpow_def_of_pos hypos x
  have hexpeq :
      Real.exp (Real.log x * y x) =
        Real.exp (Real.log (y x) * x) :=
    hxdef.symm.trans (heq.trans hydef)
  have hexp := Real.exp_injective hexpeq
  simpa [mul_comm] using hexp

theorem gap2 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      Real.log x / x = Real.log (y x) / y x := by
  intro x hx
  rcases h.2.2.2.1 x hx with ⟨hxpos, hypos, _, _⟩
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hy0 : y x ≠ 0 := ne_of_gt hypos
  apply (div_eq_div_iff hx0 hy0).2
  calc
    Real.log x * y x = y x * Real.log x := mul_comm _ _
    _ = x * Real.log (y x) := gap1 D y h x hx
    _ = Real.log (y x) * x := mul_comm _ _

theorem gap3 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      (1 - Real.log x) / x ^ 2 =
        deriv y x * (1 - Real.log (y x)) / (y x) ^ 2 := by
  intro x hx
  rcases h.2.2.2.1 x hx with ⟨hxpos, hypos, _, _⟩
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hy0 : y x ≠ 0 := ne_of_gt hypos
  have hy' : HasDerivAt y (deriv y x) x :=
    ((h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)).hasDerivAt
  have hleft0 :=
    (Real.hasDerivAt_log hx0).div (hasDerivAt_id x) hx0
  have hleft :
      HasDerivAt (fun z : ℝ => Real.log z / z)
        ((1 - Real.log x) / x ^ 2) x := by
    convert hleft0 using 1 <;> simp <;> field_simp [hx0] <;> ring
  have hright0 :=
    ((Real.hasDerivAt_log hy0).comp x hy').div hy' hy0
  have hright :
      HasDerivAt (fun z : ℝ => Real.log (y z) / y z)
        (deriv y x * (1 - Real.log (y x)) / (y x) ^ 2) x := by
    convert hright0 using 1 <;> simp <;> field_simp [hy0] <;> ring
  have heq :
      (fun z : ℝ => Real.log z / z) =ᶠ[nhds x]
        (fun z : ℝ => Real.log (y z) / y z) := by
    filter_upwards [h.1.mem_nhds hx] with z hz
    exact gap2 D y h z hz
  calc
    (1 - Real.log x) / x ^ 2 =
        deriv (fun z : ℝ => Real.log z / z) x := hleft.deriv.symm
    _ = deriv (fun z : ℝ => Real.log (y z) / y z) x := heq.deriv_eq
    _ = deriv y x * (1 - Real.log (y x)) / (y x) ^ 2 := hright.deriv

theorem gap4 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      deriv y x =
        (y x) ^ 2 * (1 - Real.log x) /
          (x ^ 2 * (1 - Real.log (y x))) := by
  intro x hx
  rcases h.2.2.2.1 x hx with ⟨hxpos, hypos, _, _⟩
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hy0 : y x ≠ 0 := ne_of_gt hypos
  have hden : 1 - Real.log (y x) ≠ 0 := h.2.2.2.2 x hx
  have hder := gap3 D y h x hx
  field_simp [hx0, hy0, hden] at hder ⊢
  nlinarith [hder]

theorem gap5 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        1 / (x ^ 4 * (1 - Real.log (y x)) ^ 2) *
          (x ^ 2 * (1 - Real.log (y x)) *
              (2 * y x * deriv y x * (1 - Real.log x) -
                (y x) ^ 2 / x) -
            (y x) ^ 2 * (1 - Real.log x) *
              (2 * x - 2 * x * Real.log (y x) -
                x ^ 2 * deriv y x / y x)) := by
  intro x hx
  rcases h.2.2.2.1 x hx with ⟨hxpos, hypos, _, _⟩
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hy0 : y x ≠ 0 := ne_of_gt hypos
  have hden : 1 - Real.log (y x) ≠ 0 := h.2.2.2.2 x hx
  have hy' : HasDerivAt y (deriv y x) x :=
    ((h.2.1 x hx).differentiableAt (h.1.mem_nhds hx)).hasDerivAt
  have hu0 :=
    (hy'.pow 2).mul
      ((hasDerivAt_const x (1 : ℝ)).sub (Real.hasDerivAt_log hx0))
  have hu :
      HasDerivAt (fun z : ℝ => (y z) ^ 2 * (1 - Real.log z))
        (2 * y x * deriv y x * (1 - Real.log x) - (y x) ^ 2 / x) x := by
    convert hu0 using 1 <;> simp <;> field_simp [hx0] <;> ring
  have hlogy := (Real.hasDerivAt_log hy0).comp x hy'
  have hv0 :=
    ((hasDerivAt_id x).pow 2).mul
      ((hasDerivAt_const x (1 : ℝ)).sub hlogy)
  have hv :
      HasDerivAt (fun z : ℝ => z ^ 2 * (1 - Real.log (y z)))
        (2 * x - 2 * x * Real.log (y x) - x ^ 2 * deriv y x / y x) x := by
    convert hv0 using 1 <;> simp <;> field_simp [hy0] <;> ring
  have hvx0 : x ^ 2 * (1 - Real.log (y x)) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx0) hden
  have hquot0 := hu.div hv hvx0
  have hquot :
      HasDerivAt
        (fun z : ℝ =>
          (y z) ^ 2 * (1 - Real.log z) /
            (z ^ 2 * (1 - Real.log (y z))))
        (1 / (x ^ 4 * (1 - Real.log (y x)) ^ 2) *
          (x ^ 2 * (1 - Real.log (y x)) *
              (2 * y x * deriv y x * (1 - Real.log x) -
                (y x) ^ 2 / x) -
            (y x) ^ 2 * (1 - Real.log x) *
              (2 * x - 2 * x * Real.log (y x) -
                x ^ 2 * deriv y x / y x))) x := by
    convert hquot0 using 1 <;>
      field_simp [hx0, hy0, hden] <;> ring
  have heq :
      deriv y =ᶠ[nhds x]
        (fun z : ℝ =>
          (y z) ^ 2 * (1 - Real.log z) /
            (z ^ 2 * (1 - Real.log (y z)))) := by
    filter_upwards [h.1.mem_nhds hx] with z hz
    exact gap4 D y h z hz
  unfold secondDeriv
  exact heq.deriv_eq.trans hquot.deriv

theorem gap6 (D : Set ℝ) (y : ℝ → ℝ)
    (h : IsC2Branch D y) :
    ∀ x ∈ D,
      secondDeriv y x =
        (y x) ^ 2 *
          (y x * (1 - Real.log x) ^ 2 -
            2 * (x - y x) * (1 - Real.log x) *
              (1 - Real.log (y x)) -
            x * (1 - Real.log (y x)) ^ 2) /
          (x ^ 4 * (1 - Real.log (y x)) ^ 3) := by
  intro x hx
  rcases h.2.2.2.1 x hx with ⟨hxpos, hypos, _, _⟩
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hy0 : y x ≠ 0 := ne_of_gt hypos
  have hden : 1 - Real.log (y x) ≠ 0 := h.2.2.2.2 x hx
  have hlog' : Real.log x = x * Real.log (y x) / y x := by
    apply (eq_div_iff hy0).2
    calc
      Real.log x * y x = y x * Real.log x := mul_comm _ _
      _ = x * Real.log (y x) := gap1 D y h x hx
  rw [gap5 D y h x hx, gap4 D y h x hx, hlog']
  field_simp [hx0, hy0, hden] <;> ring

end

end ProofGap.Exercise3374
