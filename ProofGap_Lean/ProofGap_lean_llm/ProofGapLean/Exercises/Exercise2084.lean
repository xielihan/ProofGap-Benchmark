import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2084
noncomputable section

def denom (x : ℝ) := Real.exp (2 * x) + Real.exp x - 2
def f (x : ℝ) := 1 / denom x
def primitive (x : ℝ) :=
  -x / 2 + Real.log |Real.exp x - 1| / 3 +
    Real.log (Real.exp x + 2) / 6
def Family (U : Set ℝ) (g : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (g x) x}
def Split (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ A ∈ Family U (fun x => 1 / (Real.exp x - 1)),
  ∃ B ∈ Family U (fun x => 1 / (Real.exp x + 2)),
  ∃ C, ∀ x ∈ U, F x = A x / 3 - B x / 3 + C}
def Reduced (U : Set ℝ) := {F : ℝ → ℝ |
  ∃ A ∈ Family U (fun x => 1 - Real.exp x / (Real.exp x - 1)),
  ∃ B ∈ Family U (fun x => 1 - Real.exp x / (Real.exp x + 2)),
  ∃ C, ∀ x ∈ U, F x = -A x / 3 - B x / 6 + C}
def Translates (U : Set ℝ) (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x ∈ U, F x = p x + C}
def Regular (U : Set ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, x ≠ 0

private theorem exp_sub_one_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    Real.exp x - 1 ≠ 0 := by
  apply sub_ne_zero.mpr
  intro h
  apply hx
  apply Real.exp_injective
  simpa using h

private theorem family_eq_translates_of_hasDeriv
    (U : Set ℝ) (hUopen : IsOpen U) (hUconn : IsPreconnected U)
    (g p : ℝ → ℝ) (hp : ∀ x ∈ U, HasDerivAt p (g x) x) :
    Family U g = Translates U p := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    by_cases hnonempty : U.Nonempty
    · rcases hnonempty with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - p x₀, ?_⟩
      have hdiff : DifferentiableOn ℝ (fun y => F y - p y) U := by
        intro y hy
        exact ((hF y hy).sub (hp y hy)).differentiableAt.differentiableWithinAt
      have hzero : ∀ y ∈ U, deriv (fun z => F z - p z) y = 0 := by
        intro y hy
        simpa using ((hF y hy).sub (hp y hy)).deriv
      intro x hx
      have hxy : F x - p x = F x₀ - p x₀ :=
        hUopen.is_const_of_deriv_eq_zero hUconn hdiff hzero hx hx₀
      calc
        F x = p x + (F x - p x) := by ring
        _ = p x + (F x₀ - p x₀) := by rw [hxy]
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hnonempty ⟨x, hx⟩).elim
  · rintro ⟨C, hEq⟩
    intro x hx
    have hevent : (fun y => p y + C) =ᶠ[nhds x] F := by
      filter_upwards [hUopen.mem_nhds hx] with y hy
      exact (hEq y hy).symm
    exact ((hp x hx).add_const C).congr_of_eventuallyEq hevent.symm

private theorem hasDerivAt_log_abs_exp_sub_one (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y => Real.log |Real.exp y - 1|)
      (Real.exp x / (Real.exp x - 1)) x := by
  have hne : Real.exp x - 1 ≠ 0 :=
    exp_sub_one_ne_zero_of_ne_zero hx
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · have hnegne : -(Real.exp x - 1) ≠ 0 := neg_ne_zero.mpr hne
    have hinner := ((Real.hasDerivAt_exp x).sub_const 1).neg
    have hraw := (Real.hasDerivAt_log hnegne).comp x hinner
    have hevent :
        (fun y => Real.log |Real.exp y - 1|) =ᶠ[nhds x]
          (fun y => Real.log (-(Real.exp y - 1))) := by
      filter_upwards [Iio_mem_nhds hxneg] with y hy
      have hone : Real.exp y < 1 := by
        simpa using (Real.exp_lt_exp.mpr hy)
      have hyexp : Real.exp y - 1 < 0 := sub_neg.mpr hone
      simp [abs_of_neg hyexp]
    have habs := hraw.congr_of_eventuallyEq hevent
    convert habs using 1 <;> field_simp [hne] <;> ring
  · have hinner := (Real.hasDerivAt_exp x).sub_const 1
    have hraw := (Real.hasDerivAt_log hne).comp x hinner
    have hevent :
        (fun y => Real.log |Real.exp y - 1|) =ᶠ[nhds x]
          (fun y => Real.log (Real.exp y - 1)) := by
      filter_upwards [Ioi_mem_nhds hxpos] with y hy
      have hone : 1 < Real.exp y := by
        simpa using (Real.exp_lt_exp.mpr hy)
      have hyexp : 0 < Real.exp y - 1 := sub_pos.mpr hone
      simp [abs_of_pos hyexp]
    have habs := hraw.congr_of_eventuallyEq hevent
    convert habs using 1 <;> field_simp [hne] <;> ring

private theorem hasDerivAt_model (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt
      (fun y => -y / 3 + Real.log |Real.exp y - 1| / 3 -
        y / 6 + Real.log (Real.exp y + 2) / 6)
      (f x) x := by
  have hne1 : Real.exp x - 1 ≠ 0 :=
    exp_sub_one_ne_zero_of_ne_zero hx
  have hne2 : Real.exp x + 2 ≠ 0 := by positivity
  have hlog1 := hasDerivAt_log_abs_exp_sub_one x hx
  have hlog2 := (Real.hasDerivAt_log hne2).comp x
    ((Real.hasDerivAt_exp x).add_const 2)
  have hraw := ((((hasDerivAt_id x).neg.div_const 3).add
    (hlog1.div_const 3)).sub ((hasDerivAt_id x).div_const 6)).add
    (hlog2.div_const 6)
  have hden : denom x = (Real.exp x + 2) * (Real.exp x - 1) := by
    unfold denom
    rw [show 2 * x = x + x by ring, Real.exp_add]
    ring
  have hfx : f x = 1 / ((Real.exp x + 2) * (Real.exp x - 1)) := by
    rw [f, hden]
  have hcoef :
      -1 / 3 + Real.exp x / (Real.exp x - 1) / 3 - 1 / 6 +
          (Real.exp x + 2)⁻¹ * Real.exp x / 6 = f x := by
    rw [hfx]
    field_simp [hne1, hne2]
    ring
  rw [← hcoef]
  simpa only [Function.comp_apply, id_eq] using hraw

theorem gap1 (U : Set ℝ) (hU : Regular U) :
    Family U f = Family U
      (fun x => 1 / ((Real.exp x + 2) * (Real.exp x - 1))) := by
  apply Set.ext
  intro F
  constructor <;> intro hF <;> intro x <;> intro hx
  · have hden : denom x = (Real.exp x + 2) * (Real.exp x - 1) := by
      unfold denom
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring
    simpa only [f, hden] using hF x hx
  · have hden : denom x = (Real.exp x + 2) * (Real.exp x - 1) := by
      unfold denom
      rw [show 2 * x = x + x by ring, Real.exp_add]
      ring
    simpa only [f, hden] using hF x hx
theorem gap2 (U : Set ℝ) (hU : Regular U) :
    Family U (fun x => 1 / ((Real.exp x + 2) * (Real.exp x - 1))) =
      Split U := by
  apply Set.ext
  intro F
  constructor
  · intro hF
    let B : ℝ → ℝ := fun y => y / 2 - Real.log (Real.exp y + 2) / 2
    have hB : B ∈ Family U (fun x => 1 / (Real.exp x + 2)) := by
      intro x hx
      have hne : Real.exp x + 2 ≠ 0 := by positivity
      have hlog := (Real.hasDerivAt_log hne).comp x
        ((Real.hasDerivAt_exp x).add_const 2)
      have hraw := ((hasDerivAt_id x).div_const 2).sub (hlog.div_const 2)
      change HasDerivAt (fun y => y / 2 - Real.log (Real.exp y + 2) / 2)
        (1 / (Real.exp x + 2)) x
      convert hraw using 1 <;> field_simp [hne] <;> ring
    let A : ℝ → ℝ := fun y => 3 * F y + B y
    have hA : A ∈ Family U (fun x => 1 / (Real.exp x - 1)) := by
      intro x hx
      have hne1 : Real.exp x - 1 ≠ 0 :=
        exp_sub_one_ne_zero_of_ne_zero (hU.2.2 x hx)
      have hne2 : Real.exp x + 2 ≠ 0 := by positivity
      have hraw := ((hF x hx).const_mul 3).add (hB x hx)
      change HasDerivAt (fun y => 3 * F y + B y)
        (1 / (Real.exp x - 1)) x
      convert hraw using 1 <;> field_simp [hne1, hne2] <;> ring
    refine ⟨A, hA, B, hB, 0, ?_⟩
    intro x hx
    dsimp [A]
    ring
  · rintro ⟨A, hA, B, hB, C, hEq⟩
    intro x hx
    have hne1 : Real.exp x - 1 ≠ 0 :=
      exp_sub_one_ne_zero_of_ne_zero (hU.2.2 x hx)
    have hne2 : Real.exp x + 2 ≠ 0 := by positivity
    have hraw := (((hA x hx).div_const 3).sub
      ((hB x hx).div_const 3)).add_const C
    have hder : HasDerivAt
        (fun y => A y / 3 - B y / 3 + C)
        (1 / ((Real.exp x + 2) * (Real.exp x - 1))) x := by
      convert hraw using 1 <;> field_simp [hne1, hne2] <;> ring
    have hevent :
        (fun y => A y / 3 - B y / 3 + C) =ᶠ[nhds x] F := by
      filter_upwards [hU.1.mem_nhds hx] with y hy
      exact (hEq y hy).symm
    exact hder.congr_of_eventuallyEq hevent.symm
theorem gap3 (U : Set ℝ) (hU : Regular U) : Family U f = Split U := by
  calc
    Family U f = Family U
        (fun x => 1 / ((Real.exp x + 2) * (Real.exp x - 1))) := gap1 U hU
    _ = Split U := gap2 U hU
theorem gap4 (U : Set ℝ) (hU : Regular U) : Family U f = Reduced U := by
  rw [gap3 U hU]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨A, hA, B, hB, C, hEq⟩
    let A' : ℝ → ℝ := fun y => -A y
    let B' : ℝ → ℝ := fun y => 2 * B y
    have hA' : A' ∈ Family U
        (fun x => 1 - Real.exp x / (Real.exp x - 1)) := by
      intro x hx
      have hne : Real.exp x - 1 ≠ 0 :=
        exp_sub_one_ne_zero_of_ne_zero (hU.2.2 x hx)
      change HasDerivAt (fun y => -A y)
        (1 - Real.exp x / (Real.exp x - 1)) x
      convert (hA x hx).neg using 1 <;> field_simp [hne] <;> ring
    have hB' : B' ∈ Family U
        (fun x => 1 - Real.exp x / (Real.exp x + 2)) := by
      intro x hx
      have hne : Real.exp x + 2 ≠ 0 := by positivity
      change HasDerivAt (fun y => 2 * B y)
        (1 - Real.exp x / (Real.exp x + 2)) x
      convert (hB x hx).const_mul 2 using 1 <;> field_simp [hne] <;> ring
    refine ⟨A', hA', B', hB', C, ?_⟩
    intro x hx
    dsimp [A', B']
    rw [hEq x hx]
    ring
  · rintro ⟨A, hA, B, hB, C, hEq⟩
    let A' : ℝ → ℝ := fun y => -A y
    let B' : ℝ → ℝ := fun y => B y / 2
    have hA' : A' ∈ Family U (fun x => 1 / (Real.exp x - 1)) := by
      intro x hx
      have hne : Real.exp x - 1 ≠ 0 :=
        exp_sub_one_ne_zero_of_ne_zero (hU.2.2 x hx)
      change HasDerivAt (fun y => -A y) (1 / (Real.exp x - 1)) x
      convert (hA x hx).neg using 1 <;> field_simp [hne] <;> ring
    have hB' : B' ∈ Family U (fun x => 1 / (Real.exp x + 2)) := by
      intro x hx
      have hne : Real.exp x + 2 ≠ 0 := by positivity
      change HasDerivAt (fun y => B y / 2) (1 / (Real.exp x + 2)) x
      convert (hB x hx).div_const 2 using 1 <;> field_simp [hne] <;> ring
    refine ⟨A', hA', B', hB', C, ?_⟩
    intro x hx
    dsimp [A', B']
    rw [hEq x hx]
    ring
theorem gap5 (U : Set ℝ) (hU : Regular U) :
    Family U f = Translates U
      (fun x => -x / 3 + Real.log |Real.exp x - 1| / 3 -
        x / 6 + Real.log (Real.exp x + 2) / 6) := by
  apply family_eq_translates_of_hasDeriv U hU.1 hU.2.1
  intro x hx
  exact hasDerivAt_model x (hU.2.2 x hx)
theorem gap6 (U : Set ℝ) (hU : Regular U) :
    Translates U
      (fun x => -x / 3 + Real.log |Real.exp x - 1| / 3 -
        x / 6 + Real.log (Real.exp x + 2) / 6) =
      Translates U primitive := by
  have hp :
      (fun x => -x / 3 + Real.log |Real.exp x - 1| / 3 -
        x / 6 + Real.log (Real.exp x + 2) / 6) = primitive := by
    funext x
    unfold primitive
    ring
  rw [hp]
theorem gap7 (U : Set ℝ) (hU : Regular U) :
    Family U f = Translates U primitive := by
  calc
    Family U f = Translates U
        (fun x => -x / 3 + Real.log |Real.exp x - 1| / 3 -
          x / 6 + Real.log (Real.exp x + 2) / 6) := gap5 U hU
    _ = Translates U primitive := gap6 U hU

end
end ProofGap.Exercise2084
