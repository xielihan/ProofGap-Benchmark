import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2012_1
noncomputable section

def branch : Set ℝ := Set.Ioo 0 Real.pi
def Family (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ branch, HasDerivAt F (f x) x}
def Translates (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ branch, F x = p x + C}
def I (n : ℕ) := Family (fun x => 1 / Real.sin x ^ n)
def Recurrence (n : ℕ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ I (n - 2), ∃ C, ∀ x ∈ branch,
    F x = -Real.cos x / (((n - 1 : ℕ) : ℝ) * Real.sin x ^ (n - 1)) +
      ((n - 2 : ℕ) : ℝ) / (n - 1) * G x + C}
def primitive1 (x : ℝ) := Real.log |Real.tan (x / 2)|
def primitive5 (x : ℝ) :=
  -Real.cos x / (4 * Real.sin x ^ 4) -
    3 * Real.cos x / (8 * Real.sin x ^ 2) +
    3 / 8 * Real.log |Real.tan (x / 2)|

private def reductionBase (m : ℕ) (x : ℝ) : ℝ :=
  -Real.cos x / (((m + 1 : ℕ) : ℝ) * Real.sin x ^ (m + 1))

private def reductionForm (m : ℕ) (G : ℝ → ℝ) (x : ℝ) : ℝ :=
  reductionBase m x + (m : ℝ) / (((m + 1 : ℕ) : ℝ)) * G x

private theorem family_eq_translates_of_hasDerivAt
    {f p : ℝ → ℝ}
    (hp : ∀ x ∈ branch, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  ext F
  change (∀ x ∈ branch, HasDerivAt F (f x) x) ↔
    ∃ C, ∀ x ∈ branch, F x = p x + C
  constructor
  · intro hF
    let H : ℝ → ℝ := fun y => F y - p y
    have hHd : ∀ x ∈ branch, HasDerivAt H 0 x := by
      intro x hx
      simpa [H] using (hF x hx).sub (hp x hx)
    have hHdiff : DifferentiableOn ℝ H branch := by
      intro x hx
      exact (hHd x hx).differentiableAt.differentiableWithinAt
    have hHderiv : ∀ x ∈ branch, deriv H x = 0 := by
      intro x hx
      exact (hHd x hx).deriv
    let a : ℝ := Real.pi / 2
    have ha : a ∈ branch := by
      change 0 < Real.pi / 2 ∧ Real.pi / 2 < Real.pi
      constructor <;> linarith [Real.pi_pos]
    refine ⟨H a, ?_⟩
    intro x hx
    have hconst : H x = H a :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hHdiff hHderiv hx ha
    dsimp [H] at hconst ⊢
    linarith
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] (fun y => p y + C) := by
      filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
      exact hC y hy
    exact ((hp x hx).add_const C).congr_of_eventuallyEq heq

private theorem reductionBase_hasDerivAt
    (m : ℕ) {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt (reductionBase m)
      (1 / Real.sin x ^ (m + 2) -
        (m : ℝ) / (m + 1) * (1 / Real.sin x ^ m)) x := by
  have hspos : 0 < Real.sin x :=
    Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsne : Real.sin x ≠ 0 := ne_of_gt hspos
  have hden :
      ((m + 1 : ℕ) : ℝ) * Real.sin x ^ (m + 1) ≠ 0 :=
    mul_ne_zero (by positivity) (pow_ne_zero _ hsne)
  have hd :=
    (Real.hasDerivAt_cos x).neg.div
      (((Real.hasDerivAt_sin x).pow (m + 1)).const_mul
        (((m + 1 : ℕ) : ℝ))) hden
  have htrig : Real.cos x ^ 2 = 1 - Real.sin x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x]
  convert hd using 1
  simp only [Nat.cast_add, Nat.cast_one, Nat.add_sub_cancel,
    Pi.neg_apply, Pi.pow_apply, neg_neg, pow_succ]
  field_simp [hsne]
  ring_nf
  rw [htrig]
  ring

private theorem reductionStep_hasDerivAt
    (m : ℕ) {G : ℝ → ℝ} {x : ℝ} (hx : x ∈ branch)
    (hG : HasDerivAt G (1 / Real.sin x ^ m) x) :
    HasDerivAt (reductionForm m G)
      (1 / Real.sin x ^ (m + 2)) x := by
  unfold reductionForm
  convert (reductionBase_hasDerivAt m hx).add
    (hG.const_mul ((m : ℝ) / (((m + 1 : ℕ) : ℝ)))) using 1
  simp only [Nat.cast_add, Nat.cast_one]
  ring

private theorem recurrence_step (m : ℕ) :
    I (m + 2) = Recurrence (m + 2) := by
  ext F
  simp only [I, Family, Recurrence, Set.mem_setOf_eq,
    Nat.add_sub_cancel]
  have hsub1 : m + 2 - 1 = m + 1 := by omega
  have hden :
      (((m + 2 : ℕ) : ℝ) - 1) = ((m + 1 : ℕ) : ℝ) := by
    norm_num [Nat.cast_add]
    ring
  rw [hsub1, hden]
  change
    (∀ x ∈ branch,
      HasDerivAt F (1 / Real.sin x ^ (m + 2)) x) ↔
    ∃ G,
      (∀ x ∈ branch, HasDerivAt G (1 / Real.sin x ^ m) x) ∧
      ∃ C, ∀ x ∈ branch, F x = reductionForm m G x + C
  constructor
  · intro hF
    by_cases hm : m = 0
    · subst m
      have hp0 : ∀ x ∈ branch,
          HasDerivAt (reductionBase 0) (1 / Real.sin x ^ (0 + 2)) x := by
        intro x hx
        simpa using reductionBase_hasDerivAt 0 hx
      have htrans : F ∈ Translates (reductionBase 0) := by
        rw [← family_eq_translates_of_hasDerivAt hp0]
        exact hF
      rcases htrans with ⟨C, hC⟩
      refine ⟨fun y : ℝ => y, ?_, C, ?_⟩
      · intro x hx
        simpa using hasDerivAt_id x
      · intro x hx
        simpa [reductionForm, reductionBase] using hC x hx
    · have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
      let G : ℝ → ℝ := fun y =>
        (((m + 1 : ℕ) : ℝ) / (m : ℝ)) *
          (F y - reductionBase m y)
      refine ⟨G, ?_, 0, ?_⟩
      · intro x hx
        dsimp [G]
        convert ((hF x hx).sub
          (reductionBase_hasDerivAt m hx)).const_mul
            (((m + 1 : ℕ) : ℝ) / (m : ℝ)) using 1
        field_simp [hmR]
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      · intro x hx
        dsimp [G, reductionForm]
        field_simp [hmR]
        ring
  · rintro ⟨G, hG, C, hC⟩
    have hp : ∀ x ∈ branch,
        HasDerivAt (reductionForm m G)
          (1 / Real.sin x ^ (m + 2)) x := by
      intro x hx
      exact reductionStep_hasDerivAt m hx (hG x hx)
    have htrans : F ∈ Translates (reductionForm m G) := ⟨C, hC⟩
    have hfam : F ∈ Family (fun x => 1 / Real.sin x ^ (m + 2)) := by
      rw [family_eq_translates_of_hasDerivAt hp]
      exact htrans
    exact hfam

private theorem primitive1_hasDerivAt
    {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive1 (1 / Real.sin x) x := by
  have hxhalf : x / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith [hx.1, hx.2, Real.pi_pos]
  have hcospos : 0 < Real.cos (x / 2) :=
    Real.cos_pos_of_mem_Ioo hxhalf
  have hcosne : Real.cos (x / 2) ≠ 0 := ne_of_gt hcospos
  have hsinpos : 0 < Real.sin (x / 2) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · linarith [hx.1]
    · linarith [hx.2, Real.pi_pos]
  have hsinne : Real.sin (x / 2) ≠ 0 := ne_of_gt hsinpos
  have htanpos : 0 < Real.tan (x / 2) := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_pos hsinpos hcospos
  have htan :=
    (Real.hasDerivAt_tan hcosne).comp x
      ((hasDerivAt_id x).div_const 2)
  have hlogtan :=
    (Real.hasDerivAt_log (ne_of_gt htanpos)).comp x htan
  have hxdouble : x = 2 * (x / 2) := by ring
  have hq :
      HasDerivAt (fun y => Real.log (Real.tan (y / 2)))
        (1 / Real.sin x) x := by
    convert hlogtan using 1
    rw [hxdouble, Real.sin_two_mul]
    simp [Real.tan_eq_sin_div_cos]
    field_simp [hsinne, hcosne]
  have hevent : ∀ᶠ y in nhds x, 0 < Real.tan (y / 2) :=
    htan.continuousAt (Ioi_mem_nhds htanpos)
  have heq :
      primitive1 =ᶠ[nhds x]
        (fun y => Real.log (Real.tan (y / 2))) := by
    filter_upwards [hevent] with y hy
    simp [primitive1, abs_of_pos hy]
  exact hq.congr_of_eventuallyEq heq

private theorem primitive5_hasDerivAt
    {x : ℝ} (hx : x ∈ branch) :
    HasDerivAt primitive5 (1 / Real.sin x ^ 5) x := by
  have h1 : HasDerivAt primitive1 (1 / Real.sin x ^ 1) x := by
    simpa using primitive1_hasDerivAt hx
  have h3 := reductionStep_hasDerivAt 1 hx h1
  have h5 := reductionStep_hasDerivAt 3 hx h3
  have heq :
      primitive5 = reductionForm 3 (reductionForm 1 primitive1) := by
    funext y
    simp [primitive5, primitive1, reductionForm, reductionBase]
    ring
  rw [heq]
  simpa using h5

theorem gap1 (n : ℕ) : I n = Family (fun x => 1 / Real.sin x ^ n) := by
  rfl
theorem gap2 (n : ℕ) : I n = Family (fun x =>
    (Real.sin x ^ 2 + Real.cos x ^ 2) / Real.sin x ^ n) := by
  simp [I, Real.sin_sq_add_cos_sq]
theorem gap3 (n : ℕ) : I n = Family (fun x =>
    (Real.sin x ^ 2 + Real.cos x ^ 2) / Real.sin x ^ n) := by
  exact gap2 n
theorem gap4 (n : ℕ) (hn : 2 ≤ n) : I n = Recurrence n := by
  have hn' : n = (n - 2) + 2 := by omega
  rw [hn']
  exact recurrence_step (n - 2)
theorem gap5 (n : ℕ) (hn : 2 ≤ n) : I n = Recurrence n := by
  exact gap4 n hn
theorem gap6 (n : ℕ) (hn : 2 ≤ n) : I n = Recurrence n := by
  exact gap4 n hn
theorem gap7 : I 1 = Family (fun x => 1 / Real.sin x) := by
  simpa using (gap1 1)
theorem gap8 : Family (fun x => 1 / Real.sin x) = Translates primitive1 := by
  exact family_eq_translates_of_hasDerivAt
    (fun x hx => primitive1_hasDerivAt hx)
theorem gap9 : I 1 = Translates primitive1 := by
  rw [gap7, gap8]
theorem gap10 : I 5 = Family (fun x => 1 / Real.sin x ^ 5) := by
  exact gap1 5
theorem gap11 : I 5 = Translates primitive5 := by
  calc
    I 5 = Family (fun x => 1 / Real.sin x ^ 5) := gap10
    _ = Translates primitive5 :=
      family_eq_translates_of_hasDerivAt
        (fun x hx => primitive5_hasDerivAt hx)
theorem gap12 : I 5 = Translates primitive5 := by
  exact gap11

end
end ProofGap.Exercise2012_1
