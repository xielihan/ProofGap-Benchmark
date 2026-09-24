import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2149

noncomputable section

def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def integrand (a b x : ℝ) :=
  (a * x ^ 2 + b) / (x ^ 2 + 1) * Real.arctan x
def rewritten (a b x : ℝ) :=
  (a - (a - b) / (x ^ 2 + 1)) * Real.arctan x
def ReductionFamily (a b : ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives (fun x => x / (1 + x ^ 2)),
    ∀ x,
      F x = a * x * Real.arctan x - a * G x -
        (a - b) / 2 * Real.arctan x ^ 2}
def primitive (a b x : ℝ) :=
  a * (x * Real.arctan x - 1 / 2 * Real.log (1 + x ^ 2)) -
    (a - b) / 2 * Real.arctan x ^ 2

private theorem one_add_sq_pos (x : ℝ) : 0 < 1 + x ^ 2 := by
  nlinarith [sq_nonneg x]

private theorem hasDerivAt_arctanPrimitive (x : ℝ) :
    HasDerivAt
      (fun y : ℝ =>
        y * Real.arctan y -
          (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
      (Real.arctan x) x := by
  have hboundary :
      HasDerivAt (fun y : ℝ => y * Real.arctan y)
        (Real.arctan x + x / (1 + x ^ 2)) x := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)
  have hinner : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
      norm_num <;> ring
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (1 + y ^ 2))
        ((1 + x ^ 2)⁻¹ * (2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_log (ne_of_gt (one_add_sq_pos x))).comp x hinner
  have hlogHalf :
      HasDerivAt
        (fun y : ℝ => (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
        (x / (1 + x ^ 2)) x := by
    convert hlog.const_mul (1 / 2 : ℝ) using 1 <;>
      field_simp [ne_of_gt (one_add_sq_pos x)] <;> ring
  simpa using hboundary.sub hlogHalf

private theorem hasDerivAt_logHalf (x : ℝ) :
    HasDerivAt
      (fun y : ℝ => (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
      (x / (1 + x ^ 2)) x := by
  have hboundary :
      HasDerivAt (fun y : ℝ => y * Real.arctan y)
        (Real.arctan x + x / (1 + x ^ 2)) x := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)
  have hd := hboundary.sub (hasDerivAt_arctanPrimitive x)
  convert hd using 1
  · funext y
    change (1 / 2 : ℝ) * Real.log (1 + y ^ 2) =
      y * Real.arctan y -
        (y * Real.arctan y - (1 / 2 : ℝ) * Real.log (1 + y ^ 2))
    ring
  · ring

private theorem hasDerivAt_primitive (a b x : ℝ) :
    HasDerivAt (primitive a b) (integrand a b x) x := by
  have hsq :
      HasDerivAt
        (fun y : ℝ => (a - b) / 2 * Real.arctan y ^ 2)
        ((a - b) * Real.arctan x / (1 + x ^ 2)) x := by
    convert
      ((Real.hasDerivAt_arctan x).pow 2).const_mul ((a - b) / 2)
      using 1 <;>
      field_simp [ne_of_gt (one_add_sq_pos x)] <;> ring
  have hraw := (hasDerivAt_arctanPrimitive x).const_mul a |>.sub hsq
  have hprim :
      HasDerivAt (primitive a b)
        (a * Real.arctan x -
          (a - b) * Real.arctan x / (1 + x ^ 2)) x := by
    convert hraw using 1
  convert hprim using 1
  unfold integrand
  have hx : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [hx, ne_of_gt (one_add_sq_pos x)]
  ring

theorem gap1 (a b : ℝ) :
    Antiderivatives (integrand a b) =
      Antiderivatives (rewritten a b) := by
  apply congrArg Antiderivatives
  funext x
  unfold integrand rewritten
  have hx : x ^ 2 + 1 ≠ 0 := by
    nlinarith [sq_nonneg x]
  field_simp [hx]
  ring
theorem gap2 (a b : ℝ) (ha : a ≠ 0) :
    Antiderivatives (rewritten a b) = ReductionFamily a b := by
  ext F
  constructor
  · intro hF
    have hFintegrand : F ∈ Antiderivatives (integrand a b) := by
      rw [gap1 a b]
      exact hF
    have hzero (x : ℝ) :
        HasDerivAt (fun y => F y - primitive a b y) 0 x := by
      simpa using (hFintegrand x).sub (hasDerivAt_primitive a b x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive a b y) :=
      fun x => (hzero x).differentiableAt
    have hconst :=
      is_const_of_deriv_eq_zero hdiff (fun x => (hzero x).deriv)
    let C : ℝ := F 0 - primitive a b 0
    have hFC (x : ℝ) : F x = primitive a b x + C := by
      calc
        F x = primitive a b x + (F x - primitive a b x) := by ring
        _ = primitive a b x + (F 0 - primitive a b 0) := by
          rw [hconst x 0]
        _ = primitive a b x + C := by rfl
    let G : ℝ → ℝ := fun y =>
      (1 / 2 : ℝ) * Real.log (1 + y ^ 2) - C / a
    change ∃ G ∈ Antiderivatives (fun x => x / (1 + x ^ 2)),
      ∀ x, F x = a * x * Real.arctan x - a * G x -
        (a - b) / 2 * Real.arctan x ^ 2
    refine ⟨G, ?_, ?_⟩
    · intro x
      simpa [G] using (hasDerivAt_logHalf x).sub_const (C / a)
    · intro x
      rw [hFC x]
      simp only [G, primitive]
      field_simp [ha]
      ring
  · rintro ⟨G, hG, hFG⟩
    intro x
    have hboundary :
        HasDerivAt (fun y : ℝ => y * Real.arctan y)
          (Real.arctan x + x / (1 + x ^ 2)) x := by
      simpa [div_eq_mul_inv] using
        (hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)
    have hsq :
        HasDerivAt
          (fun y : ℝ => (a - b) / 2 * Real.arctan y ^ 2)
          ((a - b) * Real.arctan x / (1 + x ^ 2)) x := by
      convert
        ((Real.hasDerivAt_arctan x).pow 2).const_mul ((a - b) / 2)
        using 1 <;>
        field_simp [ne_of_gt (one_add_sq_pos x)] <;> ring
    have hd := (hboundary.const_mul a).sub ((hG x).const_mul a) |>.sub hsq
    have hcongr (y : ℝ) :
        F y = a * (y * Real.arctan y) - a * G y -
          (a - b) / 2 * Real.arctan y ^ 2 := by
      rw [hFG y]
      ring
    apply (hd.congr_of_eventuallyEq
      (Filter.Eventually.of_forall hcongr)).congr_deriv
    unfold rewritten
    field_simp [ne_of_gt (one_add_sq_pos x)]
    ring
theorem gap3 (a b : ℝ) (ha : a ≠ 0) :
    Antiderivatives (integrand a b) = ReductionFamily a b := by
  exact (gap1 a b).trans (gap2 a b ha)
theorem gap4 (a b : ℝ) :
    Antiderivatives (integrand a b) = PrimitiveFamily (primitive a b) := by
  ext F
  simp only [Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero (x : ℝ) :
        HasDerivAt (fun y => F y - primitive a b y) 0 x := by
      simpa using (hF x).sub (hasDerivAt_primitive a b x)
    have hdiff : Differentiable ℝ (fun y => F y - primitive a b y) :=
      fun x => (hzero x).differentiableAt
    have hconst :=
      is_const_of_deriv_eq_zero hdiff (fun x => (hzero x).deriv)
    refine ⟨F 0 - primitive a b 0, ?_⟩
    intro x
    calc
      F x = primitive a b x + (F x - primitive a b x) := by ring
      _ = primitive a b x + (F 0 - primitive a b 0) := by
        rw [hconst x 0]
  · rintro ⟨C, hC⟩
    have hFeq : F = fun x => primitive a b x + C := funext hC
    intro x
    rw [hFeq]
    simpa using (hasDerivAt_primitive a b x).add_const C

end
end ProofGap.Exercise2149
