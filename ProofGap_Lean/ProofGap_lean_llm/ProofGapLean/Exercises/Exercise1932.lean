import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1932

noncomputable section

def cubeRoot (x : ℝ) := Real.sign x * Real.rpow |x| (1 / 3 : ℝ)
def xOf (t : ℝ) := (t ^ 3 + 1) / (t ^ 3 - 1)
def regularBranch : Set ℝ := {t | t ≠ 0 ∧ t ≠ 1}
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ t ∈ s, HasDerivAt F (f t) t}
def BranchwisePrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ u : Set ℝ, IsOpen u → IsPreconnected u → u ⊆ s →
    ∃ C : ℝ, ∀ t ∈ u, F t = p t + C}
def sourceIntegrand (t : ℝ) :=
  1 / cubeRoot ((xOf t + 1) ^ 2 * (xOf t - 1) ^ 4) * deriv xOf t
def ConstantScaledFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ AntiderivativesOn regularBranch (fun _ => 1),
    ∀ t ∈ regularBranch, F t = -3 / 2 * G t}
def linearPrimitive (t : ℝ) := -3 / 2 * t
def rootPrimitive (t : ℝ) :=
  -3 / 2 * cubeRoot ((xOf t + 1) / (xOf t - 1))

private theorem cubeRoot_cube (t : ℝ) : cubeRoot (t ^ 3) = t := by
  have hposroot : ∀ a : ℝ, 0 < a → Real.rpow (a ^ 3) (1 / 3 : ℝ) = a := by
    intro a ha
    have hpow : Real.rpow a (3 : ℝ) = a ^ (3 : ℕ) := by
      exact Real.rpow_natCast a 3
    calc
      Real.rpow (a ^ 3) (1 / 3 : ℝ) =
          Real.rpow (Real.rpow a (3 : ℝ)) (1 / 3 : ℝ) := by
            exact congrArg (fun x : ℝ => Real.rpow x (1 / 3 : ℝ)) hpow.symm
      _ = Real.rpow a ((3 : ℝ) * (1 / 3 : ℝ)) := by
            exact (Real.rpow_mul (le_of_lt ha) 3 (1 / 3 : ℝ)).symm
      _ = a := by norm_num
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have ht3 : t ^ 3 < 0 := by nlinarith [sq_pos_of_neg ht]
    have hnegcube : -(t ^ 3) = (-t) ^ 3 := by ring
    unfold cubeRoot
    rw [Real.sign_of_neg ht3, abs_of_neg ht3, hnegcube,
      hposroot (-t) (neg_pos.mpr ht)]
    ring
  · subst t
    simp [cubeRoot]
  · have ht3 : 0 < t ^ 3 := pow_pos ht 3
    unfold cubeRoot
    rw [Real.sign_of_pos ht3, abs_of_pos ht3, hposroot t ht]
    ring

theorem gap1 (t : ℝ) (ht : t ≠ 1) :
    xOf t = (t ^ 3 + 1) / (t ^ 3 - 1) := by
  rfl
theorem gap2 (t : ℝ) (ht : t ≠ 1) :
    HasDerivAt xOf (-6 * t ^ 2 / (t ^ 3 - 1) ^ 2) t := by
  have hden : t ^ 3 - 1 ≠ 0 := by
    intro hzero
    have hfac : (t - 1) * (t ^ 2 + t + 1) = 0 := by
      calc
        (t - 1) * (t ^ 2 + t + 1) = t ^ 3 - 1 := by ring
        _ = 0 := hzero
    rcases mul_eq_zero.mp hfac with h | h
    · exact ht (sub_eq_zero.mp h)
    · have hpos : 0 < t ^ 2 + t + 1 := by
        nlinarith [sq_nonneg (2 * t + 1)]
      exact (ne_of_gt hpos) h
  have hcube0 :=
    ((hasDerivAt_id t).mul (hasDerivAt_id t)).mul (hasDerivAt_id t)
  have hcube : HasDerivAt (fun x : ℝ => x ^ 3) (3 * t ^ 2) t := by
    convert hcube0 using 1
    · funext x
      simp only [id_eq, Pi.mul_apply]
      ring
    · simp only [id_eq, Pi.mul_apply]
      ring
  have hnum : HasDerivAt (fun x : ℝ => x ^ 3 + 1) (3 * t ^ 2) t := by
    simpa using hcube.add_const 1
  have hdenDeriv : HasDerivAt (fun x : ℝ => x ^ 3 - 1) (3 * t ^ 2) t := by
    simpa using hcube.sub_const 1
  unfold xOf
  convert hnum.div hdenDeriv hden using 1 <;> ring
theorem gap3 :
    AntiderivativesOn regularBranch sourceIntegrand =
      ConstantScaledFamily := by
  have hopen : IsOpen regularBranch := by
    have hopen0 : IsOpen (({0} : Set ℝ)ᶜ) := isOpen_compl_singleton
    have hopen1 : IsOpen (({1} : Set ℝ)ᶜ) := isOpen_compl_singleton
    simpa [regularBranch] using hopen0.inter hopen1
  have hsource : ∀ t ∈ regularBranch, sourceIntegrand t = -3 / 2 := by
    intro t ht
    have ht0 : t ≠ 0 := ht.1
    have ht1 : t ≠ 1 := ht.2
    have hden : t ^ 3 - 1 ≠ 0 := by
      intro hzero
      have hfac : (t - 1) * (t ^ 2 + t + 1) = 0 := by
        calc
          (t - 1) * (t ^ 2 + t + 1) = t ^ 3 - 1 := by ring
          _ = 0 := hzero
      rcases mul_eq_zero.mp hfac with h | h
      · exact ht1 (sub_eq_zero.mp h)
      · have hpos : 0 < t ^ 2 + t + 1 := by
          nlinarith [sq_nonneg (2 * t + 1)]
        exact (ne_of_gt hpos) h
    have harg :
        (xOf t + 1) ^ 2 * (xOf t - 1) ^ 4 =
          (4 * t ^ 2 / (t ^ 3 - 1) ^ 2) ^ 3 := by
      unfold xOf
      field_simp [hden]
      ring
    have hderiv : deriv xOf t = -6 * t ^ 2 / (t ^ 3 - 1) ^ 2 :=
      (gap2 t ht1).deriv
    unfold sourceIntegrand
    rw [hderiv, harg, cubeRoot_cube]
    field_simp [hden, ht0]
    ring
  apply Set.ext
  intro F
  constructor
  · intro hF
    refine ⟨fun t => (-2 / 3 : ℝ) * F t, ?_, ?_⟩
    · intro t ht
      have hFt := hF t ht
      rw [hsource t ht] at hFt
      convert hFt.const_mul (-2 / 3 : ℝ) using 1 <;> norm_num
    · intro t ht
      ring
  · rintro ⟨G, hG, hFG⟩
    intro t ht
    have hscaled :
        HasDerivAt (fun x => (-3 / 2 : ℝ) * G x) (-3 / 2) t := by
      convert (hG t ht).const_mul (-3 / 2 : ℝ) using 1 <;> norm_num
    have heq : F =ᶠ[nhds t] fun x => (-3 / 2 : ℝ) * G x := by
      filter_upwards [hopen.mem_nhds ht] with x hx
      exact hFG x hx
    have hFt := hscaled.congr_of_eventuallyEq heq
    rw [hsource t ht]
    exact hFt
theorem gap4 :
    ConstantScaledFamily =
      BranchwisePrimitiveFamilyOn regularBranch linearPrimitive := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨G, hG, hFG⟩
    intro u huOpen huPre huSub
    by_cases huNonempty : u.Nonempty
    · rcases huNonempty with ⟨a, ha⟩
      let H : ℝ → ℝ := fun x => G x - x
      have hH : ∀ x ∈ u, HasDerivAt H 0 x := by
        intro x hx
        dsimp [H]
        convert (hG x (huSub hx)).sub (hasDerivAt_id x) using 1 <;> ring
      have hDiff : DifferentiableOn ℝ H u := by
        intro x hx
        exact (hH x hx).differentiableAt.differentiableWithinAt
      have hDeriv : ∀ x ∈ u, deriv H x = 0 := by
        intro x hx
        exact (hH x hx).deriv
      have hConst : ∀ x ∈ u, ∀ y ∈ u, H x = H y := by
        intro x hx y hy
        exact huOpen.is_const_of_deriv_eq_zero huPre hDiff hDeriv hx hy
      refine ⟨(-3 / 2 : ℝ) * H a, ?_⟩
      intro x hx
      rw [hFG x (huSub hx)]
      have hxconst : H x = H a := hConst x hx a ha
      dsimp [linearPrimitive, H] at hxconst ⊢
      rw [← hxconst]
      ring
    · refine ⟨0, ?_⟩
      intro x hx
      exact False.elim (huNonempty ⟨x, hx⟩)
  · intro hF
    have hlocal : ∀ t ∈ regularBranch,
        ∃ u : Set ℝ, IsOpen u ∧ IsPreconnected u ∧ u ⊆ regularBranch ∧ t ∈ u := by
      intro t ht
      rcases lt_or_gt_of_ne ht.1 with htneg | htpos
      · refine ⟨Set.Iio 0, isOpen_Iio, isPreconnected_Iio, ?_, htneg⟩
        intro x hx
        exact ⟨ne_of_lt hx, ne_of_lt (lt_trans hx zero_lt_one)⟩
      · rcases lt_or_gt_of_ne ht.2 with htlt | htgt
        · refine ⟨Set.Ioo 0 1, isOpen_Ioo, isPreconnected_Ioo, ?_, ⟨htpos, htlt⟩⟩
          intro x hx
          exact ⟨ne_of_gt hx.1, ne_of_lt hx.2⟩
        · refine ⟨Set.Ioi 1, isOpen_Ioi, isPreconnected_Ioi, ?_, htgt⟩
          intro x hx
          exact ⟨ne_of_gt (lt_trans zero_lt_one hx), ne_of_gt hx⟩
    have hFderiv : ∀ t ∈ regularBranch, HasDerivAt F (-3 / 2) t := by
      intro t ht
      rcases hlocal t ht with ⟨u, huOpen, huPre, huSub, htu⟩
      rcases hF u huOpen huPre huSub with ⟨C, hC⟩
      have heq : F =ᶠ[nhds t] fun x => linearPrimitive x + C := by
        filter_upwards [huOpen.mem_nhds htu] with x hx
        exact hC x hx
      have hlin : HasDerivAt (fun x => linearPrimitive x + C) (-3 / 2) t := by
        unfold linearPrimitive
        convert ((hasDerivAt_id t).const_mul (-3 / 2 : ℝ)).add_const C using 1 <;> ring
      exact hlin.congr_of_eventuallyEq heq
    refine ⟨fun t => (-2 / 3 : ℝ) * F t, ?_, ?_⟩
    · intro t ht
      convert (hFderiv t ht).const_mul (-2 / 3 : ℝ) using 1 <;> norm_num
    · intro t ht
      ring
theorem gap5 :
    BranchwisePrimitiveFamilyOn regularBranch linearPrimitive =
      BranchwisePrimitiveFamilyOn regularBranch rootPrimitive := by
  have hroot : ∀ t ∈ regularBranch, rootPrimitive t = linearPrimitive t := by
    intro t ht
    have ht1 : t ≠ 1 := ht.2
    have hden : t ^ 3 - 1 ≠ 0 := by
      intro hzero
      have hfac : (t - 1) * (t ^ 2 + t + 1) = 0 := by
        calc
          (t - 1) * (t ^ 2 + t + 1) = t ^ 3 - 1 := by ring
          _ = 0 := hzero
      rcases mul_eq_zero.mp hfac with h | h
      · exact ht1 (sub_eq_zero.mp h)
      · have hpos : 0 < t ^ 2 + t + 1 := by
          nlinarith [sq_nonneg (2 * t + 1)]
        exact (ne_of_gt hpos) h
    have hratio : (xOf t + 1) / (xOf t - 1) = t ^ 3 := by
      unfold xOf
      field_simp [hden]
      ring
    unfold rootPrimitive linearPrimitive
    rw [hratio, cubeRoot_cube]
  apply Set.ext
  intro F
  constructor
  · intro hF u huOpen huPre huSub
    rcases hF u huOpen huPre huSub with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [hroot t (huSub ht)]
    exact hC t ht
  · intro hF u huOpen huPre huSub
    rcases hF u huOpen huPre huSub with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro t ht
    rw [← hroot t (huSub ht)]
    exact hC t ht
theorem gap6 :
    AntiderivativesOn regularBranch sourceIntegrand =
      BranchwisePrimitiveFamilyOn regularBranch rootPrimitive := by
  calc
    AntiderivativesOn regularBranch sourceIntegrand = ConstantScaledFamily := gap3
    _ = BranchwisePrimitiveFamilyOn regularBranch linearPrimitive := gap4
    _ = BranchwisePrimitiveFamilyOn regularBranch rootPrimitive := gap5

end
end ProofGap.Exercise1932
