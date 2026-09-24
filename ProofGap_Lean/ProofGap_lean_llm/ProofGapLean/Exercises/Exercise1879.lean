import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.IntermediateValue

open Set Real

namespace ProofGap.Exercise1879

noncomputable section

def domain : Set ℝ := Set.Ioi 1

def integrand (x : ℝ) : ℝ :=
  x / ((x - 1) ^ 2 * (x ^ 2 + 2 * x + 2))

def partialFractions (x : ℝ) : ℝ :=
  1 / (25 * (x - 1)) + 1 / (5 * (x - 1) ^ 2) -
    (x + 8) / (25 * (x ^ 2 + 2 * x + 2))

def antiderivatives (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}

def primitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

def auxiliaryFamily : Set (ℝ → ℝ) :=
  {F | ∃ G H : ℝ → ℝ,
    DifferentiableOn ℝ G domain ∧
      (∀ x ∈ domain, deriv G x = (2 * x + 2) / (x ^ 2 + 2 * x + 2)) ∧
    DifferentiableOn ℝ H domain ∧
      (∀ x ∈ domain, deriv H x = 1 / ((x + 1) ^ 2 + 1)) ∧
    ∀ x ∈ domain, F x =
      (1 / 25 : ℝ) * Real.log |x - 1| - 1 / (5 * (x - 1)) -
        (1 / 50 : ℝ) * G x - (7 / 25 : ℝ) * H x}

def expandedPrimitive (x : ℝ) : ℝ :=
  (1 / 25 : ℝ) * Real.log |x - 1| - 1 / (5 * (x - 1)) -
    (1 / 50 : ℝ) * Real.log (x ^ 2 + 2 * x + 2) -
    (7 / 25 : ℝ) * Real.arctan (x + 1)

def combinedPrimitive (x : ℝ) : ℝ :=
  (1 / 50 : ℝ) *
      Real.log ((x - 1) ^ 2 / (x ^ 2 + 2 * x + 2)) -
    1 / (5 * (x - 1)) - (7 / 25 : ℝ) * Real.arctan (x + 1)

private theorem isOpen_domain : IsOpen domain := by
  simpa [domain] using (isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ)))

private theorem isPreconnected_domain : IsPreconnected domain := by
  simpa [domain] using
    (isPreconnected_Ioi : IsPreconnected (Set.Ioi (1 : ℝ)))

private theorem quadratic_ne_zero (x : ℝ) : x ^ 2 + 2 * x + 2 ≠ 0 := by
  nlinarith [sq_nonneg (x + 1)]

private theorem integrand_eq_partialFractions (x : ℝ) (hx : x ≠ 1) :
    integrand x = partialFractions x := by
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hq := quadratic_ne_zero x
  have hden : (x - 1) ^ 2 * (x ^ 2 + 2 * x + 2) ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx1) hq
  have hfirst :
      1 / (25 * (x - 1)) * ((x - 1) ^ 2 * (x ^ 2 + 2 * x + 2)) =
        (1 / 25 : ℝ) * (x - 1) * (x ^ 2 + 2 * x + 2) := by
    field_simp [hx1]
  have hsecond :
      1 / (5 * (x - 1) ^ 2) * ((x - 1) ^ 2 * (x ^ 2 + 2 * x + 2)) =
        (1 / 5 : ℝ) * (x ^ 2 + 2 * x + 2) := by
    field_simp [hx1]
  have hthird :
      (x + 8) / (25 * (x ^ 2 + 2 * x + 2)) *
          ((x - 1) ^ 2 * (x ^ 2 + 2 * x + 2)) =
        ((x + 8) / 25 : ℝ) * (x - 1) ^ 2 := by
    have h25q : 25 * (x ^ 2 + 2 * x + 2) ≠ 0 :=
      mul_ne_zero (by norm_num) hq
    calc
      (x + 8) / (25 * (x ^ 2 + 2 * x + 2)) *
          ((x - 1) ^ 2 * (x ^ 2 + 2 * x + 2)) =
        ((x + 8) * ((x - 1) ^ 2 * (x ^ 2 + 2 * x + 2))) /
          (25 * (x ^ 2 + 2 * x + 2)) := by ring
      _ = ((x + 8) / 25 : ℝ) * (x - 1) ^ 2 := by
        apply (div_eq_iff h25q).2
        ring
  unfold integrand
  apply (div_eq_iff hden).2
  unfold partialFractions
  rw [sub_mul, add_mul, hfirst, hsecond, hthird]
  ring

private theorem quadraticLog_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.log (y ^ 2 + 2 * y + 2))
      ((2 * x + 2) / (x ^ 2 + 2 * x + 2)) x := by
  have hq := quadratic_ne_zero x
  have hpoly : HasDerivAt (fun y : ℝ => y ^ 2 + 2 * y + 2) (2 * x + 2) x := by
    convert ((((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_id x).const_mul 2)).add_const 2) using 1 <;>
      simp [id] <;> ring
  convert (Real.hasDerivAt_log hq).comp x hpoly using 1 <;>
    field_simp [hq] <;> ring

private theorem shiftedArctan_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.arctan (y + 1))
      (1 / ((x + 1) ^ 2 + 1)) x := by
  convert (Real.hasDerivAt_arctan (x + 1)).comp x
    ((hasDerivAt_id x).add_const 1) using 1 <;>
    simp [Function.comp_def, id] <;> ring

private theorem decomposition_hasDerivAt
    (x : ℝ) (hx : x ∈ domain) (G H : ℝ → ℝ)
    (hG : HasDerivAt G ((2 * x + 2) / (x ^ 2 + 2 * x + 2)) x)
    (hH : HasDerivAt H (1 / ((x + 1) ^ 2 + 1)) x) :
    HasDerivAt
      (fun y =>
        (1 / 25 : ℝ) * Real.log |y - 1| - 1 / (5 * (y - 1)) -
          (1 / 50 : ℝ) * G y - (7 / 25 : ℝ) * H y)
      (integrand x) x := by
  have hxgt : 1 < x := hx
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hxgt)
  have hq := quadratic_ne_zero x
  have hlogplain : HasDerivAt (fun y : ℝ => Real.log (y - 1)) (1 / (x - 1)) x := by
    convert (Real.hasDerivAt_log hx1).comp x
      ((hasDerivAt_id x).sub_const 1) using 1 <;>
      simp [Function.comp_def, id] <;> field_simp [hx1] <;> ring
  have hlog : HasDerivAt (fun y : ℝ => Real.log |y - 1|) (1 / (x - 1)) x := by
    have heq : (fun y : ℝ => Real.log |y - 1|) =ᶠ[nhds x]
        (fun y : ℝ => Real.log (y - 1)) := by
      filter_upwards [isOpen_domain.mem_nhds hx] with y hy
      rw [abs_of_pos (sub_pos.mpr hy)]
    exact hlogplain.congr_of_eventuallyEq heq
  have hden : HasDerivAt (fun y : ℝ => 5 * (y - 1)) 5 x := by
    convert (hasDerivAt_const x (5 : ℝ)).mul
      ((hasDerivAt_id x).sub_const 1) using 1 <;> simp [id] <;> ring
  have hrecip := hden.inv (mul_ne_zero (by norm_num) hx1)
  have htotal :=
    (((hlog.const_mul (1 / 25 : ℝ)).sub hrecip).sub
      (hG.const_mul (1 / 50 : ℝ))).sub (hH.const_mul (7 / 25 : ℝ))
  convert htotal using 1
  · funext y
    dsimp
    ring
  · rw [integrand_eq_partialFractions x (ne_of_gt hxgt)]
    unfold partialFractions
    have hshift : (x + 1) ^ 2 + 1 = x ^ 2 + 2 * x + 2 := by ring
    rw [hshift]
    field_simp [hx1, hq]
    ring

private theorem expandedPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt expandedPrimitive (integrand x) x := by
  unfold expandedPrimitive
  exact decomposition_hasDerivAt x hx
    (fun y : ℝ => Real.log (y ^ 2 + 2 * y + 2))
    (fun y : ℝ => Real.arctan (y + 1))
    (quadraticLog_hasDerivAt x) (shiftedArctan_hasDerivAt x)

private theorem antiderivatives_eq_primitive_expanded :
    antiderivatives integrand = primitiveFamily expandedPrimitive := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hdiff : DifferentiableOn ℝ (fun x => F x - expandedPrimitive x) domain :=
      hFdiff.sub fun x hx =>
        (expandedPrimitive_hasDerivAt x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ domain,
        deriv (fun y => F y - expandedPrimitive y) x = 0 := by
      intro x hx
      have hFat := hFdiff.differentiableAt (isOpen_domain.mem_nhds hx)
      have hsub : HasDerivAt (fun y => F y - expandedPrimitive y) 0 x := by
        convert hFat.hasDerivAt.sub (expandedPrimitive_hasDerivAt x hx) using 1
        rw [hFderiv x hx]
        ring
      exact hsub.deriv
    refine ⟨F 2 - expandedPrimitive 2, ?_⟩
    intro x hx
    have htwo : (2 : ℝ) ∈ domain := by norm_num [domain]
    have h : F x - expandedPrimitive x = F 2 - expandedPrimitive 2 := by
      exact isOpen_domain.is_const_of_deriv_eq_zero
        isPreconnected_domain hdiff hzero hx htwo
    linarith
  · rintro ⟨C, hFC⟩
    have hFhas : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
      intro x hx
      have heq : F =ᶠ[nhds x] fun y => expandedPrimitive y + C := by
        filter_upwards [isOpen_domain.mem_nhds hx] with y hy
        exact hFC y hy
      exact ((expandedPrimitive_hasDerivAt x hx).add_const C).congr_of_eventuallyEq heq
    exact ⟨
      fun x hx => (hFhas x hx).differentiableAt.differentiableWithinAt,
      fun x hx => (hFhas x hx).deriv⟩

private theorem expandedPrimitive_eq_combinedPrimitive (x : ℝ) (hx : x ∈ domain) :
    expandedPrimitive x = combinedPrimitive x := by
  have hxpos : 0 < x - 1 := sub_pos.mpr hx
  have hx1 : x - 1 ≠ 0 := ne_of_gt hxpos
  have hq := quadratic_ne_zero x
  have hlog :
      Real.log ((x - 1) ^ 2 / (x ^ 2 + 2 * x + 2)) =
        2 * Real.log |x - 1| - Real.log (x ^ 2 + 2 * x + 2) := by
    rw [Real.log_div (pow_ne_zero 2 hx1) hq, Real.log_pow]
    rw [abs_of_pos hxpos]
    norm_num
  unfold expandedPrimitive combinedPrimitive
  rw [hlog]
  ring

theorem gap1 :
    ∃ A B C D : ℝ, ∀ x, x ≠ 1 →
      integrand x = A / (x - 1) + B / (x - 1) ^ 2 +
        (C * x + D) / (x ^ 2 + 2 * x + 2) := by
  refine ⟨(1 / 25 : ℝ), (1 / 5 : ℝ), -(1 / 25 : ℝ), -(8 / 25 : ℝ), ?_⟩
  intro x hx
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  have hq := quadratic_ne_zero x
  calc
    integrand x = partialFractions x := integrand_eq_partialFractions x hx
    _ = (1 / 25 : ℝ) / (x - 1) + (1 / 5 : ℝ) / (x - 1) ^ 2 +
          (-(1 / 25 : ℝ) * x + -(8 / 25 : ℝ)) /
            (x ^ 2 + 2 * x + 2) := by
      unfold partialFractions
      field_simp [hx1, hq] <;> ring

theorem gap2 :
    ∃ A B C D : ℝ, ∀ x, x =
      A * (x - 1) * (x ^ 2 + 2 * x + 2) +
        B * (x ^ 2 + 2 * x + 2) + (C * x + D) * (x - 1) ^ 2 := by
  refine ⟨(1 / 25 : ℝ), (1 / 5 : ℝ), -(1 / 25 : ℝ), -(8 / 25 : ℝ), ?_⟩
  intro x
  ring

theorem gap3 : ∃ A C : ℝ, A + C = 0 := by
  exact ⟨0, 0, by norm_num⟩

theorem gap4 : ∃ A B C D : ℝ, A + B - 2 * C + D = 0 := by
  exact ⟨0, 0, 0, 0, by norm_num⟩

theorem gap5 : ∃ B C D : ℝ, 2 * B + C - 2 * D = 1 := by
  exact ⟨(1 / 2 : ℝ), 0, 0, by norm_num⟩

theorem gap6 : ∃ A B D : ℝ, -2 * A + 2 * B + D = 0 := by
  exact ⟨0, 0, 0, by norm_num⟩

theorem gap7 : ∃ A : ℝ, A = (1 / 25 : ℝ) := by
  exact ⟨(1 / 25 : ℝ), rfl⟩

theorem gap8 : ∃ B : ℝ, B = (1 / 5 : ℝ) := by
  exact ⟨(1 / 5 : ℝ), rfl⟩

theorem gap9 : ∃ C : ℝ, C = -(1 / 25 : ℝ) := by
  exact ⟨-(1 / 25 : ℝ), rfl⟩

theorem gap10 : ∃ D : ℝ, D = -(8 / 25 : ℝ) := by
  exact ⟨-(8 / 25 : ℝ), rfl⟩

theorem gap11 :
    antiderivatives integrand = antiderivatives partialFractions := by
  apply Set.ext
  intro F
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [← integrand_eq_partialFractions x (ne_of_gt hx)]
    exact hderiv x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [integrand_eq_partialFractions x (ne_of_gt hx)]
    exact hderiv x hx

theorem gap12 : antiderivatives integrand = auxiliaryFamily := by
  rw [antiderivatives_eq_primitive_expanded]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hFC⟩
    refine ⟨
      (fun y : ℝ => Real.log (y ^ 2 + 2 * y + 2) - 50 * C),
      (fun y : ℝ => Real.arctan (y + 1)), ?_, ?_, ?_, ?_, ?_⟩
    · intro x hx
      exact ((quadraticLog_hasDerivAt x).sub_const (50 * C)).differentiableAt.differentiableWithinAt
    · intro x hx
      exact ((quadraticLog_hasDerivAt x).sub_const (50 * C)).deriv
    · intro x hx
      exact (shiftedArctan_hasDerivAt x).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (shiftedArctan_hasDerivAt x).deriv
    · intro x hx
      rw [hFC x hx]
      unfold expandedPrimitive
      ring
  · rintro ⟨G, H, hGdiff, hGderiv, hHdiff, hHderiv, hF⟩
    have hanti : F ∈ antiderivatives integrand := by
      have hFhas : ∀ x ∈ domain, HasDerivAt F (integrand x) x := by
        intro x hx
        have hGat : HasDerivAt G ((2 * x + 2) / (x ^ 2 + 2 * x + 2)) x := by
          have h := (hGdiff.differentiableAt (isOpen_domain.mem_nhds hx)).hasDerivAt
          rw [hGderiv x hx] at h
          exact h
        have hHat : HasDerivAt H (1 / ((x + 1) ^ 2 + 1)) x := by
          have h := (hHdiff.differentiableAt (isOpen_domain.mem_nhds hx)).hasDerivAt
          rw [hHderiv x hx] at h
          exact h
        have hbase := decomposition_hasDerivAt x hx G H hGat hHat
        have heq : F =ᶠ[nhds x] fun y =>
            (1 / 25 : ℝ) * Real.log |y - 1| - 1 / (5 * (y - 1)) -
              (1 / 50 : ℝ) * G y - (7 / 25 : ℝ) * H y := by
          filter_upwards [isOpen_domain.mem_nhds hx] with y hy
          exact hF y hy
        exact hbase.congr_of_eventuallyEq heq
      exact ⟨
        fun x hx => (hFhas x hx).differentiableAt.differentiableWithinAt,
        fun x hx => (hFhas x hx).deriv⟩
    rw [← antiderivatives_eq_primitive_expanded]
    exact hanti

theorem gap13 :
    antiderivatives integrand = primitiveFamily expandedPrimitive := by
  exact antiderivatives_eq_primitive_expanded

theorem gap14 :
    antiderivatives integrand = primitiveFamily combinedPrimitive := by
  rw [gap13]
  apply Set.ext
  intro F
  constructor
  · rintro ⟨C, hFC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hFC x hx, expandedPrimitive_eq_combinedPrimitive x hx]
  · rintro ⟨C, hFC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [hFC x hx, expandedPrimitive_eq_combinedPrimitive x hx]

end

end ProofGap.Exercise1879
