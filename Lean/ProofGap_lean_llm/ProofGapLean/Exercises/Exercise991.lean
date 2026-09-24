import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise991

open Filter

noncomputable section

def f (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ 2 * Real.sin (1 / x)

def dq (g : ℝ → ℝ) (a h : ℝ) : ℝ :=
  (g (a + h) - g a) / h

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt f (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
  have hinv :
      HasDerivAt (fun y : ℝ => 1 / y) (-1 / x ^ 2) x := by
    simpa [one_div] using (hasDerivAt_id x).inv hx
  have hsin :
      HasDerivAt (fun y : ℝ => Real.sin (1 / y))
        (Real.cos (1 / x) * (-1 / x ^ 2)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sin (1 / x)).comp x hinv
  have hid : HasDerivAt (fun y : ℝ => y) 1 x :=
    hasDerivAt_id x
  have hsq :
      HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa [pow_two, two_mul] using hid.mul hid
  have hmain :
      HasDerivAt (fun y : ℝ => y ^ 2 * Real.sin (1 / y))
        (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
    convert hsq.mul hsin using 1 <;> field_simp [hx] <;> ring
  have hf :
      HasDerivAt f (2 * x * Real.sin (1 / x) - Real.cos (1 / x)) x := by
    apply hmain.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx] with y hy
    simp [f, hy]
  exact hf

theorem gap2 :
    HasDerivAt f 0 0 ↔
      Tendsto (dq f 0) (nhds 0) (nhds 0) := by
  constructor
  · intro hf
    have hslope :=
      (hasDerivAt_iff_tendsto_slope_zero
        (f := f) (f' := (0 : ℝ)) (x := (0 : ℝ))).1 hf
    have hp :
        Tendsto (dq f 0) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      refine hslope.congr' ?_
      exact Filter.Eventually.of_forall (fun h => by
        change h⁻¹ * (f (0 + h) - f 0) = dq f 0 h
        simp only [dq, zero_add, div_eq_mul_inv]
        exact mul_comm _ _)
    rw [tendsto_def] at hp ⊢
    intro s hs
    have hpre := hp s hs
    rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.1 hpre with
      ⟨u, hu, hus⟩
    refine mem_of_superset hu ?_
    intro h hh
    change dq f 0 h ∈ s
    by_cases hzero : h = 0
    · subst h
      simpa [dq] using (mem_of_mem_nhds hs)
    · apply hus
      constructor
      · exact hh
      · simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzero
  · intro hq
    have hp :
        Tendsto (dq f 0) (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
      hq.mono_left inf_le_left
    apply
      (hasDerivAt_iff_tendsto_slope_zero
        (f := f) (f' := (0 : ℝ)) (x := (0 : ℝ))).2
    refine hp.congr' ?_
    exact Filter.Eventually.of_forall (fun h => by
      change dq f 0 h = h⁻¹ * (f (0 + h) - f 0)
      simp only [dq, zero_add, div_eq_mul_inv]
      exact mul_comm _ _)

theorem gap3 :
    (fun h => dq f 0 h) = fun h => h * Real.sin (1 / h) := by
  funext h
  by_cases hh : h = 0
  · subst h
    simp [dq, f]
  · simp only [dq, zero_add]
    rw [show f h = h ^ 2 * Real.sin (1 / h) by simp [f, hh]]
    rw [show f 0 = 0 by simp [f]]
    field_simp [hh] <;> ring

theorem gap4 :
    Tendsto (fun h : ℝ => h * Real.sin (1 / h)) (nhds 0) (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hid :
      Tendsto (fun h : ℝ => h) (nhds 0) (nhds 0) :=
    tendsto_id
  rw [Metric.tendsto_nhds] at hid
  filter_upwards [hid ε hε] with h hh
  have hsin_abs : |Real.sin (1 / h)| ≤ 1 :=
    abs_le.2 ⟨Real.neg_one_le_sin (1 / h), Real.sin_le_one (1 / h)⟩
  have hsin : ‖Real.sin (1 / h)‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs] using hsin_abs
  calc
    dist (h * Real.sin (1 / h)) 0 =
        ‖h * Real.sin (1 / h)‖ := by
          rw [dist_zero_right]
    _ = ‖h‖ * ‖Real.sin (1 / h)‖ := by
          rw [norm_mul]
    _ ≤ ‖h‖ * 1 :=
      mul_le_mul_of_nonneg_left hsin (norm_nonneg h)
    _ = dist h 0 := by
      rw [mul_one, dist_zero_right]
    _ < ε := hh

theorem gap5 :
    HasDerivAt f 0 0 := by
  apply gap2.mpr
  have hfun : dq f 0 = fun h => h * Real.sin (1 / h) := by
    simpa only using gap3
  rw [hfun]
  exact gap4

theorem gap6 :
    Differentiable ℝ f := by
  intro x
  by_cases hx : x = 0
  · subst x
    exact gap5.differentiableAt
  · exact (gap1 x hx).differentiableAt

theorem gap7 :
    ¬ ∃ L : ℝ,
      Tendsto (fun x => deriv f x) (nhdsWithin 0 {0}ᶜ) (nhds L) := by
  rintro ⟨L, hL⟩
  have hD :
      Tendsto
        (fun x : ℝ =>
          2 * x * Real.sin (1 / x) - Real.cos (1 / x))
        (nhdsWithin 0 {0}ᶜ) (nhds L) := by
    refine hL.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    exact (gap1 x hx0).deriv
  have hzero :
      Tendsto (fun x : ℝ => 2 * x * Real.sin (1 / x))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have hc :
        Tendsto (fun _ : ℝ => (2 : ℝ)) (nhds 0) (nhds 2) :=
      tendsto_const_nhds
    convert (hc.mul gap4).mono_left inf_le_left using 1 <;> ring
  have hcos :
      Tendsto (fun x : ℝ => Real.cos (1 / x))
        (nhdsWithin 0 {0}ᶜ) (nhds (-L)) := by
    convert hzero.sub hD using 1 <;> ring
  have hphase (c : ℝ) :
      Tendsto (fun x : ℝ => x / (1 + c * x))
        (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
    have hc :
        Tendsto (fun _ : ℝ => c) (nhds 0) (nhds c) :=
      tendsto_const_nhds
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1) :=
      tendsto_const_nhds
    have hden0 :
        Tendsto (fun x : ℝ => 1 + c * x) (nhds 0) (nhds 1) := by
      convert hone.add (hc.mul tendsto_id) using 1 <;> ring
    have hquot0 :
        Tendsto (fun x : ℝ => x / (1 + c * x))
          (nhds 0) (nhds 0) := by
      convert tendsto_id.div hden0 one_ne_zero using 1 <;> ring
    have hden :
        Tendsto (fun x : ℝ => 1 + c * x)
          (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
      hden0.mono_left inf_le_left
    have hden_ne :
        ∀ᶠ x in nhdsWithin 0 {0}ᶜ, 1 + c * x ≠ 0 :=
      hden.eventually (eventually_ne_nhds one_ne_zero)
    have hout :
        ∀ᶠ x in nhdsWithin 0 {0}ᶜ,
          x / (1 + c * x) ∈ ({0}ᶜ : Set ℝ) := by
      filter_upwards [self_mem_nhdsWithin, hden_ne] with x hx hdx
      have hx0 : x ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
        div_ne_zero hx0 hdx
    change
      Tendsto (fun x : ℝ => x / (1 + c * x))
        (nhdsWithin 0 {0}ᶜ) (nhds 0 ⊓ principal ({0}ᶜ : Set ℝ))
    exact
      tendsto_inf.2
        ⟨hquot0.mono_left inf_le_left, tendsto_principal.2 hout⟩
  have hphase_eq (c : ℝ) :
      ∀ᶠ x in nhdsWithin 0 {0}ᶜ,
        1 / (x / (1 + c * x)) = 1 / x + c := by
    have hc :
        Tendsto (fun _ : ℝ => c) (nhds 0) (nhds c) :=
      tendsto_const_nhds
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1) :=
      tendsto_const_nhds
    have hden0 :
        Tendsto (fun x : ℝ => 1 + c * x) (nhds 0) (nhds 1) := by
      convert hone.add (hc.mul tendsto_id) using 1 <;> ring
    have hden :
        Tendsto (fun x : ℝ => 1 + c * x)
          (nhdsWithin 0 {0}ᶜ) (nhds 1) :=
      hden0.mono_left inf_le_left
    have hden_ne :
        ∀ᶠ x in nhdsWithin 0 {0}ᶜ, 1 + c * x ≠ 0 :=
      hden.eventually (eventually_ne_nhds one_ne_zero)
    filter_upwards [self_mem_nhdsWithin, hden_ne] with x hx hdx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    field_simp [hx0, hdx] <;> ring
  have hcosPi :
      Tendsto (fun x : ℝ => -Real.cos (1 / x))
        (nhdsWithin 0 {0}ᶜ) (nhds (-L)) := by
    refine (hcos.comp (hphase Real.pi)).congr' ?_
    filter_upwards [hphase_eq Real.pi] with x hx
    change Real.cos (1 / (x / (1 + Real.pi * x))) = -Real.cos (1 / x)
    rw [hx, Real.cos_add]
    simp
  have hnegCos :
      Tendsto (fun x : ℝ => -Real.cos (1 / x))
        (nhdsWithin 0 {0}ᶜ) (nhds L) := by
    convert hcos.neg using 1 <;> ring
  have hsign : -L = L := tendsto_nhds_unique hcosPi hnegCos
  have hL0 : L = 0 := by
    linarith
  have hnegSin :
      Tendsto (fun x : ℝ => -Real.sin (1 / x))
        (nhdsWithin 0 {0}ᶜ) (nhds (-L)) := by
    refine (hcos.comp (hphase (Real.pi / 2))).congr' ?_
    filter_upwards [hphase_eq (Real.pi / 2)] with x hx
    change
      Real.cos (1 / (x / (1 + (Real.pi / 2) * x))) =
        -Real.sin (1 / x)
    rw [hx, Real.cos_add]
    simp
  have hsin :
      Tendsto (fun x : ℝ => Real.sin (1 / x))
        (nhdsWithin 0 {0}ᶜ) (nhds L) := by
    convert hnegSin.neg using 1 <;> ring
  have hsq := (hsin.mul hsin).add (hcos.mul hcos)
  have hone0 :
      Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    convert hsq using 1
    · funext x
      nlinarith [Real.sin_sq_add_cos_sq (1 / x)]
    · rw [hL0]
      norm_num
  have h01 : (0 : ℝ) = 1 :=
    tendsto_nhds_unique hone0 tendsto_const_nhds
  norm_num at h01

theorem gap8 :
    ¬ ContinuousAt (fun x => deriv f x) 0 := by
  intro hcont
  apply gap7
  refine ⟨deriv f 0, ?_⟩
  exact hcont.tendsto.mono_left inf_le_left

theorem gap9 :
    ¬ ContinuousAt (fun x => deriv f x) 0 := by
  exact gap8

end

end ProofGap.Exercise991
