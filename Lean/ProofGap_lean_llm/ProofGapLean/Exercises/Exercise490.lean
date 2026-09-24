import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise490

noncomputable section

def original (a x : ℝ) : ℝ :=
  (Real.tan (a + 2 * x) - 2 * Real.tan (a + x) + Real.tan a) / x ^ 2
def differenceForm (a x : ℝ) : ℝ :=
  (Real.tan (a + 2 * x) - Real.tan (a + x) -
    (Real.tan (a + x) - Real.tan a)) / x ^ 2
def expanded (a x : ℝ) : ℝ :=
  (((Real.sin (a + 2 * x) * Real.cos (a + x) -
      Real.cos (a + 2 * x) * Real.sin (a + x)) /
      (Real.cos (a + 2 * x) * Real.cos (a + x))) +
    ((-Real.cos a * Real.sin (a + x) +
      Real.cos (a + x) * Real.sin a) /
      (Real.cos (a + x) * Real.cos a))) / x ^ 2
def combined (a x : ℝ) : ℝ :=
  Real.sin x * (Real.cos (a + x) * Real.cos a -
    Real.cos (a + x) * Real.cos (a + 2 * x)) /
    (x ^ 2 * Real.cos a * Real.cos (a + 2 * x) * Real.cos (a + x) ^ 2)
def normalized (a x : ℝ) : ℝ :=
  (Real.sin x / x) ^ 2 *
    (2 * Real.sin (a + x) /
      (Real.cos a * Real.cos (a + 2 * x) * Real.cos (a + x)))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

private theorem eventually_admissible
    (a : ℝ) (ha : Real.cos a ≠ 0) :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      x ≠ 0 ∧ Real.cos (a + x) ≠ 0 ∧
        Real.cos (a + 2 * x) ≠ 0 := by
  have hx0 :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    (show Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) from
      continuousAt_id).mono_left inf_le_left
  have hax :
      Filter.Tendsto (fun x : ℝ => a + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using tendsto_const_nhds.add hx0
  have htwo :
      Filter.Tendsto (fun x : ℝ => 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hx0
  have hax2 :
      Filter.Tendsto (fun x : ℝ => a + 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using tendsto_const_nhds.add htwo
  have hc1 :
      Filter.Tendsto (fun x : ℝ => Real.cos (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.cos a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_cos.tendsto a).comp hax
  have hc2 :
      Filter.Tendsto (fun x : ℝ => Real.cos (a + 2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.cos a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_cos.tendsto a).comp hax2
  have he1 :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.cos (a + x) ≠ 0 :=
    hc1.eventually (eventually_ne_nhds ha)
  have he2 :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.cos (a + 2 * x) ≠ 0 :=
    hc2.eventually (eventually_ne_nhds ha)
  filter_upwards [self_mem_nhdsWithin, he1, he2] with x hx h1 h2
  exact ⟨by simpa using hx, h1, h2⟩

private theorem original_eq_expanded_at
    (a x : ℝ) (hx : x ≠ 0) (ha : Real.cos a ≠ 0)
    (h1 : Real.cos (a + x) ≠ 0)
    (h2 : Real.cos (a + 2 * x) ≠ 0) :
    original a x = expanded a x := by
  unfold original expanded
  rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos,
    Real.tan_eq_sin_div_cos]
  field_simp [hx, ha, h1, h2]
  ring

private theorem expanded_eq_combined_at
    (a x : ℝ) (hx : x ≠ 0) (ha : Real.cos a ≠ 0)
    (h1 : Real.cos (a + x) ≠ 0)
    (h2 : Real.cos (a + 2 * x) ≠ 0) :
    expanded a x = combined a x := by
  have hfirst :
      Real.sin (a + 2 * x) * Real.cos (a + x) -
          Real.cos (a + 2 * x) * Real.sin (a + x) =
        Real.sin x := by
    calc
      _ = Real.sin ((a + 2 * x) - (a + x)) := by
        rw [Real.sin_sub]
      _ = Real.sin x := by congr 1 <;> ring
  have hsecond :
      -Real.cos a * Real.sin (a + x) +
          Real.cos (a + x) * Real.sin a =
        -Real.sin x := by
    calc
      _ = Real.sin (a - (a + x)) := by
        rw [Real.sin_sub]
        ring
      _ = -Real.sin x := by
        rw [show a - (a + x) = -x by ring, Real.sin_neg]
  unfold expanded combined
  rw [hfirst, hsecond]
  field_simp [hx, ha, h1, h2]
  ring

private theorem combined_eq_normalized_at
    (a x : ℝ) (hx : x ≠ 0) (ha : Real.cos a ≠ 0)
    (h1 : Real.cos (a + x) ≠ 0)
    (h2 : Real.cos (a + 2 * x) ≠ 0) :
    combined a x = normalized a x := by
  have hminus :
      Real.cos a =
        Real.cos (a + x) * Real.cos x +
          Real.sin (a + x) * Real.sin x := by
    calc
      Real.cos a = Real.cos ((a + x) - x) := by congr 1 <;> ring
      _ = _ := by rw [Real.cos_sub]
  have hplus :
      Real.cos (a + 2 * x) =
        Real.cos (a + x) * Real.cos x -
          Real.sin (a + x) * Real.sin x := by
    calc
      Real.cos (a + 2 * x) = Real.cos ((a + x) + x) := by congr 1 <;> ring
      _ = _ := by rw [Real.cos_add]
  have hdiff :
      Real.cos a - Real.cos (a + 2 * x) =
        2 * Real.sin (a + x) * Real.sin x := by
    rw [hminus, hplus]
    ring
  unfold combined normalized
  rw [show
    Real.cos (a + x) * Real.cos a -
        Real.cos (a + x) * Real.cos (a + 2 * x) =
      Real.cos (a + x) *
        (Real.cos a - Real.cos (a + 2 * x)) by ring, hdiff]
  field_simp [hx, ha, h1, h2]

private theorem tendsto_sin_div_zero :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hslope :
      Filter.Tendsto (slope Real.sin 0)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using (Real.hasDerivAt_sin 0).tendsto_slope
  apply hslope.congr'
  refine Filter.Eventually.of_forall ?_
  intro x
  change (x - 0)⁻¹ • (Real.sin x - Real.sin 0) = Real.sin x / x
  simp [div_eq_mul_inv, mul_comm]

/-- Exercise 490, gap 1; require `cos a≠0`. -/
theorem gap1 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (differenceForm a) L := by
  have h : original a = differenceForm a := by
    funext x
    unfold original differenceForm
    ring
  rw [h]

/-- Exercise 490, gap 2; require `cos a≠0`. -/
theorem gap2 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (expanded a) L := by
  unfold HasLimitAtZero
  have heq :
      original a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] expanded a := by
    filter_upwards [eventually_admissible a ha] with x hx
    exact original_eq_expanded_at a x hx.1 ha hx.2.1 hx.2.2
  exact ⟨fun h => h.congr' heq, fun h => h.congr' heq.symm⟩

/-- Exercise 490, gap 3; require `cos a≠0`. -/
theorem gap3 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (combined a) L := by
  calc
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (expanded a) L :=
      gap2 a ha L
    _ ↔ HasLimitAtZero (combined a) L := by
      unfold HasLimitAtZero
      have heq :
          expanded a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] combined a := by
        filter_upwards [eventually_admissible a ha] with x hx
        exact expanded_eq_combined_at a x hx.1 ha hx.2.1 hx.2.2
      exact ⟨fun h => h.congr' heq, fun h => h.congr' heq.symm⟩

/-- Exercise 490, gap 4; require `cos a≠0`. -/
theorem gap4 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAtZero (combined a) L ↔ HasLimitAtZero (normalized a) L := by
  unfold HasLimitAtZero
  have heq :
      combined a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized a := by
    filter_upwards [eventually_admissible a ha] with x hx
    exact combined_eq_normalized_at a x hx.1 ha hx.2.1 hx.2.2
  exact ⟨fun h => h.congr' heq, fun h => h.congr' heq.symm⟩

/-- Exercise 490, gap 5; require `cos a≠0`. -/
theorem gap5 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (normalized a) L := by
  exact (gap3 a ha L).trans (gap4 a ha L)

/-- Exercise 490, gap 6; require `cos a≠0`. -/
theorem gap6 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAtZero (original a) (2 * Real.sin a / Real.cos a ^ 3) := by
  apply (gap5 a ha (2 * Real.sin a / Real.cos a ^ 3)).mpr
  unfold HasLimitAtZero
  have hx0 :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    (show Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) from
      continuousAt_id).mono_left inf_le_left
  have hax :
      Filter.Tendsto (fun x : ℝ => a + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using tendsto_const_nhds.add hx0
  have htwo :
      Filter.Tendsto (fun x : ℝ => 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using tendsto_const_nhds.mul hx0
  have hax2 :
      Filter.Tendsto (fun x : ℝ => a + 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using tendsto_const_nhds.add htwo
  have hs1 :
      Filter.Tendsto (fun x : ℝ => Real.sin (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sin a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_sin.tendsto a).comp hax
  have hc1 :
      Filter.Tendsto (fun x : ℝ => Real.cos (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.cos a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_cos.tendsto a).comp hax
  have hc2 :
      Filter.Tendsto (fun x : ℝ => Real.cos (a + 2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.cos a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_cos.tendsto a).comp hax2
  have hden :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.cos a * Real.cos (a + 2 * x) * Real.cos (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (Real.cos a * Real.cos a * Real.cos a)) :=
    (tendsto_const_nhds.mul hc2).mul hc1
  have hfrac :
      Filter.Tendsto
        (fun x : ℝ =>
          2 * Real.sin (a + x) /
            (Real.cos a * Real.cos (a + 2 * x) * Real.cos (a + x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds
          (2 * Real.sin a /
            (Real.cos a * Real.cos a * Real.cos a))) :=
    (tendsto_const_nhds.mul hs1).div hden
      (mul_ne_zero (mul_ne_zero ha ha) ha)
  have hprod :
      Filter.Tendsto (normalized a)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds
          (2 * Real.sin a /
            (Real.cos a * Real.cos a * Real.cos a))) := by
    unfold normalized
    simpa only [one_pow, one_mul] using
      (tendsto_sin_div_zero.pow 2).mul hfrac
  have hcube :
      Real.cos a * Real.cos a * Real.cos a = Real.cos a ^ 3 := by ring
  simpa only [hcube] using hprod

end

end ProofGap.Exercise490
