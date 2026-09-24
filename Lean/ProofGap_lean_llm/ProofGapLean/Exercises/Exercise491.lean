import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise491

noncomputable section

def cot (x : ℝ) : ℝ := Real.cos x / Real.sin x
def original (a x : ℝ) : ℝ :=
  (cot (a + 2 * x) - 2 * cot (a + x) + cot a) / x ^ 2
def expanded (a x : ℝ) : ℝ :=
  (-Real.sin x * Real.sin (a + x) *
    (Real.sin a - Real.sin (a + 2 * x))) /
    (x ^ 2 * Real.sin a * Real.sin (a + x) ^ 2 * Real.sin (a + 2 * x))
def normalized (a x : ℝ) : ℝ :=
  (Real.sin x / x) ^ 2 *
    (2 * Real.cos (a + x) /
      (Real.sin a * Real.sin (a + x) * Real.sin (a + 2 * x)))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_491/1.txt`; require `sin a≠0`. -/
private theorem cot_sub_cot
    (u v : ℝ) (hu : Real.sin u ≠ 0) (hv : Real.sin v ≠ 0) :
    cot u - cot v =
      Real.sin (v - u) / (Real.sin u * Real.sin v) := by
  unfold cot
  field_simp [hu, hv]
  rw [Real.sin_sub]
  ring

private theorem original_eq_expanded_at
    (a x : ℝ) (hx : x ≠ 0) (ha : Real.sin a ≠ 0)
    (h1 : Real.sin (a + x) ≠ 0)
    (h2 : Real.sin (a + 2 * x) ≠ 0) :
    original a x = expanded a x := by
  unfold original expanded
  have hsplit :
      cot (a + 2 * x) - 2 * cot (a + x) + cot a =
        (cot (a + 2 * x) - cot (a + x)) -
          (cot (a + x) - cot a) := by
    ring
  rw [hsplit,
    cot_sub_cot (a + 2 * x) (a + x) h2 h1,
    cot_sub_cot (a + x) a h1 ha]
  rw [show a + x - (a + 2 * x) = -x by ring,
    show a - (a + x) = -x by ring, Real.sin_neg]
  field_simp [hx, ha, h1, h2]
  ring

private theorem expanded_eq_normalized_at
    (a x : ℝ) (hx : x ≠ 0) (ha : Real.sin a ≠ 0)
    (h1 : Real.sin (a + x) ≠ 0)
    (h2 : Real.sin (a + 2 * x) ≠ 0) :
    expanded a x = normalized a x := by
  have hminus :
      Real.sin a =
        Real.sin (a + x) * Real.cos x -
          Real.cos (a + x) * Real.sin x := by
    calc
      Real.sin a = Real.sin ((a + x) - x) := by
        congr 1
        ring
      _ = Real.sin (a + x) * Real.cos x -
          Real.cos (a + x) * Real.sin x := by
        rw [Real.sin_sub]
  have hplus :
      Real.sin (a + 2 * x) =
        Real.sin (a + x) * Real.cos x +
          Real.cos (a + x) * Real.sin x := by
    calc
      Real.sin (a + 2 * x) = Real.sin ((a + x) + x) := by
        congr 1
        ring
      _ = Real.sin (a + x) * Real.cos x +
          Real.cos (a + x) * Real.sin x := by
        rw [Real.sin_add]
  have htrig :
      Real.sin a - Real.sin (a + 2 * x) =
        -2 * Real.cos (a + x) * Real.sin x := by
    rw [hminus, hplus]
    ring
  unfold expanded normalized
  rw [htrig]
  field_simp [hx, ha, h1, h2]

private theorem eventually_admissible
    (a : ℝ) (ha : Real.sin a ≠ 0) :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      x ≠ 0 ∧ Real.sin (a + x) ≠ 0 ∧
        Real.sin (a + 2 * x) ≠ 0 := by
  have hx0 :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    (show Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) from
      continuousAt_id).mono_left inf_le_left
  have hax :
      Filter.Tendsto (fun x : ℝ => a + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using (tendsto_const_nhds.add hx0)
  have htwo :
      Filter.Tendsto (fun x : ℝ => 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hx0)
  have hax2 :
      Filter.Tendsto (fun x : ℝ => a + 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using (tendsto_const_nhds.add htwo)
  have hs1 :
      Filter.Tendsto (fun x : ℝ => Real.sin (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sin a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_sin.tendsto a).comp hax
  have hs2 :
      Filter.Tendsto (fun x : ℝ => Real.sin (a + 2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sin a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_sin.tendsto a).comp hax2
  have he1 :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.sin (a + x) ≠ 0 :=
    hs1.eventually (eventually_ne_nhds ha)
  have he2 :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.sin (a + 2 * x) ≠ 0 :=
    hs2.eventually (eventually_ne_nhds ha)
  filter_upwards [self_mem_nhdsWithin, he1, he2] with x hx h1 h2
  exact ⟨by simpa using hx, h1, h2⟩

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

theorem gap1 (a : ℝ) (ha : Real.sin a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (expanded a) L := by
  unfold HasLimitAtZero
  have heq :
      original a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] expanded a := by
    filter_upwards [eventually_admissible a ha] with x hx
    exact original_eq_expanded_at a x hx.1 ha hx.2.1 hx.2.2
  constructor
  · intro h
    exact h.congr' heq
  · intro h
    exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_491/2.txt`; require `sin a≠0`. -/
theorem gap2 (a : ℝ) (ha : Real.sin a ≠ 0) (L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (normalized a) L := by
  calc
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (expanded a) L :=
      gap1 a ha L
    _ ↔ HasLimitAtZero (normalized a) L := by
      unfold HasLimitAtZero
      have heq :
          expanded a =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] normalized a := by
        filter_upwards [eventually_admissible a ha] with x hx
        exact expanded_eq_normalized_at a x hx.1 ha hx.2.1 hx.2.2
      constructor
      · intro h
        exact h.congr' heq
      · intro h
        exact h.congr' heq.symm

/-- Source: `proof_gap/exercise_491/3.txt`; require `sin a≠0`. -/
theorem gap3 (a : ℝ) (ha : Real.sin a ≠ 0) :
    HasLimitAtZero (normalized a) (2 * Real.cos a / Real.sin a ^ 3) := by
  unfold HasLimitAtZero
  change
    Filter.Tendsto (fun x : ℝ => normalized a x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (2 * Real.cos a / Real.sin a ^ 3))
  have hx0 :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    (show Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) from
      continuousAt_id).mono_left inf_le_left
  have hax :
      Filter.Tendsto (fun x : ℝ => a + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using (tendsto_const_nhds.add hx0)
  have htwo :
      Filter.Tendsto (fun x : ℝ => 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hx0)
  have hax2 :
      Filter.Tendsto (fun x : ℝ => a + 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using (tendsto_const_nhds.add htwo)
  have hsx :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_sin_div_zero
  have hs1 :
      Filter.Tendsto (fun x : ℝ => Real.sin (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sin a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_sin.tendsto a).comp hax
  have hs2 :
      Filter.Tendsto (fun x : ℝ => Real.sin (a + 2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sin a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_sin.tendsto a).comp hax2
  have hc1 :
      Filter.Tendsto (fun x : ℝ => Real.cos (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.cos a)) := by
    simpa only [Function.comp_apply] using
      (Real.continuous_cos.tendsto a).comp hax
  have hden :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sin a * Real.sin (a + x) * Real.sin (a + 2 * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds (Real.sin a * Real.sin a * Real.sin a)) :=
    (tendsto_const_nhds.mul hs1).mul hs2
  have hfrac :
      Filter.Tendsto
        (fun x : ℝ =>
          2 * Real.cos (a + x) /
            (Real.sin a * Real.sin (a + x) * Real.sin (a + 2 * x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds
          (2 * Real.cos a /
            (Real.sin a * Real.sin a * Real.sin a))) :=
    (tendsto_const_nhds.mul hc1).div hden
      (mul_ne_zero (mul_ne_zero ha ha) ha)
  have hprod :
      Filter.Tendsto (fun x : ℝ => normalized a x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds
          (2 * Real.cos a /
            (Real.sin a * Real.sin a * Real.sin a))) := by
    change
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.sin x / x) ^ 2 *
            (2 * Real.cos (a + x) /
              (Real.sin a * Real.sin (a + x) * Real.sin (a + 2 * x))))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds
          (2 * Real.cos a /
            (Real.sin a * Real.sin a * Real.sin a)))
    simpa only [one_pow, one_mul] using (hsx.pow 2).mul hfrac
  have hcube :
      Real.sin a * Real.sin a * Real.sin a = Real.sin a ^ 3 := by
    ring
  simpa only [hcube] using hprod

/-- Source: `proof_gap/exercise_491/4.txt`; require `sin a≠0`. -/
theorem gap4 (a : ℝ) (ha : Real.sin a ≠ 0) :
    HasLimitAtZero (original a) (2 * Real.cos a / Real.sin a ^ 3) := by
  exact
    (gap2 a ha (2 * Real.cos a / Real.sin a ^ 3)).2
      (gap3 a ha)

end

end ProofGap.Exercise491
