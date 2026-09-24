import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise650_2

noncomputable section

def target (x : ℝ) : ℝ := x * Real.sin (Real.sqrt x)
def scale (x : ℝ) : ℝ := Real.rpow x (3 / 2)

/-- Exercise 650_2, gap 1. -/
theorem gap1 :
    Filter.Tendsto
      (fun x : ℝ => target x / (x * Real.sqrt x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hsqrt_zero :
      Filter.Tendsto (fun x : ℝ => Real.sqrt x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa only [Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.mono_left
        (show nhdsWithin 0 (Set.Ioi 0) ≤ nhds 0 from inf_le_left)
  have hsqrt_ne :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        Real.sqrt x ∈ ({0} : Set ℝ)ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := hx
    have hsqrtpos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxpos
    simpa using hsqrtpos.ne'
  have hsqrt :
      Filter.Tendsto (fun x : ℝ => Real.sqrt x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) :=
    tendsto_nhdsWithin_iff.2 ⟨hsqrt_zero, hsqrt_ne⟩
  have hsin :
      Filter.Tendsto (fun y : ℝ => Real.sin y / y)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have h := hsin.comp hsqrt
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsqrt0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hxpos).ne'
  dsimp [target]
  field_simp [hx0, hsqrt0] <;> ring

/-- Exercise 650_2, gap 2. -/
theorem gap2 :
    Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0)) target scale := by
  have hscale :
      (fun x : ℝ => scale x) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : ℝ => x * Real.sqrt x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    unfold scale
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
    change x ^ (1 + 1 / 2 : ℝ) = x * Real.sqrt x
    rw [Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
  unfold Asymptotics.IsEquivalent
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have hclose :
      ∀ᶠ x : ℝ in nhdsWithin 0 (Set.Ioi 0),
        dist (target x / (x * Real.sqrt x)) 1 < c :=
    (Metric.tendsto_nhds.1 gap1) c hc
  filter_upwards [self_mem_nhdsWithin, hscale, hclose] with x hx hs hxc
  change ‖target x - scale x‖ ≤ c * ‖scale x‖
  rw [hs]
  have hxpos : 0 < x := hx
  have hg : x * Real.sqrt x ≠ 0 :=
    mul_ne_zero (ne_of_gt hxpos) (Real.sqrt_pos.2 hxpos).ne'
  have halg :
      target x - x * Real.sqrt x =
        (target x / (x * Real.sqrt x) - 1) * (x * Real.sqrt x) := by
    field_simp [hg]
  have hnorm : ‖target x / (x * Real.sqrt x) - 1‖ ≤ c := by
    simpa [Real.dist_eq] using le_of_lt hxc
  rw [halg, norm_mul]
  exact mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)

/-- Exercise 650_2, gap 3. -/
theorem gap3 :
    Asymptotics.IsEquivalent (nhdsWithin 0 (Set.Ioi 0)) target scale := by
  exact gap2

end

end ProofGap.Exercise650_2
