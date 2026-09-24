import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise484

noncomputable section

def original (a x : ℝ) : ℝ := (Real.tan x - Real.tan a) / (x - a)
def transformed (a x : ℝ) : ℝ :=
  Real.sin (x - a) / ((x - a) * Real.cos x * Real.cos a)
def HasLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_484/1.txt`; require `cos a≠0`. -/
private theorem tendsto_congr_eventually
    {α β : Type*} {f g : α → β} {l : Filter α} {l' : Filter β}
    (hfg : f =ᶠ[l] g) :
    Filter.Tendsto f l l' ↔ Filter.Tendsto g l l' := by
  have hmap : Filter.map f l = Filter.map g l := by
    ext s
    change f ⁻¹' s ∈ l ↔ g ⁻¹' s ∈ l
    constructor
    · intro hs
      filter_upwards [hs, hfg] with x hxs hx
      change g x ∈ s
      rw [← hx]
      exact hxs
    · intro hs
      filter_upwards [hs, hfg] with x hxs hx
      change f x ∈ s
      rw [hx]
      exact hxs
  change Filter.map f l ≤ l' ↔ Filter.map g l ≤ l'
  rw [hmap]

theorem gap1 (a : ℝ) (ha : Real.cos a ≠ 0) (L : ℝ) :
    HasLimitAt (original a) a L ↔ HasLimitAt (transformed a) a L := by
  unfold HasLimitAt
  have hcos_ne :
      ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, Real.cos x ≠ 0 :=
    (Real.continuous_cos.continuousAt.eventually_ne ha).filter_mono inf_le_left
  have hpunc : ∀ᶠ x in nhdsWithin a ({a} : Set ℝ)ᶜ, x ≠ a := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  have heq :
      original a =ᶠ[nhdsWithin a ({a} : Set ℝ)ᶜ] transformed a := by
    filter_upwards [hcos_ne, hpunc] with x hcx hxa
    unfold original transformed
    rw [Real.tan_eq_sin_div_cos, Real.tan_eq_sin_div_cos, Real.sin_sub]
    field_simp [hcx, ha, hxa]
  exact tendsto_congr_eventually heq

/-- Source: `proof_gap/exercise_484/2.txt`; require `cos a≠0`. -/
theorem gap2 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt (transformed a) a (1 / Real.cos a ^ 2) := by
  unfold HasLimitAt
  let F := nhdsWithin a ({a} : Set ℝ)ᶜ
  have hpunc : ∀ᶠ x in F, x ≠ a := by
    dsimp [F]
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  have hcos_ne : ∀ᶠ x in F, Real.cos x ≠ 0 := by
    dsimp [F]
    exact
      (Real.continuous_cos.continuousAt.eventually_ne ha).filter_mono
        inf_le_left
  have hsub_nhds :
      Filter.Tendsto (fun x : ℝ => x - a) F (nhds 0) := by
    have hcont : ContinuousAt (fun x : ℝ => x - a) a :=
      continuousAt_id.sub continuousAt_const
    simpa [F] using hcont.mono_left inf_le_left
  have hsub_ne :
      Filter.Tendsto (fun x : ℝ => x - a) F
        (Filter.principal (({0} : Set ℝ)ᶜ)) := by
    rw [Filter.tendsto_principal]
    filter_upwards [hpunc] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    exact sub_ne_zero.mpr hx
  have hsub :
      Filter.Tendsto (fun x : ℝ => x - a) F
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) := by
    change Filter.Tendsto (fun x : ℝ => x - a) F
      (nhds 0 ⊓ Filter.principal (({0} : Set ℝ)ᶜ))
    exact le_inf hsub_nhds hsub_ne
  have hsin_zero :
      Filter.Tendsto (fun y : ℝ => Real.sin y / y)
        (nhdsWithin 0 (({0} : Set ℝ)ᶜ)) (nhds 1) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (Real.hasDerivAt_sin 0).tendsto_slope_zero
  have hsin :
      Filter.Tendsto (fun x : ℝ => Real.sin (x - a) / (x - a)) F
        (nhds 1) :=
    hsin_zero.comp hsub
  have hcos_inv :
      Filter.Tendsto (fun x : ℝ => (Real.cos x)⁻¹) F
        (nhds ((Real.cos a)⁻¹)) := by
    have hcont : ContinuousAt (fun x : ℝ => (Real.cos x)⁻¹) a :=
      Real.continuous_cos.continuousAt.inv₀ ha
    exact hcont.mono_left inf_le_left
  have hconst :
      Filter.Tendsto (fun _ : ℝ => (Real.cos a)⁻¹) F
        (nhds ((Real.cos a)⁻¹)) :=
    tendsto_const_nhds
  have hprod :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.sin (x - a) / (x - a)) * (Real.cos x)⁻¹ *
            (Real.cos a)⁻¹)
        F (nhds ((1 : ℝ) * (Real.cos a)⁻¹ * (Real.cos a)⁻¹)) :=
    (hsin.mul hcos_inv).mul hconst
  have heq :
      (fun x : ℝ => transformed a x) =ᶠ[F]
        (fun x : ℝ =>
          (Real.sin (x - a) / (x - a)) * (Real.cos x)⁻¹ *
            (Real.cos a)⁻¹) := by
    filter_upwards [hpunc, hcos_ne] with x hxa hcx
    unfold transformed
    field_simp [hxa, hcx, ha] <;> ring
  have hfinal :
      Filter.Tendsto (transformed a) F
        (nhds ((1 : ℝ) * (Real.cos a)⁻¹ * (Real.cos a)⁻¹)) :=
    (tendsto_congr_eventually heq).mpr hprod
  dsimp [F] at hfinal ⊢
  convert hfinal using 1 <;> field_simp [ha] <;> ring

/-- Source: `proof_gap/exercise_484/3.txt`; require `cos a≠0`. -/
theorem gap3 (a : ℝ) (ha : Real.cos a ≠ 0) :
    HasLimitAt (original a) a (1 / Real.cos a ^ 2) := by
  exact (gap1 a ha (1 / Real.cos a ^ 2)).mpr (gap2 a ha)

end

end ProofGap.Exercise484
