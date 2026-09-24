import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise494

noncomputable section

def originalNumerator (x : ℝ) : ℝ :=
  1 - Real.cos x * Real.cos (2 * x) * Real.cos (3 * x)
def expanded1 (x : ℝ) : ℝ :=
  1 - (1 / 2 : ℝ) * (Real.cos (4 * x) + Real.cos (2 * x)) * Real.cos (2 * x)
def expanded2 (x : ℝ) : ℝ :=
  1 - (1 / 2 : ℝ) * Real.cos (4 * x) * Real.cos (2 * x) -
    (1 / 2 : ℝ) * Real.cos (2 * x) ^ 2
def expanded3 (x : ℝ) : ℝ :=
  1 - (1 / 4 : ℝ) * (Real.cos (6 * x) + Real.cos (2 * x)) -
    (1 / 4 : ℝ) * (1 + Real.cos (4 * x))
def sineSquares (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * (Real.sin x ^ 2 + Real.sin (2 * x) ^ 2 + Real.sin (3 * x) ^ 2)
def original (x : ℝ) : ℝ := originalNumerator x / (1 - Real.cos x)
def transformed (x : ℝ) : ℝ :=
  sineSquares x / (2 * Real.sin (x / 2) ^ 2)
def normalized (x : ℝ) : ℝ :=
  (1 / 4 : ℝ) * ((Real.sin x / Real.sin (x / 2)) ^ 2 +
    (Real.sin (2 * x) / Real.sin (x / 2)) ^ 2 +
    (Real.sin (3 * x) / Real.sin (x / 2)) ^ 2)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_494/1.txt`. -/
private theorem sin_ratio_limit
    (c d : ℝ) (hc : c ≠ 0) (hd : d ≠ 0) :
    Filter.Tendsto
      (fun x : ℝ => Real.sin (c * x) / Real.sin (d * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (c / d)) := by
  have hsin :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert (Real.hasDerivAt_sin 0).tendsto_slope_zero using 1 <;>
      simp [div_eq_mul_inv, mul_comm]
  have hscale (a : ℝ) (ha : a ≠ 0) :
      Filter.Tendsto (fun x : ℝ => a * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hid0 :
          Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
        continuousAt_id
      have hid :
          Filter.Tendsto (fun x : ℝ => x)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
        hid0.mono_left inf_le_left
      have hconst :
          Filter.Tendsto (fun _ : ℝ => a)
            (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := tendsto_const_nhds
      simpa using hconst.mul hid
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      simpa using mul_ne_zero ha hx0
  have hc_lim :
      Filter.Tendsto (fun x : ℝ => Real.sin (c * x) / (c * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Function.comp_def] using hsin.comp (hscale c hc)
  have hd_lim :
      Filter.Tendsto (fun x : ℝ => Real.sin (d * x) / (d * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [Function.comp_def] using hsin.comp (hscale d hd)
  have hd_ne :
      ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        Real.sin (d * x) / (d * x) ≠ 0 :=
    hd_lim.eventually (eventually_ne_nhds (by norm_num : (1 : ℝ) ≠ 0))
  have hconst :
      Filter.Tendsto (fun _ : ℝ => c / d)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (c / d)) := tendsto_const_nhds
  have hmodel :
      Filter.Tendsto
        (fun x : ℝ =>
          (c / d) *
            ((Real.sin (c * x) / (c * x)) /
              (Real.sin (d * x) / (d * x))))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (c / d)) := by
    simpa using hconst.mul (hc_lim.div hd_lim (by norm_num : (1 : ℝ) ≠ 0))
  apply hmodel.congr'
  filter_upwards [self_mem_nhdsWithin, hd_ne] with x hx hdx
  have hx0 : x ≠ 0 := by simpa using hx
  have hsin_ne : Real.sin (d * x) ≠ 0 := by
    intro hz
    apply hdx
    simp [hz]
  field_simp [hc, hd, hx0, hsin_ne] <;> ring_nf

theorem gap1 (x : ℝ) : originalNumerator x = expanded1 x := by
  have hprod :
      Real.cos (4 * x) + Real.cos (2 * x) =
        2 * Real.cos x * Real.cos (3 * x) := by
    have h4 : Real.cos (4 * x) = Real.cos (3 * x + x) :=
      congrArg Real.cos (by ring)
    have h2 : Real.cos (2 * x) = Real.cos (3 * x - x) :=
      congrArg Real.cos (by ring)
    rw [h4, h2, Real.cos_add, Real.cos_sub]
    ring
  unfold originalNumerator expanded1
  rw [hprod]
  ring

/-- Source: `proof_gap/exercise_494/2.txt`. -/
theorem gap2 (x : ℝ) : expanded1 x = expanded2 x := by
  unfold expanded1 expanded2
  ring

/-- Source: `proof_gap/exercise_494/3.txt`. -/
theorem gap3 (x : ℝ) : originalNumerator x = expanded2 x := by
  rw [gap1 x, gap2 x]

/-- Source: `proof_gap/exercise_494/4.txt`. -/
theorem gap4 (x : ℝ) : originalNumerator x = expanded3 x := by
  have hprod :
      Real.cos (6 * x) + Real.cos (2 * x) =
        2 * Real.cos (4 * x) * Real.cos (2 * x) := by
    have h6 : Real.cos (6 * x) = Real.cos (4 * x + 2 * x) :=
      congrArg Real.cos (by ring)
    have h2 : Real.cos (2 * x) = Real.cos (4 * x - 2 * x) :=
      congrArg Real.cos (by ring)
    calc
      Real.cos (6 * x) + Real.cos (2 * x) =
          Real.cos (4 * x + 2 * x) + Real.cos (4 * x - 2 * x) :=
        congrArg₂ (· + ·) h6 h2
      _ = 2 * Real.cos (4 * x) * Real.cos (2 * x) := by
        rw [Real.cos_add, Real.cos_sub]
        ring
  have hdouble :
      1 + Real.cos (4 * x) = 2 * Real.cos (2 * x) ^ 2 := by
    have h4 : Real.cos (4 * x) = Real.cos (2 * x + 2 * x) :=
      congrArg Real.cos (by ring)
    rw [h4, Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq (2 * x)]
  rw [gap3 x]
  unfold expanded2 expanded3
  rw [hprod, hdouble]
  ring

/-- Source: `proof_gap/exercise_494/5.txt`. -/
theorem gap5 (x : ℝ) : expanded3 x = sineSquares x := by
  have hs (t : ℝ) :
      Real.sin t ^ 2 = (1 - Real.cos (2 * t)) / 2 := by
    have h2 : Real.cos (2 * t) = Real.cos (t + t) :=
      congrArg Real.cos (by ring)
    rw [h2, Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq t]
  unfold expanded3 sineSquares
  rw [hs x, hs (2 * x), hs (3 * x)]
  ring_nf

/-- Source: `proof_gap/exercise_494/6.txt`. -/
theorem gap6 (x : ℝ) : originalNumerator x = sineSquares x := by
  rw [gap4 x, gap5 x]

/-- Source: `proof_gap/exercise_494/7.txt`. -/
theorem gap7 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero transformed L := by
  have hden (x : ℝ) :
      1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have hx : Real.cos x = Real.cos (x / 2 + x / 2) :=
      congrArg Real.cos (by ring)
    rw [hx, Real.cos_add]
    nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
  have hfun : original = transformed := by
    funext x
    unfold original transformed
    rw [gap6 x, hden x]
  rw [hfun]

/-- Source: `proof_gap/exercise_494/8.txt`. -/
theorem gap8 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero normalized L := by
  have hpoint (x : ℝ) : transformed x = normalized x := by
    by_cases hs : Real.sin (x / 2) = 0
    · simp [transformed, normalized, sineSquares, hs]
    · unfold transformed normalized sineSquares
      field_simp [hs]
      <;> ring
  have hfun : transformed = normalized := funext hpoint
  rw [gap7 L, hfun]

/-- Source: `proof_gap/exercise_494/9.txt`. -/
theorem gap9 : HasLimitAtZero normalized ((1 / 4 : ℝ) * (4 + 16 + 36)) := by
  have h1 :
      Filter.Tendsto (fun x : ℝ => Real.sin x / Real.sin (x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((1 : ℝ) / (1 / 2))) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (sin_ratio_limit (1 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num))
  have h2 :
      Filter.Tendsto (fun x : ℝ => Real.sin (2 * x) / Real.sin (x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((2 : ℝ) / (1 / 2))) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (sin_ratio_limit (2 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num))
  have h3 :
      Filter.Tendsto (fun x : ℝ => Real.sin (3 * x) / Real.sin (x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds ((3 : ℝ) / (1 / 2))) := by
    simpa [div_eq_mul_inv, mul_comm] using
      (sin_ratio_limit (3 : ℝ) (1 / 2 : ℝ) (by norm_num) (by norm_num))
  have hq :
      Filter.Tendsto (fun _ : ℝ => (1 / 4 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 4 : ℝ)) :=
    tendsto_const_nhds
  have hall := hq.mul (((h1.pow 2).add (h2.pow 2)).add (h3.pow 2))
  unfold HasLimitAtZero normalized
  convert hall using 1 <;> norm_num

/-- Source: `proof_gap/exercise_494/10.txt`. -/
theorem gap10 : (1 / 4 : ℝ) * (4 + 16 + 36) = 14 := by
  norm_num

/-- Source: `proof_gap/exercise_494/11.txt`. -/
theorem gap11 : HasLimitAtZero original 14 := by
  apply (gap8 14).2
  rw [← gap10]
  exact gap9

end

end ProofGap.Exercise494
