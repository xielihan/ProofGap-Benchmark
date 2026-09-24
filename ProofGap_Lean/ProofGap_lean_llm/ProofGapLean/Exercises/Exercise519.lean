import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise519

noncomputable section

def original (x : ℝ) : ℝ :=
  Real.rpow ((1 + Real.tan x) / (1 + Real.sin x)) (1 / Real.sin x)
def transformed (x : ℝ) : ℝ :=
  Real.rpow (1 + 1 / ((1 + Real.sin x) / (Real.tan x - Real.sin x)))
    (((1 + Real.sin x) / (Real.tan x - Real.sin x)) *
      ((1 - Real.cos x) / (Real.cos x * (1 + Real.sin x))))
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 519, gap 1; interpret variable powers by `Real.rpow`. -/
private theorem tendsto_of_eventually_eq
    {α β : Type*} {l : Filter α} {la : Filter β} {f g : α → β}
    (hfg : f =ᶠ[l] g) (hg : Filter.Tendsto g l la) :
    Filter.Tendsto f l la := by
  change Filter.map f l ≤ la
  rw [Filter.map_congr hfg]
  exact hg

private theorem sin_div_tendsto :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa only [zero_add, Real.sin_zero, sub_zero, Real.cos_zero,
    div_eq_mul_inv, mul_comm, smul_eq_mul] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

private theorem base_hasDerivAt :
    HasDerivAt
      (fun x : ℝ => (1 + Real.tan x) / (1 + Real.sin x)) 0 0 := by
  have ht_div :
      HasDerivAt (fun x : ℝ => Real.sin x / Real.cos x) 1 0 := by
    have h :=
      (Real.hasDerivAt_sin 0).div (Real.hasDerivAt_cos 0)
        (by norm_num : Real.cos 0 ≠ 0)
    convert h using 1 <;> norm_num
  have ht : HasDerivAt (fun x : ℝ => Real.tan x) 1 0 := by
    simpa only [Real.tan_eq_sin_div_cos] using ht_div
  have hn : HasDerivAt (fun x : ℝ => 1 + Real.tan x) 1 0 := by
    simpa using ht.const_add 1
  have hd : HasDerivAt (fun x : ℝ => 1 + Real.sin x) 1 0 := by
    simpa using (Real.hasDerivAt_sin 0).const_add 1
  simpa using hn.div hd (by norm_num : 1 + Real.sin 0 ≠ 0)

private theorem log_base_hasDerivAt :
    HasDerivAt
      (fun x : ℝ => Real.log ((1 + Real.tan x) / (1 + Real.sin x))) 0 0 := by
  have hl :
      HasDerivAt Real.log 1
        ((1 + Real.tan 0) / (1 + Real.sin 0)) := by
    simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
  simpa using hl.comp 0 base_hasDerivAt

private theorem eventually_regular :
    ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      x ≠ 0 ∧ Real.sin x ≠ 0 ∧ Real.cos x ≠ 0 ∧
        1 + Real.sin x ≠ 0 ∧ Real.tan x - Real.sin x ≠ 0 ∧
        0 < (1 + Real.tan x) / (1 + Real.sin x) := by
  let F := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hxne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hsinratio :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x) F (nhds 1) := by
    simpa [F] using sin_div_tendsto
  have hsinratio_pos : ∀ᶠ x : ℝ in F, 0 < Real.sin x / x :=
    hsinratio.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hcos_cont : ContinuousAt Real.cos 0 :=
    Real.continuous_cos.continuousAt
  change
    Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at hcos_cont
  have hcos_full :
      Filter.Tendsto (fun x : ℝ => Real.cos x) (nhds 0) (nhds 1) := by
    simpa using hcos_cont
  have hcoslim :
      Filter.Tendsto (fun x : ℝ => Real.cos x) F (nhds 1) :=
    hcos_full.mono_left inf_le_left
  have hcos_pos : ∀ᶠ x : ℝ in F, 0 < Real.cos x :=
    hcoslim.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hsum_cont :
      ContinuousAt (fun x : ℝ => 1 + Real.sin x) 0 := by
    simpa using
      (((continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).add
        Real.continuous_sin).continuousAt)
  change
    Filter.Tendsto (fun x : ℝ => 1 + Real.sin x) (nhds 0)
      (nhds (1 + Real.sin 0)) at hsum_cont
  have hsum_full :
      Filter.Tendsto (fun x : ℝ => 1 + Real.sin x) (nhds 0) (nhds 1) := by
    simpa using hsum_cont
  have hsumlim :
      Filter.Tendsto (fun x : ℝ => 1 + Real.sin x) F (nhds 1) :=
    hsum_full.mono_left inf_le_left
  have hsum_pos : ∀ᶠ x : ℝ in F, 0 < 1 + Real.sin x :=
    hsumlim.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hbase_cont :
      ContinuousAt
        (fun x : ℝ => (1 + Real.tan x) / (1 + Real.sin x)) 0 :=
    base_hasDerivAt.continuousAt
  change
    Filter.Tendsto
      (fun x : ℝ => (1 + Real.tan x) / (1 + Real.sin x))
      (nhds 0)
      (nhds ((1 + Real.tan 0) / (1 + Real.sin 0))) at hbase_cont
  have hbase_full :
      Filter.Tendsto
        (fun x : ℝ => (1 + Real.tan x) / (1 + Real.sin x))
        (nhds 0) (nhds 1) := by
    simpa using hbase_cont
  have hbaselim :
      Filter.Tendsto
        (fun x : ℝ => (1 + Real.tan x) / (1 + Real.sin x))
        F (nhds 1) :=
    hbase_full.mono_left inf_le_left
  have hbase_pos :
      ∀ᶠ x : ℝ in F, 0 < (1 + Real.tan x) / (1 + Real.sin x) :=
    hbaselim.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hxne, hsinratio_pos, hcos_pos, hsum_pos, hbase_pos] with
      x hx hsr hc hs hb
  have hsin : Real.sin x ≠ 0 := by
    intro h
    rw [h, zero_div] at hsr
    linarith
  have hcos : Real.cos x ≠ 0 := ne_of_gt hc
  have hsum : 1 + Real.sin x ≠ 0 := ne_of_gt hs
  have hcos_one : Real.cos x ≠ 1 := by
    intro h
    have hi := Real.sin_sq_add_cos_sq x
    rw [h] at hi
    have hz : Real.sin x = 0 := by
      nlinarith [sq_nonneg (Real.sin x)]
    exact hsin hz
  have hdiff : Real.tan x - Real.sin x ≠ 0 := by
    intro hzero
    have hquot : Real.sin x / Real.cos x = Real.sin x := by
      apply sub_eq_zero.mp
      simpa [Real.tan_eq_sin_div_cos] using hzero
    have hmul : Real.sin x = Real.sin x * Real.cos x :=
      (div_eq_iff hcos).mp hquot
    have hz : Real.sin x * (1 - Real.cos x) = 0 := by
      calc
        Real.sin x * (1 - Real.cos x) =
            Real.sin x - Real.sin x * Real.cos x := by ring
        _ = 0 := sub_eq_zero.mpr hmul
    rcases mul_eq_zero.mp hz with hz | hz
    · exact hsin hz
    · apply hcos_one
      linarith
  exact ⟨hx, hsin, hcos, hsum, hdiff, hb⟩

private theorem original_eq_transformed_of_regular
    (x : ℝ) (hs : Real.sin x ≠ 0) (hc : Real.cos x ≠ 0)
    (hsum : 1 + Real.sin x ≠ 0)
    (hdiff : Real.tan x - Real.sin x ≠ 0) :
    original x = transformed x := by
  have hb :
      1 + 1 / ((1 + Real.sin x) / (Real.tan x - Real.sin x)) =
        (1 + Real.tan x) / (1 + Real.sin x) := by
    field_simp [hsum, hdiff]
    ring
  have hdiff' : Real.sin x / Real.cos x - Real.sin x ≠ 0 := by
    simpa [Real.tan_eq_sin_div_cos] using hdiff
  have hone : 1 - Real.cos x ≠ 0 := by
    intro h
    have hc1 : Real.cos x = 1 := (sub_eq_zero.mp h).symm
    apply hdiff
    simp [Real.tan_eq_sin_div_cos, hc1]
  have he :
      ((1 + Real.sin x) / (Real.tan x - Real.sin x)) *
          ((1 - Real.cos x) / (Real.cos x * (1 + Real.sin x))) =
        1 / Real.sin x := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hs, hc, hsum, hdiff', hone]
  unfold original transformed
  rw [hb, he]

private theorem eventually_original_eq_transformed :
    original =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] transformed := by
  filter_upwards [eventually_regular] with x hx
  rcases hx with ⟨_, hs, hc, hsum, hdiff, _⟩
  exact original_eq_transformed_of_regular x hs hc hsum hdiff

private theorem log_quotient_tendsto :
    Filter.Tendsto
      (fun x : ℝ =>
        Real.log ((1 + Real.tan x) / (1 + Real.sin x)) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  simpa [div_eq_mul_inv, mul_comm] using
    log_base_hasDerivAt.tendsto_slope_zero

private theorem original_tendsto_exp_zero :
    HasLimitAtZero original (Real.exp 0) := by
  let F := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hsinratio :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x) F (nhds 1) := by
    simpa [F] using sin_div_tendsto
  have hlog :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log ((1 + Real.tan x) / (1 + Real.sin x)) / x)
        F (nhds 0) := by
    simpa [F] using log_quotient_tendsto
  have hcombined := hlog.div hsinratio (by norm_num : (1 : ℝ) ≠ 0)
  have hcombined' :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.log ((1 + Real.tan x) / (1 + Real.sin x)) / x) /
            (Real.sin x / x))
        F (nhds 0) := by
    simpa using hcombined
  have hrewrite :
      (fun x : ℝ =>
          (Real.log ((1 + Real.tan x) / (1 + Real.sin x)) / x) /
            (Real.sin x / x)) =ᶠ[F]
        (fun x : ℝ =>
          Real.log ((1 + Real.tan x) / (1 + Real.sin x)) / Real.sin x) := by
    filter_upwards [eventually_regular] with x hx
    rcases hx with ⟨hx, hs, _, _, _, _⟩
    field_simp [hx, hs]
  have hquot :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.log ((1 + Real.tan x) / (1 + Real.sin x)) / Real.sin x)
        F (nhds 0) :=
    tendsto_of_eventually_eq hrewrite.symm hcombined'
  have hexp :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.exp
            (Real.log ((1 + Real.tan x) / (1 + Real.sin x)) /
              Real.sin x))
        F (nhds (Real.exp 0)) :=
    Real.continuous_exp.continuousAt.tendsto.comp hquot
  have hpow :
      original =ᶠ[F]
        (fun x : ℝ =>
          Real.exp
            (Real.log ((1 + Real.tan x) / (1 + Real.sin x)) /
              Real.sin x)) := by
    filter_upwards [eventually_regular] with x hx
    rcases hx with ⟨_, _, _, _, _, hb⟩
    unfold original
    calc
      Real.rpow ((1 + Real.tan x) / (1 + Real.sin x))
          (1 / Real.sin x) =
        Real.exp
          (Real.log ((1 + Real.tan x) / (1 + Real.sin x)) *
            (1 / Real.sin x)) :=
        Real.rpow_def_of_pos hb (1 / Real.sin x)
      _ = Real.exp
          (Real.log ((1 + Real.tan x) / (1 + Real.sin x)) /
            Real.sin x) := by
        congr 1
        simp only [div_eq_mul_inv, one_mul]
  unfold HasLimitAtZero
  simpa [F] using tendsto_of_eventually_eq hpow hexp

theorem gap1 (L : ℝ) :
    HasLimitAtZero original L ↔ HasLimitAtZero transformed L := by
  unfold HasLimitAtZero
  constructor
  · intro h
    exact tendsto_of_eventually_eq eventually_original_eq_transformed.symm h
  · intro h
    exact tendsto_of_eventually_eq eventually_original_eq_transformed h

/-- Exercise 519, gap 2. -/
theorem gap2 : HasLimitAtZero transformed (Real.exp 0) := by
  exact (gap1 (Real.exp 0)).mp original_tendsto_exp_zero

/-- Exercise 519, gap 3. -/
theorem gap3 : Real.exp 0 = 1 := by
  norm_num

/-- Exercise 519, gap 4. -/
theorem gap4 : HasLimitAtZero original 1 := by
  simpa using original_tendsto_exp_zero

end

end ProofGap.Exercise519
