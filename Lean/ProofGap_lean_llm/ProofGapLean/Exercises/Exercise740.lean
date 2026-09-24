import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise740

noncomputable section

def core1 (x : ℝ) : ℝ :=
  (Real.sqrt (1 + x) - 1) /
    (Real.rpow (1 + x) (1 / 3 : ℝ) - 1)

def core2 (x : ℝ) : ℝ := Real.tan (2 * x) / x
def core3 (x : ℝ) : ℝ := Real.sin x * Real.sin (1 / x)
def core4 (x : ℝ) : ℝ := Real.rpow (1 + x) (1 / x)
def core5 (x : ℝ) : ℝ := (1 / x ^ 2) * Real.exp (-(1 / x ^ 2))
def core6 (x : ℝ) : ℝ := Real.rpow x x
def core7 (x : ℝ) : ℝ := x * (Real.log x) ^ 2

/-- Source: `proof_gap/exercise_740/1.txt`; the conjunction of continuity
claims for seven unrelated functions cannot be equivalent to this single
limit.  Keep the intended first limit computation. -/
private def shiftedExpLog (a x : ℝ) : ℝ :=
  Real.exp (a * Real.log (1 + x)) - 1

private theorem eventually_one_add_pos :
    ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < 1 + x := by
  have hb : Metric.ball (0 : ℝ) 1 ∈
      nhdsWithin 0 ({0} : Set ℝ)ᶜ :=
    mem_nhdsWithin_of_mem_nhds
      (Metric.ball_mem_nhds (0 : ℝ) (by norm_num))
  filter_upwards [hb] with x hx
  have hxabs : |x| < 1 := by
    simpa [Metric.mem_ball, Real.dist_eq] using hx
  linarith [neg_lt_of_abs_lt hxabs]

private theorem hasDerivAt_log_one_add :
    HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).const_add 1 using 1 <;> norm_num
  have houter : HasDerivAt Real.log
      ((1 + (0 : ℝ))⁻¹) (1 + (0 : ℝ)) :=
    Real.hasDerivAt_log (by norm_num)
  convert houter.comp 0 hinner using 1 <;> norm_num

private theorem hasDerivAt_shiftedExpLog (a : ℝ) :
    HasDerivAt (shiftedExpLog a) a 0 := by
  have hmul : HasDerivAt (fun x : ℝ => a * Real.log (1 + x)) a 0 := by
    simpa using hasDerivAt_log_one_add.const_mul a
  have houter : HasDerivAt Real.exp
      (Real.exp (a * Real.log (1 + (0 : ℝ))))
      (a * Real.log (1 + (0 : ℝ))) :=
    Real.hasDerivAt_exp _
  convert (houter.comp 0 hmul).sub_const 1 using 1 <;>
    norm_num [shiftedExpLog]

private theorem tendsto_div_of_hasDerivAt_zero
    {f g : ℝ → ℝ} {a b : ℝ}
    (hf : HasDerivAt f a 0) (hg : HasDerivAt g b 0)
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hb : b ≠ 0)
    (hgne : ∀ᶠ x in nhdsWithin 0 ({0} : Set ℝ)ᶜ, g x ≠ 0) :
    Filter.Tendsto (fun x => f x / g x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (a / b)) := by
  have h := hf.tendsto_slope.div hg.tendsto_slope hb
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin, hgne] with x hx hgx
  have hx0 : x ≠ 0 := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
  change ((x - 0)⁻¹ • (f x - f 0)) /
      ((x - 0)⁻¹ • (g x - g 0)) = f x / g x
  rw [hf0, hg0]
  simp only [sub_zero, smul_eq_mul]
  field_simp [hx0, hgx]

private theorem continuousAt_iff_of_punctured_limit
    (f g : ℝ → ℝ) (L : ℝ)
    (heq : ∀ x : ℝ, x ≠ 0 → f x = g x)
    (hlim : Filter.Tendsto g (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)) :
    ContinuousAt f 0 ↔ f 0 = L := by
  constructor
  · intro hf
    have hf' : Filter.Tendsto f
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (f 0)) :=
      hf.mono_left inf_le_left
    have hg' : Filter.Tendsto f
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L) := by
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (heq x (by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx)).symm
    exact tendsto_nhds_unique hf' hg'
  · intro hv
    rw [ContinuousAt, hv, Metric.tendsto_nhds]
    rw [Metric.tendsto_nhds] at hlim
    intro ε hε
    have he := hlim ε hε
    change {x | dist (g x) L < ε} ∈
      nhdsWithin 0 ({0} : Set ℝ)ᶜ at he
    obtain ⟨s, hs, hsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
    filter_upwards [hs] with x hx
    by_cases hx0 : x = 0
    · subst x
      simp [hv, hε]
    · change dist (f x) L < ε
      rw [heq x hx0]
      exact hsub ⟨hx, by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff]⟩

private theorem continuousWithinAt_iff_of_right_limit
    (f g : ℝ → ℝ) (L : ℝ)
    (heq : ∀ x : ℝ, 0 < x → f x = g x)
    (hlim : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    ContinuousWithinAt f (Set.Ici 0) 0 ↔ f 0 = L := by
  constructor
  · intro hf
    have hmono :
        nhdsWithin (0 : ℝ) (Set.Ioi (0 : ℝ)) ≤
          nhdsWithin 0 (Set.Ici 0) :=
      nhdsWithin_mono (0 : ℝ) Set.Ioi_subset_Ici_self
    have hf' : Filter.Tendsto f
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
      hf.mono_left hmono
    have hg' : Filter.Tendsto f
        (nhdsWithin 0 (Set.Ioi 0)) (nhds L) := by
      apply hlim.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact (heq x (by simpa only [Set.mem_Ioi] using hx)).symm
    exact tendsto_nhds_unique hf' hg'
  · intro hv
    rw [ContinuousWithinAt, hv, Metric.tendsto_nhds]
    rw [Metric.tendsto_nhds] at hlim
    intro ε hε
    have he := hlim ε hε
    change {x | dist (g x) L < ε} ∈
      nhdsWithin 0 (Set.Ioi 0) at he
    obtain ⟨s, hs, hsub⟩ :=
      mem_nhdsWithin_iff_exists_mem_nhds_inter.mp he
    apply mem_nhdsWithin_iff_exists_mem_nhds_inter.mpr
    refine ⟨s, hs, ?_⟩
    rintro x ⟨hxs, hxnonneg⟩
    by_cases hx0 : x = 0
    · subst x
      simp [hv, hε]
    · have hxpos : 0 < x :=
        lt_of_le_of_ne
          (by simpa only [Set.mem_Ici] using hxnonneg) (Ne.symm hx0)
      change dist (f x) L < ε
      rw [heq x hxpos]
      exact hsub ⟨hxs, by simpa only [Set.mem_Ioi]⟩

theorem gap1 :
    Filter.Tendsto core1 (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (3 / 2 : ℝ)) := by
  have hlim := tendsto_div_of_hasDerivAt_zero
    (f := shiftedExpLog (1 / 2 : ℝ))
    (g := shiftedExpLog (1 / 3 : ℝ))
    (hasDerivAt_shiftedExpLog (1 / 2 : ℝ))
    (hasDerivAt_shiftedExpLog (1 / 3 : ℝ))
    (by simp [shiftedExpLog]) (by simp [shiftedExpLog])
    (by norm_num)
    (by
      filter_upwards [self_mem_nhdsWithin, eventually_one_add_pos] with x hx hbase
      have hx0 : x ≠ 0 := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
      change Real.exp ((1 / 3 : ℝ) * Real.log (1 + x)) - 1 ≠ 0
      intro hz
      have he : Real.exp ((1 / 3 : ℝ) * Real.log (1 + x)) = 1 :=
        sub_eq_zero.mp hz
      have hm : (1 / 3 : ℝ) * Real.log (1 + x) = 0 := by
        apply Real.exp_injective
        simpa using he
      have hl : Real.log (1 + x) = 0 := by
        exact (mul_eq_zero.mp hm).resolve_left (by norm_num)
      have hb : 1 + x = 1 := by
        calc
          1 + x = Real.exp (Real.log (1 + x)) := (Real.exp_log hbase).symm
          _ = 1 := by rw [hl]; norm_num
      exact hx0 (by linarith))
  have hcore : core1 =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      fun x => shiftedExpLog (1 / 2 : ℝ) x /
        shiftedExpLog (1 / 3 : ℝ) x := by
    filter_upwards [eventually_one_add_pos] with x hx
    have hnum : Real.sqrt (1 + x) =
        Real.exp ((1 / 2 : ℝ) * Real.log (1 + x)) := by
      rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
      congr 1
      ring
    have hden : Real.rpow (1 + x) (1 / 3 : ℝ) =
        Real.exp (Real.log (1 + x) * (1 / 3 : ℝ)) := by
      exact Real.rpow_def_of_pos hx (1 / 3 : ℝ)
    simp only [core1, shiftedExpLog]
    rw [hnum, hden]
    simp only [mul_comm]
  have hout := hlim.congr' hcore.symm
  convert hout using 1 <;> norm_num

/-- Source: `proof_gap/exercise_740/2.txt`; state the removable-extension
criterion only for `f₁`, with its needed punctured formula hypothesis. -/
theorem gap2 (f₁ : ℝ → ℝ)
    (h₁ : ∀ x : ℝ, x ≠ 0 → f₁ x = core1 x) :
    ContinuousAt f₁ 0 ↔ f₁ 0 = (3 / 2 : ℝ) := by
  exact continuousAt_iff_of_punctured_limit f₁ core1 (3 / 2 : ℝ) h₁ gap1

/-- Source: `proof_gap/exercise_740/3.txt`; isolate the second limit. -/
theorem gap3 :
    Filter.Tendsto core2 (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
  have hinner : HasDerivAt (fun x : ℝ => 2 * x) 2 0 := by
    convert (hasDerivAt_id (𝕜 := ℝ) 0).const_mul 2 using 1 <;> norm_num
  have hsin : HasDerivAt (fun x : ℝ => Real.sin (2 * x)) 2 0 := by
    have houter := Real.hasDerivAt_sin (2 * (0 : ℝ))
    convert houter.comp 0 hinner using 1 <;> norm_num
  have hquot : Filter.Tendsto (fun x : ℝ => Real.sin (2 * x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    have h := tendsto_div_of_hasDerivAt_zero
      (f := fun x : ℝ => Real.sin (2 * x))
      (g := fun x : ℝ => x)
      hsin (hasDerivAt_id (𝕜 := ℝ) 0)
      (by norm_num) (by norm_num) (by norm_num)
      (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx)
    simpa using h
  have hscale : Filter.Tendsto (fun x : ℝ => 2 * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => 2 * x) 0 := hinner.continuousAt
    simpa only [mul_zero] using
      hc.mono_left
        (show nhdsWithin 0 ({0} : Set ℝ)ᶜ ≤ nhds 0 from inf_le_left)
  have hcos0 : Filter.Tendsto Real.cos (nhds 0) (nhds 1) := by
    have hc : ContinuousAt Real.cos (0 : ℝ) :=
      Real.continuous_cos.continuousAt
    change Filter.Tendsto Real.cos (nhds 0) (nhds (Real.cos 0)) at hc
    simpa using hc
  have hcos : Filter.Tendsto (fun x : ℝ => Real.cos (2 * x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    hcos0.comp hscale
  have h := hquot.div hcos (by norm_num)
  have heq : core2 =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
      fun x : ℝ => (Real.sin (2 * x) / x) / Real.cos (2 * x) := by
    filter_upwards with x
    simp only [core2, Real.tan_eq_sin_div_cos, div_eq_mul_inv]
    ring
  have hout := h.congr' heq.symm
  simpa using hout

/-- Source: `proof_gap/exercise_740/4.txt`; state the criterion only for
`f₂`. -/
theorem gap4 (f₂ : ℝ → ℝ)
    (h₂ : ∀ x : ℝ, x ≠ 0 → f₂ x = core2 x) :
    ContinuousAt f₂ 0 ↔ f₂ 0 = 2 := by
  exact continuousAt_iff_of_punctured_limit f₂ core2 2 h₂ gap3

/-- Source: `proof_gap/exercise_740/5.txt`; isolate the third limit. -/
theorem gap5 :
    Filter.Tendsto core3 (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  have hc : ContinuousAt (fun x : ℝ => |Real.sin x|) 0 :=
    Real.continuous_sin.continuousAt.abs
  change Filter.Tendsto (fun x : ℝ => |Real.sin x|)
    (nhds 0) (nhds |Real.sin 0|) at hc
  have hsfull : Filter.Tendsto (fun x : ℝ => |Real.sin x|)
      (nhds 0) (nhds 0) := by
    simpa using hc
  have hs : Filter.Tendsto (fun x : ℝ => |Real.sin x|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hsfull.mono_left inf_le_left
  have hsneg : Filter.Tendsto (fun x : ℝ => -|Real.sin x|)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert hs.neg using 1 <;> norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hsneg hs ?_ ?_
  · filter_upwards with x
    have hsin : |Real.sin (1 / x)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have habs : |core3 x| ≤ |Real.sin x| := by
      calc
        |core3 x| = |Real.sin x| * |Real.sin (1 / x)| := by
          simp [core3, abs_mul]
        _ ≤ |Real.sin x| * 1 :=
          mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
        _ = |Real.sin x| := by ring
    exact le_trans (neg_le_neg habs) (neg_abs_le _)
  · filter_upwards with x
    have hsin : |Real.sin (1 / x)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    have habs : |core3 x| ≤ |Real.sin x| := by
      calc
        |core3 x| = |Real.sin x| * |Real.sin (1 / x)| := by
          simp [core3, abs_mul]
        _ ≤ |Real.sin x| * 1 :=
          mul_le_mul_of_nonneg_left hsin (abs_nonneg _)
        _ = |Real.sin x| := by ring
    exact le_trans (le_abs_self (core3 x)) habs

/-- Source: `proof_gap/exercise_740/6.txt`; state the criterion only for
`f₃`. -/
theorem gap6 (f₃ : ℝ → ℝ)
    (h₃ : ∀ x : ℝ, x ≠ 0 → f₃ x = core3 x) :
    ContinuousAt f₃ 0 ↔ f₃ 0 = 0 := by
  exact continuousAt_iff_of_punctured_limit f₃ core3 0 h₃ gap5

/-- Source: `proof_gap/exercise_740/7.txt`; translate the real exponent with
`Real.rpow` and isolate the fourth limit. -/
theorem gap7 :
    Filter.Tendsto core4 (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhds (Real.exp 1)) := by
  have hquot : Filter.Tendsto
      (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have h := tendsto_div_of_hasDerivAt_zero
      (f := fun x : ℝ => Real.log (1 + x)) (g := fun x : ℝ => x)
      hasDerivAt_log_one_add (hasDerivAt_id (𝕜 := ℝ) 0)
      (by norm_num) (by norm_num) (by norm_num)
      (by
        filter_upwards [self_mem_nhdsWithin] with x hx
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx)
    simpa using h
  have hexp0 : Filter.Tendsto Real.exp (nhds 1) (nhds (Real.exp 1)) :=
    Real.continuous_exp.continuousAt
  have hexp : Filter.Tendsto
      (fun x : ℝ => Real.exp (Real.log (1 + x) / x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1)) :=
    hexp0.comp hquot
  apply hexp.congr'
  filter_upwards [eventually_one_add_pos] with x hx
  simp only [core4]
  change Real.exp (Real.log (1 + x) / x) = (1 + x) ^ (1 / x : ℝ)
  rw [Real.rpow_def_of_pos hx (1 / x : ℝ)]
  congr 1
  simp only [div_eq_mul_inv, one_mul]

/-- Source: `proof_gap/exercise_740/8.txt`; state the criterion only for
`f₄`. -/
theorem gap8 (f₄ : ℝ → ℝ)
    (h₄ : ∀ x : ℝ, x ≠ 0 → f₄ x = core4 x) :
    ContinuousAt f₄ 0 ↔ f₄ 0 = Real.exp 1 := by
  exact continuousAt_iff_of_punctured_limit f₄ core4 (Real.exp 1) h₄ gap7

/-- Source: `proof_gap/exercise_740/9.txt`; isolate the fifth limit. -/
theorem gap9 :
    Filter.Tendsto core5 (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hsquare_nhds : Filter.Tendsto (fun x : ℝ => x ^ 2) F (nhds 0) := by
    have h : Filter.Tendsto (fun x : ℝ => x ^ 2)
        (nhds 0) (nhds (0 ^ 2)) :=
      (continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow 2
    simpa [F] using h.mono_left inf_le_left
  have hsquare : Filter.Tendsto (fun x : ℝ => x ^ 2) F
      (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hsquare_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    simpa only [Set.mem_Ioi] using sq_pos_of_ne_zero hx0
  have hinv : Filter.Tendsto (fun x : ℝ => (x ^ 2)⁻¹) F Filter.atTop :=
    tendsto_inv_nhdsGT_zero.comp hsquare
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hinv
  apply h.congr'
  filter_upwards with x
  simp [core5, one_div, pow_one]

/-- Source: `proof_gap/exercise_740/10.txt`; state the criterion only for
`f₅`. -/
theorem gap10 (f₅ : ℝ → ℝ)
    (h₅ : ∀ x : ℝ, x ≠ 0 → f₅ x = core5 x) :
    ContinuousAt f₅ 0 ↔ f₅ 0 = 0 := by
  exact continuousAt_iff_of_punctured_limit f₅ core5 0 h₅ gap9

/-- Source: `proof_gap/exercise_740/11.txt`; the source defines `x^x` only
for `x>0`, so use a right-hand limit and `Real.rpow`. -/
theorem gap11 :
    Filter.Tendsto core6 (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hlog : Filter.Tendsto Real.log
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hneglog : Filter.Tendsto (fun x : ℝ => -Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [(Filter.tendsto_atBot.1 hlog (-b))] with x hx
    linarith
  have hdecay :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp hneglog
  have hnegxlog : Filter.Tendsto (fun x : ℝ => -(x * Real.log x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    apply hdecay.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
    simp only [Function.comp_apply, pow_one]
    rw [neg_neg, Real.exp_log hxpos]
    ring
  have hxlog : Filter.Tendsto (fun x : ℝ => x * Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    convert hnegxlog.neg using 1 <;> norm_num
  have hexp0 : Filter.Tendsto Real.exp (nhds (0 : ℝ))
      (nhds (Real.exp 0)) :=
    Real.continuous_exp.continuousAt
  have h := hexp0.comp hxlog
  have heq : core6 =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      fun x : ℝ => Real.exp (x * Real.log x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
    have hpow : x ^ (x : ℝ) = Real.exp (Real.log x * x) :=
      Real.rpow_def_of_pos hxpos (x : ℝ)
    simp only [core6]
    change x ^ (x : ℝ) = Real.exp (x * Real.log x)
    simpa only [mul_comm] using hpow
  have hout := h.congr' heq.symm
  convert hout using 1 <;> norm_num

/-- Source: `proof_gap/exercise_740/12.txt`; continuity is relative to the
closed half-line because the source supplies no negative-side definition. -/
theorem gap12 (f₆ : ℝ → ℝ)
    (h₆ : ∀ x : ℝ, 0 < x → f₆ x = core6 x) :
    ContinuousWithinAt f₆ (Set.Ici 0) 0 ↔ f₆ 0 = 1 := by
  exact continuousWithinAt_iff_of_right_limit f₆ core6 1 h₆ gap11

/-- Source: `proof_gap/exercise_740/13.txt`; use the right-hand limit imposed
by the logarithm's domain. -/
theorem gap13 :
    Filter.Tendsto core7 (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hlog : Filter.Tendsto Real.log
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atBot :=
    Real.tendsto_log_nhdsGT_zero
  have hneglog : Filter.Tendsto (fun x : ℝ => -Real.log x)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [(Filter.tendsto_atBot.1 hlog (-b))] with x hx
    linarith
  have h :=
    (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp hneglog
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := by simpa only [Set.mem_Ioi] using hx
  simp only [Function.comp_apply, core7]
  rw [neg_neg, Real.exp_log hxpos]
  ring

/-- Source: `proof_gap/exercise_740/14.txt`; continuity is relative to the
closed half-line. -/
theorem gap14 (f₇ : ℝ → ℝ)
    (h₇ : ∀ x : ℝ, 0 < x → f₇ x = core7 x) :
    ContinuousWithinAt f₇ (Set.Ici 0) 0 ↔ f₇ 0 = 0 := by
  exact continuousWithinAt_iff_of_right_limit f₇ core7 0 h₇ gap13

/-- Source: `proof_gap/exercise_740/15.txt`; replace the source's
non-associative seven-tuple notation by seven value hypotheses, and use
one-sided continuity for the two functions defined only on `x>0`. -/
theorem gap15
    (f₁ f₂ f₃ f₄ f₅ f₆ f₇ : ℝ → ℝ)
    (h₁ : ∀ x : ℝ, x ≠ 0 → f₁ x = core1 x)
    (h₂ : ∀ x : ℝ, x ≠ 0 → f₂ x = core2 x)
    (h₃ : ∀ x : ℝ, x ≠ 0 → f₃ x = core3 x)
    (h₄ : ∀ x : ℝ, x ≠ 0 → f₄ x = core4 x)
    (h₅ : ∀ x : ℝ, x ≠ 0 → f₅ x = core5 x)
    (h₆ : ∀ x : ℝ, 0 < x → f₆ x = core6 x)
    (h₇ : ∀ x : ℝ, 0 < x → f₇ x = core7 x)
    (hv₁ : f₁ 0 = (3 / 2 : ℝ))
    (hv₂ : f₂ 0 = 2)
    (hv₃ : f₃ 0 = 0)
    (hv₄ : f₄ 0 = Real.exp 1)
    (hv₅ : f₅ 0 = 0)
    (hv₆ : f₆ 0 = 1)
    (hv₇ : f₇ 0 = 0) :
    ContinuousAt f₁ 0 ∧
    ContinuousAt f₂ 0 ∧
    ContinuousAt f₃ 0 ∧
    ContinuousAt f₄ 0 ∧
    ContinuousAt f₅ 0 ∧
    ContinuousWithinAt f₆ (Set.Ici 0) 0 ∧
    ContinuousWithinAt f₇ (Set.Ici 0) 0 := by
  exact ⟨(gap2 f₁ h₁).2 hv₁,
    (gap4 f₂ h₂).2 hv₂,
    (gap6 f₃ h₃).2 hv₃,
    (gap8 f₄ h₄).2 hv₄,
    (gap10 f₅ h₅).2 hv₅,
    (gap12 f₆ h₆).2 hv₆,
    (gap14 f₇ h₇).2 hv₇⟩

end

end ProofGap.Exercise740
