import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1359

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def basePower (x : ℝ) : ℝ := Real.rpow (1 + x) (1 / x)
def f₀ (x : ℝ) : ℝ := (basePower x - Real.exp 1) / x
def f₁ (x : ℝ) : ℝ :=
  basePower x * (1 / (x * (1 + x)) - Real.log (1 + x) / x ^ 2)
def f₂ (x : ℝ) : ℝ :=
  Real.exp 1 * ((x / (1 + x) - Real.log (1 + x)) / x ^ 2)
def f₃ (x : ℝ) : ℝ :=
  Real.exp 1 *
    ((1 / (1 + x) ^ 2 - 1 / (1 + x)) / (2 * x))
def f₄ (x : ℝ) : ℝ := -Real.exp 1 * (1 / (2 * (1 + x) ^ 2))

private def q (x : ℝ) :=
  (x / (1 + x) - Real.log (1 + x)) / x ^ 2

private def r (x : ℝ) :=
  (1 / (1 + x) ^ 2 - 1 / (1 + x)) / (2 * x)

private theorem tid :
    Tendsto (fun x : ℝ => x) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
  Filter.tendsto_id.mono_left inf_le_left

private theorem base_pos :
    ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 0 < 1 + x := by
  have h : ∀ᶠ x : ℝ in nhds 0, -1 < x := eventually_gt_nhds (by norm_num)
  exact (h.filter_mono inf_le_left).mono (by intros; linarith)

private theorem log_div_limit :
    Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hinner : HasDerivAt (fun x : ℝ => 1 + x) 1 0 :=
    (hasDerivAt_id (0 : ℝ)).const_add (1 : ℝ)
  have hlog : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    have houter := Real.hasDerivAt_log (x := (1 + (0 : ℝ))) (by norm_num)
    have hc := houter.comp 0 hinner
    convert hc using 1 <;> norm_num [Function.comp_def] <;> ring
  have hs := hasDerivAt_iff_tendsto_slope.mp hlog
  apply hs.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := by simpa using hx
  simp [slope_def_field, hx0]

private theorem basePower_limit :
    Tendsto basePower (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1)) := by
  have he : Tendsto (fun x : ℝ => Real.exp (Real.log (1 + x) / x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp 1)) :=
    (Real.continuous_exp.continuousAt : ContinuousAt Real.exp 1).tendsto.comp log_div_limit
  apply he.congr'
  filter_upwards [base_pos, self_mem_nhdsWithin] with x hpos hx
  have hx0 : x ≠ 0 := by simpa using hx
  have hr : Real.rpow (1 + x) (1 / x) =
      Real.exp (Real.log (1 + x) * (1 / x)) :=
    Real.rpow_def_of_pos hpos (1 / x)
  rw [basePower, hr]
  congr 1
  field_simp [hx0]

private theorem r_limit :
    Tendsto r (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1 / 2 : ℝ)) := by
  have hbase : Tendsto (fun x : ℝ => 1 + x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert tendsto_const_nhds.add tid using 1 <;> norm_num
  have hcont : Tendsto (fun x : ℝ => -(1 / (2 * (1 + x) ^ 2)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1 / 2 : ℝ)) := by
    have hp := hbase.pow 2
    have htwo :
        Tendsto (fun _ : ℝ => (2 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) :=
      tendsto_const_nhds
    have hone :
        Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
      tendsto_const_nhds
    have hd := htwo.mul hp
    have hi := hone.div hd (by norm_num)
    convert hi.neg using 1 <;> norm_num
  apply hcont.congr'
  filter_upwards [self_mem_nhdsWithin, base_pos] with x hx hpos
  have hx0 : x ≠ 0 := by simpa using hx
  have hb0 : 1 + x ≠ 0 := hpos.ne'
  simp only [r]
  field_simp [hx0, hb0]
  ring

private theorem q_limit :
    Tendsto q (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1 / 2 : ℝ)) := by
  let N : ℝ → ℝ := fun x => x / (1 + x) - Real.log (1 + x)
  have hN :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt N (1 / (1 + x) ^ 2 - 1 / (1 + x)) x := by
    filter_upwards [base_pos] with x hpos
    have hid := hasDerivAt_id x
    have hbase := hid.const_add 1
    have hdiv := hid.div hbase hpos.ne'
    have hlog := (Real.hasDerivAt_log hpos.ne').comp x hbase
    dsimp [N]
    convert hdiv.sub hlog using 1 <;> simp [id, Function.comp_def] <;>
      field_simp [hpos.ne'] <;> ring
  have hden :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    filter_upwards with x
    convert (hasDerivAt_id x).pow 2 using 1 <;> simp [id] <;> ring
  have hden_ne : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, 2 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact mul_ne_zero (by norm_num) (by simpa using hx)
  have hzeroN : Tendsto N (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    have hbase : Tendsto (fun x : ℝ => 1 + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
      convert tendsto_const_nhds.add tid using 1 <;> norm_num
    have hfrac := tid.div hbase (by norm_num)
    have hlog : Tendsto (fun x : ℝ => Real.log (1 + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
      have hl : Tendsto Real.log (nhds 1) (nhds 0) := by
        simpa using (Real.continuousAt_log one_ne_zero).tendsto
      exact hl.comp hbase
    convert hfrac.sub hlog using 1 <;> norm_num [N]
  have hzeroDen : Tendsto (fun y : ℝ => y ^ 2)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert tid.pow 2 using 1 <;> norm_num
  apply HasDerivAt.lhopital_zero_nhdsNE hN hden hden_ne hzeroN hzeroDen
  change Tendsto r (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1 / 2 : ℝ))
  exact r_limit

private theorem f₄_limit : HasLimitAtZero f₄ (-Real.exp 1 / 2) := by
  have hbase : Tendsto (fun x : ℝ => 1 + x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert tendsto_const_nhds.add tid using 1 <;> norm_num
  have hp := hbase.pow 2
  have htwo :
      Tendsto (fun _ : ℝ => (2 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) :=
    tendsto_const_nhds
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) :=
    tendsto_const_nhds
  have hd := htwo.mul hp
  have hi := hone.div hd (by norm_num)
  unfold HasLimitAtZero
  convert tendsto_const_nhds.mul hi using 1 <;> norm_num [f₄] <;> ring

private theorem f₃_limit : HasLimitAtZero f₃ (-Real.exp 1 / 2) := by
  unfold HasLimitAtZero
  convert tendsto_const_nhds.mul r_limit using 1 <;> norm_num [f₃, r] <;> ring

private theorem f₂_limit : HasLimitAtZero f₂ (-Real.exp 1 / 2) := by
  unfold HasLimitAtZero
  convert tendsto_const_nhds.mul q_limit using 1 <;> norm_num [f₂, q] <;> ring

private theorem f₁_limit : HasLimitAtZero f₁ (-Real.exp 1 / 2) := by
  unfold HasLimitAtZero
  have hp := basePower_limit.mul q_limit
  have hp' : Tendsto (fun x => basePower x * q x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-Real.exp 1 / 2)) := by
    convert hp using 1 <;> ring
  apply hp'.congr'
  filter_upwards [self_mem_nhdsWithin, base_pos] with x hx hpos
  have hx0 : x ≠ 0 := by simpa using hx
  have hb0 : 1 + x ≠ 0 := hpos.ne'
  simp only [f₁, q]
  field_simp [hx0, hb0]

private theorem basePower_deriv :
    ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      HasDerivAt basePower (f₁ x) x := by
  filter_upwards [self_mem_nhdsWithin, base_pos] with x hx hpos
  have hx0 : x ≠ 0 := by simpa using hx
  have hbase := (hasDerivAt_id x).const_add 1
  have hinv := (hasDerivAt_const (x := x) (c := (1 : ℝ))).div
    (hasDerivAt_id x) hx0
  have hraw := hbase.rpow hinv hpos
  have hrsub : Real.rpow (1 + x) (1 / x - 1) =
      Real.rpow (1 + x) (1 / x) / (1 + x) :=
    Real.rpow_sub_one hpos.ne' (1 / x)
  convert hraw using 1
  simp only [Pi.div_apply, Pi.one_apply, id_eq, one_mul, zero_mul, zero_sub]
  change f₁ x =
    1 / x * Real.rpow (1 + x) (1 / x - 1) +
      (-1 / x ^ 2) * Real.rpow (1 + x) (1 / x) * Real.log (1 + x)
  rw [hrsub]
  dsimp [basePower, f₁]
  field_simp [hx0, hpos.ne']
  ring

private theorem f₀_limit : HasLimitAtZero f₀ (-Real.exp 1 / 2) := by
  have hnum :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt (fun y => basePower y - Real.exp 1) (f₁ x) x := by
    filter_upwards [basePower_deriv] with x hx
    simpa using hx.sub_const (Real.exp 1)
  have hden :
      ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
        HasDerivAt (fun y : ℝ => y) 1 x := by
    filter_upwards with x
    simpa using hasDerivAt_id x
  have hden_ne : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, (1 : ℝ) ≠ 0 :=
    Filter.Eventually.of_forall (fun _ => one_ne_zero)
  have hzeroNum : Tendsto (fun y => basePower y - Real.exp 1)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert basePower_limit.sub tendsto_const_nhds using 1 <;> norm_num
  have hdiv : Tendsto (fun x => f₁ x / (1 : ℝ))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-Real.exp 1 / 2)) := by
    simpa using f₁_limit
  simpa [f₀] using
    HasDerivAt.lhopital_zero_nhdsNE hnum hden hden_ne hzeroNum tid hdiv

theorem gap1 : HasLimitAtZero f₀ (-Real.exp 1 / 2) ↔
    HasLimitAtZero f₁ (-Real.exp 1 / 2) := by
  constructor <;> intro _
  · exact f₁_limit
  · exact f₀_limit
theorem gap2 : HasLimitAtZero f₀ (-Real.exp 1 / 2) ↔
    HasLimitAtZero f₂ (-Real.exp 1 / 2) := by
  constructor <;> intro _
  · exact f₂_limit
  · exact f₀_limit
theorem gap3 : HasLimitAtZero f₀ (-Real.exp 1 / 2) ↔
    HasLimitAtZero f₃ (-Real.exp 1 / 2) := by
  constructor <;> intro _
  · exact f₃_limit
  · exact f₀_limit
theorem gap4 : HasLimitAtZero f₃ (-Real.exp 1 / 2) ↔
    HasLimitAtZero f₄ (-Real.exp 1 / 2) := by
  constructor <;> intro _
  · exact f₄_limit
  · exact f₃_limit
theorem gap5 : HasLimitAtZero f₄ (-Real.exp 1 / 2) := by exact f₄_limit
theorem gap6 : HasLimitAtZero f₀ (-Real.exp 1 / 2) := by exact f₀_limit

end

end ProofGap.Exercise1359
