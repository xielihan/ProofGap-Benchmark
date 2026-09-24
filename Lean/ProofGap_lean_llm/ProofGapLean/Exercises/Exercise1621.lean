import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1621

noncomputable section

def f (x : ℝ) := x ^ 2 + 1 / x ^ 2 - 10 * x
def newtonStep (x : ℝ) := x - f x / deriv f x
def Approx (actual expected tolerance : ℝ) : Prop :=
  |actual - expected| < tolerance
def smallApproximant : ℕ → ℝ
  | 1 => 0.459
  | 2 => 0.471
  | 3 => 0.472
  | _ => 0
def largeApproximant : ℕ → ℝ
  | 1 => 9.999
  | _ => 0
def reportedRoots : Set ℝ := {0.472, 9.999}
def ApproxRootSet (samples : Set ℝ) (tolerance : ℝ) : Prop :=
  (∀ s ∈ samples, ∃ r, f r = 0 ∧ |s - r| < tolerance) ∧
    (∀ r, f r = 0 → 0 < r → ∃ s ∈ samples, |r - s| < tolerance)

private def q (x : ℝ) : ℝ := x ^ 3 * (10 - x)

private theorem hasDerivAt_f (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt f (2 * x - 2 / x ^ 3 - 10) x := by
  unfold f
  convert (((hasDerivAt_id x).pow 2).add
      ((hasDerivAt_const x (1 : ℝ)).div ((hasDerivAt_id x).pow 2)
        (pow_ne_zero 2 hx))).sub
      ((hasDerivAt_const x (10 : ℝ)).mul (hasDerivAt_id x)) using 1 <;>
    simp [hx] <;> field_simp [hx] <;> ring

private theorem deriv_f_eq (x : ℝ) (hx : x ≠ 0) :
    deriv f x = 2 * x - 2 / x ^ 3 - 10 :=
  (hasDerivAt_f x hx).deriv

private theorem second_deriv_f_eq (x : ℝ) (hx : x ≠ 0) :
    deriv (deriv f) x = 2 + 6 / x ^ 4 := by
  let g : ℝ → ℝ := fun y => 2 * y - 2 / y ^ 3 - 10
  have heq : deriv f =ᶠ[nhds x] g := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact deriv_f_eq y hy
  have hg : HasDerivAt g (2 + 6 / x ^ 4) x := by
    dsimp [g]
    convert (((hasDerivAt_const x (2 : ℝ)).mul (hasDerivAt_id x)).sub
        ((hasDerivAt_const x (2 : ℝ)).div ((hasDerivAt_id x).pow 3)
          (pow_ne_zero 3 hx))).sub
        (hasDerivAt_const x (10 : ℝ)) using 1 <;>
      simp [hx] <;> field_simp [hx] <;> ring
  calc
    deriv (deriv f) x = deriv g x := heq.deriv_eq
    _ = 2 + 6 / x ^ 4 := hg.deriv

private theorem q_eq_one_of_f_eq_zero (x : ℝ) (hx : x ≠ 0)
    (hfx : f x = 0) : q x = 1 := by
  unfold f at hfx
  field_simp [hx] at hfx
  unfold q
  ring_nf at hfx ⊢
  linarith

private theorem f_eq_zero_of_q_eq (x : ℝ) (hx : x ≠ 0)
    (hqx : q x = 1) : f x = 0 := by
  unfold f
  field_simp [hx]
  unfold q at hqx
  ring_nf at hqx ⊢
  linarith

private theorem q_strict_small {x y : ℝ}
    (hx : x ∈ Set.Ioo (0.4 : ℝ) 0.5)
    (hy : y ∈ Set.Ioo (0.4 : ℝ) 0.5) (hxy : x < y) : q x < q y := by
  have hxpos : 0 < x := by nlinarith [hx.1]
  have hypos : 0 < y := by nlinarith [hy.1]
  have hxone : x < 1 := by nlinarith [hx.2]
  have hyone : y < 1 := by nlinarith [hy.2]
  have hy3 : y ^ 3 < y ^ 2 := by
    nlinarith [mul_pos (pow_pos hypos 2) (sub_pos.mpr hyone)]
  have hy2x : y ^ 2 * x < y ^ 2 := by
    nlinarith [mul_pos (pow_pos hypos 2) (sub_pos.mpr hxone)]
  have hyx2 : y * x ^ 2 < x ^ 2 := by
    nlinarith [mul_pos (pow_pos hxpos 2) (sub_pos.mpr hyone)]
  have hx3 : x ^ 3 < x ^ 2 := by
    nlinarith [mul_pos (pow_pos hxpos 2) (sub_pos.mpr hxone)]
  have hcoef :
      0 < 10 * (y ^ 2 + y * x + x ^ 2) -
        (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3) := by
    nlinarith [pow_pos hxpos 2, pow_pos hypos 2]
  have hfac :
      q y - q x = (y - x) *
        (10 * (y ^ 2 + y * x + x ^ 2) -
          (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)) := by
    unfold q
    ring
  have hp := mul_pos (sub_pos.mpr hxy) hcoef
  nlinarith [hfac]

private theorem q_strict_large {x y : ℝ}
    (hx : x ∈ Set.Ioo (9.99 : ℝ) 10)
    (hy : y ∈ Set.Ioo (9.99 : ℝ) 10) (hxy : x < y) : q y < q x := by
  have hxpos : 0 < x := by nlinarith [hx.1]
  have hypos : 0 < y := by nlinarith [hy.1]
  have hy3 : (9.99 : ℝ) * y ^ 2 < y ^ 3 := by
    nlinarith [mul_pos (pow_pos hypos 2) (sub_pos.mpr hy.1)]
  have hy2x : (9.99 : ℝ) * y ^ 2 < y ^ 2 * x := by
    nlinarith [mul_pos (pow_pos hypos 2) (sub_pos.mpr hx.1)]
  have hyx2 : (9.99 : ℝ) * x ^ 2 < y * x ^ 2 := by
    nlinarith [mul_pos (pow_pos hxpos 2) (sub_pos.mpr hy.1)]
  have hx3 : (9.99 : ℝ) * x ^ 2 < x ^ 3 := by
    nlinarith [mul_pos (pow_pos hxpos 2) (sub_pos.mpr hx.1)]
  have hcoef :
      10 * (y ^ 2 + y * x + x ^ 2) -
        (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3) < 0 := by
    nlinarith [pow_pos hxpos 2, pow_pos hypos 2]
  have hfac :
      q y - q x = (y - x) *
        (10 * (y ^ 2 + y * x + x ^ 2) -
          (y ^ 3 + y ^ 2 * x + y * x ^ 2 + x ^ 3)) := by
    unfold q
    ring
  have hp := mul_neg_of_pos_of_neg (sub_pos.mpr hxy) hcoef
  nlinarith [hfac]

private theorem deriv_f_lt_neg_twenty_five {x : ℝ}
    (hx : x ∈ Set.Ioo (0.4 : ℝ) 0.5) : deriv f x < -25 := by
  have hxpos : 0 < x := by nlinarith [hx.1]
  have hx0 : x ≠ 0 := ne_of_gt hxpos
  have hsub : 0 < (0.5 : ℝ) - x := sub_pos.mpr hx.2
  have hmul1 : 0 < x * ((0.5 : ℝ) - x) := mul_pos hxpos hsub
  have hmul2 : 0 < x ^ 2 * ((0.5 : ℝ) - x) :=
    mul_pos (pow_pos hxpos 2) hsub
  have hx3 : x ^ 3 < (1 / 8 : ℝ) := by nlinarith
  have hx3pos : 0 < x ^ 3 := pow_pos hxpos 3
  have hdiv : 16 < 2 / x ^ 3 := by
    apply (lt_div_iff₀ hx3pos).2
    nlinarith
  rw [deriv_f_eq x hx0]
  nlinarith [hx.2]

private theorem positive_root_location (r : ℝ) (hrzero : f r = 0)
    (hrpos : 0 < r) :
    r ∈ Set.Ioo (0.4 : ℝ) 0.5 ∨ r ∈ Set.Ioo (9.99 : ℝ) 10 := by
  have hr0 : r ≠ 0 := ne_of_gt hrpos
  have hq := q_eq_one_of_f_eq_zero r hr0 hrzero
  have hrten : r < 10 := by
    by_contra hn
    have hten : (10 : ℝ) ≤ r := le_of_not_gt hn
    have hp3 : 0 ≤ r ^ 3 := (pow_pos hrpos 3).le
    have hnonpos : r ^ 3 * (10 - r) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hp3 (by linarith)
    unfold q at hq
    nlinarith
  have hrpointfour : (0.4 : ℝ) < r := by
    by_contra hn
    have hrle : r ≤ (0.4 : ℝ) := le_of_not_gt hn
    have h1 : 0 ≤ r * ((0.4 : ℝ) - r) :=
      mul_nonneg hrpos.le (sub_nonneg.mpr hrle)
    have h2 : 0 ≤ r ^ 2 * ((0.4 : ℝ) - r) :=
      mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrle)
    have h4 : 0 < r ^ 3 * r := mul_pos (pow_pos hrpos 3) hrpos
    unfold q at hq
    nlinarith
  by_cases hsmall : r < (0.5 : ℝ)
  · exact Or.inl ⟨hrpointfour, hsmall⟩
  · have hrhalf : (0.5 : ℝ) ≤ r := le_of_not_gt hsmall
    have hrlarge : (9.99 : ℝ) < r := by
      by_contra hn
      have hrle : r ≤ (9.99 : ℝ) := le_of_not_gt hn
      have hqgt : 1 < q r := by
        by_cases hfirst : r < 1
        · have h1 : 0 ≤ r * (r - (0.5 : ℝ)) :=
            mul_nonneg hrpos.le (sub_nonneg.mpr hrhalf)
          have h2 : 0 ≤ r ^ 2 * (r - (0.5 : ℝ)) :=
            mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrhalf)
          have hp : 0 < r ^ 3 * ((10 - r) - 9) :=
            mul_pos (pow_pos hrpos 3) (by nlinarith)
          unfold q
          nlinarith
        · have hrone : 1 ≤ r := le_of_not_gt hfirst
          by_cases hsecond : r < 9
          · have h1 : 0 ≤ r * (r - 1) :=
              mul_nonneg hrpos.le (sub_nonneg.mpr hrone)
            have h2 : 0 ≤ r ^ 2 * (r - 1) :=
              mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrone)
            have hp : 0 < r ^ 3 * ((10 - r) - 1) :=
              mul_pos (pow_pos hrpos 3) (by nlinarith)
            unfold q
            nlinarith
          · have hrnine : (9 : ℝ) ≤ r := le_of_not_gt hsecond
            have h1 : 0 ≤ r * (r - 9) :=
              mul_nonneg hrpos.le (sub_nonneg.mpr hrnine)
            have h2 : 0 ≤ r ^ 2 * (r - 9) :=
              mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hrnine)
            have hp : 0 ≤ r ^ 3 * ((10 - r) - (0.01 : ℝ)) :=
              mul_nonneg (pow_pos hrpos 3).le (by nlinarith)
            unfold q
            nlinarith
      linarith
    exact Or.inr ⟨hrlarge, hrten⟩

theorem gap1 : f 0.4 = 2.41 := by
  norm_num [f]
theorem gap2 : f 0.5 = -0.75 := by
  norm_num [f]
theorem gap3 (x : ℝ) (hx : x ∈ Set.Ioo (0.4 : ℝ) 0.5) :
    deriv f x ≠ 0 := by
  intro hzero
  have hlt := deriv_f_lt_neg_twenty_five hx
  rw [hzero] at hlt
  norm_num at hlt
theorem gap4 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (0.4 : ℝ) 0.5 ∧ f ξ = 0 := by
  have hc : Continuous (fun x : ℝ => q x - 1) := by
    simpa [q] using
      (((continuous_id.pow 3).mul (continuous_const.sub continuous_id)).sub
        continuous_const)
  have hi := intermediate_value_Icc (f := fun x : ℝ => q x - 1)
    (show (0.4 : ℝ) ≤ 0.5 by norm_num) hc.continuousOn
  have hz : (0 : ℝ) ∈ Set.Icc (q 0.4 - 1) (q 0.5 - 1) := by
    norm_num [q]
  rcases hi hz with ⟨ξ, hξ, hξzero⟩
  have hξa : ξ ≠ 0.4 := by
    intro h
    subst ξ
    norm_num [q] at hξzero
  have hξb : ξ ≠ 0.5 := by
    intro h
    subst ξ
    norm_num [q] at hξzero
  have hξI : ξ ∈ Set.Ioo (0.4 : ℝ) 0.5 :=
    ⟨lt_of_le_of_ne hξ.1 hξa.symm, lt_of_le_of_ne hξ.2 hξb⟩
  have hqξ : q ξ = 1 := by linarith
  have hξ0 : ξ ≠ 0 := by nlinarith [hξI.1]
  refine ⟨ξ, ⟨hξI, f_eq_zero_of_q_eq ξ hξ0 hqξ⟩, ?_⟩
  intro y hy
  have hy0 : y ≠ 0 := by nlinarith [hy.1.1]
  have hqy := q_eq_one_of_f_eq_zero y hy0 hy.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyξ | hξy
  · have hstrict := q_strict_small hy.1 hξI hyξ
    linarith
  · have hstrict := q_strict_small hξI hy.1 hξy
    linarith
theorem gap5 (x : ℝ) (hx : 0 < x) :
    deriv (deriv f) x ≠ 0 := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [second_deriv_f_eq x hx0]
  have hx4 : 0 < x ^ 4 := pow_pos hx 4
  have hdiv : 0 < 6 / x ^ 4 := div_pos (by norm_num) hx4
  nlinarith
theorem gap6 : f 0.4 * deriv (deriv f) 0.4 > 0 := by
  rw [second_deriv_f_eq 0.4 (by norm_num)]
  norm_num [f]
theorem gap7 : newtonStep 0.4 = 0.4 - f 0.4 / deriv f 0.4 := by
  rfl
theorem gap8 : Approx (newtonStep 0.4) 0.459 (1 / 1000) := by
  unfold Approx newtonStep
  rw [deriv_f_eq 0.4 (by norm_num)]
  norm_num [f]
theorem gap9 : smallApproximant 1 = 0.459 := by
  rfl
theorem gap10 : newtonStep 0.459 = 0.459 - f 0.459 / deriv f 0.459 := by
  rfl
theorem gap11 : Approx (newtonStep 0.459) 0.471 (1 / 1000) := by
  unfold Approx newtonStep
  rw [deriv_f_eq 0.459 (by norm_num)]
  norm_num [f]
theorem gap12 : smallApproximant 2 = 0.471 := by
  rfl
theorem gap13 : newtonStep 0.471 = 0.471 - f 0.471 / deriv f 0.471 := by
  rfl
theorem gap14 : Approx (newtonStep 0.471) 0.472 (1 / 1000) := by
  unfold Approx newtonStep
  rw [deriv_f_eq 0.471 (by norm_num)]
  norm_num [f]
theorem gap15 : smallApproximant 3 = 0.472 := by
  rfl
theorem gap16 : Approx (f 0.472) (-0.009) (1 / 1000) := by
  norm_num [Approx, f]
theorem gap17 : ∃ m : ℝ, m = 25 := by
  exact ⟨25, rfl⟩
theorem gap18 :
    sInf ((fun x : ℝ => |deriv f x|) '' Set.Ioo (0.4 : ℝ) 0.5) =
      |deriv f 0.5| := by
  let S : Set ℝ := (fun x : ℝ => |deriv f x|) '' Set.Ioo (0.4 : ℝ) 0.5
  have hnonempty : S.Nonempty := by
    refine ⟨|deriv f 0.45|, ?_⟩
    exact ⟨0.45, by norm_num, rfl⟩
  have hlower : ∀ z ∈ S, (25 : ℝ) ≤ z := by
    rintro z ⟨x, hx, rfl⟩
    change (25 : ℝ) ≤ |deriv f x|
    have hd := deriv_f_lt_neg_twenty_five hx
    rw [abs_of_neg (by linarith)]
    linarith
  have hbd : BddBelow S := ⟨25, hlower⟩
  have hlo : (25 : ℝ) ≤ sInf S := le_csInf hnonempty hlower
  let g : ℝ → ℝ := fun x => |2 * x - 2 / x ^ 3 - 10|
  have hgcont : ContinuousAt g 0.5 := by
    dsimp [g]
    exact (((continuousAt_const.mul continuousAt_id).sub
      (continuousAt_const.div (continuousAt_id.pow 3) (by norm_num))).sub
        continuousAt_const).abs
  have ht : Tendsto g
      (nhdsWithin (0.5 : ℝ) (Set.Iio (0.5 : ℝ))) (nhds (g 0.5)) :=
    hgcont.tendsto.mono_left inf_le_left
  have ha : ∀ᶠ x in nhdsWithin (0.5 : ℝ) (Set.Iio (0.5 : ℝ)),
      (0.4 : ℝ) < x :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  have hb : ∀ᶠ x in nhdsWithin (0.5 : ℝ) (Set.Iio (0.5 : ℝ)),
      x < (0.5 : ℝ) := self_mem_nhdsWithin
  have hev : ∀ᶠ x in nhdsWithin (0.5 : ℝ) (Set.Iio (0.5 : ℝ)),
      sInf S ≤ g x := by
    filter_upwards [ha, hb] with x hax hxb
    have hm : |deriv f x| ∈ S := ⟨x, ⟨hax, hxb⟩, rfl⟩
    have hs := csInf_le hbd hm
    rw [deriv_f_eq x (by nlinarith)] at hs
    exact hs
  have hconst : Tendsto (fun _ : ℝ => sInf S)
      (nhdsWithin (0.5 : ℝ) (Set.Iio (0.5 : ℝ))) (nhds (sInf S)) :=
    tendsto_const_nhds
  have hup : sInf S ≤ g 0.5 :=
    le_of_tendsto_of_tendsto hconst ht hev
  have hgval : g 0.5 = 25 := by
    norm_num [g]
  rw [hgval] at hup
  have hend : |deriv f 0.5| = 25 := by
    rw [deriv_f_eq 0.5 (by norm_num)]
    norm_num
  change sInf S = |deriv f 0.5|
  rw [hend]
  exact le_antisymm hup hlo
theorem gap19 : |deriv f 0.5| = 25 := by
  rw [deriv_f_eq 0.5 (by norm_num)]
  norm_num
theorem gap20 : ∃ m : ℝ, m = 25 := by
  exact ⟨25, rfl⟩
theorem gap21 :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0.4 : ℝ) 0.5 ∧ f ξ₁ = 0 ∧
      |0.472 - ξ₁| ≤ |f 0.472| / 25 := by
  rcases gap4 with ⟨ξ, ⟨hξI, hξzero⟩, huniq⟩
  have hξ0 : ξ ≠ 0 := by nlinarith [hξI.1]
  have hξpos : 0 < ξ := lt_trans (by norm_num : (0 : ℝ) < 0.4) hξI.1
  have hqξ := q_eq_one_of_f_eq_zero ξ hξ0 hξzero
  have hq472 : 1 < q 0.472 := by norm_num [q]
  have h472I : (0.472 : ℝ) ∈ Set.Ioo (0.4 : ℝ) 0.5 := by norm_num
  have hξlt : ξ < (0.472 : ℝ) := by
    by_contra hn
    have hle : (0.472 : ℝ) ≤ ξ := le_of_not_gt hn
    rcases hle.eq_or_lt with heq | hlt
    · subst ξ
      linarith
    · have hs := q_strict_small h472I hξI hlt
      linarith
  have hcont : ContinuousOn f (Set.Icc ξ (0.472 : ℝ)) := by
    intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le hξpos hx.1
    exact (hasDerivAt_f x (ne_of_gt hxpos)).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Set.Ioo ξ (0.472 : ℝ)) := by
    intro x hx
    have hxpos : 0 < x := lt_trans hξpos hx.1
    exact (hasDerivAt_f x (ne_of_gt hxpos)).differentiableAt.differentiableWithinAt
  rcases exists_deriv_eq_slope f hξlt hcont hdiff with ⟨c, hcI, hcSlope⟩
  have hcSmall : c ∈ Set.Ioo (0.4 : ℝ) 0.5 :=
    ⟨lt_trans hξI.1 hcI.1, lt_trans hcI.2 h472I.2⟩
  have hdc := deriv_f_lt_neg_twenty_five hcSmall
  have hden : 0 < (0.472 : ℝ) - ξ := sub_pos.mpr hξlt
  have hslope := hcSlope
  field_simp [ne_of_gt hden] at hslope
  have hfneg : f 0.472 < 0 := by norm_num [f]
  refine ⟨ξ, hξI, hξzero, ?_⟩
  rw [abs_of_pos hden, abs_of_neg hfneg]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 25)).2
  nlinarith
theorem gap22 : |f 0.472| / 25 < 0.001 := by
  norm_num [f]
theorem gap23 :
    ∃ ξ₁ : ℝ, ξ₁ ∈ Set.Ioo (0.4 : ℝ) 0.5 ∧ f ξ₁ = 0 ∧
      |0.472 - ξ₁| < 0.001 := by
  rcases gap21 with ⟨ξ, hξI, hξzero, herr⟩
  refine ⟨ξ, hξI, hξzero, ?_⟩
  have hb := gap22
  exact lt_of_le_of_lt herr hb
theorem gap24 : Approx (f 9.9) (-0.98) (1 / 1000) := by
  norm_num [Approx, f]
theorem gap25 : Approx (f 9.99) (-0.09) (1 / 1000) := by
  norm_num [Approx, f]
theorem gap26 : f 10 = 0.01 := by
  norm_num [f]
theorem gap27 : f 9.99 * f 10 < 0 := by
  norm_num [f]
theorem gap28 (x : ℝ) (hx : x ∈ Set.Ioo (9.99 : ℝ) 10) :
    deriv f x ≠ 0 := by
  have hxpos : 0 < x := by nlinarith [hx.1]
  have hx1 : 1 < x := by nlinarith [hx.1]
  have h1 : 0 < x * (x - 1) := mul_pos hxpos (sub_pos.mpr hx1)
  have h2 : 0 < x ^ 2 * (x - 1) :=
    mul_pos (pow_pos hxpos 2) (sub_pos.mpr hx1)
  have hx3 : 1 < x ^ 3 := by nlinarith
  have hdiv : 2 / x ^ 3 < 2 := by
    apply (div_lt_iff₀ (by positivity : 0 < x ^ 3)).2
    nlinarith
  rw [deriv_f_eq x (ne_of_gt hxpos)]
  nlinarith [hx.1]
theorem gap29 :
    ∃! ξ : ℝ, ξ ∈ Set.Ioo (9.99 : ℝ) 10 ∧ f ξ = 0 := by
  have hc : Continuous (fun x : ℝ => 1 - q x) := by
    simpa [q] using
      (continuous_const.sub
        ((continuous_id.pow 3).mul (continuous_const.sub continuous_id)))
  have hi := intermediate_value_Icc (f := fun x : ℝ => 1 - q x)
    (show (9.99 : ℝ) ≤ 10 by norm_num) hc.continuousOn
  have hz : (0 : ℝ) ∈ Set.Icc (1 - q 9.99) (1 - q 10) := by
    norm_num [q]
  rcases hi hz with ⟨ξ, hξ, hξzero⟩
  have hξa : ξ ≠ 9.99 := by
    intro h
    subst ξ
    norm_num [q] at hξzero
  have hξb : ξ ≠ 10 := by
    intro h
    subst ξ
    norm_num [q] at hξzero
  have hξI : ξ ∈ Set.Ioo (9.99 : ℝ) 10 :=
    ⟨lt_of_le_of_ne hξ.1 hξa.symm, lt_of_le_of_ne hξ.2 hξb⟩
  have hqξ : q ξ = 1 := by linarith
  have hξ0 : ξ ≠ 0 := by nlinarith [hξI.1]
  refine ⟨ξ, ⟨hξI, f_eq_zero_of_q_eq ξ hξ0 hqξ⟩, ?_⟩
  intro y hy
  have hy0 : y ≠ 0 := by nlinarith [hy.1.1]
  have hqy := q_eq_one_of_f_eq_zero y hy0 hy.2
  by_contra hne
  rcases lt_or_gt_of_ne hne with hyξ | hξy
  · have hstrict := q_strict_large hy.1 hξI hyξ
    linarith
  · have hstrict := q_strict_large hξI hy.1 hξy
    linarith
theorem gap30 : f 10 * deriv (deriv f) 10 > 0 := by
  rw [second_deriv_f_eq 10 (by norm_num)]
  norm_num [f]
theorem gap31 : newtonStep 10 = 10 - f 10 / deriv f 10 := by
  rfl
theorem gap32 : Approx (newtonStep 10) 9.999 (1 / 1000000) := by
  unfold Approx newtonStep
  rw [deriv_f_eq 10 (by norm_num)]
  norm_num [f]
theorem gap33 : largeApproximant 1 = 9.999 := by
  rfl
theorem gap34 :
    ∃ ξ₂ : ℝ, ξ₂ ∈ Set.Ioo (9.99 : ℝ) 10 ∧ f ξ₂ = 0 ∧
      |9.999 - ξ₂| < 0.001 := by
  rcases gap29 with ⟨ξ, ⟨hξI, hξzero⟩, huniq⟩
  have hξ0 : ξ ≠ 0 := by nlinarith [hξI.1]
  have hqξ := q_eq_one_of_f_eq_zero ξ hξ0 hξzero
  have h998I : (9.998 : ℝ) ∈ Set.Ioo (9.99 : ℝ) 10 := by norm_num
  have hq998 : 1 < q 9.998 := by norm_num [q]
  have hlo : (9.998 : ℝ) < ξ := by
    by_contra hn
    have hle : ξ ≤ (9.998 : ℝ) := le_of_not_gt hn
    rcases hle.eq_or_lt with heq | hlt
    · subst ξ
      linarith
    · have hs := q_strict_large hξI h998I hlt
      linarith
  refine ⟨ξ, hξI, hξzero, ?_⟩
  rw [abs_lt]
  constructor <;> nlinarith [hξI.2]
theorem gap35 : ApproxRootSet reportedRoots 0.001 := by
  constructor
  · intro s hs
    simp [reportedRoots] at hs
    rcases hs with rfl | rfl
    · rcases gap23 with ⟨r, hrI, hrzero, hrclose⟩
      exact ⟨r, hrzero, hrclose⟩
    · rcases gap34 with ⟨r, hrI, hrzero, hrclose⟩
      exact ⟨r, hrzero, hrclose⟩
  · intro r hrzero hrpos
    rcases positive_root_location r hrzero hrpos with hrSmall | hrLarge
    · rcases gap23 with ⟨ξ, hξI, hξzero, hξclose⟩
      rcases gap4 with ⟨η, hη, huniq⟩
      have hrEq : r = η := huniq r ⟨hrSmall, hrzero⟩
      have hξEq : ξ = η := huniq ξ ⟨hξI, hξzero⟩
      subst r
      subst ξ
      refine ⟨0.472, ?_, ?_⟩
      · simp [reportedRoots]
      · simpa [abs_sub_comm] using hξclose
    · rcases gap34 with ⟨ξ, hξI, hξzero, hξclose⟩
      rcases gap29 with ⟨η, hη, huniq⟩
      have hrEq : r = η := huniq r ⟨hrLarge, hrzero⟩
      have hξEq : ξ = η := huniq ξ ⟨hξI, hξzero⟩
      subst r
      subst ξ
      refine ⟨9.999, ?_, ?_⟩
      · simp [reportedRoots]
      · simpa [abs_sub_comm] using hξclose

end
end ProofGap.Exercise1621
