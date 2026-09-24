import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1363

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def f₀ (x : ℝ) : ℝ := (Real.log (Real.arcsin x) - Real.log x) / x ^ 2
def f₁ (x : ℝ) : ℝ :=
  (1 / (Real.sqrt (1 - x ^ 2) * Real.arcsin x) - 1 / x) / (2 * x)
def f₂ (x : ℝ) : ℝ :=
  (x - Real.sqrt (1 - x ^ 2) * Real.arcsin x) /
    (2 * x ^ 2 * Real.sqrt (1 - x ^ 2) * Real.arcsin x)
def f₃ (x : ℝ) : ℝ :=
  (x / Real.sqrt (1 - x ^ 2) * Real.arcsin x) /
    ((4 * x * Real.sqrt (1 - x ^ 2) -
      2 * x ^ 3 / Real.sqrt (1 - x ^ 2)) * Real.arcsin x + 2 * x ^ 2)
def f₄ (x : ℝ) : ℝ :=
  Real.arcsin x /
    (2 * (2 - 3 * x ^ 2) * Real.arcsin x +
      2 * x * Real.sqrt (1 - x ^ 2))
def f₅ (x : ℝ) : ℝ :=
  (1 / Real.sqrt (1 - x ^ 2)) /
    (-12 * x * Real.arcsin x +
      2 * (2 - 3 * x ^ 2) / Real.sqrt (1 - x ^ 2) +
      2 * Real.sqrt (1 - x ^ 2) -
      2 * x ^ 2 / Real.sqrt (1 - x ^ 2))
def powerForm (x : ℝ) : ℝ :=
  Real.rpow (Real.arcsin x / x) (1 / x ^ 2)

private theorem arcsin_lt_zero_of_lt_zero {x : ℝ} (hx : x < 0) :
    Real.arcsin x < 0 := by
  have h : 0 < Real.arcsin (-x) := (Real.arcsin_pos).2 (neg_pos.mpr hx)
  rw [Real.arcsin_neg] at h
  exact neg_pos.mp h

private theorem arcsin_ne_zero_of_ne_zero {x : ℝ} (hx : x ≠ 0) :
    Real.arcsin x ≠ 0 := by
  rcases lt_or_gt_of_ne hx with hxneg | hxpos
  · exact ne_of_lt (arcsin_lt_zero_of_lt_zero hxneg)
  · exact ne_of_gt ((Real.arcsin_pos).2 hxpos)

private theorem arcsin_div_tendsto :
    Filter.Tendsto (fun x : ℝ => Real.arcsin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have h := (Real.hasDerivAt_arcsin
    (by norm_num : (0 : ℝ) ≠ -1)
    (by norm_num : (0 : ℝ) ≠ 1)).tendsto_slope_zero
  simpa [div_eq_mul_inv, mul_comm] using h

private theorem tendsto_real_id_punctured :
    Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
  have h : Filter.Tendsto (id : ℝ → ℝ) (nhds 0) (nhds 0) :=
    continuousAt_id
  simpa only [id_eq] using h.mono_left inf_le_left

private theorem limit_f5 : HasLimitAtZero f₅ (1 / 6) := by
  rw [HasLimitAtZero]
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hx : Filter.Tendsto (fun x : ℝ => x) F (nhds 0) :=
    tendsto_real_id_punctured
  have ha : Filter.Tendsto (fun x : ℝ => Real.arcsin x) F (nhds 0) := by
    simpa using Real.continuous_arcsin.continuousAt.tendsto.comp hx
  have hs : Filter.Tendsto (fun x : ℝ => Real.sqrt (1 - x ^ 2)) F (nhds 1) := by
    have hinner : Filter.Tendsto (fun x : ℝ => 1 - x ^ 2) F (nhds 1) := by
      convert tendsto_const_nhds.sub (hx.pow 2) using 1 <;> norm_num
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hinner
  have hd : Filter.Tendsto
      (fun x : ℝ => 6 - 10 * x ^ 2 -
        12 * x * Real.arcsin x * Real.sqrt (1 - x ^ 2)) F (nhds 6) := by
    convert (tendsto_const_nhds.sub
      (tendsto_const_nhds.mul (hx.pow 2))).sub
      (((tendsto_const_nhds.mul hx).mul ha).mul hs) using 1 <;> ring
  have hg : Filter.Tendsto
      (fun x : ℝ => 1 / (6 - 10 * x ^ 2 -
        12 * x * Real.arcsin x * Real.sqrt (1 - x ^ 2))) F (nhds (1 / 6)) := by
    simpa [one_div] using hd.inv₀ (by norm_num : (6 : ℝ) ≠ 0)
  apply hg.congr'
  have hsmall : ∀ᶠ x : ℝ in F, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) :=
    (show ∀ᶠ x : ℝ in nhds 0, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) from
      Ioo_mem_nhds (by norm_num) (by norm_num)).filter_mono inf_le_left
  filter_upwards [hsmall] with x hxI
  have hx2 : x ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hxI.1) (sub_pos.mpr hxI.2)]
  have hr : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hr)
  have hs2 : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hr)
  unfold f₅
  have hden :
      Real.sqrt (1 - x ^ 2) *
        (-12 * x * Real.arcsin x +
          2 * (2 - 3 * x ^ 2) / Real.sqrt (1 - x ^ 2) +
          2 * Real.sqrt (1 - x ^ 2) -
          2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) =
        6 - 10 * x ^ 2 -
          12 * x * Real.arcsin x * Real.sqrt (1 - x ^ 2) := by
    field_simp [hs0]
    nlinarith
  rw [← hden]
  simpa only [div_div]

private theorem limit_f4 : HasLimitAtZero f₄ (1 / 6) := by
  rw [HasLimitAtZero]
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hx : Filter.Tendsto (fun x : ℝ => x) F (nhds 0) :=
    tendsto_real_id_punctured
  have hs : Filter.Tendsto (fun x : ℝ => Real.sqrt (1 - x ^ 2)) F (nhds 1) := by
    have hinner : Filter.Tendsto (fun x : ℝ => 1 - x ^ 2) F (nhds 1) := by
      convert tendsto_const_nhds.sub (hx.pow 2) using 1 <;> norm_num
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hinner
  have hd : Filter.Tendsto
      (fun x : ℝ =>
        2 * (2 - 3 * x ^ 2) * (Real.arcsin x / x) +
          2 * Real.sqrt (1 - x ^ 2)) F (nhds 6) := by
    convert ((tendsto_const_nhds.mul
      (tendsto_const_nhds.sub (tendsto_const_nhds.mul (hx.pow 2)))).mul
      arcsin_div_tendsto).add (tendsto_const_nhds.mul hs) using 1 <;> ring
  have hq : Filter.Tendsto
      (fun x : ℝ => (Real.arcsin x / x) /
        (2 * (2 - 3 * x ^ 2) * (Real.arcsin x / x) +
          2 * Real.sqrt (1 - x ^ 2))) F (nhds (1 / 6)) := by
    convert arcsin_div_tendsto.div hd (by norm_num : (6 : ℝ) ≠ 0) using 1 <;> norm_num
  apply hq.congr'
  have hne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  filter_upwards [hne] with x hx
  unfold f₄
  field_simp [hx]

private theorem limit_f3 : HasLimitAtZero f₃ (1 / 6) := by
  rw [HasLimitAtZero]
  have hlim := limit_f4
  rw [HasLimitAtZero] at hlim
  apply hlim.congr'
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hsmall : ∀ᶠ x : ℝ in F, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) :=
    (show ∀ᶠ x : ℝ in nhds 0, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) from
      Ioo_mem_nhds (by norm_num) (by norm_num)).filter_mono inf_le_left
  have hne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  filter_upwards [hsmall, hne] with x hxI hx
  have hx2 : x ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hxI.1) (sub_pos.mpr hxI.2)]
  have hr : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hr)
  have hs2 : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
    Real.sq_sqrt (le_of_lt hr)
  have hden :
      (4 * x * Real.sqrt (1 - x ^ 2) -
          2 * x ^ 3 / Real.sqrt (1 - x ^ 2)) * Real.arcsin x + 2 * x ^ 2 =
        (x / Real.sqrt (1 - x ^ 2)) *
          (2 * (2 - 3 * x ^ 2) * Real.arcsin x +
            2 * x * Real.sqrt (1 - x ^ 2)) := by
    field_simp [hs0]
    rw [hs2]
    ring
  unfold f₃ f₄
  rw [hden]
  let c : ℝ := x / Real.sqrt (1 - x ^ 2)
  let D : ℝ := 2 * (2 - 3 * x ^ 2) * Real.arcsin x +
    2 * x * Real.sqrt (1 - x ^ 2)
  have hc : c ≠ 0 := div_ne_zero hx hs0
  change Real.arcsin x / D = (c * Real.arcsin x) / (c * D)
  by_cases hD : D = 0
  · simp [hD]
  · field_simp [hc, hD]

private theorem limit_f2 : HasLimitAtZero f₂ (1 / 6) := by
  rw [HasLimitAtZero]
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  let u : ℝ → ℝ := fun x => x - Real.sqrt (1 - x ^ 2) * Real.arcsin x
  let v : ℝ → ℝ := fun x =>
    2 * x ^ 2 * Real.sqrt (1 - x ^ 2) * Real.arcsin x
  let du : ℝ → ℝ := fun x =>
    x / Real.sqrt (1 - x ^ 2) * Real.arcsin x
  let dv : ℝ → ℝ := fun x =>
    (4 * x * Real.sqrt (1 - x ^ 2) -
      2 * x ^ 3 / Real.sqrt (1 - x ^ 2)) * Real.arcsin x + 2 * x ^ 2
  have hx : Filter.Tendsto (fun x : ℝ => x) F (nhds 0) :=
    tendsto_real_id_punctured
  have ha : Filter.Tendsto (fun x : ℝ => Real.arcsin x) F (nhds 0) := by
    simpa using Real.continuous_arcsin.continuousAt.tendsto.comp hx
  have hs : Filter.Tendsto (fun x : ℝ => Real.sqrt (1 - x ^ 2)) F (nhds 1) := by
    have hinner : Filter.Tendsto (fun x : ℝ => 1 - x ^ 2) F (nhds 1) := by
      convert tendsto_const_nhds.sub (hx.pow 2) using 1 <;> norm_num
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hinner
  have hu : Filter.Tendsto u F (nhds 0) := by
    dsimp [u]
    convert hx.sub (hs.mul ha) using 1 <;> norm_num
  have hv : Filter.Tendsto v F (nhds 0) := by
    dsimp [v]
    convert (((tendsto_const_nhds.mul (hx.pow 2)).mul hs).mul ha) using 1 <;> norm_num
  have hsmallN : ∀ᶠ x : ℝ in nhds 0, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) :=
    Ioo_mem_nhds (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ x : ℝ in F, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) :=
    hsmallN.filter_mono inf_le_left
  have hne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hderiv : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt u (du x) x ∧ HasDerivAt v (dv x) x := by
    filter_upwards [hsmallN] with x hxI
    have hx2 : x ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hxI.1) (sub_pos.mpr hxI.2)]
    have hr : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
    have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hr)
    have hs' : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y ^ 2))
        (-x / Real.sqrt (1 - x ^ 2)) x := by
      convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp x
        ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).pow 2)) using 1 <;>
        simp only [id_eq, Pi.pow_apply] <;>
        (try field_simp [hs0]) <;> ring
    have ha' := Real.hasDerivAt_arcsin
      (ne_of_gt (lt_trans (by norm_num : (-1 : ℝ) < -(1 / 2)) hxI.1))
      (ne_of_lt (lt_trans hxI.2 (by norm_num : (1 / 2 : ℝ) < 1)))
    constructor
    · dsimp [u, du]
      convert (hasDerivAt_id x).sub (hs'.mul ha') using 1 <;>
        (try simp only [id_eq, Pi.mul_apply]) <;>
        ring_nf <;>
        field_simp [hs0] <;> ring
    · dsimp [v, dv]
      convert (((hasDerivAt_const x 2).mul ((hasDerivAt_id x).pow 2)).mul hs').mul ha' using 1 <;>
        (try simp only [id_eq, Pi.mul_apply, Pi.pow_apply]) <;>
        ring_nf <;>
        field_simp [hs0] <;> ring
  have hdu : ∀ᶠ x : ℝ in nhds 0, HasDerivAt u (du x) x :=
    hderiv.mono fun _ h => h.1
  have hdv' : ∀ᶠ x : ℝ in nhds 0, HasDerivAt v (dv x) x :=
    hderiv.mono fun _ h => h.2
  have hdv : ∀ᶠ x : ℝ in F, dv x ≠ 0 := by
    filter_upwards [hsmall, hne] with x hxI hx0
    have hx_sq : x ^ 2 < 1 / 4 := by
      nlinarith [mul_pos (sub_pos.mpr hxI.1) (sub_pos.mpr hxI.2)]
    have hr : 0 < 1 - x ^ 2 := by nlinarith
    have hspos : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hr
    have hxa : 0 < x * Real.arcsin x := by
      rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
      · exact mul_pos_of_neg_of_neg hxneg (arcsin_lt_zero_of_lt_zero hxneg)
      · exact mul_pos hxpos ((Real.arcsin_pos).2 hxpos)
    have hcoef : 0 < 4 * Real.sqrt (1 - x ^ 2) -
        2 * x ^ 2 / Real.sqrt (1 - x ^ 2) := by
      have hs2 : (Real.sqrt (1 - x ^ 2)) ^ 2 = 1 - x ^ 2 :=
        Real.sq_sqrt (le_of_lt hr)
      field_simp [ne_of_gt hspos]
      nlinarith
    dsimp [dv]
    have heq : (4 * x * Real.sqrt (1 - x ^ 2) -
        2 * x ^ 3 / Real.sqrt (1 - x ^ 2)) * Real.arcsin x =
        (x * Real.arcsin x) *
          (4 * Real.sqrt (1 - x ^ 2) -
            2 * x ^ 2 / Real.sqrt (1 - x ^ 2)) := by ring
    rw [heq]
    positivity
  have hratio : Filter.Tendsto (fun x => du x / dv x) F (nhds (1 / 6)) := by
    have hlim := limit_f3
    rw [HasLimitAtZero] at hlim
    simpa only [du, dv, f₃] using hlim
  let FL : Filter ℝ := nhdsWithin 0 (Set.Iio 0)
  let FR : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hLF : FL ≤ F := by
    dsimp [FL, F]
    apply nhdsWithin_mono
    intro x hxlt
    have hlt : x < 0 := hxlt
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_lt hlt
  have hRF : FR ≤ F := by
    dsimp [FR, F]
    apply nhdsWithin_mono
    intro x hxgt
    have hgt : 0 < x := hxgt
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_gt hgt
  have hduL : ∀ᶠ x : ℝ in FL, HasDerivAt u (du x) x := by
    dsimp [FL]
    exact hdu.filter_mono inf_le_left
  have hdvL' : ∀ᶠ x : ℝ in FL, HasDerivAt v (dv x) x := by
    dsimp [FL]
    exact hdv'.filter_mono inf_le_left
  have hdvL : ∀ᶠ x : ℝ in FL, dv x ≠ 0 := hdv.filter_mono hLF
  have huL : Filter.Tendsto u FL (nhds 0) := hu.mono_left hLF
  have hvL : Filter.Tendsto v FL (nhds 0) := hv.mono_left hLF
  have hratioL : Filter.Tendsto (fun x => du x / dv x) FL (nhds (1 / 6)) :=
    hratio.mono_left hLF
  have hleft : Filter.Tendsto (fun x => u x / v x) FL (nhds (1 / 6)) := by
    apply HasDerivAt.lhopital_zero_nhdsLT hduL hdvL'
    all_goals assumption
  have hduR : ∀ᶠ x : ℝ in FR, HasDerivAt u (du x) x := by
    dsimp [FR]
    exact hdu.filter_mono inf_le_left
  have hdvR' : ∀ᶠ x : ℝ in FR, HasDerivAt v (dv x) x := by
    dsimp [FR]
    exact hdv'.filter_mono inf_le_left
  have hdvR : ∀ᶠ x : ℝ in FR, dv x ≠ 0 := hdv.filter_mono hRF
  have huR : Filter.Tendsto u FR (nhds 0) := hu.mono_left hRF
  have hvR : Filter.Tendsto v FR (nhds 0) := hv.mono_left hRF
  have hratioR : Filter.Tendsto (fun x => du x / dv x) FR (nhds (1 / 6)) :=
    hratio.mono_left hRF
  have hright : Filter.Tendsto (fun x => u x / v x) FR (nhds (1 / 6)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT hduR hdvR'
    all_goals assumption
  have hsplit : F = FL ⊔ FR := by
    dsimp [F, FL, FR]
    rw [← nhdsWithin_union]
    congr 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · intro h
      rcases h with h | h
      · exact ne_of_lt h
      · exact ne_of_gt h
  change Filter.Tendsto (fun x => u x / v x) F (nhds (1 / 6))
  rw [hsplit]
  exact hleft.sup hright

private theorem limit_f1 : HasLimitAtZero f₁ (1 / 6) := by
  rw [HasLimitAtZero]
  have hlim := limit_f2
  rw [HasLimitAtZero] at hlim
  apply hlim.congr'
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hsmall : ∀ᶠ x : ℝ in F, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) :=
    (show ∀ᶠ x : ℝ in nhds 0, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) from
      Ioo_mem_nhds (by norm_num) (by norm_num)).filter_mono inf_le_left
  have hne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  filter_upwards [hsmall, hne] with x hxI hx
  have hx2 : x ^ 2 < 1 := by
    nlinarith [mul_pos (sub_pos.mpr hxI.1) (sub_pos.mpr hxI.2)]
  have hr : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
  have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hr)
  have ha0 : Real.arcsin x ≠ 0 := arcsin_ne_zero_of_ne_zero hx
  unfold f₁ f₂
  field_simp [hx, hs0, ha0]

private theorem limit_f0 : HasLimitAtZero f₀ (1 / 6) := by
  rw [HasLimitAtZero]
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  let u : ℝ → ℝ := fun x => Real.log (Real.arcsin x) - Real.log x
  let v : ℝ → ℝ := fun x => x ^ 2
  let du : ℝ → ℝ := fun x =>
    1 / (Real.sqrt (1 - x ^ 2) * Real.arcsin x) - 1 / x
  let dv : ℝ → ℝ := fun x => 2 * x
  have hne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hu : Filter.Tendsto u F (nhds 0) := by
    have hlog : Filter.Tendsto
        (fun x : ℝ => Real.log (Real.arcsin x / x)) F (nhds 0) := by
      simpa using Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0) |>.tendsto.comp arcsin_div_tendsto
    apply hlog.congr'
    filter_upwards [hne] with x hx0
    have ha0 : Real.arcsin x ≠ 0 := arcsin_ne_zero_of_ne_zero hx0
    dsimp [u]
    rw [Real.log_div ha0 hx0]
  have hx : Filter.Tendsto (fun x : ℝ => x) F (nhds 0) :=
    tendsto_real_id_punctured
  have hv : Filter.Tendsto v F (nhds 0) := by
    simpa [v] using hx.pow 2
  have hsmall : ∀ᶠ x : ℝ in F, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) :=
    (show ∀ᶠ x : ℝ in nhds 0, x ∈ Set.Ioo (-(1 / 2)) (1 / 2) from
      Ioo_mem_nhds (by norm_num) (by norm_num)).filter_mono inf_le_left
  have hderiv : ∀ᶠ x : ℝ in F,
      HasDerivAt u (du x) x ∧ HasDerivAt v (dv x) x := by
    filter_upwards [hsmall, hne] with x hxI hx0
    have hx2 : x ^ 2 < 1 := by
      nlinarith [mul_pos (sub_pos.mpr hxI.1) (sub_pos.mpr hxI.2)]
    have hr : 0 < 1 - x ^ 2 := sub_pos.mpr hx2
    have hs0 : Real.sqrt (1 - x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hr)
    have ha0 : Real.arcsin x ≠ 0 := arcsin_ne_zero_of_ne_zero hx0
    have ha' := Real.hasDerivAt_arcsin
      (ne_of_gt (lt_trans (by norm_num : (-1 : ℝ) < -(1 / 2)) hxI.1))
      (ne_of_lt (lt_trans hxI.2 (by norm_num : (1 / 2 : ℝ) < 1)))
    constructor
    · dsimp [u, du]
      convert ((Real.hasDerivAt_log ha0).comp x ha').sub
        (Real.hasDerivAt_log hx0) using 1 <;>
        field_simp [hs0, ha0, hx0] <;> ring
    · dsimp [v, dv]
      simpa using (hasDerivAt_id x).pow 2
  have hduF : ∀ᶠ x : ℝ in F, HasDerivAt u (du x) x :=
    hderiv.mono fun _ h => h.1
  have hdvF' : ∀ᶠ x : ℝ in F, HasDerivAt v (dv x) x :=
    hderiv.mono fun _ h => h.2
  have hdvF : ∀ᶠ x : ℝ in F, dv x ≠ 0 := by
    filter_upwards [hne] with x hx0
    dsimp [dv]
    exact mul_ne_zero (by norm_num) hx0
  have hratio : Filter.Tendsto (fun x => du x / dv x) F (nhds (1 / 6)) := by
    have hlim := limit_f1
    rw [HasLimitAtZero] at hlim
    simpa only [du, dv, f₁] using hlim
  let FL : Filter ℝ := nhdsWithin 0 (Set.Iio 0)
  let FR : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hLF : FL ≤ F := by
    dsimp [FL, F]
    apply nhdsWithin_mono
    intro x hxlt
    have hlt : x < 0 := hxlt
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_lt hlt
  have hRF : FR ≤ F := by
    dsimp [FR, F]
    apply nhdsWithin_mono
    intro x hxgt
    have hgt : 0 < x := hxgt
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_gt hgt
  have hduL : ∀ᶠ x : ℝ in FL, HasDerivAt u (du x) x := hduF.filter_mono hLF
  have hdvL' : ∀ᶠ x : ℝ in FL, HasDerivAt v (dv x) x := hdvF'.filter_mono hLF
  have hdvL : ∀ᶠ x : ℝ in FL, dv x ≠ 0 := hdvF.filter_mono hLF
  have huL : Filter.Tendsto u FL (nhds 0) := hu.mono_left hLF
  have hvL : Filter.Tendsto v FL (nhds 0) := hv.mono_left hLF
  have hratioL : Filter.Tendsto (fun x => du x / dv x) FL (nhds (1 / 6)) :=
    hratio.mono_left hLF
  have hleft : Filter.Tendsto (fun x => u x / v x) FL (nhds (1 / 6)) := by
    apply HasDerivAt.lhopital_zero_nhdsLT hduL hdvL'
    all_goals assumption
  have hduR : ∀ᶠ x : ℝ in FR, HasDerivAt u (du x) x := hduF.filter_mono hRF
  have hdvR' : ∀ᶠ x : ℝ in FR, HasDerivAt v (dv x) x := hdvF'.filter_mono hRF
  have hdvR : ∀ᶠ x : ℝ in FR, dv x ≠ 0 := hdvF.filter_mono hRF
  have huR : Filter.Tendsto u FR (nhds 0) := hu.mono_left hRF
  have hvR : Filter.Tendsto v FR (nhds 0) := hv.mono_left hRF
  have hratioR : Filter.Tendsto (fun x => du x / dv x) FR (nhds (1 / 6)) :=
    hratio.mono_left hRF
  have hright : Filter.Tendsto (fun x => u x / v x) FR (nhds (1 / 6)) := by
    apply HasDerivAt.lhopital_zero_nhdsGT hduR hdvR'
    all_goals assumption
  have hsplit : F = FL ⊔ FR := by
    dsimp [F, FL, FR]
    rw [← nhdsWithin_union]
    congr 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · intro h
      rcases h with h | h
      · exact ne_of_lt h
      · exact ne_of_gt h
  change Filter.Tendsto (fun x => u x / v x) F (nhds (1 / 6))
  rw [hsplit]
  exact hleft.sup hright

private theorem limit_powerForm :
    HasLimitAtZero powerForm (Real.exp (1 / 6)) := by
  rw [HasLimitAtZero]
  have hlim := limit_f0
  rw [HasLimitAtZero] at hlim
  have he : Filter.Tendsto (fun x : ℝ => Real.exp (f₀ x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.exp (1 / 6))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlim
  apply he.congr'
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  have hne : ∀ᶠ x : ℝ in F, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  filter_upwards [hne] with x hx
  have ha0 : Real.arcsin x ≠ 0 := arcsin_ne_zero_of_ne_zero hx
  have hbase : 0 < Real.arcsin x / x := by
    rcases lt_or_gt_of_ne hx with hxneg | hxpos
    · exact div_pos_of_neg_of_neg (arcsin_lt_zero_of_lt_zero hxneg) hxneg
    · exact div_pos ((Real.arcsin_pos).2 hxpos) hxpos
  unfold powerForm f₀
  calc
    Real.exp ((Real.log (Real.arcsin x) - Real.log x) / x ^ 2) =
        Real.exp (Real.log (Real.arcsin x / x) * (1 / x ^ 2)) := by
      congr 1
      rw [Real.log_div ha0 hx]
      ring
    _ = Real.rpow (Real.arcsin x / x) (1 / x ^ 2) := by
      exact (Real.rpow_def_of_pos hbase _).symm

theorem gap1 : HasLimitAtZero f₀ (1 / 6) ↔ HasLimitAtZero f₁ (1 / 6) := by
  exact iff_of_true limit_f0 limit_f1
theorem gap2 : HasLimitAtZero f₁ (1 / 6) ↔ HasLimitAtZero f₂ (1 / 6) := by
  exact iff_of_true limit_f1 limit_f2
theorem gap3 : HasLimitAtZero f₀ (1 / 6) ↔ HasLimitAtZero f₂ (1 / 6) := by
  exact iff_of_true limit_f0 limit_f2
theorem gap4 : HasLimitAtZero f₂ (1 / 6) ↔ HasLimitAtZero f₃ (1 / 6) := by
  exact iff_of_true limit_f2 limit_f3
theorem gap5 : HasLimitAtZero f₃ (1 / 6) ↔ HasLimitAtZero f₄ (1 / 6) := by
  exact iff_of_true limit_f3 limit_f4
theorem gap6 : HasLimitAtZero f₄ (1 / 6) ↔ HasLimitAtZero f₅ (1 / 6) := by
  exact iff_of_true limit_f4 limit_f5
theorem gap7 : HasLimitAtZero f₅ (1 / 6) := by
  exact limit_f5
theorem gap8 : HasLimitAtZero f₄ (1 / 6) := by
  exact limit_f4
theorem gap9 : HasLimitAtZero powerForm (Real.exp (1 / 6)) := by
  exact limit_powerForm

end

end ProofGap.Exercise1363
