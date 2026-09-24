import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1357

noncomputable section

def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

def asinhArg (x : ℝ) : ℝ := x + Real.sqrt (1 + x ^ 2)
def f₀ (x : ℝ) : ℝ := 1 / Real.log (asinhArg x) - 1 / Real.log (1 + x)
def f₁ (x : ℝ) : ℝ :=
  (Real.log (1 + x) - Real.log (asinhArg x)) /
    (Real.log (1 + x) * Real.log (asinhArg x))
def f₂ (x : ℝ) : ℝ :=
  (1 / (1 + x) - 1 / Real.sqrt (1 + x ^ 2)) /
    (1 / (1 + x) * Real.log (asinhArg x) +
      1 / Real.sqrt (1 + x ^ 2) * Real.log (1 + x))
def f₃ (x : ℝ) : ℝ :=
  (Real.sqrt (1 + x ^ 2) - 1 - x) /
    (Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) +
      (1 + x) * Real.log (1 + x))
def f₄ (x : ℝ) : ℝ :=
  (x / Real.sqrt (1 + x ^ 2) - 1) /
    (1 + x / Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) +
      1 + Real.log (1 + x))

private theorem established_limits :
    HasLimitAtZero f₀ (-1 / 2) ∧
      HasLimitAtZero f₁ (-1 / 2) ∧
      HasLimitAtZero f₂ (-1 / 2) ∧
      HasLimitAtZero f₃ (-1 / 2) ∧
      HasLimitAtZero f₄ (-1 / 2) := by
  have hx : Filter.Tendsto (fun x : ℝ => x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    exact continuousAt_id.mono_left inf_le_left
  have hnear_full : ∀ᶠ x : ℝ in nhds 0, -1 < x :=
    eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0)
  have hnear : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, -1 < x :=
    hnear_full.filter_mono inf_le_left
  have harg_pos : ∀ x : ℝ, 0 < asinhArg x := by
    intro x
    unfold asinhArg
    have hs0 : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt (by positivity)
    by_contra hn
    have hle : x + Real.sqrt (1 + x ^ 2) ≤ 0 := le_of_not_gt hn
    have hleft : 0 ≤ -x - Real.sqrt (1 + x ^ 2) := by linarith
    have hright : 0 ≤ -x + Real.sqrt (1 + x ^ 2) := by linarith
    nlinarith [mul_nonneg hleft hright]
  have hA' : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.log (asinhArg y))
      (1 / Real.sqrt (1 + x ^ 2)) x := by
    intro x
    have hsne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have hu : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      convert (hasDerivAt_const x (1 : ℝ)).add ((hasDerivAt_id x).pow 2) using 1 <;>
        simp [id] <;> ring
    have hsder : HasDerivAt (fun y : ℝ => Real.sqrt (1 + y ^ 2))
        (x / Real.sqrt (1 + x ^ 2)) x := by
      convert (Real.hasDerivAt_sqrt (by positivity : (1 + x ^ 2 : ℝ) ≠ 0)).comp x hu using 1 <;>
        simp [id] <;> field_simp [hsne] <;> ring
    have hargder : HasDerivAt asinhArg
        (1 + x / Real.sqrt (1 + x ^ 2)) x := by
      unfold asinhArg
      exact (hasDerivAt_id x).add hsder
    have hargne : asinhArg x ≠ 0 := ne_of_gt (harg_pos x)
    have hsumne : x + Real.sqrt (1 + x ^ 2) ≠ 0 := by
      simpa [asinhArg] using hargne
    convert (Real.hasDerivAt_log hargne).comp x hargder using 1 <;>
      simp [asinhArg, id] <;> field_simp [hsumne, hsne] <;> ring
  have hB' : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + x)) x := by
    filter_upwards [hnear_full] with x hxnear
    have hlin : HasDerivAt (fun y : ℝ => 1 + y) 1 x := by
      convert (hasDerivAt_const x (1 : ℝ)).add (hasDerivAt_id x) using 1 <;>
        simp [id] <;> ring
    convert (Real.hasDerivAt_log (by linarith : (1 + x : ℝ) ≠ 0)).comp x hlin using 1 <;>
      simp [id] <;> ring
  have hs : Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    convert (tendsto_const_nhds.add (hx.pow 2)).sqrt using 1 <;> norm_num
  have ha : Filter.Tendsto asinhArg
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa [asinhArg] using hx.add hs
  have hla : Filter.Tendsto (fun x : ℝ => Real.log (asinhArg x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert ha.log (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hbase : Filter.Tendsto (fun x : ℝ => 1 + x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    simpa using (tendsto_const_nhds.add hx :
      Filter.Tendsto (fun x : ℝ => 1 + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 + 0)))
  have hlb : Filter.Tendsto (fun x : ℝ => Real.log (1 + x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert hbase.log (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hslopeA : Filter.Tendsto (fun x : ℝ => Real.log (asinhArg x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have ht := (hA' 0).tendsto_slope_zero
    simpa [div_eq_inv_mul, asinhArg] using ht
  have hBder : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    have hlin : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := by
      convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id 0) using 1 <;>
        norm_num [id]
    have hlog : HasDerivAt Real.log (1 / (1 + 0)) (1 + 0) := by
      convert Real.hasDerivAt_log (x := (1 + 0 : ℝ)) (by norm_num) using 1 <;>
        norm_num
    convert hlog.comp 0 hlin using 1 <;> norm_num
  have hslopeB : Filter.Tendsto (fun x : ℝ => Real.log (1 + x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have ht := hBder.tendsto_slope_zero
    simpa [div_eq_inv_mul] using ht
  have hn_rhs : Filter.Tendsto
      (fun x : ℝ => x / (Real.sqrt (1 + x ^ 2) + 1) - 1)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1)) := by
    have hden : Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x ^ 2) + 1)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
      convert hs.add tendsto_const_nhds using 1 <;> norm_num
    convert (hx.div hden (by norm_num : (2 : ℝ) ≠ 0)).sub tendsto_const_nhds using 1 <;> norm_num
  have hn : Filter.Tendsto
      (fun x : ℝ => (Real.sqrt (1 + x ^ 2) - 1 - x) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1)) := by
    apply hn_rhs.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx0
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx0
    have hp : Real.sqrt (1 + x ^ 2) + 1 ≠ 0 := by positivity
    have hs2 : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt (by positivity)
    field_simp [hx0, hp] <;> nlinarith [hs2]
  have hd_rhs : Filter.Tendsto
      (fun x : ℝ =>
        Real.sqrt (1 + x ^ 2) * (Real.log (asinhArg x) / x) +
          (1 + x) * (Real.log (1 + x) / x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    convert (hs.mul hslopeA).add (hbase.mul hslopeB) using 1 <;> norm_num
  have hd : Filter.Tendsto
      (fun x : ℝ =>
        (Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) +
          (1 + x) * Real.log (1 + x)) / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    apply hd_rhs.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx0
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx0
    field_simp [hx0]
  have h3 : HasLimitAtZero f₃ (-1 / 2) := by
    unfold HasLimitAtZero
    have hq := hn.div hd (by norm_num : (2 : ℝ) ≠ 0)
    apply hq.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx0
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx0
    unfold f₃
    by_cases hD : Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) +
        (1 + x) * Real.log (1 + x) = 0
    · simp [hD]
    · change
        ((Real.sqrt (1 + x ^ 2) - 1 - x) / x) /
            ((Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) +
              (1 + x) * Real.log (1 + x)) / x) =
          (Real.sqrt (1 + x ^ 2) - 1 - x) /
            (Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) +
              (1 + x) * Real.log (1 + x))
      field_simp [hx0, hD] <;> ring
  have h2 : HasLimitAtZero f₂ (-1 / 2) := by
    unfold HasLimitAtZero at h3 ⊢
    apply h3.congr'
    filter_upwards [hnear] with x hxnear
    unfold f₂ f₃
    have hsne : Real.sqrt (1 + x ^ 2) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by positivity))
    have hx1 : 1 + x ≠ 0 := by linarith
    field_simp [hsne, hx1]
    ring
  have hN0 : Filter.Tendsto
      (fun x : ℝ => Real.log (1 + x) - Real.log (asinhArg x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert hlb.sub hla using 1 <;> norm_num
  have hD0 : Filter.Tendsto
      (fun x : ℝ => Real.log (1 + x) * Real.log (asinhArg x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert hlb.mul hla using 1 <;> norm_num
  have hN' : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt
        (fun y : ℝ => Real.log (1 + y) - Real.log (asinhArg y))
        (1 / (1 + x) - 1 / Real.sqrt (1 + x ^ 2)) x := by
    filter_upwards [hB'] with x hxder
    exact hxder.sub (hA' x)
  have hD' : ∀ᶠ x : ℝ in nhds 0,
      HasDerivAt
        (fun y : ℝ => Real.log (1 + y) * Real.log (asinhArg y))
        (1 / (1 + x) * Real.log (asinhArg x) +
          1 / Real.sqrt (1 + x ^ 2) * Real.log (1 + x)) x := by
    filter_upwards [hB'] with x hxder
    simpa [mul_comm, mul_left_comm, mul_assoc] using hxder.mul (hA' x)
  have hDne : ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
      1 / (1 + x) * Real.log (asinhArg x) +
        1 / Real.sqrt (1 + x ^ 2) * Real.log (1 + x) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin, hnear] with x hx0 hxnear
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx0
    have hs0 : 0 ≤ Real.sqrt (1 + x ^ 2) := Real.sqrt_nonneg _
    have hs2 : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hspos : 0 < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.2 (by positivity)
    rcases lt_or_gt_of_ne hx0 with hxneg | hxpos
    · have hslt : Real.sqrt (1 + x ^ 2) < 1 - x := by
        by_contra hn
        have hge : 1 - x ≤ Real.sqrt (1 + x ^ 2) := le_of_not_gt hn
        have hprod := mul_nonneg
          (sub_nonneg.mpr hge)
          (by linarith [hs0] : 0 ≤ Real.sqrt (1 + x ^ 2) + (1 - x))
        nlinarith
      have harglt : asinhArg x < 1 := by
        unfold asinhArg
        linarith
      have hla_neg : Real.log (asinhArg x) < 0 :=
        Real.log_neg (harg_pos x) harglt
      have hlb_neg : Real.log (1 + x) < 0 :=
        Real.log_neg (by linarith) (by linarith)
      have hc1 : 0 < 1 / (1 + x) := one_div_pos.2 (by linarith)
      have hc2 : 0 < 1 / Real.sqrt (1 + x ^ 2) := one_div_pos.2 hspos
      have ht1 : 1 / (1 + x) * Real.log (asinhArg x) < 0 :=
        mul_neg_of_pos_of_neg hc1 hla_neg
      have ht2 : 1 / Real.sqrt (1 + x ^ 2) * Real.log (1 + x) < 0 :=
        mul_neg_of_pos_of_neg hc2 hlb_neg
      linarith
    · have hsone : 1 < Real.sqrt (1 + x ^ 2) := by
        by_contra hn
        have hsle : Real.sqrt (1 + x ^ 2) ≤ 1 := le_of_not_gt hn
        have hprod := mul_nonneg
          (sub_nonneg.mpr hsle)
          (by linarith [hs0] : 0 ≤ 1 + Real.sqrt (1 + x ^ 2))
        nlinarith
      have harggt : 1 < asinhArg x := by
        unfold asinhArg
        linarith
      have hla_pos : 0 < Real.log (asinhArg x) := Real.log_pos harggt
      have hlb_pos : 0 < Real.log (1 + x) := Real.log_pos (by linarith)
      have hc1 : 0 < 1 / (1 + x) := one_div_pos.2 (by linarith)
      have hc2 : 0 < 1 / Real.sqrt (1 + x ^ 2) := one_div_pos.2 hspos
      have ht1 : 0 < 1 / (1 + x) * Real.log (asinhArg x) := mul_pos hc1 hla_pos
      have ht2 : 0 < 1 / Real.sqrt (1 + x ^ 2) * Real.log (1 + x) := mul_pos hc2 hlb_pos
      linarith
  have hquot : Filter.Tendsto
      (fun x : ℝ =>
        (1 / (1 + x) - 1 / Real.sqrt (1 + x ^ 2)) /
          (1 / (1 + x) * Real.log (asinhArg x) +
            1 / Real.sqrt (1 + x ^ 2) * Real.log (1 + x)))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1 / 2)) := by
    unfold HasLimitAtZero f₂ at h2
    exact h2
  have hright_le : nhdsWithin (0 : ℝ) (Set.Ioi 0) ≤
      nhdsWithin 0 ({0} : Set ℝ)ᶜ := by
    apply nhdsWithin_mono
    intro x hxpos
    simp only [Set.mem_Ioi] at hxpos
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hleft_le : nhdsWithin (0 : ℝ) (Set.Iio 0) ≤
      nhdsWithin 0 ({0} : Set ℝ)ᶜ := by
    apply nhdsWithin_mono
    intro x hxneg
    simp only [Set.mem_Iio] at hxneg
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have h1right : Filter.Tendsto
      (fun x : ℝ =>
        (Real.log (1 + x) - Real.log (asinhArg x)) /
          (Real.log (1 + x) * Real.log (asinhArg x)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-1 / 2)) := by
    exact HasDerivAt.lhopital_zero_nhdsGT
      (hN'.filter_mono inf_le_left)
      (hD'.filter_mono inf_le_left)
      (hDne.filter_mono hright_le)
      (hN0.mono_left hright_le)
      (hD0.mono_left hright_le)
      (hquot.mono_left hright_le)
  have h1left : Filter.Tendsto
      (fun x : ℝ =>
        (Real.log (1 + x) - Real.log (asinhArg x)) /
          (Real.log (1 + x) * Real.log (asinhArg x)))
      (nhdsWithin 0 (Set.Iio 0)) (nhds (-1 / 2)) := by
    exact HasDerivAt.lhopital_zero_nhdsLT
      (hN'.filter_mono inf_le_left)
      (hD'.filter_mono inf_le_left)
      (hDne.filter_mono hleft_le)
      (hN0.mono_left hleft_le)
      (hD0.mono_left hleft_le)
      (hquot.mono_left hleft_le)
  have hpunctured : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · intro hx0
      exact lt_or_gt_of_ne hx0
    · rintro (hxneg | hxpos)
      · linarith
      · linarith
  have h1 : HasLimitAtZero f₁ (-1 / 2) := by
    unfold HasLimitAtZero f₁
    rw [hpunctured, nhdsWithin_union]
    exact h1left.sup h1right
  have heq01 : f₀ =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ] f₁ := by
    filter_upwards [self_mem_nhdsWithin, hnear] with x hx0 hxnear
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx0
    unfold f₀ f₁
    have hs2 : (Real.sqrt (1 + x ^ 2)) ^ 2 = 1 + x ^ 2 :=
      Real.sq_sqrt (by positivity)
    have hargne : asinhArg x ≠ 1 := by
      intro he
      unfold asinhArg at he
      have hxzero : x = 0 := by nlinarith
      exact hx0 hxzero
    have hAne : Real.log (asinhArg x) ≠ 0 := by
      intro hz
      rw [Real.log_eq_zero] at hz
      rcases hz with hz | hz | hz
      · exact (ne_of_gt (harg_pos x)) hz
      · exact hargne hz
      · nlinarith [harg_pos x]
    have hbpos : 0 < 1 + x := by linarith
    have hBne : Real.log (1 + x) ≠ 0 := by
      intro hz
      rw [Real.log_eq_zero] at hz
      rcases hz with hz | hz | hz
      · exact (ne_of_gt hbpos) hz
      · apply hx0
        linarith
      · nlinarith
    field_simp [hAne, hBne]
  have h0 : HasLimitAtZero f₀ (-1 / 2) := by
    unfold HasLimitAtZero at h1 ⊢
    exact h1.congr' heq01.symm
  have hq4 : Filter.Tendsto (fun x : ℝ => x / Real.sqrt (1 + x ^ 2))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    convert hx.div hs (by norm_num : (1 : ℝ) ≠ 0) using 1 <;> norm_num
  have hn4 : Filter.Tendsto
      (fun x : ℝ => x / Real.sqrt (1 + x ^ 2) - 1)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (-1)) := by
    convert hq4.sub tendsto_const_nhds using 1 <;> norm_num
  have hd4 : Filter.Tendsto
      (fun x : ℝ =>
        1 + x / Real.sqrt (1 + x ^ 2) * Real.log (asinhArg x) +
          1 + Real.log (1 + x))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 2) := by
    convert (((tendsto_const_nhds.add (hq4.mul hla)).add tendsto_const_nhds).add hlb) using 1 <;> norm_num
  have h4 : HasLimitAtZero f₄ (-1 / 2) := by
    unfold HasLimitAtZero f₄
    convert hn4.div hd4 (by norm_num : (2 : ℝ) ≠ 0) using 1 <;> norm_num
  exact ⟨h0, h1, h2, h3, h4⟩

theorem gap1 : HasLimitAtZero f₀ (-1 / 2) ↔ HasLimitAtZero f₁ (-1 / 2) := by
  refine ⟨?_, ?_⟩
  · exact fun _ => established_limits.2.1
  · exact fun _ => established_limits.1
theorem gap2 : HasLimitAtZero f₀ (-1 / 2) ↔ HasLimitAtZero f₂ (-1 / 2) := by
  refine ⟨?_, ?_⟩
  · exact fun _ => established_limits.2.2.1
  · exact fun _ => established_limits.1
theorem gap3 : HasLimitAtZero f₀ (-1 / 2) ↔ HasLimitAtZero f₃ (-1 / 2) := by
  refine ⟨?_, ?_⟩
  · exact fun _ => established_limits.2.2.2.1
  · exact fun _ => established_limits.1
theorem gap4 : HasLimitAtZero f₀ (-1 / 2) ↔ HasLimitAtZero f₄ (-1 / 2) := by
  refine ⟨?_, ?_⟩
  · exact fun _ => established_limits.2.2.2.2
  · exact fun _ => established_limits.1
theorem gap5 : HasLimitAtZero f₄ (-1 / 2) := by
  exact established_limits.2.2.2.2
theorem gap6 : HasLimitAtZero f₀ (-1 / 2) := by
  exact established_limits.1

end

end ProofGap.Exercise1357
