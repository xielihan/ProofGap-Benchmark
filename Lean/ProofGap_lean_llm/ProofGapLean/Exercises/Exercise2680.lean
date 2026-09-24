import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.SummationFilter
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise2680

noncomputable section

open Filter

def sign (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n

def term (p : ℝ) (n : ℕ) : ℝ :=
  sign n / Real.rpow (n + sign n) p

def leadingTerm (p : ℝ) (n : ℕ) : ℝ :=
  sign n / Real.rpow n p

def correction (p : ℝ) (n : ℕ) : ℝ :=
  p / Real.rpow n (p + 1)

def remainder (p : ℝ) (n : ℕ) : ℝ :=
  term p n - (leadingTerm p n - correction p n)

def comparison (q : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n q

def ConditionallySummable (p : ℝ) : Prop :=
  ProofGap.SeriesConverges (fun n : ℕ => term p (n + 2)) ∧
    ¬ Summable (fun n : ℕ => |term p (n + 2)|)

private theorem factor_pos2680 (n : ℕ) (hn : 2 ≤ n) :
    0 < 1 + sign n / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have habs : |sign n / (n : ℝ)| = 1 / (n : ℝ) := by
    simp [sign, abs_div, abs_of_pos hnpos]
  have hhalf : 1 / (n : ℝ) ≤ (1 : ℝ) / 2 :=
    one_div_le_one_div_of_le (by norm_num) hn2
  have hlower := neg_abs_le (sign n / (n : ℝ))
  rw [habs] at hlower
  linarith

private theorem rpowLinearRemainder_isBigO2680 (p : ℝ) :
    Asymptotics.IsBigO (nhds 0)
      (fun u : ℝ => Real.rpow (1 + u) (-p) - (1 - p * u))
      (fun u : ℝ => u ^ 2) := by
  let s : Set ℝ := Set.Ioi (-1)
  let g : ℝ → ℝ := fun u => Real.rpow (1 + u) (-p) - (1 - p * u)
  have hfcont : ContDiffOn ℝ 2 (fun u : ℝ => Real.rpow (1 + u) (-p)) s := by
    apply (contDiffOn_const.add contDiffOn_id).rpow_const_of_ne
    intro u hu
    dsimp [s] at hu
    simp only [id_eq]
    change -1 < u at hu
    linarith
  have hgcont : ContDiffOn ℝ 2 g s := by
    simpa [g] using
      hfcont.sub (contDiffOn_const.sub (contDiffOn_const.mul contDiffOn_id))
  have hfderiv :
      HasDerivAt (fun u : ℝ => Real.rpow (1 + u) (-p)) (-p) 0 := by
    simpa [add_comm] using
      ((hasDerivAt_id 0).add_const 1).rpow_const (p := -p) (Or.inl (by norm_num))
  have hlinderiv : HasDerivAt (fun u : ℝ => 1 - p * u) (-p) 0 := by
    convert (hasDerivAt_const 0 1).sub
      ((hasDerivAt_const 0 p).mul (hasDerivAt_id 0)) using 1 <;> ring
  have hgderiv : HasDerivAt g 0 0 := by
    simpa [g] using hfderiv.sub hlinderiv
  have hg0 : g 0 = 0 := by simp [g]
  have hiter1 : iteratedDerivWithin 1 g s 0 = 0 := by
    rw [iteratedDerivWithin_one]
    exact hgderiv.hasDerivWithinAt.derivWithin
      ((uniqueDiffOn_Ioi (-1)) 0 (by simp [s]))
  have hsconv : Convex ℝ s := by simpa [s] using convex_Ioi (-1 : ℝ)
  have htaylor := taylor_isLittleO (s := s) (x₀ := (0 : ℝ))
    hsconv (by simp [s]) hgcont
  have hpoly : Asymptotics.IsBigO (nhdsWithin 0 s)
      (fun u : ℝ => taylorWithinEval g 2 s 0 u) (fun u : ℝ => u ^ 2) := by
    let c : ℝ := (2 : ℝ)⁻¹ * iteratedDerivWithin 2 g s 0
    have hc := (Asymptotics.isBigO_refl (fun u : ℝ => u ^ 2) (nhdsWithin 0 s)).const_mul_left c
    apply hc.congr_left
    intro u
    dsimp [c]
    norm_num [taylorWithinEval_succ, hg0, hiter1]
    ring
  have htaylor' : Asymptotics.IsBigO (nhdsWithin 0 s)
      (fun u : ℝ => g u - taylorWithinEval g 2 s 0 u) (fun u : ℝ => u ^ 2) := by
    simpa only [sub_zero] using htaylor.isBigO
  have hwithin : Asymptotics.IsBigO (nhdsWithin 0 s) g (fun u : ℝ => u ^ 2) := by
    simpa only [sub_add_cancel] using htaylor'.add hpoly
  rw [isOpen_Ioi.nhdsWithin_eq (by simp [s])] at hwithin
  simpa [g] using hwithin

theorem gap1 :
    ∀ p : ℝ, ∀ n : ℕ, 2 ≤ n →
      term p n =
        sign n /
          (Real.rpow n p * Real.rpow (1 + sign n / n) p) := by
  intro p n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have habs : |sign n| = 1 := by simp [sign]
  have hsge : (-1 : ℝ) ≤ sign n := by
    simpa [habs] using neg_abs_le (sign n)
  have hfactor : 0 ≤ 1 + sign n / (n : ℝ) := by
    have : (-1 : ℝ) / n ≤ sign n / n :=
      div_le_div_of_nonneg_right hsge hnpos.le
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have : (-1 : ℝ) ≤ sign n / n := by
      calc
        (-1 : ℝ) ≤ (-1 : ℝ) / n := by
          rw [le_div_iff₀ hnpos]
          nlinarith
        _ ≤ sign n / n := this
    linarith
  unfold term
  rw [show (n : ℝ) + sign n =
      (n : ℝ) * (1 + sign n / (n : ℝ)) by
        field_simp [hnpos.ne'] <;> ring]
  congr 1
  exact Real.mul_rpow hnpos.le hfactor

theorem gap2 :
    ∀ p : ℝ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ =>
          1 / Real.rpow (1 + sign (n + 2) / (n + 2 : ℝ)) p -
            (1 - p * sign (n + 2) / (n + 2 : ℝ)))
        (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2)) := by
  intro p
  let u : ℕ → ℝ := fun n => sign (n + 2) / ((n + 2 : ℕ) : ℝ)
  have hu : Tendsto u atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 2)
    convert h using 1
    funext n
    dsimp [u]
    rw [abs_div]
    simp only [sign, abs_pow, abs_neg, abs_one, one_pow]
    rw [abs_of_nonneg (by positivity)]
  have hcomp := (rpowLinearRemainder_isBigO2680 p).comp_tendsto hu
  apply hcomp.congr
  · intro n
    dsimp [u]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    have hpos : 0 ≤ 1 + sign (n + 2) / ((n : ℝ) + 2) := by
      simpa [Nat.cast_add] using (factor_pos2680 (n + 2) (by omega)).le
    have hrpow :
        (1 + sign (n + 2) / ((n : ℝ) + 2)) ^ (-p) =
          1 / (1 + sign (n + 2) / ((n : ℝ) + 2)) ^ p := by
      simpa [one_div] using
        (Real.rpow_neg hpos p)
    rw [hrpow]
    ring
  · intro n
    dsimp [u]
    rw [div_pow]
    have hs : sign (n + 2) ^ 2 = 1 := by
      calc
        sign (n + 2) ^ 2 = |sign (n + 2)| ^ 2 := (sq_abs _).symm
        _ = 1 := by simp [sign]
    rw [hs]
    norm_num [Nat.cast_add]

private theorem sign_sq2680 (n : ℕ) : sign n ^ 2 = 1 := by
  calc
    sign n ^ 2 = |sign n| ^ 2 := (sq_abs _).symm
    _ = 1 := by simp [sign]

private theorem leading_isBigO2680 (p : ℝ) :
    Asymptotics.IsBigO atTop
      (fun n : ℕ => leadingTerm p (n + 2))
      (fun n : ℕ => comparison p (n + 2)) := by
  refine Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall ?_)
  intro n
  unfold leadingTerm comparison
  simp only [norm_div, norm_one, one_mul]
  have hs : ‖sign (n + 2)‖ = 1 := by simp [sign, Real.norm_eq_abs]
  rw [hs]

private theorem seriesConvergesOfSummable2680 {f : ℕ → ℝ} (hf : Summable f) :
    ProofGap.SeriesConverges f := by
  rcases hf with ⟨s, hs⟩
  change Summable f (SummationFilter.conditional ℕ)
  refine ⟨s, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff, Function.comp_def]
  exact (Summable.hasSum_iff_tendsto_nat ⟨s, hs⟩).1 hs

private theorem signDiv_tendsto_zero2680 :
    Tendsto (fun n : ℕ => sign (n + 2) / (n + 2 : ℝ)) atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
    (tendsto_add_atTop_nat 2)
  convert h using 1
  funext n
  rw [Real.norm_eq_abs, abs_div]
  simp only [sign, abs_pow, abs_neg, abs_one, one_pow]
  rw [abs_of_nonneg (by positivity)]
  norm_num [Nat.cast_add]

theorem gap3 :
    ∀ p : ℝ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => remainder p (n + 2))
        (fun n : ℕ => comparison (p + 2) (n + 2)) := by
  intro p
  have hprod := (leading_isBigO2680 p).mul (gap2 p)
  apply hprod.congr
  · intro n
    unfold remainder leadingTerm correction
    rw [gap1 p (n + 2) (by omega)]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    have hNpos : 0 < (n : ℝ) + 2 := by positivity
    have hpow1 : Real.rpow ((n : ℝ) + 2) (p + 1) =
        Real.rpow ((n : ℝ) + 2) p * Real.rpow ((n : ℝ) + 2) 1 :=
      Real.rpow_add hNpos p 1
    have hpowOne : Real.rpow ((n : ℝ) + 2) 1 = (n : ℝ) + 2 :=
      Real.rpow_one _
    rw [hpow1, hpowOne]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring_nf
    rw [sign_sq2680]
    ring
  · intro n
    unfold comparison
    simp only [Nat.cast_add, Nat.cast_ofNat]
    have hNpos : 0 < (n : ℝ) + 2 := by positivity
    have hpow2 : Real.rpow ((n : ℝ) + 2) (p + 2) =
        Real.rpow ((n : ℝ) + 2) p * Real.rpow ((n : ℝ) + 2) 2 :=
      Real.rpow_add hNpos p 2
    have hpowTwo : Real.rpow ((n : ℝ) + 2) 2 = ((n : ℝ) + 2) ^ (2 : ℕ) :=
      Real.rpow_two _
    rw [hpow2, hpowTwo]
    simp only [one_div, mul_inv_rev]
    ring

theorem gap4 :
    ∀ p : ℝ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ =>
          term p (n + 2) -
            (leadingTerm p (n + 2) - correction p (n + 2)))
        (fun n : ℕ => comparison (p + 2) (n + 2)) := by
  intro p
  simpa [remainder] using gap3 p

theorem gap5 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      (ProofGap.SeriesConverges (fun n : ℕ => leadingTerm p (n + 2)) ∧
        ¬ Summable (fun n : ℕ => |leadingTerm p (n + 2)|)) := by
  intro p hp hp1
  constructor
  · let coeff : ℕ → ℝ := fun n => 1 / Real.rpow ((n + 2 : ℕ) : ℝ) p
    have hcoeffAnti : Antitone coeff := by
      intro i j hij
      have hiPos : 0 < (((i + 2 : ℕ) : ℝ)) := by positivity
      have hjPos : 0 < (((j + 2 : ℕ) : ℝ)) := by positivity
      have hijCast : (((i + 2 : ℕ) : ℝ)) ≤ (((j + 2 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.add_le_add_right hij 2
      have hiNeg : coeff i = Real.rpow ((i + 2 : ℕ) : ℝ) (-p) := by
        dsimp [coeff]
        simpa [one_div] using (Real.rpow_neg hiPos.le p).symm
      have hjNeg : coeff j = Real.rpow ((j + 2 : ℕ) : ℝ) (-p) := by
        dsimp [coeff]
        simpa [one_div] using (Real.rpow_neg hjPos.le p).symm
      rw [hiNeg, hjNeg]
      exact Real.rpow_le_rpow_of_nonpos hiPos hijCast (by linarith)
    have hcoeffZero : Tendsto coeff atTop (nhds 0) := by
      have hbase : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
      have hneg := (tendsto_rpow_neg_atTop hp).comp hbase
      apply hneg.congr'
      filter_upwards with n
      have hnPos : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
      dsimp [coeff]
      simpa [one_div] using (Real.rpow_neg hnPos.le p)
    rcases hcoeffAnti.tendsto_alternating_series_of_tendsto_zero hcoeffZero with
      ⟨L, hL⟩
    change Summable (fun n : ℕ => leadingTerm p (n + 2))
      (SummationFilter.conditional ℕ)
    refine ⟨L, ?_⟩
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff, Function.comp_def]
    simpa [leadingTerm, sign, coeff, pow_add, Nat.cast_add] using hL
  · intro habs
    have hshift : Summable (fun n : ℕ =>
        1 / Real.rpow ((n + 2 : ℕ) : ℝ) p) := by
      refine habs.congr ?_
      intro n
      unfold leadingTerm
      change |sign (n + 2) / Real.rpow ((n + 2 : ℕ) : ℝ) p| =
        1 / Real.rpow ((n + 2 : ℕ) : ℝ) p
      rw [abs_div]
      have hsabs : |sign (n + 2)| = 1 := by simp [sign]
      have habsden : |Real.rpow ((n + 2 : ℕ) : ℝ) p| =
          Real.rpow ((n + 2 : ℕ) : ℝ) p :=
        abs_of_nonneg (Real.rpow_nonneg (by positivity) p)
      rw [hsabs, habsden]
    have hfull : Summable (fun n : ℕ => 1 / Real.rpow n p) :=
      (summable_nat_add_iff 2).1 (by simpa using hshift)
    have hgt := Real.summable_one_div_nat_rpow.mp hfull
    linarith

theorem gap6 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      Summable (fun n : ℕ => correction p (n + 2)) := by
  intro p hp _
  have hs : Summable (fun n : ℕ => 1 / Real.rpow n (p + 1)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hshift := (summable_nat_add_iff 2).mpr hs
  simpa [correction, div_eq_mul_inv] using hshift.mul_left p

theorem gap7 :
    ∀ p : ℝ, 0 < p → p ≤ 1 →
      Summable (fun n : ℕ => comparison (p + 2) (n + 2)) := by
  intro p hp _
  have hs : Summable (fun n : ℕ => 1 / Real.rpow n (p + 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  simpa [comparison] using (summable_nat_add_iff 2).mpr hs

theorem gap8 :
    ∀ p : ℝ, 0 < p → p ≤ 1 → ConditionallySummable p := by
  intro p hp hp1
  have hlead := (gap5 p hp hp1).1
  have hcorr := gap6 p hp hp1
  have hrem : Summable (fun n : ℕ => remainder p (n + 2)) :=
    summable_of_isBigO_nat (gap7 p hp hp1) (gap3 p)
  constructor
  · have hcorrConv : ProofGap.SeriesConverges
        (fun n : ℕ => correction p (n + 2)) :=
      seriesConvergesOfSummable2680 hcorr
    have hremConv : ProofGap.SeriesConverges
        (fun n : ℕ => remainder p (n + 2)) :=
      seriesConvergesOfSummable2680 hrem
    change Summable (fun n : ℕ => term p (n + 2))
      (SummationFilter.conditional ℕ)
    change Summable (fun n : ℕ => leadingTerm p (n + 2))
      (SummationFilter.conditional ℕ) at hlead
    change Summable (fun n : ℕ => correction p (n + 2))
      (SummationFilter.conditional ℕ) at hcorrConv
    change Summable (fun n : ℕ => remainder p (n + 2))
      (SummationFilter.conditional ℕ) at hremConv
    refine ((hlead.sub hcorrConv).add hremConv).congr ?_
    intro n
    unfold remainder
    ring
  · intro habs
    have hterm : Summable (fun n : ℕ => term p (n + 2)) := habs.of_abs
    have hleadStd : Summable (fun n : ℕ => leadingTerm p (n + 2)) := by
      refine ((hterm.add hcorr).sub hrem).congr ?_
      intro n
      unfold remainder
      ring
    have hleadAbs : Summable (fun n : ℕ => |leadingTerm p (n + 2)|) := by
      exact hleadStd.abs
    exact (gap5 p hp hp1).2 hleadAbs

theorem gap9 :
    ∀ p : ℝ, 1 < p →
      Asymptotics.IsBigO atTop
        (fun n : ℕ => term p (n + 2))
        (fun n : ℕ => comparison p (n + 2)) := by
  intro p hp
  have hu := signDiv_tendsto_zero2680
  have hsqT : Tendsto (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2))
      atTop (nhds 0) := by
    have heq : (fun n : ℕ => 1 / ((n + 2 : ℝ) ^ 2)) =
        (fun n : ℕ => (sign (n + 2) / (n + 2 : ℝ)) ^ 2) := by
      funext n
      rw [div_pow, sign_sq2680]
    rw [heq]
    simpa using hu.pow 2
  have herror := (gap2 p).trans (hsqT.isBigO_one ℝ)
  have hlinearT : Tendsto
      (fun n : ℕ => 1 - p * sign (n + 2) / (n + 2 : ℝ))
      atTop (nhds 1) := by
    have hpT : Tendsto
        (fun n : ℕ => p * (sign (n + 2) / (n + 2 : ℝ)))
        atTop (nhds 0) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => p) atTop (nhds p)).mul hu)
    simpa only [sub_zero, mul_div_assoc] using tendsto_const_nhds.sub hpT
  have hrecip : Asymptotics.IsBigO atTop
      (fun n : ℕ => 1 / Real.rpow (1 + sign (n + 2) / (n + 2 : ℝ)) p)
      (fun _ : ℕ => (1 : ℝ)) := by
    have hsum := herror.add (hlinearT.isBigO_one ℝ)
    apply hsum.congr_left
    intro n
    ring
  have hprod := (leading_isBigO2680 p).mul hrecip
  apply hprod.congr
  · intro n
    rw [gap1 p (n + 2) (by omega)]
    unfold leadingTerm
    simp only [Nat.cast_add, Nat.cast_ofNat, div_eq_mul_inv, mul_inv_rev]
    ring
  · intro n
    simp [comparison]

theorem gap10 :
    ∀ p : ℝ, 1 < p →
      Summable (fun n : ℕ => |term p (n + 2)|) := by
  intro p hp
  have hs : Summable (fun n : ℕ => 1 / Real.rpow n p) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hcomp : Summable (fun n : ℕ => comparison p (n + 2)) := by
    simpa [comparison] using (summable_nat_add_iff 2).mpr hs
  have hnorm : Summable (fun n : ℕ => ‖term p (n + 2)‖) :=
    summable_of_isBigO_nat hcomp (gap9 p hp).norm_left
  simpa [Real.norm_eq_abs] using hnorm

theorem gap11 :
    ∀ p : ℝ, p ≤ 0 →
      ¬ Tendsto (fun n : ℕ => term p (n + 2)) atTop (nhds 0) := by
  intro p hp hlim
  have habs : Tendsto (fun n : ℕ => |term p (n + 2)|) atTop (nhds 0) := by
    simpa using hlim.abs
  have hsmall : ∀ᶠ n : ℕ in atTop, |term p (n + 2)| < 1 :=
    habs.eventually (Iio_mem_nhds (by norm_num))
  rcases eventually_atTop.1 hsmall with ⟨N, hN⟩
  have hlarge : 1 ≤ |term p (N + 2)| := by
    have hsabs : |sign (N + 2)| = 1 := by simp [sign]
    have hsge := neg_abs_le (sign (N + 2))
    rw [hsabs] at hsge
    have hcast : (2 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) := by norm_num
    have hbase : 1 ≤ ((N + 2 : ℕ) : ℝ) + sign (N + 2) := by linarith
    have hbasePos : 0 < ((N + 2 : ℕ) : ℝ) + sign (N + 2) :=
      lt_of_lt_of_le zero_lt_one hbase
    have hpowPos := Real.rpow_pos_of_pos hbasePos p
    have hpowLe := Real.rpow_le_one_of_one_le_of_nonpos hbase hp
    unfold term
    rw [abs_div, hsabs]
    have habspow :
        |Real.rpow (((N + 2 : ℕ) : ℝ) + sign (N + 2)) p| =
          Real.rpow (((N + 2 : ℕ) : ℝ) + sign (N + 2)) p :=
      abs_of_pos hpowPos
    rw [habspow]
    exact one_le_one_div hpowPos hpowLe
  linarith [hN N le_rfl]

theorem gap12 :
    ∀ p : ℝ, p ≤ 0 →
      ¬ Summable (fun n : ℕ => term p (n + 2)) := by
  intro p hp hs
  apply gap11 p hp
  simpa [Nat.cofinite_eq_atTop] using hs.tendsto_cofinite_zero

end

end ProofGap.Exercise2680
