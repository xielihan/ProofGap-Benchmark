import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

namespace ProofGap.Exercise2687

noncomputable section

open Filter
open scoped BigOperators

def block (l : ℕ) : Finset ℕ :=
  Finset.Ico (l ^ 2) ((l + 1) ^ 2)

def term (p : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ Nat.sqrt n / Real.rpow n p

def blockTerm (p : ℝ) (l : ℕ) : ℝ :=
  ∑ n ∈ block l, term p n

def amplitude (p : ℝ) (l : ℕ) : ℝ :=
  ∑ n ∈ block l, 1 / Real.rpow n p

def originalPartialSum (p : ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, term p n

def blockPartialSum (p : ℝ) (M : ℕ) : ℝ :=
  ∑ l ∈ Finset.Icc 1 M, blockTerm p l

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧ ¬ Summable (fun n => |f n|)

private theorem rpow_neg_sub_lower {p x y : ℝ}
    (hp : 0 < p) (hx : 0 < x) (hxy : x < y) :
    p * (y - x) * Real.rpow y (-p - 1) ≤
      Real.rpow x (-p) - Real.rpow y (-p) := by
  have hcont :
      ContinuousOn (fun z : ℝ => Real.rpow z (-p)) (Set.Icc x y) := by
    intro z hz
    exact
      (Real.hasDerivAt_rpow_const
        (p := -p) (Or.inl (ne_of_gt (hx.trans_le hz.1)))).continuousAt.continuousWithinAt
  have hderiv :
      ∀ z ∈ Set.Ioo x y,
        HasDerivAt (fun w : ℝ => Real.rpow w (-p))
          ((-p) * Real.rpow z (-p - 1)) z := by
    intro z hz
    exact Real.hasDerivAt_rpow_const
      (p := -p) (Or.inl (ne_of_gt (hx.trans hz.1)))
  obtain ⟨c, hc, hcEq⟩ :=
    exists_hasDerivAt_eq_slope
      (f := fun z : ℝ => Real.rpow z (-p))
      (f' := fun z : ℝ => (-p) * Real.rpow z (-p - 1))
      hxy hcont hderiv
  have hdiff : 0 < y - x := sub_pos.mpr hxy
  have hcMul :
      ((-p) * Real.rpow c (-p - 1)) * (y - x) =
        Real.rpow y (-p) - Real.rpow x (-p) :=
    (eq_div_iff hdiff.ne').mp hcEq
  have hformula :
      Real.rpow x (-p) - Real.rpow y (-p) =
        p * (y - x) * Real.rpow c (-p - 1) := by
    calc
      Real.rpow x (-p) - Real.rpow y (-p) =
          -(Real.rpow y (-p) - Real.rpow x (-p)) := by ring
      _ = -(((-p) * Real.rpow c (-p - 1)) * (y - x)) := by
        rw [hcMul]
      _ = p * (y - x) * Real.rpow c (-p - 1) := by ring
  have hc0 : 0 < c := hx.trans hc.1
  have hrpow :
      Real.rpow y (-p - 1) ≤ Real.rpow c (-p - 1) :=
    Real.rpow_le_rpow_of_nonpos hc0 hc.2.le (by linarith)
  calc
    p * (y - x) * Real.rpow y (-p - 1) ≤
        p * (y - x) * Real.rpow c (-p - 1) :=
      mul_le_mul_of_nonneg_left hrpow
        (mul_nonneg hp.le hdiff.le)
    _ = Real.rpow x (-p) - Real.rpow y (-p) := hformula.symm

private theorem seriesConverges_tendsto_zero {f : ℕ → ℝ}
    (hf : ProofGap.SeriesConverges f) :
    Tendsto f atTop (nhds 0) := by
  rcases hf with ⟨s, hs⟩
  have hsum :
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (nhds s) := by
    unfold HasSum at hs
    rw [SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff] at hs
    simpa [Function.comp_def] using hs
  have hsumSucc := hsum.comp (tendsto_add_atTop_nat 1)
  have hdiff := hsumSucc.sub hsum
  simpa [Finset.sum_range_succ] using hdiff

private theorem seriesConverges_of_nat_add {f : ℕ → ℝ} (k : ℕ)
    (hf : ProofGap.SeriesConverges (fun n : ℕ => f (n + k))) :
    ProofGap.SeriesConverges f := by
  rcases hf with ⟨s, hs⟩
  have htail :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range n, f (i + k))
        atTop (nhds s) := by
    unfold HasSum at hs
    rw [SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff] at hs
    simpa [Function.comp_def] using hs
  have hconst :
      Tendsto (fun _ : ℕ => ∑ i ∈ Finset.range k, f i)
        atTop (nhds (∑ i ∈ Finset.range k, f i)) :=
    tendsto_const_nhds
  have hadd := hconst.add htail
  have hshift :
      Tendsto
        (fun n : ℕ => ∑ i ∈ Finset.range (n + k), f i)
        atTop
        (nhds ((∑ i ∈ Finset.range k, f i) + s)) := by
    convert hadd using 1
    funext n
    rw [add_comm n k, Finset.sum_range_add]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [add_comm]
  have hfull :
      Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i)
        atTop
        (nhds ((∑ i ∈ Finset.range k, f i) + s)) := by
    apply (tendsto_add_atTop_iff_nat k).mp
    simpa using hshift
  refine ⟨(∑ i ∈ Finset.range k, f i) + s, ?_⟩
  unfold HasSum
  rw [SummationFilter.conditional_filter_eq_map_range,
    Filter.tendsto_map'_iff]
  simpa [Function.comp_def] using hfull

theorem gap1 :
    ∀ l n : ℕ, n ∈ block l → l ^ 2 ≤ n ∧ n < (l + 1) ^ 2 := by
  intro l n hn
  simpa [block] using hn

theorem gap2 :
    ∀ l : ℕ, (block l).card = 2 * l + 1 := by
  intro l
  simp [block, pow_two, Nat.add_mul, Nat.mul_add]
  omega

theorem gap3 (p : ℝ) :
    ∀ l : ℕ, blockTerm p l =
      ∑ n ∈ block l, (-1 : ℝ) ^ l / Real.rpow n p := by
  intro l
  unfold blockTerm
  apply Finset.sum_congr rfl
  intro n hn
  have hsqrt : Nat.sqrt n = l :=
    ((Nat.eq_sqrt').2 (gap1 l n hn)).symm
  simp only [term, hsqrt]

theorem gap4 (p : ℝ) :
    ∀ l : ℕ,
      (∑ n ∈ block l, (-1 : ℝ) ^ l / Real.rpow n p) =
        (-1 : ℝ) ^ l * amplitude p l := by
  intro l
  simp [amplitude, div_eq_mul_inv, Finset.mul_sum]

theorem gap5 (p : ℝ) :
    ∀ l : ℕ, blockTerm p l = (-1 : ℝ) ^ l * amplitude p l := by
  intro l
  rw [gap3 p l, gap4 p l]

theorem gap6 (p : ℝ) (hp : 1 / 2 < p) :
    ∀ l : ℕ, 1 ≤ l →
      amplitude p l - amplitude p (l + 1) ≥
        p * Real.rpow l (2 * p - 1) * (2 * (l : ℝ) + 1) ^ 2 /
            Real.rpow ((l : ℝ) ^ 2 + 4 * l + 1) (2 * p + 1 / 2) -
          2 / Real.rpow ((l : ℝ) ^ 2 + 4 * l + 2) p := by
  intro l hl
  let a : ℕ := l ^ 2
  let d : ℕ := 2 * l + 1
  let f : ℕ → ℝ := fun n => 1 / Real.rpow n p
  let XN : ℕ := a + 2 * d - 1
  let YN : ℕ := a + 2 * d
  have hp0 : 0 < p := by linarith
  have hd0 : 0 < d := by dsimp [d]; omega
  have hXN : XN = l ^ 2 + 4 * l + 1 := by
    dsimp [XN, a, d]
    omega
  have hYN : YN = l ^ 2 + 4 * l + 2 := by
    dsimp [YN, a, d]
    omega
  have hAl :
      amplitude p l = ∑ k ∈ Finset.range d, f (a + k) := by
    unfold amplitude block
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen0 : (l + 1) ^ 2 - l ^ 2 = d := by
      dsimp [d]
      simp [pow_two, Nat.add_mul, Nat.mul_add]
      omega
    rw [hlen0]
  have hAnext :
      amplitude p (l + 1) =
        (∑ k ∈ Finset.range d, f (a + d + k)) +
          f (a + 2 * d) + f (a + 2 * d + 1) := by
    unfold amplitude block
    rw [Finset.sum_Ico_eq_sum_range]
    have hlen :
        (l + 1 + 1) ^ 2 - (l + 1) ^ 2 = d + 2 := by
      dsimp [d]
      simp [pow_two, Nat.add_mul, Nat.mul_add]
      omega
    have hstart : (l + 1) ^ 2 = a + d := by
      dsimp [a, d]
      simp [pow_two, Nat.add_mul, Nat.mul_add]
      omega
    rw [hlen, Finset.sum_range_add]
    rw [hstart]
    change
      (∑ x ∈ Finset.range d, f (a + d + x)) +
          (∑ x ∈ Finset.range 2, f (a + d + (d + x))) =
        (∑ x ∈ Finset.range d, f (a + d + x)) +
          f (a + 2 * d) + f (a + 2 * d + 1)
    simp [Finset.sum_range_succ]
    have h0 : a + d + d = a + 2 * d := by omega
    have h1 : a + d + (d + 1) = a + 2 * d + 1 := by omega
    rw [h0, h1]
    ring
  have hpair :
      ∀ k ∈ Finset.range d,
        p * (d : ℝ) * Real.rpow (XN : ℝ) (-p - 1) ≤
          f (a + k) - f (a + d + k) := by
    intro k hk
    have hklt : k < d := Finset.mem_range.mp hk
    have hxNat : 0 < a + k := by
      dsimp [a]
      have hl0 : 0 < l := by omega
      exact Nat.add_pos_left (pow_pos hl0 2) k
    have hxyNat : a + k < a + d + k := by omega
    have hyXNat : a + d + k ≤ XN := by
      dsimp [XN]
      omega
    have hx : 0 < ((a + k : ℕ) : ℝ) := by exact_mod_cast hxNat
    have hxy :
        ((a + k : ℕ) : ℝ) < ((a + d + k : ℕ) : ℝ) := by
      exact_mod_cast hxyNat
    have hy0 : 0 < ((a + d + k : ℕ) : ℝ) := hx.trans hxy
    have hyX :
        ((a + d + k : ℕ) : ℝ) ≤ (XN : ℝ) := by
      exact_mod_cast hyXNat
    have hmv :=
      rpow_neg_sub_lower hp0 hx hxy
    have hmono :
        Real.rpow (XN : ℝ) (-p - 1) ≤
          Real.rpow ((a + d + k : ℕ) : ℝ) (-p - 1) :=
      Real.rpow_le_rpow_of_nonpos hy0 hyX (by linarith)
    have hconst :
        p * (d : ℝ) * Real.rpow (XN : ℝ) (-p - 1) ≤
          p * (((a + d + k : ℕ) : ℝ) - ((a + k : ℕ) : ℝ)) *
            Real.rpow ((a + d + k : ℕ) : ℝ) (-p - 1) := by
      have hdiff :
          (((a + d + k : ℕ) : ℝ) - ((a + k : ℕ) : ℝ)) =
            (d : ℝ) := by
        norm_num
      rw [hdiff]
      exact mul_le_mul_of_nonneg_left hmono
        (mul_nonneg hp0.le (Nat.cast_nonneg d))
    calc
      p * (d : ℝ) * Real.rpow (XN : ℝ) (-p - 1) ≤
          p * (((a + d + k : ℕ) : ℝ) - ((a + k : ℕ) : ℝ)) *
            Real.rpow ((a + d + k : ℕ) : ℝ) (-p - 1) := hconst
      _ ≤ Real.rpow ((a + k : ℕ) : ℝ) (-p) -
          Real.rpow ((a + d + k : ℕ) : ℝ) (-p) := hmv
      _ = f (a + k) - f (a + d + k) := by
        dsimp [f]
        rw [Real.rpow_neg hx.le p,
          Real.rpow_neg hy0.le p]
        simp only [one_div]
  have hpairSum :
      p * (d : ℝ) ^ 2 * Real.rpow (XN : ℝ) (-p - 1) ≤
        ∑ k ∈ Finset.range d, (f (a + k) - f (a + d + k)) := by
    calc
      p * (d : ℝ) ^ 2 * Real.rpow (XN : ℝ) (-p - 1) =
          ∑ k ∈ Finset.range d,
            p * (d : ℝ) * Real.rpow (XN : ℝ) (-p - 1) := by
        simp
        ring
      _ ≤ ∑ k ∈ Finset.range d,
          (f (a + k) - f (a + d + k)) :=
        Finset.sum_le_sum fun k hk => hpair k hk
  have hYN0 : 0 < YN := by
    dsimp [YN, a, d]
    omega
  have hextra :
      f YN + f (YN + 1) ≤
        2 / Real.rpow (YN : ℝ) p := by
    have hbase : (YN : ℝ) ≤ ((YN + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_succ YN
    have hpow :
        Real.rpow (YN : ℝ) p ≤
          Real.rpow ((YN + 1 : ℕ) : ℝ) p :=
      Real.rpow_le_rpow (by positivity) hbase hp0.le
    have hterm :
        f (YN + 1) ≤ f YN := by
      dsimp [f]
      exact one_div_le_one_div_of_le
        (Real.rpow_pos_of_pos (by positivity) p) hpow
    calc
      f YN + f (YN + 1) ≤ f YN + f YN :=
        by simpa [add_comm] using add_le_add_left hterm (f YN)
      _ = 2 / Real.rpow (YN : ℝ) p := by
        dsimp [f]
        ring
  have hsimple :
      p * (d : ℝ) ^ 2 * Real.rpow (XN : ℝ) (-p - 1) -
          2 / Real.rpow (YN : ℝ) p ≤
        amplitude p l - amplitude p (l + 1) := by
    rw [hAl, hAnext]
    have hh := sub_le_sub hpairSum hextra
    rw [Finset.sum_sub_distrib] at hh
    dsimp [YN] at hh ⊢
    linarith
  have hX0 : 0 < (XN : ℝ) := by
    have hX0Nat : 0 < XN := by
      rw [hXN]
      have hl0 : 0 < l := by omega
      have : 0 < l ^ 2 := pow_pos hl0 2
      omega
    exact_mod_cast hX0Nat
  have hq : 0 < p - 1 / 2 := by linarith
  have hbaseLX :
      (l : ℝ) ^ 2 ≤ (XN : ℝ) := by
    exact_mod_cast (by
      rw [hXN]
      omega : l ^ 2 ≤ XN)
  have hLpow :
      Real.rpow (l : ℝ) (2 * p - 1) ≤
        Real.rpow (XN : ℝ) (p - 1 / 2) := by
    have hbasepow :
        Real.rpow ((l : ℝ) ^ 2) (p - 1 / 2) ≤
          Real.rpow (XN : ℝ) (p - 1 / 2) :=
      Real.rpow_le_rpow (sq_nonneg (l : ℝ)) hbaseLX hq.le
    calc
      Real.rpow (l : ℝ) (2 * p - 1) =
          Real.rpow (l : ℝ) (2 * (p - 1 / 2)) := by
        congr 1
        ring
      _ =
          Real.rpow ((l : ℝ) ^ 2) (p - 1 / 2) := by
        exact
          (Real.rpow_natCast_mul
            (x := (l : ℝ)) (by positivity) 2 (p - 1 / 2))
      _ ≤ Real.rpow (XN : ℝ) (p - 1 / 2) := hbasepow
  have hprod :
      Real.rpow (XN : ℝ) (2 * p + 1 / 2) *
          Real.rpow (XN : ℝ) (-p - 1) =
        Real.rpow (XN : ℝ) (p - 1 / 2) := by
    calc
      Real.rpow (XN : ℝ) (2 * p + 1 / 2) *
          Real.rpow (XN : ℝ) (-p - 1) =
          Real.rpow (XN : ℝ)
            ((2 * p + 1 / 2) + (-p - 1)) :=
        (Real.rpow_add hX0 (2 * p + 1 / 2) (-p - 1)).symm
      _ = Real.rpow (XN : ℝ) (p - 1 / 2) := by
        congr 1
        ring
  have hdenpos :
      0 < Real.rpow (XN : ℝ) (2 * p + 1 / 2) :=
    Real.rpow_pos_of_pos hX0 _
  have hfrac :
      Real.rpow (l : ℝ) (2 * p - 1) /
          Real.rpow (XN : ℝ) (2 * p + 1 / 2) ≤
        Real.rpow (XN : ℝ) (-p - 1) := by
    apply (div_le_iff₀ hdenpos).2
    calc
      Real.rpow (l : ℝ) (2 * p - 1) ≤
          Real.rpow (XN : ℝ) (p - 1 / 2) := hLpow
      _ = Real.rpow (XN : ℝ) (2 * p + 1 / 2) *
          Real.rpow (XN : ℝ) (-p - 1) := hprod.symm
      _ = Real.rpow (XN : ℝ) (-p - 1) *
          Real.rpow (XN : ℝ) (2 * p + 1 / 2) := by
        ring
  have hmain :
      p * Real.rpow (l : ℝ) (2 * p - 1) * (d : ℝ) ^ 2 /
          Real.rpow (XN : ℝ) (2 * p + 1 / 2) ≤
        p * (d : ℝ) ^ 2 * Real.rpow (XN : ℝ) (-p - 1) := by
    have hmul :=
      mul_le_mul_of_nonneg_left hfrac
        (mul_nonneg hp0.le (sq_nonneg (d : ℝ)))
    calc
      p * Real.rpow (l : ℝ) (2 * p - 1) * (d : ℝ) ^ 2 /
          Real.rpow (XN : ℝ) (2 * p + 1 / 2) =
          (p * (d : ℝ) ^ 2) *
            (Real.rpow (l : ℝ) (2 * p - 1) /
              Real.rpow (XN : ℝ) (2 * p + 1 / 2)) := by ring
      _ ≤ (p * (d : ℝ) ^ 2) *
          Real.rpow (XN : ℝ) (-p - 1) := hmul
      _ = p * (d : ℝ) ^ 2 *
          Real.rpow (XN : ℝ) (-p - 1) := by ring
  rw [hXN] at hmain
  rw [hXN, hYN] at hsimple
  dsimp [d] at hmain hsimple
  norm_num at hmain hsimple ⊢
  linarith

theorem gap7 (p : ℝ) (hp : 1 / 2 < p) :
    Tendsto
      (fun l : ℕ =>
        Real.rpow ((l : ℝ) ^ 2 + 4 * l + 1) (p + 1 / 2) /
          (Real.rpow l (2 * p - 1) * ((l : ℝ) ^ 2 + l + 1 / 4)))
      atTop (nhds 1) := by
  let u : ℕ → ℝ := fun l =>
    (((l : ℝ) ^ 2 + 4 * l + 1) / (l : ℝ) ^ 2)
  let v : ℕ → ℝ := fun l =>
    (((l : ℝ) ^ 2 + l + 1 / 4) / (l : ℝ) ^ 2)
  have hinv :
      Tendsto (fun l : ℕ => ((l : ℝ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have huNorm :
      Tendsto
        (fun l : ℕ =>
          1 + 4 * ((l : ℝ)⁻¹) + (l : ℝ)⁻¹ * (l : ℝ)⁻¹)
        atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)).add
        (hinv.mul hinv))
  have hvNorm :
      Tendsto
        (fun l : ℕ =>
          1 + (l : ℝ)⁻¹ + (1 / 4) * ((l : ℝ)⁻¹ * (l : ℝ)⁻¹))
        atTop (nhds 1) := by
    simpa using
      ((tendsto_const_nhds.add hinv).add
        (tendsto_const_nhds.mul (hinv.mul hinv)))
  have hu : Tendsto u atTop (nhds 1) := by
    apply huNorm.congr'
    filter_upwards [eventually_ge_atTop 1] with l hl
    dsimp [u]
    have hl0 : (l : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : l ≠ 0)
    field_simp [hl0]
  have hv : Tendsto v atTop (nhds 1) := by
    apply hvNorm.congr'
    filter_upwards [eventually_ge_atTop 1] with l hl
    dsimp [v]
    have hl0 : (l : ℝ) ≠ 0 := by
      exact_mod_cast (by omega : l ≠ 0)
    field_simp [hl0]
  have huPow :
      Tendsto (fun l => Real.rpow (u l) (p + 1 / 2))
        atTop (nhds 1) := by
    have hc :=
      (Real.continuousAt_rpow_const 1 (p + 1 / 2)
        (Or.inl one_ne_zero)).tendsto.comp hu
    simpa using hc
  have hnormalized :
      Tendsto
        (fun l => Real.rpow (u l) (p + 1 / 2) / v l)
        atTop (nhds 1) := by
    simpa using huPow.div hv (by norm_num)
  apply hnormalized.congr'
  filter_upwards [eventually_ge_atTop 1] with l hl
  have hx : 0 < (l : ℝ) := by exact_mod_cast hl
  have hX : 0 < (l : ℝ) ^ 2 + 4 * l + 1 := by positivity
  have hB : 0 < (l : ℝ) ^ 2 + l + 1 / 4 := by positivity
  have hpow :
      Real.rpow ((l : ℝ) ^ 2) (p + 1 / 2) =
        Real.rpow (l : ℝ) (2 * p - 1) * (l : ℝ) ^ 2 := by
    calc
      Real.rpow ((l : ℝ) ^ 2) (p + 1 / 2) =
          Real.rpow (l : ℝ) (2 * (p + 1 / 2)) := by
        exact
          (Real.rpow_natCast_mul
            (x := (l : ℝ)) hx.le 2 (p + 1 / 2)).symm
      _ = Real.rpow (l : ℝ) ((2 * p - 1) + 2) := by
        congr 1
        ring
      _ = Real.rpow (l : ℝ) (2 * p - 1) *
          Real.rpow (l : ℝ) 2 := by
        exact Real.rpow_add hx (2 * p - 1) 2
      _ = Real.rpow (l : ℝ) (2 * p - 1) * (l : ℝ) ^ 2 := by
        congr 1
        exact Real.rpow_two (l : ℝ)
  dsimp [u, v]
  rw [Real.div_rpow hX.le (sq_nonneg (l : ℝ)) (p + 1 / 2)]
  field_simp [hx.ne', hX.ne', hB.ne',
    (Real.rpow_pos_of_pos hx (2 * p - 1)).ne']
  calc
    (l : ℝ) ^ 2 * Real.rpow (l : ℝ) (p * 2 - 1) =
        Real.rpow (l : ℝ) (2 * p - 1) * (l : ℝ) ^ 2 := by
      ring
    _ = Real.rpow ((l : ℝ) ^ 2) (p + 1 / 2) := hpow.symm
    _ = Real.rpow ((l : ℝ) ^ 2) ((p * 2 + 1) / 2) := by
      congr 1
      ring

theorem gap8 (p : ℝ) (hp : 1 / 2 < p) :
    ∃ L : ℕ, ∀ l ≥ L, amplitude p (l + 1) < amplitude p l := by
  have hp0 : 0 < p := by linarith
  have hp2 : 1 < 2 * p := by linarith
  have hR :
      ∀ᶠ l : ℕ in atTop,
        Real.rpow ((l : ℝ) ^ 2 + 4 * l + 1) (p + 1 / 2) /
            (Real.rpow l (2 * p - 1) *
              ((l : ℝ) ^ 2 + l + 1 / 4)) <
          2 * p :=
    (tendsto_order.1 (gap7 p hp)).2 (2 * p) hp2
  rcases (eventually_atTop.1 hR) with ⟨L, hL⟩
  refine ⟨max L 1, ?_⟩
  intro l hl
  have hlL : L ≤ l := le_trans (le_max_left L 1) hl
  have hl1 : 1 ≤ l := le_trans (le_max_right L 1) hl
  have hx : 0 < (l : ℝ) := by exact_mod_cast hl1
  let X : ℝ := (l : ℝ) ^ 2 + 4 * l + 1
  let Y : ℝ := (l : ℝ) ^ 2 + 4 * l + 2
  let B : ℝ := (l : ℝ) ^ 2 + l + 1 / 4
  have hX : 0 < X := by dsimp [X]; positivity
  have hY : 0 < Y := by dsimp [Y]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  have hlpow : 0 < Real.rpow (l : ℝ) (2 * p - 1) :=
    Real.rpow_pos_of_pos hx _
  have hden :
      0 < Real.rpow (l : ℝ) (2 * p - 1) * B :=
    mul_pos hlpow hB
  have hratio :
      Real.rpow X (p + 1 / 2) /
          (Real.rpow (l : ℝ) (2 * p - 1) * B) <
        2 * p := by
    simpa [X, B] using hL l hlL
  have hclear :
      Real.rpow X (p + 1 / 2) <
        (2 * p) *
          (Real.rpow (l : ℝ) (2 * p - 1) * B) :=
    (div_lt_iff₀ hden).mp hratio
  have hcore :
      2 * Real.rpow X (p + 1 / 2) <
        p * Real.rpow (l : ℝ) (2 * p - 1) *
          (2 * (l : ℝ) + 1) ^ 2 := by
    calc
      2 * Real.rpow X (p + 1 / 2) <
          2 * ((2 * p) *
            (Real.rpow (l : ℝ) (2 * p - 1) * B)) :=
        mul_lt_mul_of_pos_left hclear (by norm_num)
      _ = p * Real.rpow (l : ℝ) (2 * p - 1) *
          (2 * (l : ℝ) + 1) ^ 2 := by
        dsimp [B]
        ring
  have hXp : 0 < Real.rpow X p :=
    Real.rpow_pos_of_pos hX _
  have hXbig : 0 < Real.rpow X (2 * p + 1 / 2) :=
    Real.rpow_pos_of_pos hX _
  have hsplit :
      Real.rpow X (2 * p + 1 / 2) =
        Real.rpow X (p + 1 / 2) * Real.rpow X p := by
    calc
      Real.rpow X (2 * p + 1 / 2) =
          Real.rpow X ((p + 1 / 2) + p) := by
        congr 1
        ring
      _ = Real.rpow X (p + 1 / 2) * Real.rpow X p :=
        Real.rpow_add hX (p + 1 / 2) p
  have hfirst :
      2 / Real.rpow X p <
        (p * Real.rpow (l : ℝ) (2 * p - 1) *
            (2 * (l : ℝ) + 1) ^ 2) /
          Real.rpow X (2 * p + 1 / 2) := by
    apply (div_lt_div_iff₀ hXp hXbig).2
    calc
      2 * Real.rpow X (2 * p + 1 / 2) =
          (2 * Real.rpow X (p + 1 / 2)) *
            Real.rpow X p := by
        rw [hsplit]
        ring
      _ < (p * Real.rpow (l : ℝ) (2 * p - 1) *
            (2 * (l : ℝ) + 1) ^ 2) *
          Real.rpow X p :=
        mul_lt_mul_of_pos_right hcore hXp
  have hXY : X ≤ Y := by
    dsimp [X, Y]
    linarith
  have hpowXY : Real.rpow X p ≤ Real.rpow Y p :=
    Real.rpow_le_rpow hX.le hXY hp0.le
  have hsecond :
      2 / Real.rpow Y p ≤ 2 / Real.rpow X p :=
    div_le_div_of_nonneg_left (by norm_num) hXp hpowXY
  have hpositive :
      0 <
        p * Real.rpow (l : ℝ) (2 * p - 1) *
              (2 * (l : ℝ) + 1) ^ 2 /
            Real.rpow X (2 * p + 1 / 2) -
          2 / Real.rpow Y p := by
    rw [sub_pos]
    exact hsecond.trans_lt hfirst
  have hbound := gap6 p hp l hl1
  dsimp [X, Y] at hpositive
  linarith

theorem gap9 (p : ℝ) (hp : 1 / 2 < p) :
    ∃ L : ℕ, AntitoneOn (amplitude p) {l : ℕ | L ≤ l} := by
  rcases gap8 p hp with ⟨L, hL⟩
  refine ⟨L, antitoneOn_nat_Ici_of_succ_le ?_⟩
  intro l hl
  exact (hL l hl).le

private theorem amplitude_lower_of_pos (p : ℝ) (hp0 : 0 < p) :
    ∀ l : ℕ, 1 ≤ l →
      (2 * (l : ℝ) + 1) / Real.rpow (l + 1) (2 * p) <
        amplitude p l := by
  intro l hl
  have hblock : (block l).Nonempty := by
    rw [block, Finset.nonempty_Ico]
    nlinarith
  have hsum :
      (∑ n ∈ block l,
          1 / Real.rpow (((l + 1) ^ 2 : ℕ)) p) <
        amplitude p l := by
    unfold amplitude
    apply Finset.sum_lt_sum_of_nonempty hblock
    intro n hn
    have hn' := gap1 l n hn
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hbase :
        (n : ℝ) < ((((l + 1) ^ 2 : ℕ) : ℝ)) := by
      exact_mod_cast hn'.2
    have hpow :
        Real.rpow (n : ℝ) p <
          Real.rpow ((((l + 1) ^ 2 : ℕ) : ℝ)) p :=
      Real.rpow_lt_rpow hn0 hbase hp0
    exact one_div_lt_one_div_of_lt
      (Real.rpow_pos_of_pos (by
        have hl0 : 0 < l := by omega
        have hlpow : 0 < l ^ 2 := pow_pos hl0 2
        have : 0 < n := lt_of_lt_of_le hlpow hn'.1
        exact_mod_cast this) p)
      hpow
  have hden :
      Real.rpow ((((l + 1) ^ 2 : ℕ) : ℝ)) p =
        Real.rpow (((l + 1 : ℕ) : ℝ)) (2 * p) := by
    norm_num [Nat.cast_pow]
    exact
      (Real.rpow_natCast_mul
        (x := (l : ℝ) + 1) (by positivity) 2 p).symm
  calc
    (2 * (l : ℝ) + 1) / Real.rpow (l + 1) (2 * p) =
        ∑ n ∈ block l,
          1 / Real.rpow (((l + 1) ^ 2 : ℕ)) p := by
      rw [Finset.sum_const, gap2]
      simp only [nsmul_eq_mul]
      rw [hden]
      norm_num
      ring
    _ < amplitude p l := hsum

theorem gap10 (p : ℝ) (hp : 1 / 2 < p) :
    ∀ l : ℕ, 1 ≤ l →
      (2 * (l : ℝ) + 1) / Real.rpow (l + 1) (2 * p) <
        amplitude p l := by
  exact amplitude_lower_of_pos p (by linarith)

theorem gap11 (p : ℝ) (hp : 1 / 2 < p) :
    ∀ l : ℕ, 1 ≤ l →
      amplitude p l ≤
        (2 * (l : ℝ) + 1) / Real.rpow l (2 * p) := by
  intro l hl
  have hp0 : 0 < p := by linarith
  have hsum :
      amplitude p l ≤
        ∑ n ∈ block l, 1 / Real.rpow (l ^ 2 : ℕ) p := by
    unfold amplitude
    apply Finset.sum_le_sum
    intro n hn
    have hn' := gap1 l n hn
    have hbase :
        ((((l ^ 2 : ℕ) : ℝ))) ≤ (n : ℝ) := by
      exact_mod_cast hn'.1
    have hpow :
        Real.rpow ((((l ^ 2 : ℕ) : ℝ))) p ≤
          Real.rpow (n : ℝ) p :=
      Real.rpow_le_rpow (by positivity) hbase hp0.le
    exact one_div_le_one_div_of_le
      (Real.rpow_pos_of_pos (by positivity) p) hpow
  have hden :
      Real.rpow (((l ^ 2 : ℕ) : ℝ)) p =
        Real.rpow (l : ℝ) (2 * p) := by
    norm_num [Nat.cast_pow]
    exact
      (Real.rpow_natCast_mul
        (x := (l : ℝ)) (by positivity) 2 p).symm
  calc
    amplitude p l ≤
        ∑ n ∈ block l, 1 / Real.rpow (l ^ 2 : ℕ) p := hsum
    _ = (2 * (l : ℝ) + 1) / Real.rpow l (2 * p) := by
      rw [Finset.sum_const, gap2]
      simp only [nsmul_eq_mul]
      rw [hden]
      norm_num
      ring

theorem gap12 (p : ℝ) (hp : 1 / 2 < p) :
    Tendsto (fun l : ℕ => amplitude p (l + 1)) atTop (nhds 0) := by
  have hexp : 0 < 2 * p - 1 := by linarith
  have hbase :
      Tendsto (fun l : ℕ => ((l + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hmajorant :
      Tendsto
        (fun l : ℕ =>
          3 * Real.rpow ((l + 1 : ℕ) : ℝ) (-(2 * p - 1)))
        atTop (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul
        ((tendsto_rpow_neg_atTop hexp).comp hbase))
  refine squeeze_zero' ?_ ?_ hmajorant
  · exact Filter.Eventually.of_forall fun l => by
      unfold amplitude
      exact Finset.sum_nonneg fun n _ =>
        div_nonneg zero_le_one
          (Real.rpow_nonneg (by positivity) p)
  · exact Filter.Eventually.of_forall fun l => by
      have hx : 0 < (((l + 1 : ℕ) : ℝ)) := by positivity
      have hx1 : 1 ≤ (((l + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_le_succ (Nat.zero_le l)
      calc
        amplitude p (l + 1) ≤
            (2 * ((l + 1 : ℕ) : ℝ) + 1) /
              Real.rpow (l + 1 : ℕ) (2 * p) :=
          gap11 p hp (l + 1) (by omega)
        _ ≤ 3 * ((l + 1 : ℕ) : ℝ) /
              Real.rpow (l + 1 : ℕ) (2 * p) := by
          exact div_le_div_of_nonneg_right (by linarith)
            (Real.rpow_nonneg hx.le (2 * p))
        _ = 3 * Real.rpow ((l + 1 : ℕ) : ℝ) (-(2 * p - 1)) := by
          have hneg :
              Real.rpow ((l + 1 : ℕ) : ℝ) (-(2 * p - 1)) =
                (Real.rpow ((l + 1 : ℕ) : ℝ) (2 * p - 1))⁻¹ :=
            Real.rpow_neg hx.le (2 * p - 1)
          have hsub :
              Real.rpow ((l + 1 : ℕ) : ℝ) (2 * p - 1) =
                Real.rpow ((l + 1 : ℕ) : ℝ) (2 * p) /
                  ((l + 1 : ℕ) : ℝ) :=
            Real.rpow_sub_one hx.ne' (2 * p)
          rw [hneg, hsub, inv_div]
          ring

theorem gap13 (p : ℝ) (hp : 1 / 2 < p) :
    ProofGap.SeriesConverges (fun l : ℕ => blockTerm p (l + 1)) := by
  rcases gap9 p hp with ⟨L, hantiOn⟩
  have hanti :
      Antitone (fun n : ℕ => amplitude p (n + L + 1)) := by
    intro m n hmn
    apply hantiOn
    · simp
      omega
    · simp
      omega
    · omega
  have hzero :
      Tendsto (fun n : ℕ => amplitude p (n + L + 1))
        atTop (nhds 0) := by
    have hshift :=
      (tendsto_add_atTop_iff_nat L).mpr (gap12 p hp)
    simpa [add_assoc] using hshift
  obtain ⟨s, hs⟩ :=
    hanti.tendsto_alternating_series_of_tendsto_zero hzero
  have htail :
      ProofGap.SeriesConverges
        (fun n : ℕ => blockTerm p ((n + L) + 1)) := by
    let c : ℝ := (-1 : ℝ) ^ (L + 1)
    unfold ProofGap.SeriesConverges
    refine ⟨c * s, ?_⟩
    unfold HasSum
    rw [SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff]
    have hc :
        Tendsto (fun _ : ℕ => c) atTop (nhds c) :=
      tendsto_const_nhds
    have hmul := hc.mul hs
    convert hmul using 1
    funext n
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change
      blockTerm p (i + L + 1) =
        c * ((-1 : ℝ) ^ i * amplitude p (i + L + 1))
    rw [gap5]
    dsimp [c]
    rw [show i + L + 1 = i + (L + 1) by omega, pow_add]
    ring
  exact
    seriesConverges_of_nat_add
      (f := fun l : ℕ => blockTerm p (l + 1)) L htail

private theorem amplitude_nonneg (p : ℝ) (l : ℕ) :
    0 ≤ amplitude p l := by
  unfold amplitude
  exact Finset.sum_nonneg fun n _ =>
    div_nonneg zero_le_one
      (Real.rpow_nonneg (by positivity) p)

private theorem abs_blockTerm_eq_amplitude (p : ℝ) (l : ℕ) :
    |blockTerm p l| = amplitude p l := by
  rw [gap5]
  rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (amplitude_nonneg p l)]

theorem gap14 (p : ℝ) (hp₁ : 1 / 2 < p) (hp₂ : p ≤ 1) :
    ConditionallySummable (fun l : ℕ => blockTerm p (l + 1)) := by
  refine ⟨gap13 p hp₁, ?_⟩
  intro habs
  have hamp :
      Summable (fun l : ℕ => amplitude p (l + 1)) := by
    simpa only [abs_blockTerm_eq_amplitude] using habs
  have hshift :
      Summable (fun n : ℕ =>
        1 / Real.rpow ((n + 2 : ℕ) : ℝ) (2 * p - 1)) := by
    refine Summable.of_nonneg_of_le
      (fun n => div_nonneg zero_le_one
        (Real.rpow_nonneg (by positivity) (2 * p - 1))) ?_ hamp
    intro n
    have hx : 0 < (((n + 2 : ℕ) : ℝ)) := by positivity
    have hsub :
        Real.rpow ((n + 2 : ℕ) : ℝ) (2 * p - 1) =
          Real.rpow ((n + 2 : ℕ) : ℝ) (2 * p) /
            ((n + 2 : ℕ) : ℝ) :=
      Real.rpow_sub_one hx.ne' (2 * p)
    calc
      1 / Real.rpow ((n + 2 : ℕ) : ℝ) (2 * p - 1) =
          ((n + 2 : ℕ) : ℝ) /
            Real.rpow ((n + 2 : ℕ) : ℝ) (2 * p) := by
        rw [hsub]
        field_simp [hx.ne',
          (Real.rpow_pos_of_pos hx (2 * p)).ne']
      _ ≤ (2 * ((n + 1 : ℕ) : ℝ) + 1) /
            Real.rpow ((n + 2 : ℕ) : ℝ) (2 * p) := by
        exact div_le_div_of_nonneg_right (by norm_num; linarith)
          (Real.rpow_nonneg hx.le (2 * p))
      _ ≤ amplitude p (n + 1) :=
        by
          rw [show ((n + 2 : ℕ) : ℝ) =
            ((n + 1 : ℕ) : ℝ) + 1 by
              exact_mod_cast (by omega : n + 2 = (n + 1) + 1)]
          exact (gap10 p hp₁ (n + 1) (by omega)).le
  have hfull :
      Summable (fun n : ℕ =>
        1 / Real.rpow (n : ℝ) (2 * p - 1)) :=
    (_root_.summable_nat_add_iff 2).mp hshift
  have hq : 1 < 2 * p - 1 :=
    Real.summable_one_div_nat_rpow.mp hfull
  linarith

theorem gap15 (p : ℝ) (hp : 1 < p) :
    Summable (fun l : ℕ => |blockTerm p (l + 1)|) := by
  have hpHalf : 1 / 2 < p := by linarith
  have hq : 1 < 2 * p - 1 := by linarith
  have hfull :
      Summable (fun n : ℕ =>
        1 / Real.rpow (n : ℝ) (2 * p - 1)) :=
    Real.summable_one_div_nat_rpow.mpr hq
  have hshift :
      Summable (fun n : ℕ =>
        1 / Real.rpow ((n + 1 : ℕ) : ℝ) (2 * p - 1)) :=
    (_root_.summable_nat_add_iff 1).mpr hfull
  have hmajor :
      Summable (fun n : ℕ =>
        3 / Real.rpow ((n + 1 : ℕ) : ℝ) (2 * p - 1)) := by
    simpa [mul_div_assoc] using hshift.mul_left 3
  refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) ?_ hmajor
  intro n
  have hx : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hx1 : 1 ≤ (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hsub :
      Real.rpow ((n + 1 : ℕ) : ℝ) (2 * p - 1) =
        Real.rpow ((n + 1 : ℕ) : ℝ) (2 * p) /
          ((n + 1 : ℕ) : ℝ) :=
    Real.rpow_sub_one hx.ne' (2 * p)
  calc
    |blockTerm p (n + 1)| = amplitude p (n + 1) :=
      abs_blockTerm_eq_amplitude p (n + 1)
    _ ≤ (2 * ((n + 1 : ℕ) : ℝ) + 1) /
        Real.rpow (n + 1 : ℕ) (2 * p) :=
      gap11 p hpHalf (n + 1) (by omega)
    _ ≤ 3 * ((n + 1 : ℕ) : ℝ) /
        Real.rpow (n + 1 : ℕ) (2 * p) := by
      exact div_le_div_of_nonneg_right (by linarith)
        (Real.rpow_nonneg hx.le (2 * p))
    _ = 3 / Real.rpow ((n + 1 : ℕ) : ℝ) (2 * p - 1) := by
      rw [hsub]
      field_simp [hx.ne',
        (Real.rpow_pos_of_pos hx (2 * p)).ne']

theorem gap16 (p : ℝ) (hp : p ≤ 1 / 2) :
    ¬ ProofGap.SeriesConverges (fun l : ℕ => blockTerm p (l + 1)) := by
  intro hseries
  have habszero :
      Tendsto (fun l : ℕ => |blockTerm p (l + 1)|)
        atTop (nhds 0) := by
    simpa using (seriesConverges_tendsto_zero hseries).abs
  have hampzero :
      Tendsto (fun l : ℕ => amplitude p (l + 1))
        atTop (nhds 0) := by
    simpa only [abs_blockTerm_eq_amplitude] using habszero
  have hlower : ∀ l : ℕ, (1 : ℝ) ≤ amplitude p (l + 1) := by
    intro l
    by_cases hp0 : 0 < p
    · have hblock :=
        (amplitude_lower_of_pos p hp0 (l + 1) (by omega)).le
      have hx : 0 < (((l + 2 : ℕ) : ℝ)) := by positivity
      have hx1 : 1 ≤ (((l + 2 : ℕ) : ℝ)) := by
        exact_mod_cast (by omega : 1 ≤ l + 2)
      have hden :
          Real.rpow ((l + 2 : ℕ) : ℝ) (2 * p) ≤
            ((l + 2 : ℕ) : ℝ) := by
        calc
          Real.rpow ((l + 2 : ℕ) : ℝ) (2 * p) ≤
              Real.rpow ((l + 2 : ℕ) : ℝ) 1 :=
            Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
          _ = ((l + 2 : ℕ) : ℝ) := by
            exact Real.rpow_one _
      have hnum :
          Real.rpow ((l + 2 : ℕ) : ℝ) (2 * p) ≤
            2 * ((l + 1 : ℕ) : ℝ) + 1 := by
        calc
          Real.rpow ((l + 2 : ℕ) : ℝ) (2 * p) ≤
              ((l + 2 : ℕ) : ℝ) := hden
          _ ≤ 2 * ((l + 1 : ℕ) : ℝ) + 1 := by
            norm_num
            linarith
      have hone :
          (1 : ℝ) ≤
            (2 * ((l + 1 : ℕ) : ℝ) + 1) /
              Real.rpow ((l + 2 : ℕ) : ℝ) (2 * p) :=
        (le_div_iff₀ (Real.rpow_pos_of_pos hx (2 * p))).2
          (by simpa using hnum)
      have hblock' :
          (2 * ((l + 1 : ℕ) : ℝ) + 1) /
              Real.rpow ((l + 2 : ℕ) : ℝ) (2 * p) ≤
            amplitude p (l + 1) := by
        rw [show ((l + 2 : ℕ) : ℝ) =
          ((l + 1 : ℕ) : ℝ) + 1 by
            exact_mod_cast (by omega : l + 2 = (l + 1) + 1)]
        exact hblock
      exact hone.trans hblock'
    · have hpnonpos : p ≤ 0 := le_of_not_gt hp0
      let n0 : ℕ := (l + 1) ^ 2
      have hn0mem : n0 ∈ block (l + 1) := by
        dsimp [n0, block]
        simp only [Finset.mem_Ico, le_refl, true_and]
        exact Nat.pow_lt_pow_left (by omega) (by norm_num)
      have hn01 : (1 : ℝ) ≤ (n0 : ℝ) := by
        have hn0Nat : 1 ≤ n0 := by
          dsimp [n0]
          have : 0 < l + 1 := by omega
          exact pow_pos this 2
        exact_mod_cast hn0Nat
      have hrpow :
          Real.rpow (n0 : ℝ) p ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hn01 hpnonpos
      have hterm :
          (1 : ℝ) ≤ 1 / Real.rpow (n0 : ℝ) p :=
        (le_div_iff₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hn01) p)).2
          (by simpa using hrpow)
      have hsingle :
          1 / Real.rpow (n0 : ℝ) p ≤ amplitude p (l + 1) := by
        unfold amplitude
        exact Finset.single_le_sum
          (fun n _ => div_nonneg zero_le_one
            (Real.rpow_nonneg (by positivity) p))
          hn0mem
      exact hterm.trans hsingle
  have hbad : (1 : ℝ) ≤ 0 :=
    ge_of_tendsto hampzero (Filter.Eventually.of_forall hlower)
  norm_num at hbad

private theorem seriesConverges_iff_tendsto_range {f : ℕ → ℝ} :
    ProofGap.SeriesConverges f ↔
      ∃ s : ℝ,
        Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i)
          atTop (nhds s) := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    unfold HasSum at hs
    rw [SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff] at hs
    simpa [Function.comp_def] using hs
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    unfold HasSum
    rw [SummationFilter.conditional_filter_eq_map_range,
      Filter.tendsto_map'_iff]
    simpa [Function.comp_def] using hs

private theorem originalPartialSum_eq_sum_range (p : ℝ) (N : ℕ) :
    originalPartialSum p N =
      ∑ n ∈ Finset.range N, term p (n + 1) := by
  unfold originalPartialSum
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem blockPartialSum_eq_sum_range (p : ℝ) (M : ℕ) :
    blockPartialSum p M =
      ∑ l ∈ Finset.range M, blockTerm p (l + 1) := by
  unfold blockPartialSum
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [Finset.sum_Ico_eq_sum_range]
  simp [Nat.add_comm]

private theorem blockPartialSum_eq_originalPartialSum (p : ℝ) :
    ∀ M : ℕ,
      blockPartialSum p M = originalPartialSum p ((M + 1) ^ 2 - 1) := by
  intro M
  induction M with
  | zero =>
      simp [blockPartialSum, originalPartialSum]
  | succ M ih =>
      rw [blockPartialSum]
      rw [Finset.sum_Icc_succ_top (by omega)]
      change blockPartialSum p M + blockTerm p (M + 1) = _
      rw [ih]
      have hleft :
          originalPartialSum p ((M + 1) ^ 2 - 1) =
            ∑ n ∈ Finset.Ico 1 ((M + 1) ^ 2), term p n := by
        unfold originalPartialSum
        apply Finset.sum_congr
        · ext n
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega
        · intro n hn
          rfl
      have hright :
          originalPartialSum p ((M + 1 + 1) ^ 2 - 1) =
            ∑ n ∈ Finset.Ico 1 ((M + 1 + 1) ^ 2), term p n := by
        unfold originalPartialSum
        apply Finset.sum_congr
        · ext n
          simp only [Finset.mem_Icc, Finset.mem_Ico]
          omega
        · intro n hn
          rfl
      rw [hleft, hright]
      unfold blockTerm block
      have hfirstBound : 1 ≤ (M + 1) ^ 2 := by
        simpa using
          (pow_le_pow_left' (by omega : (1 : ℕ) ≤ M + 1) 2)
      have hsecondBound : (M + 1) ^ 2 ≤ (M + 1 + 1) ^ 2 :=
        pow_le_pow_left' (by omega) 2
      exact
        Finset.sum_Ico_consecutive (term p) hfirstBound hsecondBound

theorem gap17 (p : ℝ) :
    ∀ N M : ℕ, 1 ≤ M → M ^ 2 ≤ N → N < (M + 1) ^ 2 →
      |originalPartialSum p N - blockPartialSum p (M - 1)| ≤
        |blockTerm p M| := by
  intro N M hM hMN hN
  have hblocks :
      blockPartialSum p (M - 1) = originalPartialSum p (M ^ 2 - 1) := by
    simpa [Nat.sub_add_cancel hM] using
      blockPartialSum_eq_originalPartialSum p (M - 1)
  have hsplit :
      originalPartialSum p N =
        originalPartialSum p (M ^ 2 - 1) +
          ∑ n ∈ Finset.Icc (M ^ 2) N, term p n := by
    unfold originalPartialSum
    have hfirst :
        (∑ n ∈ Finset.Icc 1 (M ^ 2 - 1), term p n) =
          ∑ n ∈ Finset.Ico 1 (M ^ 2), term p n := by
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      · intro n hn
        rfl
    have hlast :
        (∑ n ∈ Finset.Icc (M ^ 2) N, term p n) =
          ∑ n ∈ Finset.Ico (M ^ 2) (N + 1), term p n := by
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      · intro n hn
        rfl
    have hall :
        (∑ n ∈ Finset.Icc 1 N, term p n) =
          ∑ n ∈ Finset.Ico 1 (N + 1), term p n := by
      apply Finset.sum_congr
      · ext n
        simp only [Finset.mem_Icc, Finset.mem_Ico]
        omega
      · intro n hn
        rfl
    rw [hfirst, hlast, hall]
    have hMpow : 1 ≤ M ^ 2 := by
      simpa using (pow_le_pow_left' hM 2)
    exact
      (Finset.sum_Ico_consecutive (term p) hMpow (by omega)).symm
  rw [hblocks, hsplit]
  simp only [add_sub_cancel_left]
  calc
    |∑ n ∈ Finset.Icc (M ^ 2) N, term p n| ≤
        ∑ n ∈ Finset.Icc (M ^ 2) N, |term p n| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ block M, |term p n| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        simp only [block, Finset.mem_Ico]
        exact ⟨hn.1, lt_of_le_of_lt hn.2 hN⟩
      · intro n hnBlock hnPrefix
        exact abs_nonneg _
    _ = amplitude p M := by
      unfold amplitude
      apply Finset.sum_congr rfl
      intro n hn
      unfold term
      have hnonneg : 0 ≤ Real.rpow (n : ℝ) p :=
        Real.rpow_nonneg (by positivity) p
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg hnonneg]
    _ = |blockTerm p M| := (abs_blockTerm_eq_amplitude p M).symm

theorem gap18 (p : ℝ) (hp₁ : 1 / 2 < p) (hp₂ : p ≤ 1) :
    ConditionallySummable (fun n : ℕ => term p (n + 1)) := by
  unfold ConditionallySummable
  constructor
  · rcases
        seriesConverges_iff_tendsto_range.mp (gap13 p hp₁) with
      ⟨s, hs⟩
    have hblock :
        Tendsto (fun M : ℕ => blockPartialSum p M) atTop (nhds s) := by
      apply hs.congr'
      exact Filter.Eventually.of_forall fun M =>
        (blockPartialSum_eq_sum_range p M).symm
    have hsqrt : Tendsto Nat.sqrt atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro K
      filter_upwards [eventually_ge_atTop (K ^ 2)] with N hN
      exact Nat.le_sqrt'.2 hN
    have hsqrtSub :
        Tendsto (fun N : ℕ => Nat.sqrt N - 1) atTop atTop := by
      refine tendsto_atTop.2 ?_
      intro K
      filter_upwards [eventually_ge_atTop ((K + 1) ^ 2)] with N hN
      have hroot : K + 1 ≤ Nat.sqrt N := Nat.le_sqrt'.2 hN
      omega
    have hamp : Tendsto (amplitude p) atTop (nhds 0) :=
      (tendsto_add_atTop_iff_nat 1).mp (gap12 p hp₁)
    have hboundZero :
        Tendsto (fun N : ℕ => |blockTerm p (Nat.sqrt N)|)
          atTop (nhds 0) := by
      apply (hamp.comp hsqrt).congr'
      exact Filter.Eventually.of_forall fun N =>
        (abs_blockTerm_eq_amplitude p (Nat.sqrt N)).symm
    have habsError :
        Tendsto
          (fun N : ℕ =>
            |originalPartialSum p N -
              blockPartialSum p (Nat.sqrt N - 1)|)
          atTop (nhds 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun N => abs_nonneg _) ?_
        hboundZero
      filter_upwards [eventually_ge_atTop 1] with N hN
      have hrootPos : 0 < Nat.sqrt N := Nat.sqrt_pos.mpr (by omega)
      exact gap17 p N (Nat.sqrt N) (by omega)
        (Nat.sqrt_le' N) (Nat.lt_succ_sqrt' N)
    have herror :
        Tendsto
          (fun N : ℕ =>
            originalPartialSum p N -
              blockPartialSum p (Nat.sqrt N - 1))
          atTop (nhds 0) := by
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      simpa only [Real.norm_eq_abs] using habsError
    have horiginal :
        Tendsto (fun N : ℕ => originalPartialSum p N)
          atTop (nhds s) := by
      simpa only [Function.comp_apply, sub_add_cancel, zero_add] using
        herror.add (hblock.comp hsqrtSub)
    apply seriesConverges_iff_tendsto_range.mpr
    refine ⟨s, ?_⟩
    apply horiginal.congr'
    exact Filter.Eventually.of_forall fun N =>
      originalPartialSum_eq_sum_range p N
  · intro habs
    have hshift :
        Summable (fun n : ℕ =>
          1 / Real.rpow ((n + 1 : ℕ) : ℝ) p) := by
      apply habs.congr
      intro n
      unfold term
      have hnonneg :
          0 ≤ Real.rpow ((n + 1 : ℕ) : ℝ) p :=
        Real.rpow_nonneg (by positivity) p
      rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
        abs_of_nonneg hnonneg]
    have hfull :
        Summable (fun n : ℕ => 1 / Real.rpow (n : ℝ) p) :=
      (_root_.summable_nat_add_iff 1).mp hshift
    have hpLarge : 1 < p := Real.summable_one_div_nat_rpow.mp hfull
    linarith

theorem gap19 (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ => |term p (n + 1)|) := by
  have hfull :
      Summable (fun n : ℕ => 1 / Real.rpow (n : ℝ) p) :=
    Real.summable_one_div_nat_rpow.mpr hp
  have hshift :
      Summable (fun n : ℕ =>
        1 / Real.rpow ((n + 1 : ℕ) : ℝ) p) :=
    (_root_.summable_nat_add_iff 1).mpr hfull
  refine hshift.congr (fun n => ?_)
  unfold term
  have hnonneg :
      0 ≤ Real.rpow ((n + 1 : ℕ) : ℝ) p :=
    Real.rpow_nonneg (by positivity) p
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg hnonneg]

theorem gap20 (p : ℝ) (hp : p ≤ 1 / 2) :
    ¬ ProofGap.SeriesConverges (fun n : ℕ => term p (n + 1)) := by
  intro horiginalSeries
  rcases seriesConverges_iff_tendsto_range.mp horiginalSeries with
    ⟨s, hs⟩
  have horiginal :
      Tendsto (fun N : ℕ => originalPartialSum p N)
        atTop (nhds s) := by
    apply hs.congr'
    exact Filter.Eventually.of_forall fun N =>
      (originalPartialSum_eq_sum_range p N).symm
  have hendpoints :
      Tendsto (fun M : ℕ => (M + 1) ^ 2 - 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro K
    filter_upwards [eventually_ge_atTop K] with M hM
    have hsq : M + 1 ≤ (M + 1) ^ 2 := by
      calc
        M + 1 = (M + 1) * 1 := by omega
        _ ≤ (M + 1) * (M + 1) :=
          Nat.mul_le_mul_left (M + 1) (by omega)
        _ = (M + 1) ^ 2 := by simp [pow_two]
    omega
  have hblock :
      Tendsto (fun M : ℕ => blockPartialSum p M)
        atTop (nhds s) := by
    apply (horiginal.comp hendpoints).congr'
    exact Filter.Eventually.of_forall fun M =>
      (blockPartialSum_eq_originalPartialSum p M).symm
  apply gap16 p hp
  apply seriesConverges_iff_tendsto_range.mpr
  refine ⟨s, ?_⟩
  apply hblock.congr'
  exact Filter.Eventually.of_forall fun M =>
    blockPartialSum_eq_sum_range p M

end

end ProofGap.Exercise2687
