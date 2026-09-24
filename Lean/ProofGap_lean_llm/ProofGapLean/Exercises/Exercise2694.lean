import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

namespace ProofGap.Exercise2694

noncomputable section

open Filter
open scoped BigOperators
open scoped Topology

def rawTerm (p : ℝ) (j : ℕ) : ℝ :=
  let n := j / 3 + 1
  match j % 3 with
  | 0 => 1 / Real.rpow (4 * n - 3) p
  | 1 => 1 / Real.rpow (4 * n - 1) p
  | _ => -(1 / Real.rpow (2 * n) p)

def groupedTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (4 * n) p * Real.rpow (1 - 3 / (4 * (n : ℝ))) (-p) +
    1 / Real.rpow (4 * n) p * Real.rpow (1 - 1 / (4 * (n : ℝ))) (-p) -
    1 / Real.rpow (2 * n) p

def leadingTerm (p : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow (2 * n) p * (1 / Real.rpow 2 (p - 1) - 1)

def correctionTerm (p : ℝ) (n : ℕ) : ℝ :=
  4 * p / Real.rpow (4 * n) (p + 1)

def expansionRemainder (p : ℝ) (n : ℕ) : ℝ :=
  groupedTerm p n - leadingTerm p n - correctionTerm p n

def ConditionallySummable (f : ℕ → ℝ) : Prop :=
  ProofGap.SeriesConverges f ∧ ¬ Summable (fun n => |f n|)

private theorem one_sub_rpow_taylor_bound (p : ℝ) :
    ∃ C : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) (3 / 4 : ℝ),
      |Real.rpow (1 - x) (-p) - (1 + p * x)| ≤ C * x ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.rpow (1 - x) (-p)
  have hf : ContDiffOn ℝ 2 f (Set.Icc (0 : ℝ) (3 / 4 : ℝ)) := by
    apply (contDiff_const.sub contDiff_id).contDiffOn.rpow_const_of_ne
    intro x hx
    dsimp [f]
    linarith [hx.2]
  obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := 1)
    (a := (0 : ℝ)) (b := (3 / 4 : ℝ)) (by norm_num) hf
  refine ⟨C, fun x hx => ?_⟩
  have hd : HasDerivAt f p 0 := by
    dsimp [f]
    convert ((hasDerivAt_id (x := (0 : ℝ))).const_sub 1).rpow_const
      (p := -p) (Or.inl (by norm_num)) using 1 <;> norm_num
  have hu : UniqueDiffWithinAt ℝ (Set.Icc (0 : ℝ) (3 / 4 : ℝ)) 0 :=
    (uniqueDiffOn_Icc (by norm_num)).uniqueDiffWithinAt (by norm_num)
  have hderiv : derivWithin f (Set.Icc (0 : ℝ) (3 / 4 : ℝ)) 0 = p := by
    rw [hd.differentiableAt.derivWithin hu]
    exact hd.deriv
  dsimp [f] at hderiv
  simpa [Real.norm_eq_abs, f, hderiv, mul_comm] using hC x hx

private theorem expansionRemainder_eq_taylor_remainders (p : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    expansionRemainder p n =
      1 / Real.rpow (4 * n) p *
        ((Real.rpow (1 - 3 / (4 * (n : ℝ))) (-p) -
            (1 + p * (3 / (4 * (n : ℝ))))) +
          (Real.rpow (1 - 1 / (4 * (n : ℝ))) (-p) -
            (1 + p * (1 / (4 * (n : ℝ)))))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n := by positivity
  have h4n : (0 : ℝ) < 4 * n := by positivity
  have hpow4 :
      Real.rpow (4 * (n : ℝ)) p =
        Real.rpow (2 * (n : ℝ)) p * Real.rpow 2 p := by
    calc
      Real.rpow (4 * (n : ℝ)) p = Real.rpow ((2 * (n : ℝ)) * 2) p := by congr 1 <;> ring
      _ = Real.rpow (2 * (n : ℝ)) p * Real.rpow 2 p :=
        Real.mul_rpow h2n.le (by norm_num)
  have hpow2sub : Real.rpow 2 (p - 1) = Real.rpow 2 p / 2 := by
    simpa using Real.rpow_sub (by norm_num : (0 : ℝ) < 2) p 1
  have hlead :
      1 / Real.rpow (2 * (n : ℝ)) p * (1 / Real.rpow 2 (p - 1) - 1) =
        2 / Real.rpow (4 * (n : ℝ)) p - 1 / Real.rpow (2 * (n : ℝ)) p := by
    rw [hpow2sub, hpow4]
    field_simp
  have hpow4add :
      Real.rpow (4 * (n : ℝ)) (p + 1) =
        Real.rpow (4 * (n : ℝ)) p * (4 * (n : ℝ)) := by
    calc
      Real.rpow (4 * (n : ℝ)) (p + 1) =
          Real.rpow (4 * (n : ℝ)) p * Real.rpow (4 * (n : ℝ)) 1 :=
        Real.rpow_add h4n p 1
      _ = Real.rpow (4 * (n : ℝ)) p * (4 * (n : ℝ)) := by
        congr 1
        exact Real.rpow_one _
  have hcorr :
      4 * p / Real.rpow (4 * (n : ℝ)) (p + 1) =
        1 / Real.rpow (4 * (n : ℝ)) p *
          (p * (3 / (4 * (n : ℝ)) + 1 / (4 * (n : ℝ)))) := by
    rw [hpow4add]
    field_simp
    ring
  simp only [expansionRemainder, groupedTerm, leadingTerm, correctionTerm,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [hlead, hcorr]
  ring

private theorem expansionRemainder_bigO (p : ℝ) :
    Asymptotics.IsBigO atTop (expansionRemainder p)
      (fun n : ℕ => 1 / Real.rpow n (p + 2)) := by
  obtain ⟨C, hC⟩ := one_sub_rpow_taylor_bound p
  refine Asymptotics.IsBigO.of_bound
    (|C| * ((5 / 8 : ℝ) * (1 / Real.rpow 4 p))) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : (0 : ℝ) < 4 * (n : ℝ) := by positivity
  have hx3 : 3 / (4 * (n : ℝ)) ∈ Set.Icc (0 : ℝ) (3 / 4 : ℝ) := by
    constructor
    · positivity
    · calc
        3 / (4 * (n : ℝ)) ≤ 3 / (4 * (1 : ℝ)) := by gcongr
        _ = 3 / 4 := by norm_num
  have hx1 : 1 / (4 * (n : ℝ)) ∈ Set.Icc (0 : ℝ) (3 / 4 : ℝ) := by
    constructor
    · positivity
    · calc
        1 / (4 * (n : ℝ)) ≤ 1 / (4 * (1 : ℝ)) := by gcongr
        _ ≤ 3 / 4 := by norm_num
  have h3 := hC (3 / (4 * (n : ℝ))) hx3
  have h1 := hC (1 / (4 * (n : ℝ))) hx1
  have h3' :
      |Real.rpow (1 - 3 / (4 * (n : ℝ))) (-p) -
          (1 + p * (3 / (4 * (n : ℝ))))| ≤
        |C| * (3 / (4 * (n : ℝ))) ^ 2 :=
    h3.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _))
  have h1' :
      |Real.rpow (1 - 1 / (4 * (n : ℝ))) (-p) -
          (1 + p * (1 / (4 * (n : ℝ))))| ≤
        |C| * (1 / (4 * (n : ℝ))) ^ 2 :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (sq_nonneg _))
  have hpow4mul :
      Real.rpow (4 * (n : ℝ)) p = Real.rpow 4 p * Real.rpow n p :=
    Real.mul_rpow (by norm_num) hnR.le
  have hpowNadd :
      Real.rpow (n : ℝ) (p + 2) = Real.rpow n p * (n : ℝ) ^ 2 := by
    calc
      Real.rpow (n : ℝ) (p + 2) = Real.rpow n p * Real.rpow n 2 :=
        Real.rpow_add hnR p 2
      _ = Real.rpow n p * (n : ℝ) ^ 2 := by
        congr 1
        exact Real.rpow_natCast _ 2
  have hscale :
      1 / Real.rpow (4 * (n : ℝ)) p *
          ((3 / (4 * (n : ℝ))) ^ 2 + (1 / (4 * (n : ℝ))) ^ 2) =
        ((5 / 8 : ℝ) * (1 / Real.rpow 4 p)) *
          (1 / Real.rpow (n : ℝ) (p + 2)) := by
    rw [hpow4mul, hpowNadd]
    field_simp
    ring
  rw [expansionRemainder_eq_taylor_remainders p n hn]
  have hq : 0 < 1 / Real.rpow (4 * (n : ℝ)) p :=
    one_div_pos.mpr (Real.rpow_pos_of_pos h4n p)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hq]
  calc
    1 / Real.rpow (4 * (n : ℝ)) p *
        |(Real.rpow (1 - 3 / (4 * (n : ℝ))) (-p) -
            (1 + p * (3 / (4 * (n : ℝ))))) +
          (Real.rpow (1 - 1 / (4 * (n : ℝ))) (-p) -
            (1 + p * (1 / (4 * (n : ℝ)))))| ≤
        1 / Real.rpow (4 * (n : ℝ)) p *
          (|Real.rpow (1 - 3 / (4 * (n : ℝ))) (-p) -
              (1 + p * (3 / (4 * (n : ℝ))))| +
            |Real.rpow (1 - 1 / (4 * (n : ℝ))) (-p) -
              (1 + p * (1 / (4 * (n : ℝ))))|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) hq.le
    _ ≤ 1 / Real.rpow (4 * (n : ℝ)) p *
          (|C| * (3 / (4 * (n : ℝ))) ^ 2 +
            |C| * (1 / (4 * (n : ℝ))) ^ 2) :=
      mul_le_mul_of_nonneg_left (add_le_add h3' h1') hq.le
    _ = |C| * (1 / Real.rpow (4 * (n : ℝ)) p *
          ((3 / (4 * (n : ℝ))) ^ 2 + (1 / (4 * (n : ℝ))) ^ 2)) := by ring
    _ = |C| * (((5 / 8 : ℝ) * (1 / Real.rpow 4 p)) *
          (1 / Real.rpow (n : ℝ) (p + 2))) := by rw [hscale]
    _ = |C| * ((5 / 8 : ℝ) * (1 / Real.rpow 4 p)) *
          ‖1 / Real.rpow (n : ℕ) (p + 2)‖ := by
      have hcomp : 0 < 1 / Real.rpow (n : ℝ) (p + 2) :=
        one_div_pos.mpr (Real.rpow_pos_of_pos hnR (p + 2))
      rw [Real.norm_eq_abs, abs_of_pos hcomp]
      norm_num
      ring

private theorem seriesConverges_of_tendsto_sum_range {f : ℕ → ℝ}
    (h : ∃ l, Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, f i) atTop (𝓝 l)) :
    ProofGap.SeriesConverges f := by
  rcases h with ⟨l, hl⟩
  refine ⟨l, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range]
  exact hl

private theorem correctionTerm_summable (p : ℝ) (hp : 0 < p) :
    Summable (fun n : ℕ => correctionTerm p (n + 1)) := by
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) (p + 1)) := by
    have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) (p + 1)).mpr (by linarith)
    refine h.congr fun n => ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    rw [← Real.rpow_eq_pow]
  have hscaled := hbase.mul_left (4 * p / Real.rpow 4 (p + 1))
  refine hscaled.congr fun n => ?_
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  have hpow : Real.rpow (4 * ((n : ℝ) + 1)) (p + 1) =
      Real.rpow 4 (p + 1) * Real.rpow ((n : ℝ) + 1) (p + 1) :=
    Real.mul_rpow (by norm_num) hn
  simp only [correctionTerm, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
  rw [hpow]
  ring

private theorem expansionRemainder_summable (p : ℝ) (hp : -1 < p) :
    Summable (fun n : ℕ => expansionRemainder p (n + 1)) := by
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow n (p + 2)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  have hall : Summable (expansionRemainder p) :=
    summable_of_isBigO_nat hbase (expansionRemainder_bigO p)
  exact hall.comp_injective (fun _ _ h => by omega)

private theorem one_lt_of_summable_shifted_rpow (p : ℝ)
    (h : Summable (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + 1) p)) :
    1 < p := by
  have h' : Summable (fun n : ℕ => 1 / |(n : ℝ) + 1| ^ p) := by
    refine h.congr fun n => ?_
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
    rw [← Real.rpow_eq_pow]
  exact (Real.summable_one_div_nat_add_rpow (1 : ℝ) p).mp h'

private theorem one_lt_of_summable_abs_rawTerm (p : ℝ)
    (habs : Summable (fun j : ℕ => |rawTerm p j|)) :
    1 < p := by
  have hsub : Summable (fun n : ℕ => |rawTerm p (3 * n + 2)|) :=
    habs.comp_injective (fun _ _ h => by omega)
  have heven : Summable (fun n : ℕ => 1 / Real.rpow (2 * (n + 1)) p) := by
    refine hsub.congr fun n => ?_
    have hdiv : (3 * n + 2) / 3 = n := by omega
    have hmod : (3 * n + 2) % 3 = 2 := by omega
    simp only [rawTerm, hdiv, hmod]
    rw [abs_neg, abs_div, abs_one]
    simp only [Nat.cast_add, Nat.cast_one]
    have hrpos : 0 < Real.rpow (2 * ((n : ℝ) + 1)) p :=
      Real.rpow_pos_of_pos (by positivity) p
    have habs : |Real.rpow (2 * ((n : ℝ) + 1)) p| =
        Real.rpow (2 * ((n : ℝ) + 1)) p := abs_of_pos hrpos
    rw [habs]
  have hscaled : Summable (fun n : ℕ =>
      (1 / Real.rpow 2 p) * (1 / Real.rpow ((n : ℝ) + 1) p)) := by
    refine heven.congr fun n => ?_
    have hmul : Real.rpow (2 * ((n : ℝ) + 1)) p =
        Real.rpow 2 p * Real.rpow ((n : ℝ) + 1) p := by
      simpa only [Real.rpow_eq_pow] using
        Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num)
          (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    rw [hmul]
    field_simp
  have hc : 1 / Real.rpow 2 p ≠ 0 :=
    one_div_ne_zero (Real.rpow_pos_of_pos (by norm_num) p).ne'
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + 1) p) :=
    (summable_mul_left_iff hc).mp hscaled
  exact one_lt_of_summable_shifted_rpow p hbase

theorem gap1 (p : ℝ) (hp : 1 < p) :
    Summable (fun n : ℕ =>
      |(-1 : ℝ) ^ n / Real.rpow (n + 1) p|) := by
  have h := (Real.summable_one_div_nat_add_rpow (1 : ℝ) p).mpr hp
  refine h.congr fun n => ?_
  have hb : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hbabs : |(n : ℝ) + 1| = (n : ℝ) + 1 := abs_of_pos hb
  have hrabs : |Real.rpow ((n : ℝ) + 1) p| = Real.rpow ((n : ℝ) + 1) p :=
    abs_of_pos (Real.rpow_pos_of_pos hb p)
  rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, hbabs, hrabs]
  norm_num [Nat.cast_add, Nat.cast_one]

theorem gap2 (p : ℝ) (hp : 1 < p) :
    Summable (fun j : ℕ => |rawTerm p j|) := by
  have hp0 : 0 ≤ p := le_trans (by norm_num) hp.le
  have hdom := (gap1 p hp).mul_left (Real.rpow 2 p)
  refine hdom.of_nonneg_of_le (fun j => abs_nonneg _) fun j => ?_
  have hbaseAbs :
      |(-1 : ℝ) ^ j / Real.rpow (j + 1) p| = 1 / Real.rpow (j + 1) p := by
    have hd : 0 < Real.rpow ((j : ℝ) + 1) p :=
      Real.rpow_pos_of_pos (by positivity) p
    rw [abs_div]
    simp only [abs_pow, abs_neg, abs_one, one_pow]
    rw [abs_of_pos hd]
  rw [hbaseAbs]
  have hInv (d : ℕ) (hd : 0 < d) (hjd : j + 1 ≤ 2 * d) :
      1 / Real.rpow d p ≤ Real.rpow 2 p * (1 / Real.rpow (j + 1) p) := by
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd
    have hx : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) / 2 := by positivity
    have hxle : (((j + 1 : ℕ) : ℝ) / 2) ≤ (d : ℝ) := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
      exact_mod_cast (by simpa [mul_comm] using hjd)
    have hrle :
        Real.rpow (((j + 1 : ℕ) : ℝ) / 2) p ≤ Real.rpow d p :=
      Real.rpow_le_rpow hx.le hxle hp0
    have hinv :
        1 / Real.rpow d p ≤ 1 / Real.rpow (((j + 1 : ℕ) : ℝ) / 2) p :=
      one_div_le_one_div_of_le (Real.rpow_pos_of_pos hx p) hrle
    calc
      1 / Real.rpow d p ≤ 1 / Real.rpow (((j + 1 : ℕ) : ℝ) / 2) p := hinv
      _ = Real.rpow 2 p * (1 / Real.rpow (j + 1) p) := by
        have hdivpow :
            Real.rpow (((j + 1 : ℕ) : ℝ) / 2) p =
              Real.rpow (j + 1) p / Real.rpow 2 p :=
          by
            convert Real.div_rpow
              (show (0 : ℝ) ≤ ((j + 1 : ℕ) : ℝ) by positivity)
              (show (0 : ℝ) ≤ 2 by norm_num) p using 1 <;>
              norm_num [Nat.cast_add, Nat.cast_one]
        rw [hdivpow, one_div_div]
        ring
  by_cases h0 : j % 3 = 0
  · have hd : 0 < 4 * (j / 3 + 1) - 3 := by omega
    have hjd : j + 1 ≤ 2 * (4 * (j / 3 + 1) - 3) := by omega
    have h := hInv (4 * (j / 3 + 1) - 3) hd hjd
    have hsub : 3 ≤ 4 * (j / 3 + 1) := by omega
    have hdcast : (((4 * (j / 3 + 1) - 3 : ℕ) : ℝ)) =
        4 * ((j / 3 : ℕ) : ℝ) + 4 - 3 := by
      rw [Nat.cast_sub hsub]
      push_cast
      ring
    rw [hdcast] at h
    have hdR : 0 < 4 * ((j / 3 : ℕ) : ℝ) + 4 - 3 := by
      rw [← hdcast]
      exact_mod_cast hd
    have hbase : 4 * (((j / 3 + 1 : ℕ) : ℝ)) - 3 =
        4 * ((j / 3 : ℕ) : ℝ) + 4 - 3 := by push_cast; ring
    have habs : |Real.rpow (4 * (((j / 3 + 1 : ℕ) : ℝ)) - 3) p| =
        Real.rpow (4 * (((j / 3 + 1 : ℕ) : ℝ)) - 3) p :=
      abs_of_pos (Real.rpow_pos_of_pos (by rw [hbase]; exact hdR) p)
    simp only [rawTerm, h0]
    rw [abs_div, abs_one, habs]
    convert h using 1 <;> rw [hbase]
  · by_cases h1 : j % 3 = 1
    · have hd : 0 < 4 * (j / 3 + 1) - 1 := by omega
      have hjd : j + 1 ≤ 2 * (4 * (j / 3 + 1) - 1) := by omega
      have h := hInv (4 * (j / 3 + 1) - 1) hd hjd
      have hsub : 1 ≤ 4 * (j / 3 + 1) := by omega
      have hdcast : (((4 * (j / 3 + 1) - 1 : ℕ) : ℝ)) =
          4 * ((j / 3 : ℕ) : ℝ) + 4 - 1 := by
        rw [Nat.cast_sub hsub]
        push_cast
        ring
      rw [hdcast] at h
      have hdR : 0 < 4 * ((j / 3 : ℕ) : ℝ) + 4 - 1 := by
        rw [← hdcast]
        exact_mod_cast hd
      have hbase : 4 * (((j / 3 + 1 : ℕ) : ℝ)) - 1 =
          4 * ((j / 3 : ℕ) : ℝ) + 4 - 1 := by push_cast; ring
      have habs : |Real.rpow (4 * (((j / 3 + 1 : ℕ) : ℝ)) - 1) p| =
          Real.rpow (4 * (((j / 3 + 1 : ℕ) : ℝ)) - 1) p :=
        abs_of_pos (Real.rpow_pos_of_pos (by rw [hbase]; exact hdR) p)
      simp only [rawTerm, h0, h1]
      rw [abs_div, abs_one, habs]
      convert h using 1 <;> rw [hbase]
    · have h2 : j % 3 = 2 := by omega
      have hd : 0 < 2 * (j / 3 + 1) := by omega
      have hjd : j + 1 ≤ 2 * (2 * (j / 3 + 1)) := by omega
      have h := hInv (2 * (j / 3 + 1)) hd hjd
      have hdcast : (((2 * (j / 3 + 1) : ℕ) : ℝ)) =
          2 * (((j / 3 : ℕ) : ℝ) + 1) := by push_cast; ring
      rw [hdcast] at h
      have hdR : 0 < 2 * (((j / 3 : ℕ) : ℝ) + 1) := by positivity
      have hbase : 2 * (((j / 3 + 1 : ℕ) : ℝ)) =
          2 * (((j / 3 : ℕ) : ℝ) + 1) := by push_cast; ring
      have habs : |Real.rpow (2 * (((j / 3 + 1 : ℕ) : ℝ))) p| =
          Real.rpow (2 * (((j / 3 + 1 : ℕ) : ℝ))) p :=
        abs_of_pos (Real.rpow_pos_of_pos (by rw [hbase]; exact hdR) p)
      simp only [rawTerm, h0, h1, h2]
      rw [abs_neg, abs_div, abs_one, habs]
      convert h using 1 <;> rw [hbase]

theorem gap3 (p : ℝ) :
    ∀ n : ℕ, 1 ≤ n →
      groupedTerm p n =
        1 / (Real.rpow (4 * n) p *
          Real.rpow (1 - 3 / (4 * (n : ℝ))) p) +
        1 / (Real.rpow (4 * n) p *
          Real.rpow (1 - 1 / (4 * (n : ℝ))) p) -
        1 / Real.rpow (2 * n) p := by
  intro n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hb3 : 0 < 1 - 3 / (4 * (n : ℝ)) := by
    have h4n : (0 : ℝ) < 4 * (n : ℝ) := by positivity
    rw [sub_pos, div_lt_one h4n]
    nlinarith
  have hb1 : 0 < 1 - 1 / (4 * (n : ℝ)) := by
    have h4n : (0 : ℝ) < 4 * (n : ℝ) := by positivity
    rw [sub_pos, div_lt_one h4n]
    nlinarith
  have hr3 :
      Real.rpow (1 - 3 / (4 * (n : ℝ))) (-p) =
        (Real.rpow (1 - 3 / (4 * (n : ℝ))) p)⁻¹ :=
    Real.rpow_neg hb3.le p
  have hr1 :
      Real.rpow (1 - 1 / (4 * (n : ℝ))) (-p) =
        (Real.rpow (1 - 1 / (4 * (n : ℝ))) p)⁻¹ :=
    Real.rpow_neg hb1.le p
  rw [groupedTerm]
  rw [hr3, hr1]
  field_simp

theorem gap4 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    (∀ n : ℕ, 1 ≤ n →
      groupedTerm p n =
        leadingTerm p n + correctionTerm p n + expansionRemainder p n) ∧
    Asymptotics.IsBigO atTop (expansionRemainder p)
      (fun n : ℕ => 1 / Real.rpow n (p + 2)) := by
  constructor
  · intro n hn
    simp [expansionRemainder]
  · exact expansionRemainder_bigO p

theorem gap5 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ¬ Summable (fun n : ℕ => leadingTerm p (n + 1)) := by
  intro hlead
  let c : ℝ :=
    1 / Real.rpow 2 p * (1 / Real.rpow 2 (p - 1) - 1)
  have hpowPos : 0 < Real.rpow 2 (p - 1) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hpowLt : Real.rpow 2 (p - 1) < 1 := by
    rw [Real.rpow_eq_pow]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hcpos : 0 < c := by
    dsimp [c]
    exact mul_pos
      (one_div_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
      (sub_pos.mpr (one_lt_one_div hpowPos hpowLt))
  have hscaled : Summable (fun n : ℕ =>
      c * (1 / Real.rpow ((n : ℝ) + 1) p)) := by
    refine hlead.congr fun n => ?_
    simp only [leadingTerm, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one]
    have hmul : Real.rpow (2 * ((n : ℝ) + 1)) p =
        Real.rpow 2 p * Real.rpow ((n : ℝ) + 1) p := by
      simpa only [Real.rpow_eq_pow] using
        Real.mul_rpow (show (0 : ℝ) ≤ 2 by norm_num)
          (show (0 : ℝ) ≤ (n : ℝ) + 1 by positivity)
    rw [hmul]
    dsimp [c]
    field_simp
  have hbase : Summable (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + 1) p) :=
    (summable_mul_left_iff hcpos.ne').mp hscaled
  linarith [one_lt_of_summable_shifted_rpow p hbase]

theorem gap6 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ¬ Summable (fun n : ℕ => groupedTerm p (n + 1)) := by
  intro hgrouped
  apply gap5 p hp₀ hp₁
  have h := (hgrouped.sub (correctionTerm_summable p hp₀)).sub
    (expansionRemainder_summable p (by linarith))
  refine h.congr fun n => ?_
  simp [expansionRemainder]

theorem gap7 (p : ℝ) (hp₀ : 0 < p) (hp₁ : p < 1) :
    ¬ Summable (fun j : ℕ => rawTerm p j) := by
  intro hraw
  have habs : Summable (fun j : ℕ => |rawTerm p j|) := by
    exact hraw.abs
  linarith [one_lt_of_summable_abs_rawTerm p habs]

theorem gap8 (p : ℝ) (hp : p = 1) :
    (∀ n : ℕ, 1 ≤ n →
      groupedTerm p n = correctionTerm p n + expansionRemainder p n) ∧
    Asymptotics.IsBigO atTop (expansionRemainder p)
      (fun n : ℕ => 1 / Real.rpow n 3) := by
  subst p
  constructor
  · intro n hn
    simp [expansionRemainder, leadingTerm]
  · convert expansionRemainder_bigO 1 using 1
    norm_num

theorem gap9 (p : ℝ) (hp : p = 1) :
    Summable (fun n : ℕ => groupedTerm p (n + 1)) := by
  subst p
  have h := (correctionTerm_summable 1 (by norm_num)).add
    (expansionRemainder_summable 1 (by norm_num))
  refine h.congr fun n => ?_
  simp [expansionRemainder, leadingTerm]

private theorem sum_range_three (f : ℕ → ℝ) (N : ℕ) :
    (∑ j ∈ Finset.range (3 * N), f j) =
      ∑ n ∈ Finset.range N, (f (3 * n) + f (3 * n + 1) + f (3 * n + 2)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [show 3 * (N + 1) = 3 * N + 3 by omega,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, ih]
      ring

private theorem rawTerm_one_block (n : ℕ) :
    rawTerm 1 (3 * n) + rawTerm 1 (3 * n + 1) + rawTerm 1 (3 * n + 2) =
      groupedTerm 1 (n + 1) := by
  have hdiv0 : (3 * n) / 3 = n := by omega
  have hdiv1 : (3 * n + 1) / 3 = n := by omega
  have hdiv2 : (3 * n + 2) / 3 = n := by omega
  have hmod0 : (3 * n) % 3 = 0 := by omega
  have hmod1 : (3 * n + 1) % 3 = 1 := by omega
  have hmod2 : (3 * n + 2) % 3 = 2 := by omega
  have hden0 : 4 * (n + 1) - 3 = 4 * n + 1 := by omega
  have hden1 : 4 * (n + 1) - 1 = 4 * n + 3 := by omega
  rw [gap3 1 (n + 1) (by omega)]
  simp [rawTerm, hdiv0, hdiv1, hdiv2, hmod0, hmod1, hmod2,
    hden0, hden1]
  field_simp
  ring

private theorem rawTerm_one_sum_three (N : ℕ) :
    (∑ j ∈ Finset.range (3 * N), rawTerm 1 j) =
      ∑ n ∈ Finset.range N, groupedTerm 1 (n + 1) := by
  rw [sum_range_three]
  exact Finset.sum_congr rfl fun n _ => rawTerm_one_block n

theorem gap10 (p : ℝ) (hp : p = 1) :
    ProofGap.SeriesConverges (fun j : ℕ => rawTerm p j) := by
  subst p
  let r : ℕ → ℝ := fun N =>
    if N % 3 = 0 then 0
    else if N % 3 = 1 then rawTerm 1 (3 * (N / 3))
    else rawTerm 1 (3 * (N / 3)) + rawTerm 1 (3 * (N / 3) + 1)
  have hsum (N : ℕ) :
      (∑ j ∈ Finset.range N, rawTerm 1 j) =
        (∑ n ∈ Finset.range (N / 3), groupedTerm 1 (n + 1)) + r N := by
    have hcases : N % 3 = 0 ∨ N % 3 = 1 ∨ N % 3 = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · have hN : N = 3 * (N / 3) := by omega
      rw [hN, rawTerm_one_sum_three]
      simp [r]
    · have hN : N = 3 * (N / 3) + 1 := by omega
      have hq : (3 * (N / 3) + 1) / 3 = N / 3 := by omega
      rw [hN, Finset.sum_range_succ, rawTerm_one_sum_three]
      simp [r, hq]
    · have hN : N = 3 * (N / 3) + 2 := by omega
      have hq : (3 * (N / 3) + 2) / 3 = N / 3 := by omega
      rw [hN, Finset.sum_range_succ, Finset.sum_range_succ,
        rawTerm_one_sum_three]
      simp [r, hq, add_assoc]
  have hbase : Tendsto (fun m : ℕ => (1 / ((m : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h4q : Tendsto (fun N : ℕ => 4 * (N / 3)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨3 * b, fun N hN => ?_⟩
    omega
  have h4q2 : Tendsto (fun N : ℕ => 4 * (N / 3) + 2) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨3 * b, fun N hN => ?_⟩
    omega
  have ha : Tendsto (fun N : ℕ => rawTerm 1 (3 * (N / 3))) atTop (𝓝 0) := by
    refine (hbase.comp h4q).congr' (Filter.Eventually.of_forall fun N => ?_)
    have hdiv : (3 * (N / 3)) / 3 = N / 3 := by omega
    have hmod : (3 * (N / 3)) % 3 = 0 := by omega
    have hden : 4 * (N / 3 + 1) - 3 = 4 * (N / 3) + 1 := by omega
    simp [rawTerm, hdiv, hmod, hden]
    ring
  have hb : Tendsto (fun N : ℕ => rawTerm 1 (3 * (N / 3) + 1)) atTop (𝓝 0) := by
    refine (hbase.comp h4q2).congr' (Filter.Eventually.of_forall fun N => ?_)
    have hdiv : (3 * (N / 3) + 1) / 3 = N / 3 := by omega
    have hmod : (3 * (N / 3) + 1) % 3 = 1 := by omega
    have hden : 4 * (N / 3 + 1) - 1 = 4 * (N / 3) + 3 := by omega
    simp [rawTerm, hdiv, hmod, hden]
    ring
  have hr : Tendsto r atTop (𝓝 0) := by
    dsimp [r]
    have hab : Tendsto
        (fun N : ℕ => rawTerm 1 (3 * (N / 3)) + rawTerm 1 (3 * (N / 3) + 1))
        atTop (𝓝 0) := by
      simpa using ha.add hb
    exact tendsto_const_nhds.if' (ha.if' hab)
  let L : ℝ := ∑' n : ℕ, groupedTerm 1 (n + 1)
  have hgnorm : Summable (fun n : ℕ => ‖groupedTerm 1 (n + 1)‖) := by
    simpa only [Real.norm_eq_abs] using (gap9 1 rfl).abs
  have hG : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, groupedTerm 1 (n + 1))
      atTop (𝓝 L) := by
    exact (hasSum_iff_tendsto_nat_of_summable_norm hgnorm).mp (gap9 1 rfl).hasSum
  have hq : Tendsto (fun N : ℕ => N / 3) atTop atTop :=
    le_of_eq (map_div_atTop_eq_nat 3 (by omega))
  have hGq := hG.comp hq
  have htotal : Tendsto
      (fun N : ℕ =>
        (∑ n ∈ Finset.range (N / 3), groupedTerm 1 (n + 1)) + r N)
      atTop (𝓝 (L + 0)) := hGq.add hr
  have hraw : Tendsto
      (fun N : ℕ => ∑ j ∈ Finset.range N, rawTerm 1 j)
      atTop (𝓝 L) := by
    simpa only [add_zero] using
      htotal.congr' (Filter.Eventually.of_forall fun N => (hsum N).symm)
  exact seriesConverges_of_tendsto_sum_range ⟨L, hraw⟩

theorem gap11 (p : ℝ) (hp : p = 1) :
    ¬ Summable (fun j : ℕ => |rawTerm p j|) := by
  subst p
  intro habs
  linarith [one_lt_of_summable_abs_rawTerm 1 habs]

theorem gap12 (p : ℝ) (hp : p = 1) :
    ConditionallySummable (fun j : ℕ => rawTerm p j) := by
  exact ⟨gap10 p hp, gap11 p hp⟩

theorem gap13 (p : ℝ) (hp : p ≤ 0) :
    ¬ Summable (fun j : ℕ => rawTerm p j) := by
  intro hraw
  have habs : Summable (fun j : ℕ => |rawTerm p j|) := by
    exact hraw.abs
  linarith [one_lt_of_summable_abs_rawTerm p habs]

end

end ProofGap.Exercise2694
