import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Topology.Algebra.InfiniteSum.Basic

namespace ProofGap.Exercise3104

noncomputable section

open Filter
open scoped BigOperators Topology

def stirlingBase (n : ℕ) : ℝ :=
  Real.rpow n ((n : ℝ) + 1 / 2)

def a (n : ℕ) : ℝ :=
  (Nat.factorial n : ℝ) * Real.exp n / stirlingBase n

def powerStep (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (n : ℝ)) ((n : ℝ) + 1 / 2)

def upperExponent (n : ℕ) : ℝ :=
  1 + 1 / (12 * (n : ℝ) * (n + 1))

def logExpansion (n : ℕ) : ℝ :=
  (2 / (2 * (n : ℝ) + 1)) *
    ∑' j : ℕ,
      1 / (((2 * j + 1 : ℕ) : ℝ) * (2 * (n : ℝ) + 1) ^ (2 * j))

def corrected (n : ℕ) : ℝ :=
  a n * Real.exp (-1 / (12 * (n : ℝ)))

def StrictlyDecreasingFromOne (u : ℕ → ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → u (n + 1) < u n

def BoundedBelowFromOne (u : ℕ → ℝ) : Prop :=
  ∃ b : ℝ, ∀ n : ℕ, 1 ≤ n → b ≤ u n

def stirlingFormula (A : ℝ) (n : ℕ) (θ : ℝ) : Prop :=
  (Nat.factorial n : ℝ) =
    A * Real.rpow n ((n : ℝ) + 1 / 2) * Real.exp (-(n : ℝ)) *
      Real.exp (θ / (12 * (n : ℝ)))

def wallisSequence (n : ℕ) : ℝ :=
  (1 / (2 * (n : ℝ) + 1)) *
    ((2 : ℝ) ^ (2 * n) * (Nat.factorial n : ℝ) ^ 2 /
      (Nat.factorial (2 * n) : ℝ)) ^ 2

theorem gap1 :
    ∀ n : ℕ, 1 ≤ n →
      a n / a (n + 1) = powerStep n / Real.exp 1 := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hn1pos : (0 : ℝ) < n + 1 := by positivity
  have hbase :
      1 + 1 / (n : ℝ) = ((n : ℝ) + 1) / (n : ℝ) := by
    field_simp
  have hsucc :
      stirlingBase (n + 1) =
        ((n : ℝ) + 1) *
          Real.rpow ((n : ℝ) + 1) ((n : ℝ) + 1 / 2) := by
    unfold stirlingBase
    push_cast
    simp only [Real.rpow_eq_pow]
    rw [show (n : ℝ) + 1 + 1 / 2 = ((n : ℝ) + 1 / 2) + 1 by ring,
      Real.rpow_add_one hn1pos.ne']
    ring
  have hquot :
      Real.rpow (((n : ℝ) + 1) / (n : ℝ)) ((n : ℝ) + 1 / 2) =
        Real.rpow ((n : ℝ) + 1) ((n : ℝ) + 1 / 2) /
          Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2) := by
    simp only [Real.rpow_eq_pow]
    exact Real.div_rpow hn1pos.le hnpos.le _
  unfold a powerStep
  rw [hsucc]
  unfold stirlingBase
  rw [hbase, hquot, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, Real.exp_add]
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hexpn : Real.exp (n : ℝ) ≠ 0 := Real.exp_ne_zero _
  have hexp1 : Real.exp 1 ≠ 0 := Real.exp_ne_zero _
  have hrn :
      Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  have hrn1 :
      Real.rpow ((n : ℝ) + 1) ((n : ℝ) + 1 / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hn1pos _).ne'
  field_simp [hfact, hexpn, hexp1, hrn, hrn1]

theorem gap2 :
    ∀ n : ℕ, 1 ≤ n →
      Real.log ((n + 1 : ℕ) / (n : ℝ)) = logExpansion n := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hsum := (Real.hasSum_log_one_add_inv hnpos).tsum_eq
  have harg : ((n + 1 : ℕ) : ℝ) / (n : ℝ) = 1 + (n : ℝ)⁻¹ := by
    push_cast
    field_simp
  rw [harg, ← hsum]
  unfold logExpansion
  rw [← tsum_mul_left]
  apply tsum_congr
  intro j
  have hden : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  push_cast
  rw [one_div_pow]
  field_simp [hden]
  ring

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n →
      1 < ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ)) := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hlog :=
    Real.lt_log_one_add_of_pos (show 0 < 1 / (n : ℝ) by positivity)
  have hfac : 0 < (n : ℝ) + 1 / 2 := by positivity
  have hmul := mul_lt_mul_of_pos_left hlog hfac
  have hid :
      ((n : ℝ) + 1 / 2) *
          (2 * (1 / (n : ℝ)) / (1 / (n : ℝ) + 2)) = 1 := by
    field_simp
    ring
  rwa [hid] at hmul

theorem gap4 :
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ)) <
        upperExponent n := by
  intro n hn
  have hnpos : (0 : ℝ) < n := by positivity
  let d : ℝ := 2 * (n : ℝ) + 1
  let z : ℝ := 1 / d ^ 2
  let f : ℕ → ℝ := fun j =>
    1 / (((2 * j + 1 : ℕ) : ℝ) * d ^ (2 * j))
  let g : ℕ → ℝ := fun k => (z / 3) * z ^ k
  have hdpos : 0 < d := by dsimp [d]; positivity
  have hzpos : 0 < z := by dsimp [z]; positivity
  have hzlt : z < 1 := by
    dsimp [z]
    rw [div_lt_one (sq_pos_of_pos hdpos)]
    nlinarith
  have hznonneg : 0 ≤ z := hzpos.le
  have hgeom : Summable (fun k : ℕ => z ^ k) :=
    (hasSum_geometric_of_lt_one hznonneg hzlt).summable
  have hf_eq (j : ℕ) :
      f j = (1 / (((2 * j + 1 : ℕ) : ℝ))) * z ^ j := by
    dsimp [f, z]
    rw [one_div_pow]
    have hd0 : d ≠ 0 := hdpos.ne'
    field_simp [hd0]
    ring
  have hfnonneg : ∀ j : ℕ, 0 ≤ f j := by
    intro j
    rw [hf_eq]
    positivity
  have hfle : ∀ j : ℕ, f j ≤ z ^ j := by
    intro j
    rw [hf_eq]
    have hcoef : 1 / (((2 * j + 1 : ℕ) : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]
      norm_cast
      omega
    exact mul_le_of_le_one_left (pow_nonneg hznonneg _) hcoef
  have hfsum : Summable f :=
    Summable.of_nonneg_of_le hfnonneg hfle hgeom
  have htail_le : ∀ k : ℕ, f (k + 1) ≤ g k := by
    intro k
    rw [hf_eq]
    dsimp [g]
    have hcoef :
        1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) ≤ 1 / 3 := by
      gcongr
      norm_cast
      omega
    rw [pow_succ]
    calc
      1 / (((2 * (k + 1) + 1 : ℕ) : ℝ)) * (z ^ k * z)
          ≤ (1 / 3) * (z ^ k * z) :=
        mul_le_mul_of_nonneg_right hcoef
          (mul_nonneg (pow_nonneg hznonneg _) hznonneg)
      _ = z / 3 * z ^ k := by ring
  have htail_strict : f (1 + 1) < g 1 := by
    rw [hf_eq]
    dsimp [g]
    norm_num
    nlinarith [sq_pos_of_pos hzpos]
  have hgsum : Summable g := by
    dsimp [g]
    exact hgeom.mul_left (z / 3)
  have htail :
      (∑' k : ℕ, f (k + 1)) < ∑' k : ℕ, g k :=
    (hfsum.comp_injective Nat.succ_injective).tsum_lt_tsum
      htail_le htail_strict hgsum
  have hgsum_value : (∑' k : ℕ, g k) = (z / 3) / (1 - z) := by
    exact ((hasSum_geometric_of_lt_one hznonneg hzlt).mul_left (z / 3)).tsum_eq
  have hmajor :
      (z / 3) / (1 - z) =
        1 / (12 * (n : ℝ) * (n + 1)) := by
    dsimp [z, d]
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    have hn10 : (n : ℝ) + 1 ≠ 0 := by positivity
    have hdiff : (2 * (n : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
      nlinarith
    field_simp [hdiff, hn0, hn10]
    ring
  have hsplit := hfsum.sum_add_tsum_nat_add 1
  have hfzero : f 0 = 1 := by
    dsimp [f]
    norm_num
  have hfull :
      (∑' j : ℕ, f j) <
        1 + 1 / (12 * (n : ℝ) * (n + 1)) := by
    simp only [Finset.sum_range_one, hfzero] at hsplit
    calc
      (∑' j : ℕ, f j) = 1 + ∑' k : ℕ, f (k + 1) := hsplit.symm
      _ < 1 + ∑' k : ℕ, g k := by linarith
      _ = 1 + 1 / (12 * (n : ℝ) * (n + 1)) := by
        rw [hgsum_value, hmajor]
  have harg :
      1 + 1 / (n : ℝ) = ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    push_cast
    field_simp
  rw [harg, gap2 n hn]
  unfold logExpansion upperExponent
  have hcoef :
      ((n : ℝ) + 1 / 2) * (2 / (2 * (n : ℝ) + 1)) = 1 := by
    field_simp
  rw [← mul_assoc, hcoef, one_mul]
  simpa [f, d] using hfull

theorem gap5 :
    ∀ n : ℕ, 1 ≤ n →
      1 < ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ)) := by
  exact gap3

theorem gap6 :
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℝ) + 1 / 2) * Real.log (1 + 1 / (n : ℝ)) <
        upperExponent n := by
  exact gap4

theorem gap7 :
    ∀ n : ℕ, 1 ≤ n → 1 < upperExponent n := by
  intro n hn
  unfold upperExponent
  have hnpos : (0 : ℝ) < n := by positivity
  have hden : 0 < 12 * (n : ℝ) * (n + 1) := by positivity
  have hinv : 0 < 1 / (12 * (n : ℝ) * (n + 1)) := one_div_pos.mpr hden
  linarith

theorem gap8 :
    ∀ n : ℕ, 1 ≤ n → Real.exp 1 < powerStep n := by
  intro n hn
  have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
  unfold powerStep
  rw [Real.rpow_eq_pow]
  rw [← Real.exp_log (Real.rpow_pos_of_pos hbase _), Real.exp_lt_exp,
    Real.log_rpow hbase]
  exact gap3 n hn

theorem gap9 :
    ∀ n : ℕ, 1 ≤ n →
      powerStep n < Real.exp (upperExponent n) := by
  intro n hn
  have hbase : 0 < 1 + 1 / (n : ℝ) := by positivity
  unfold powerStep
  rw [Real.rpow_eq_pow]
  rw [← Real.exp_log (Real.rpow_pos_of_pos hbase _), Real.exp_lt_exp,
    Real.log_rpow hbase]
  exact gap4 n hn

theorem gap10 :
    ∀ n : ℕ, 1 ≤ n →
      Real.exp 1 < Real.exp (upperExponent n) := by
  intro n hn
  exact Real.exp_lt_exp.mpr (gap7 n hn)

theorem gap11 :
    ∀ n : ℕ, 1 ≤ n →
      Real.exp 1 < powerStep n ∧
        powerStep n < Real.exp (upperExponent n) := by
  exact fun n hn => ⟨gap8 n hn, gap9 n hn⟩

theorem gap12 :
    ∀ n : ℕ, 1 ≤ n → 0 < a (n + 1) := by
  intro n hn
  unfold a stirlingBase
  apply div_pos
  · exact mul_pos (by positivity) (Real.exp_pos _)
  · exact Real.rpow_pos_of_pos (by positivity) _

theorem gap13 :
    ∀ n : ℕ, 1 ≤ n → a (n + 1) < a n := by
  intro n hn
  have hanext : 0 < a (n + 1) := gap12 n hn
  have hratio :
      1 < a n / a (n + 1) := by
    rw [gap1 n hn]
    exact (lt_div_iff₀ (Real.exp_pos 1)).2 (by
      simpa using gap8 n hn)
  have hid : a n / a (n + 1) * a (n + 1) = a n := by
    field_simp [hanext.ne']
  nlinarith [mul_lt_mul_of_pos_right hratio hanext]

theorem gap14 :
    ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  intro n hn
  unfold a stirlingBase
  apply div_pos
  · exact mul_pos (by positivity) (Real.exp_pos _)
  · exact Real.rpow_pos_of_pos (by positivity) _

theorem gap15 :
    ∀ n : ℕ, 1 ≤ n → corrected n < corrected (n + 1) := by
  intro n hn
  let u : ℝ := 1 / (12 * (n : ℝ) * (n + 1))
  have hnpos : (0 : ℝ) < n := by positivity
  have hnextpos : 0 < corrected (n + 1) := by
    unfold corrected
    exact mul_pos (gap12 n hn) (Real.exp_pos _)
  have hexpdiff :
      -1 / (12 * (n : ℝ)) + 1 / (12 * ((n + 1 : ℕ) : ℝ)) = -u := by
    dsimp [u]
    push_cast
    field_simp
    ring
  have hratio :
      corrected n / corrected (n + 1) =
        (powerStep n / Real.exp 1) * Real.exp (-u) := by
    unfold corrected
    rw [← div_mul_div_comm, gap1 n hn, ← Real.exp_sub]
    rw [show -1 / (12 * (n : ℝ)) - -1 / (12 * ((n + 1 : ℕ) : ℝ)) =
      -1 / (12 * (n : ℝ)) + 1 / (12 * ((n + 1 : ℕ) : ℝ)) by ring,
      hexpdiff]
  have hless :
      (powerStep n / Real.exp 1) * Real.exp (-u) < 1 := by
    have hs := mul_lt_mul_of_pos_right (gap9 n hn) (Real.exp_pos (-1 - u))
    have hleft :
        (powerStep n / Real.exp 1) * Real.exp (-u) =
          powerStep n * Real.exp (-1 - u) := by
      rw [show -1 - u = -1 + -u by ring, Real.exp_add, Real.exp_neg]
      field_simp [Real.exp_ne_zero (1 : ℝ)]
      rw [mul_assoc]
      rw [← Real.exp_add]
      norm_num
    have hright :
        Real.exp (upperExponent n) * Real.exp (-1 - u) = 1 := by
      unfold upperExponent
      change Real.exp (1 + u) * Real.exp (-1 - u) = 1
      rw [← Real.exp_add]
      norm_num
    rw [← hleft, hright] at hs
    exact hs
  rw [← hratio] at hless
  have hm := mul_lt_mul_of_pos_right hless hnextpos
  have hid : corrected n / corrected (n + 1) * corrected (n + 1) =
      corrected n := by
    field_simp [hnextpos.ne']
  nlinarith

theorem gap16 : StrictlyDecreasingFromOne a := by
  exact gap13

theorem gap17 : BoundedBelowFromOne a := by
  refine ⟨0, ?_⟩
  intro n hn
  exact (gap14 n hn).le

theorem gap18 :
    ∃ A : ℝ, Tendsto a atTop (𝓝 A) := by
  let u : ℕ → ℝ := fun n => a (n + 1)
  have huanti : Antitone u :=
    antitone_nat_of_succ_le fun n => (gap13 (n + 1) (by omega)).le
  have hlower : (0 : ℝ) ∈ lowerBounds (Set.range u) := by
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    exact (gap14 (n + 1) (by omega)).le
  refine ⟨sInf (Set.range u), ?_⟩
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  exact tendsto_atTop_ciInf huanti ⟨0, hlower⟩

theorem gap19 (A : ℝ) (ha : Tendsto a atTop (𝓝 A)) :
    Tendsto corrected atTop (𝓝 A) := by
  have hinv :
      Tendsto (fun n : ℕ => (1 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hexponent :
      Tendsto (fun n : ℕ => -1 / (12 * (n : ℝ))) atTop (𝓝 0) := by
    have h :
        Tendsto
          (fun n : ℕ => (-(1 / 12 : ℝ)) * (1 / (n : ℝ)))
          atTop (𝓝 ((-(1 / 12 : ℝ)) * 0)) :=
      tendsto_const_nhds.mul hinv
    convert h using 1 <;> norm_num
    funext n
    ring
  have hexp :
      Tendsto (fun n : ℕ => Real.exp (-1 / (12 * (n : ℝ))))
        atTop (𝓝 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hexponent
  simpa [corrected] using ha.mul hexp

theorem gap20 :
    ∃ A : ℝ,
      Tendsto a atTop (𝓝 A) ∧
      ∀ n : ℕ, 1 ≤ n →
        ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
          a n = A * Real.exp (θ / (12 * (n : ℝ))) := by
  obtain ⟨A, hA⟩ := gap18
  have haAnti : Antitone (fun k : ℕ => a (k + 1)) :=
    antitone_nat_of_succ_le fun k => (gap13 (k + 1) (by omega)).le
  have hcMono : Monotone (fun k : ℕ => corrected (k + 1)) :=
    monotone_nat_of_le_succ fun k => (gap15 (k + 1) (by omega)).le
  have hAShift :
      Tendsto (fun k : ℕ => a (k + 1)) atTop (𝓝 A) :=
    hA.comp (tendsto_add_atTop_nat 1)
  have hCShift :
      Tendsto (fun k : ℕ => corrected (k + 1)) atTop (𝓝 A) :=
    (gap19 A hA).comp (tendsto_add_atTop_nat 1)
  have hAbelow (k : ℕ) : A ≤ a (k + 1) :=
    haAnti.le_of_tendsto hAShift k
  have hCbelow (k : ℕ) : corrected (k + 1) ≤ A :=
    hcMono.ge_of_tendsto hCShift k
  have hApos : 0 < A := by
    have hc1pos : 0 < corrected 1 := by
      unfold corrected
      exact mul_pos (gap14 1 (by omega)) (Real.exp_pos _)
    have hstrict := gap15 1 (by omega)
    linarith [hCbelow 1]
  refine ⟨A, hA, ?_⟩
  intro n hn
  have hnpos : (0 : ℝ) < n := by positivity
  have hanpos : 0 < a n := gap14 n hn
  have hAn : A < a n :=
    lt_of_le_of_lt (hAbelow n) (gap13 n hn)
  have hCn : corrected n < A :=
    lt_of_lt_of_le (gap15 n hn) (hCbelow n)
  let c : ℝ := 1 / (12 * (n : ℝ))
  let θ : ℝ := 12 * (n : ℝ) * Real.log (a n / A)
  have hratio_gt : 1 < a n / A :=
    (lt_div_iff₀ hApos).2 (by simpa using hAn)
  have hlogpos : 0 < Real.log (a n / A) :=
    Real.log_pos hratio_gt
  have hratio_lt : a n / A < Real.exp c := by
    have hcpos : 0 < Real.exp c := Real.exp_pos _
    have hmul := mul_lt_mul_of_pos_right hCn hcpos
    have hleft :
        corrected n * Real.exp c = a n := by
      unfold corrected
      rw [mul_assoc, ← Real.exp_add]
      have hzero : -1 / (12 * (n : ℝ)) + c = 0 := by
        dsimp [c]
        ring
      rw [hzero, Real.exp_zero, mul_one]
    have hright : A * Real.exp c = A * Real.exp c := rfl
    rw [hleft, hright] at hmul
    exact (div_lt_iff₀ hApos).2 (by simpa [mul_comm] using hmul)
  have hloglt : Real.log (a n / A) < c := by
    have h :=
      Real.strictMonoOn_log
        (div_pos hanpos hApos) (Real.exp_pos c) hratio_lt
    simpa using h
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hθlt : θ < 1 := by
    dsimp [θ]
    dsimp [c] at hloglt
    have hm := mul_lt_mul_of_pos_left hloglt
      (show 0 < 12 * (n : ℝ) by positivity)
    field_simp at hm
    exact hm
  refine ⟨θ, hθpos, hθlt, ?_⟩
  have hθ :
      θ / (12 * (n : ℝ)) = Real.log (a n / A) := by
    dsimp [θ]
    field_simp
  rw [hθ, Real.exp_log (div_pos hanpos hApos)]
  field_simp [hApos.ne']

theorem gap21 :
    ∃ A : ℝ, ∀ n : ℕ, 1 ≤ n →
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ stirlingFormula A n θ := by
  obtain ⟨A, hA, hθ⟩ := gap20
  refine ⟨A, ?_⟩
  intro n hn
  obtain ⟨θ, hθpos, hθlt, haeq⟩ := hθ n hn
  refine ⟨θ, hθpos, hθlt, ?_⟩
  unfold stirlingFormula
  unfold a at haeq
  have hnpos : (0 : ℝ) < n := by positivity
  have hbase : stirlingBase n ≠ 0 := by
    unfold stirlingBase
    exact (Real.rpow_pos_of_pos hnpos _).ne'
  have hexpn : Real.exp (n : ℝ) ≠ 0 := Real.exp_ne_zero _
  field_simp [hbase] at haeq
  unfold stirlingBase at haeq
  calc
    (Nat.factorial n : ℝ) =
        ((Nat.factorial n : ℝ) * Real.exp (n : ℝ)) *
          Real.exp (-(n : ℝ)) := by
      rw [mul_assoc, ← Real.exp_add]
      norm_num
    _ = (A * Real.exp (θ / (12 * (n : ℝ))) *
          Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2)) *
          Real.exp (-(n : ℝ)) := by
      rw [haeq]
      ring
    _ = A * Real.rpow n ((n : ℝ) + 1 / 2) *
          Real.exp (-(n : ℝ)) *
          Real.exp (θ / (12 * (n : ℝ))) := by ring

theorem gap22 :
    Tendsto wallisSequence atTop (𝓝 (Real.pi / 2)) := by
  apply Real.Wallis.tendsto_W_nhds_pi_div_two.congr'
  exact Eventually.of_forall fun n => by
    rw [Real.Wallis.W_eq_factorial_ratio]
    unfold wallisSequence
    rw [div_pow, mul_pow]
    have hpow : ((2 : ℝ) ^ (2 * n)) ^ 2 = (2 : ℝ) ^ (4 * n) := by
      rw [← pow_mul]
      congr 1
      omega
    rw [hpow]
    have hfact : (Nat.factorial (2 * n) : ℝ) ≠ 0 := by positivity
    have hlin : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
    field_simp [hfact, hlin]

private lemma a_eq_sqrt_two_mul_stirlingSeq (n : ℕ) (hn : 1 ≤ n) :
    a n = Real.sqrt 2 * Stirling.stirlingSeq n := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hbase :
      stirlingBase n = (n : ℝ) ^ n * Real.sqrt (n : ℝ) := by
    unfold stirlingBase
    simp only [Real.rpow_eq_pow]
    rw [Real.rpow_add hnpos, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hsqrt :
      Real.sqrt (2 * (n : ℝ)) =
        Real.sqrt 2 * Real.sqrt (n : ℝ) := by
    exact Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2) _
  have hexp :
      Real.exp (n : ℝ) = (Real.exp 1) ^ n := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  unfold a Stirling.stirlingSeq
  rw [hbase, hsqrt, hexp, div_pow]
  have hfact : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hsqrtn : Real.sqrt (n : ℝ) ≠ 0 := by positivity
  have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
  have hexp1 : Real.exp 1 ≠ 0 := Real.exp_ne_zero _
  have hnpow : (n : ℝ) ^ n ≠ 0 := pow_ne_zero _ hnpos.ne'
  field_simp [hfact, hsqrtn, hsqrt2, hexp1, hnpow]

private lemma a_eq_of_stirlingFormula
    (A : ℝ) (n : ℕ) (θ : ℝ) (hn : 1 ≤ n)
    (hf : stirlingFormula A n θ) :
    a n = A * Real.exp (θ / (12 * (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by positivity
  have hrpow :
      Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  unfold stirlingFormula at hf
  unfold a
  rw [hf]
  have hbaseval :
      stirlingBase n =
        Real.rpow (n : ℝ) ((n : ℝ) + 1 / 2) := rfl
  rw [hbaseval]
  have hden :
      (n : ℝ) ^ (((n : ℝ) * 2 + 1) / 2 : ℝ) ≠ 0 :=
    (Real.rpow_pos_of_pos hnpos _).ne'
  field_simp [hden]
  rw [mul_assoc, ← Real.exp_add]
  norm_num

theorem gap23 (A : ℝ)
    (hformula :
      ∀ n : ℕ, 1 ≤ n →
        ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ stirlingFormula A n θ)
    (hwallis : Tendsto wallisSequence atTop (𝓝 (Real.pi / 2))) :
    Real.pi / 2 = A ^ 2 / 4 := by
  choose θ hθpos hθlt hθformula using
    fun k : ℕ => hformula (k + 1) (by omega)
  have haeq (k : ℕ) :
      a (k + 1) =
        A * Real.exp (θ k / (12 * ((k + 1 : ℕ) : ℝ))) :=
    a_eq_of_stirlingFormula A (k + 1) (θ k) (by omega) (hθformula k)
  have hApos : 0 < A := by
    have hapos : 0 < a 1 := gap14 1 (by omega)
    have hexppos :
        0 < Real.exp (θ 0 / (12 * (((0 + 1 : ℕ) : ℝ)))) :=
      Real.exp_pos _
    rw [haeq 0] at hapos
    exact pos_of_mul_pos_left hapos hexppos.le
  have hupper :
      Tendsto (fun k : ℕ => 1 / (12 * ((k + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    have h0 :
        Tendsto (fun k : ℕ => 1 / ((k + 1 : ℕ) : ℝ))
          atTop (𝓝 0) :=
      by
        simpa [Nat.cast_add, Nat.cast_one] using
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    have h :
        Tendsto
          (fun k : ℕ => (1 / 12 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ)))
          atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul h0
    convert h using 1 <;> norm_num
    funext k
    ring
  have hexponent :
      Tendsto
        (fun k : ℕ => θ k / (12 * ((k + 1 : ℕ) : ℝ)))
        atTop (𝓝 0) := by
    apply squeeze_zero'
      (g := fun k : ℕ => 1 / (12 * ((k + 1 : ℕ) : ℝ)))
    · exact Eventually.of_forall fun k => by
        exact div_nonneg (hθpos k).le (by positivity)
    · exact Eventually.of_forall fun k => by
        exact (div_le_div_iff_of_pos_right (by positivity)).2 (hθlt k).le
    · exact hupper
  have hexp :
      Tendsto
        (fun k : ℕ =>
          Real.exp (θ k / (12 * ((k + 1 : ℕ) : ℝ))))
        atTop (𝓝 1) := by
    simpa using Real.continuous_exp.continuousAt.tendsto.comp hexponent
  have haShift : Tendsto (fun k : ℕ => a (k + 1)) atTop (𝓝 A) := by
    have hprod :
        Tendsto
          (fun k : ℕ =>
            A * Real.exp (θ k / (12 * ((k + 1 : ℕ) : ℝ))))
          atTop (𝓝 (A * 1)) :=
      tendsto_const_nhds.mul hexp
    simpa using hprod.congr'
      (Eventually.of_forall fun k => (haeq k).symm)
  have hknown :
      Tendsto (fun k : ℕ => a (k + 1))
        atTop (𝓝 (Real.sqrt 2 * Real.sqrt Real.pi)) := by
    have hs :=
      Stirling.tendsto_stirlingSeq_sqrt_pi.comp
        (tendsto_add_atTop_nat 1)
    have hp :
        Tendsto
          (fun k : ℕ =>
            Real.sqrt 2 * Stirling.stirlingSeq (k + 1))
          atTop (𝓝 (Real.sqrt 2 * Real.sqrt Real.pi)) :=
      tendsto_const_nhds.mul hs
    apply hp.congr'
    exact Eventually.of_forall fun k =>
      (a_eq_sqrt_two_mul_stirlingSeq (k + 1) (by omega)).symm
  have hAeq : A = Real.sqrt 2 * Real.sqrt Real.pi :=
    tendsto_nhds_unique haShift hknown
  have hsqrt2 : (Real.sqrt 2) ^ 2 = 2 := by
    simpa using Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqrtpi : (Real.sqrt Real.pi) ^ 2 = Real.pi := by
    simpa using Real.sq_sqrt Real.pi_pos.le
  rw [hAeq]
  nlinarith [sq_nonneg (Real.sqrt 2 * Real.sqrt Real.pi)]

theorem gap24 (A : ℝ) (hA : Real.pi / 2 = A ^ 2 / 4) :
    A ^ 2 = 2 * Real.pi := by
  linarith

theorem gap25 (A : ℝ) (hApos : 0 < A) (hA : A ^ 2 = 2 * Real.pi) :
    A = Real.sqrt (2 * Real.pi) := by
  have hnonneg : 0 ≤ 2 * Real.pi := by positivity
  have hsqrt : (Real.sqrt (2 * Real.pi)) ^ 2 = 2 * Real.pi := by
    simpa using Real.sq_sqrt hnonneg
  have hsqrtnonneg : 0 ≤ Real.sqrt (2 * Real.pi) := Real.sqrt_nonneg _
  nlinarith

theorem gap26 :
    ∀ n : ℕ, 1 ≤ n →
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        stirlingFormula (Real.sqrt (2 * Real.pi)) n θ := by
  obtain ⟨A, hformula⟩ := gap21
  have hApi : Real.pi / 2 = A ^ 2 / 4 :=
    gap23 A hformula gap22
  have hAsq : A ^ 2 = 2 * Real.pi :=
    gap24 A hApi
  have hApos : 0 < A := by
    obtain ⟨θ, hθpos, hθlt, hf⟩ := hformula 1 (by omega)
    unfold stirlingFormula at hf
    norm_num at hf
    have hfac : 0 < Real.exp (-1) * Real.exp (θ / 12) := by
      positivity
    have hprod : 0 < A * (Real.exp (-1) * Real.exp (θ / 12)) := by
      rw [← mul_assoc, ← hf]
      norm_num
    exact pos_of_mul_pos_left hprod hfac.le
  have hAeq : A = Real.sqrt (2 * Real.pi) :=
    gap25 A hApos hAsq
  intro n hn
  obtain ⟨θ, hθpos, hθlt, hf⟩ := hformula n hn
  exact ⟨θ, hθpos, hθlt, by simpa [← hAeq] using hf⟩

theorem gap27 :
    ∃ A : ℝ,
      A ≠ 0 ∧
      Tendsto a atTop (𝓝 A) ∧
      A = Real.sqrt (2 * Real.pi) := by
  let A : ℝ := Real.sqrt 2 * Real.sqrt Real.pi
  have hAlim : Tendsto a atTop (𝓝 A) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    have hs :=
      Stirling.tendsto_stirlingSeq_sqrt_pi.comp
        (tendsto_add_atTop_nat 1)
    have hp :
        Tendsto
          (fun k : ℕ =>
            Real.sqrt 2 * Stirling.stirlingSeq (k + 1))
          atTop (𝓝 A) := by
      exact tendsto_const_nhds.mul hs
    apply hp.congr'
    exact Eventually.of_forall fun k =>
      (a_eq_sqrt_two_mul_stirlingSeq (k + 1) (by omega)).symm
  have hAeq : A = Real.sqrt (2 * Real.pi) := by
    dsimp [A]
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  refine ⟨A, ?_, hAlim, hAeq⟩
  dsimp [A]
  positivity

end

end ProofGap.Exercise3104
