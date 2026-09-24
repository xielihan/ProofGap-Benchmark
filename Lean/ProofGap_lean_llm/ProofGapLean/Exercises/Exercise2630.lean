import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic

namespace ProofGap.Exercise2630

noncomputable section

open Filter
open scoped BigOperators

def logFactorial (n : ℕ) : ℝ :=
  Real.log (Nat.factorial n : ℝ)

def term (a : ℝ) (n : ℕ) : ℝ :=
  logFactorial n / Real.rpow n a

def comparison (a : ℝ) (n : ℕ) : ℝ :=
  1 / Real.rpow n (a - 1)

def averageLog (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.Icc 1 n, Real.log k) / n

def converges (a : ℝ) : Prop :=
  Summable (fun n : ℕ => term a (n + 1))

def stirlingFormula (n : ℕ) (θ : ℝ) : Prop :=
  (Nat.factorial n : ℝ) =
    Real.sqrt (2 * Real.pi * n) * (n : ℝ) ^ n *
      Real.exp (-(n : ℝ) + θ / (12 * n))

private theorem oneDivRpowEq {x p : ℝ} (hx : 0 < x) :
    1 / Real.rpow x p = Real.rpow x (-p) := by
  calc
    1 / Real.rpow x p = (Real.rpow x p)⁻¹ := by rw [one_div]
    _ = (Real.exp (Real.log x * p))⁻¹ := by
      change (x ^ p)⁻¹ = (Real.exp (Real.log x * p))⁻¹
      rw [Real.rpow_def_of_pos hx p]
    _ = Real.exp (Real.log x * (-p)) := by
      rw [← Real.exp_neg]
      congr 1 <;> ring
    _ = Real.rpow x (-p) := by
      change Real.exp (Real.log x * (-p)) = x ^ (-p)
      rw [Real.rpow_def_of_pos hx (-p)]

private theorem rpowAddOne {x p : ℝ} (hx : 0 < x) :
    Real.rpow x (p + 1) = Real.rpow x p * x := by
  have hone : Real.rpow x (1 : ℝ) = x := by
    change x ^ (1 : ℝ) = x
    rw [Real.rpow_def_of_pos hx (1 : ℝ)]
    simpa only [mul_one, one_mul] using (Real.exp_log hx)
  calc
    Real.rpow x (p + 1) =
        Real.rpow x p * Real.rpow x (1 : ℝ) := by
      change x ^ (p + 1) = x ^ p * x ^ (1 : ℝ)
      exact Real.rpow_add hx p (1 : ℝ)
    _ = Real.rpow x p * x := by rw [hone]

private theorem shiftedRpowSummable {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => 1 / Real.rpow ((n : ℝ) + 1) p) := by
  have hexp : -p < -1 := by linarith
  have hs : Summable (fun n : ℕ => Real.rpow n (-p)) :=
    Real.summable_nat_rpow.2 hexp
  have htailNat :
      Summable (fun n : ℕ => Real.rpow (((n + 1 : ℕ) : ℝ)) (-p)) :=
    (summable_nat_add_iff 1).2 hs
  have htail :
      Summable (fun n : ℕ => Real.rpow ((n : ℝ) + 1) (-p)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using htailNat
  refine htail.congr ?_
  intro n
  have hx : 0 < (n : ℝ) + 1 := by positivity
  exact (oneDivRpowEq (p := p) hx).symm

private theorem summableLogDivNatRpow {p : ℝ} (hp : 1 < p) :
    Summable (fun n : ℕ => Real.log (n + 1) / Real.rpow (n + 1) p) := by
  let d : ℝ := (p - 1) / 2
  let q : ℝ := p - d
  have hd : 0 < d := by dsimp [d]; linarith
  have hq : 1 < q := by dsimp [q, d]; linarith
  have hs := shiftedRpowSummable (p := q) hq
  have hscaled := hs.mul_left (1 / d)
  refine hscaled.of_norm_bounded ?_
  intro n
  let x : ℝ := (n : ℝ) + 1
  have hnnonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx : 1 ≤ x := by dsimp [x]; linarith
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlognonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hrdpos : 0 < Real.rpow x d := Real.rpow_pos_of_pos hxpos d
  have hrqpos : 0 < Real.rpow x q := Real.rpow_pos_of_pos hxpos q
  have hrppos : 0 < Real.rpow x p := Real.rpow_pos_of_pos hxpos p
  have hlogr := Real.log_le_sub_one_of_pos hrdpos
  have hlogpow : Real.log (Real.rpow x d) = d * Real.log x := by
    change Real.log (x ^ d) = d * Real.log x
    exact Real.log_rpow hxpos d
  rw [hlogpow] at hlogr
  have hbound : Real.log x ≤ Real.rpow x d / d := by
    apply (le_div_iff₀ hd).2
    nlinarith
  have hpqd : p = q + d := by dsimp [q, d]; ring
  have hpow : Real.rpow x p = Real.rpow x q * Real.rpow x d := by
    rw [hpqd]
    change x ^ (q + d) = x ^ q * x ^ d
    exact Real.rpow_add hxpos q d
  change |Real.log x / Real.rpow x p| ≤
    (1 / d) * (1 / Real.rpow x q)
  rw [abs_div, abs_of_nonneg hlognonneg]
  have habsp : |Real.rpow x p| = Real.rpow x p := abs_of_pos hrppos
  rw [habsp, hpow]
  calc
    Real.log x / (Real.rpow x q * Real.rpow x d) ≤
        (Real.rpow x d / d) / (Real.rpow x q * Real.rpow x d) :=
      div_le_div_of_nonneg_right hbound (mul_pos hrqpos hrdpos).le
    _ = (1 / d) * (1 / Real.rpow x q) := by
      field_simp [ne_of_gt hd, ne_of_gt hrqpos, ne_of_gt hrdpos] <;> ring

private theorem factorialLogIcc (n : ℕ) :
    Real.log (Nat.factorial n : ℝ) =
      ∑ k ∈ Finset.Icc 1 n, Real.log k := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.factorial_succ, Nat.cast_mul]
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [ih]
      rw [Finset.sum_Icc_succ_top (by omega)]
      simp [add_comm]

private theorem logStirlingDiffLe2630 (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2)) <
      1 / (12 * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) := by
  let x : ℝ := 1 / (2 * ((m + 1 : ℕ) : ℝ) + 1)
  let r : ℝ := x ^ 2
  have hxpos : 0 < x := by dsimp [x]; positivity
  have hxlt : x < 1 := by
    dsimp [x]
    apply (div_lt_one (by positivity)).2
    have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hrnonneg : 0 ≤ r := by dsimp [r]; positivity
  have hrlt : r < 1 := by
    dsimp [r]
    nlinarith
  have hgeo0 := hasSum_geometric_of_lt_one hrnonneg hrlt
  have hgeo : HasSum
      (fun k : ℕ => (1 / 3 : ℝ) * r ^ (k + 1))
      ((1 / 3 : ℝ) * r * (1 - r)⁻¹) := by
    convert hgeo0.mul_left ((1 / 3 : ℝ) * r) using 1
    · funext k
      rw [pow_succ]
      ring
  have hseries := Stirling.log_stirlingSeq_diff_hasSum m
  have hle :
      Real.log (Stirling.stirlingSeq (m + 1)) -
          Real.log (Stirling.stirlingSeq (m + 2)) <
        (1 / 3 : ℝ) * r * (1 - r)⁻¹ := by
    apply hasSum_lt (i := 1) _ _ hseries hgeo
    · intro k
      have hdenpos : 0 < 2 * ((k + 1 : ℕ) : ℝ) + 1 := by positivity
      have hden : (3 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) + 1 := by
        have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        norm_num
        linarith
      have hcoeff :
          1 / (2 * ((k + 1 : ℕ) : ℝ) + 1) ≤ (1 / 3 : ℝ) := by
        apply (div_le_iff₀ hdenpos).2
        nlinarith
      have hrpow : 0 ≤ r ^ (k + 1) := pow_nonneg hrnonneg _
      exact mul_le_mul_of_nonneg_right hcoeff hrpow
    · dsimp [r, x]
      apply mul_lt_mul_of_pos_right (by norm_num)
      positivity
  calc
    Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2)) <
        (1 / 3 : ℝ) * r * (1 - r)⁻¹ := hle
    _ = 1 / (12 * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) := by
      have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm2 : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
      have hbase : 0 < 2 * ((m + 1 : ℕ) : ℝ) + 1 := by positivity
      have hrem : 0 < 1 - r := sub_pos.mpr hrlt
      rw [inv_eq_one_div]
      field_simp [ne_of_gt hrem]
      dsimp [r, x]
      field_simp [ne_of_gt hm1, ne_of_gt hm2, ne_of_gt hbase]
      <;> norm_num
      <;> ring

private theorem logStirlingDiffLtSub2630 (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2)) <
      1 / (12 * ((m + 1 : ℕ) : ℝ)) -
        1 / (12 * ((m + 2 : ℕ) : ℝ)) := by
  calc
    Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2)) <
        1 / (12 * ((m + 1 : ℕ) : ℝ) * ((m + 2 : ℕ) : ℝ)) :=
      logStirlingDiffLe2630 m
    _ = 1 / (12 * ((m + 1 : ℕ) : ℝ)) -
        1 / (12 * ((m + 2 : ℕ) : ℝ)) := by
      have hm1 : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
      have hm2 : 0 < ((m + 2 : ℕ) : ℝ) := by positivity
      field_simp [ne_of_gt hm1, ne_of_gt hm2]
      <;> norm_num
      <;> ring

private theorem logStirlingDiffPos2630 (m : ℕ) :
    0 < Real.log (Stirling.stirlingSeq (m + 1)) -
      Real.log (Stirling.stirlingSeq (m + 2)) := by
  have hs := Stirling.log_stirlingSeq_diff_hasSum m
  have hp : 0 < ∑' k : ℕ,
      1 / (2 * ((k + 1 : ℕ) : ℝ) + 1) *
        ((1 / (2 * ((m + 1 : ℕ) : ℝ) + 1)) ^ 2) ^ (k + 1) := by
    exact hs.summable.tsum_pos (fun k => by positivity) 0 (by positivity)
  rw [hs.tsum_eq] at hp
  exact hp

private theorem logStirlingErrorLe2630 (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt Real.pi) ≤
      1 / (12 * ((m + 1 : ℕ) : ℝ)) := by
  let f : ℕ → ℝ := fun k =>
    Real.log (Stirling.stirlingSeq (m + k + 1))
  let b : ℕ → ℝ := fun k =>
    1 / (12 * ((m + k + 1 : ℕ) : ℝ))
  have hstep : ∀ k : ℕ, f k - f (k + 1) ≤ b k - b (k + 1) := by
    intro k
    have h := (logStirlingDiffLtSub2630 (m + k)).le
    dsimp [f, b]
    convert h using 1 <;> norm_num <;> ring
  have hfinite : ∀ N : ℕ, f 0 - f N ≤ b 0 - b N := by
    intro N
    calc
      f 0 - f N = ∑ k ∈ Finset.range N, (f k - f (k + 1)) := by
        simpa using (Finset.sum_range_sub' f N).symm
      _ ≤ ∑ k ∈ Finset.range N, (b k - b (k + 1)) := by
        exact Finset.sum_le_sum fun k _ => hstep k
      _ = b 0 - b N := by
        simpa using (Finset.sum_range_sub' b N)
  have hseq : Tendsto
      (fun N : ℕ => Stirling.stirlingSeq (m + N + 1)) atTop
      (nhds (Real.sqrt Real.pi)) := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      (Stirling.tendsto_stirlingSeq_sqrt_pi.comp
        (tendsto_add_atTop_nat (m + 1)))
  have hlog : Tendsto
      (fun N : ℕ => Real.log (Stirling.stirlingSeq (m + N + 1))) atTop
      (nhds (Real.log (Real.sqrt Real.pi))) :=
    hseq.log (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  have hleft : Tendsto
      (fun N : ℕ => Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + N + 1))) atTop
      (nhds (Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Real.sqrt Real.pi))) :=
    tendsto_const_nhds.sub hlog
  apply le_of_tendsto' hleft
  intro N
  calc
    Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + N + 1)) = f 0 - f N := by
      simp [f]
    _ ≤ b 0 - b N := hfinite N
    _ ≤ b 0 := sub_le_self _ (by dsimp [b]; positivity)
    _ = 1 / (12 * ((m + 1 : ℕ) : ℝ)) := by simp [b]

private theorem logStirlingErrorPos2630 (m : ℕ) :
    0 < Real.log (Stirling.stirlingSeq (m + 1)) -
      Real.log (Real.sqrt Real.pi) := by
  have hdiff := logStirlingDiffPos2630 m
  have hsqrt : Real.sqrt Real.pi ≤ Stirling.stirlingSeq (m + 2) :=
    Stirling.sqrt_pi_le_stirlingSeq (by omega)
  have hlog : Real.log (Real.sqrt Real.pi) ≤
      Real.log (Stirling.stirlingSeq (m + 2)) :=
    Real.log_le_log (by positivity) hsqrt
  linarith

private theorem logStirlingErrorLt2630 (m : ℕ) :
    Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt Real.pi) <
      1 / (12 * ((m + 1 : ℕ) : ℝ)) := by
  have hdiff := logStirlingDiffLtSub2630 m
  have htail := logStirlingErrorLe2630 (m + 1)
  calc
    Real.log (Stirling.stirlingSeq (m + 1)) - Real.log (Real.sqrt Real.pi) =
        (Real.log (Stirling.stirlingSeq (m + 1)) -
          Real.log (Stirling.stirlingSeq (m + 2))) +
        (Real.log (Stirling.stirlingSeq (m + 2)) -
          Real.log (Real.sqrt Real.pi)) := by ring
    _ < (1 / (12 * ((m + 1 : ℕ) : ℝ)) -
          1 / (12 * ((m + 2 : ℕ) : ℝ))) +
        1 / (12 * ((m + 2 : ℕ) : ℝ)) := by
      exact add_lt_add_of_lt_of_le hdiff (by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail)
    _ = 1 / (12 * ((m + 1 : ℕ) : ℝ)) := by ring

theorem gap1 (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ stirlingFormula n θ := by
  cases n with
  | zero => omega
  | succ m =>
      let e : ℝ := Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Real.sqrt Real.pi)
      let θ : ℝ := 12 * ((m + 1 : ℕ) : ℝ) * e
      have hepos : 0 < e := by
        exact logStirlingErrorPos2630 m
      have helt : e < 1 / (12 * ((m + 1 : ℕ) : ℝ)) := by
        exact logStirlingErrorLt2630 m
      have hscale : 0 < 12 * ((m + 1 : ℕ) : ℝ) := by positivity
      have hθpos : 0 < θ := by
        dsimp [θ]
        exact mul_pos hscale hepos
      have hθlt : θ < 1 := by
        have hmul := mul_lt_mul_of_pos_left helt hscale
        calc
          θ = (12 * ((m + 1 : ℕ) : ℝ)) * e := by simp [θ]
          _ < (12 * ((m + 1 : ℕ) : ℝ)) *
              (1 / (12 * ((m + 1 : ℕ) : ℝ))) := hmul
          _ = 1 := by field_simp
      refine ⟨θ, hθpos, hθlt, ?_⟩
      have hseqpos : 0 < Stirling.stirlingSeq (m + 1) :=
        Stirling.stirlingSeq'_pos m
      have hsqrtpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
      have hexpe : Real.exp e =
          Stirling.stirlingSeq (m + 1) / Real.sqrt Real.pi := by
        dsimp [e]
        rw [Real.exp_sub, Real.exp_log hseqpos, Real.exp_log hsqrtpi]
      have hθdiv : θ / (12 * ((m + 1 : ℕ) : ℝ)) = e := by
        dsimp [θ]
        field_simp
      have hroot :
          Real.sqrt (2 * Real.pi * ((m + 1 : ℕ) : ℝ)) =
            Real.sqrt Real.pi * Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) := by
        rw [show 2 * Real.pi * ((m + 1 : ℕ) : ℝ) =
          Real.pi * (2 * ((m + 1 : ℕ) : ℝ)) by ring]
        rw [Real.sqrt_mul Real.pi_pos.le]
      have hpow :
          ((m + 1 : ℕ) : ℝ) ^ (m + 1) *
              Real.exp (-((m + 1 : ℕ) : ℝ)) =
            (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
        rw [show -((m + 1 : ℕ) : ℝ) =
          ((m + 1 : ℕ) : ℝ) * (-1 : ℝ) by ring]
        rw [Real.exp_nat_mul]
        rw [← mul_pow]
        congr 2
        rw [show (-1 : ℝ) = -(1 : ℝ) by ring, Real.exp_neg]
      have hsqrt2 : 0 < Real.sqrt (2 * ((m + 1 : ℕ) : ℝ)) := by
        positivity
      have hpowden : 0 <
          (((m + 1 : ℕ) : ℝ) / Real.exp 1) ^ (m + 1) := by
        positivity
      unfold stirlingFormula
      symm
      rw [hθdiv, Real.exp_add]
      calc
        Real.sqrt (2 * Real.pi * ↑(m + 1)) * ↑(m + 1) ^ (m + 1) *
            (Real.exp (-↑(m + 1)) * Real.exp e) =
            (Real.sqrt Real.pi * Real.sqrt (2 * ↑(m + 1))) *
              ((↑(m + 1) / Real.exp 1) ^ (m + 1)) * Real.exp e := by
              rw [hroot]
              calc
                (Real.sqrt Real.pi * Real.sqrt (2 * ↑(m + 1))) *
                    ↑(m + 1) ^ (m + 1) *
                      (Real.exp (-↑(m + 1)) * Real.exp e) =
                  (Real.sqrt Real.pi * Real.sqrt (2 * ↑(m + 1))) *
                    (↑(m + 1) ^ (m + 1) * Real.exp (-↑(m + 1))) *
                      Real.exp e := by ring
                _ = (Real.sqrt Real.pi * Real.sqrt (2 * ↑(m + 1))) *
                    ((↑(m + 1) / Real.exp 1) ^ (m + 1)) * Real.exp e := by
                  rw [hpow]
        _ = (Real.sqrt Real.pi * Real.sqrt (2 * ↑(m + 1))) *
            ((↑(m + 1) / Real.exp 1) ^ (m + 1)) *
              (Stirling.stirlingSeq (m + 1) / Real.sqrt Real.pi) := by
                rw [hexpe]
        _ = (Nat.factorial (m + 1) : ℝ) := by
          rw [Stirling.stirlingSeq]
          field_simp [ne_of_gt hsqrtpi, ne_of_gt hsqrt2, ne_of_gt hpowden]
          <;> ring

theorem gap2 (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : ℝ, 0 < θ ∧ stirlingFormula n θ := by
  rcases gap1 n hn with ⟨θ, hθpos, hθlt, hformula⟩
  exact ⟨θ, hθpos, hformula⟩

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : ℝ, θ < 1 ∧ stirlingFormula n θ := by
  rcases gap1 n hn with ⟨θ, hθpos, hθlt, hformula⟩
  exact ⟨θ, hθlt, hformula⟩

theorem gap4 (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
      term a n =
        Real.log (2 * Real.pi) / (2 * Real.rpow n a) +
        Real.log n / (2 * Real.rpow n a) +
        Real.log n / Real.rpow n (a - 1) +
        θ / (12 * Real.rpow n (a + 1)) -
        1 / Real.rpow n (a - 1) := by
  rcases gap1 n hn with ⟨θ, hθpos, hθlt, hstirling⟩
  refine ⟨θ, hθpos, hθlt, ?_⟩
  unfold term logFactorial
  unfold stirlingFormula at hstirling
  rw [hstirling]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_sqrt (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_pow]
  rw [Real.log_exp]
  have hsub : Real.rpow n a = Real.rpow n (a - 1) * (n : ℝ) := by
    calc
      Real.rpow n a = Real.rpow n ((a - 1) + 1) := by
        congr 1 <;> ring
      _ = Real.rpow n (a - 1) * (n : ℝ) := by
        exact rpowAddOne (x := (n : ℝ)) (p := a - 1) hnr
  have hadd : Real.rpow n (a + 1) = Real.rpow n a * (n : ℝ) := by
    exact rpowAddOne (x := (n : ℝ)) (p := a) hnr
  have hra0 : Real.rpow n a ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnr a)
  have hrsub0 : Real.rpow n (a - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnr (a - 1))
  rw [hadd, hsub]
  field_simp [hn0, hra0, hrsub0] <;> ring

theorem gap5 (a : ℝ) (ha : 2 < a) :
    Summable (fun n : ℕ => 1 / Real.rpow (n + 1) a) := by
  exact shiftedRpowSummable (p := a) (by linarith)

theorem gap6 (a : ℝ) (ha : 2 < a) :
    Summable (fun n : ℕ => Real.log (n + 1) / Real.rpow (n + 1) a) := by
  exact summableLogDivNatRpow (p := a) (by linarith)

theorem gap7 (a : ℝ) (ha : 2 < a) :
    Summable
      (fun n : ℕ => Real.log (n + 1) / Real.rpow (n + 1) (a - 1)) := by
  exact summableLogDivNatRpow (p := a - 1) (by linarith)

theorem gap8 (a : ℝ) (ha : 2 < a) (θ : ℕ → ℝ)
    (hθ : ∀ n, |θ n| ≤ 1) :
    Summable (fun n : ℕ => θ (n + 1) / Real.rpow (n + 1) (a + 1)) := by
  have hs : Summable (fun n : ℕ => 1 / Real.rpow (n + 1) (a + 1)) := by
    exact shiftedRpowSummable (p := a + 1) (by linarith)
  refine hs.of_norm_bounded ?_
  intro n
  change |θ (n + 1) / Real.rpow (n + 1) (a + 1)| ≤
    1 / Real.rpow (n + 1) (a + 1)
  have hdenpos : 0 < Real.rpow (n + 1) (a + 1) := by
    apply Real.rpow_pos_of_pos
    positivity
  rw [abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hθ (n + 1)) hdenpos.le

theorem gap9 (a : ℝ) (ha : 2 < a) :
    Summable (fun n : ℕ => comparison a (n + 1)) := by
  unfold comparison
  have hs := shiftedRpowSummable (p := a - 1) (by linarith)
  simpa only [Nat.cast_add, Nat.cast_one] using hs

theorem gap10 (a : ℝ) (ha : 2 < a) :
    converges a := by
  classical
  choose θ hθpos hθlt hformula using fun n : ℕ => gap4 a (n + 1) (by omega)
  have hθabs : ∀ n, |θ n| ≤ 1 := by
    intro n
    rw [abs_of_pos (hθpos n)]
    exact (hθlt n).le
  have h1 := gap5 a ha
  have h2 := gap6 a ha
  have h3 := gap7 a ha
  let θ' : ℕ → ℝ := fun m => if m = 0 then 0 else θ (m - 1)
  have hθ' : ∀ m, |θ' m| ≤ 1 := by
    intro m
    by_cases hm : m = 0
    · simp [θ', hm]
    · simpa [θ', hm] using hθabs (m - 1)
  have h4' := gap8 a ha θ' hθ'
  have h4 : Summable (fun n : ℕ => θ n / Real.rpow (n + 1) (a + 1)) := by
    simpa [θ'] using h4'
  have h5 := gap9 a ha
  have h12 := (h1.mul_left (Real.log (2 * Real.pi) / 2)).add
    (h2.mul_left (1 / 2))
  have h123 := h12.add h3
  have h1234 := h123.add (h4.mul_left (1 / 12))
  have hsum := h1234.sub h5
  unfold converges
  refine hsum.congr ?_
  intro n
  unfold comparison
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    (hformula n).symm

theorem gap11 :
    Tendsto (fun n : ℕ => Real.log (n + 1)) atTop atTop := by
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop b] with n hn
    omega
  have h := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hshift)
  apply h.congr'
  filter_upwards with n
  simp

theorem gap12 :
    Tendsto (fun n : ℕ => averageLog (n + 1)) atTop atTop := by
  have hlower : ∀ m : ℕ, 1 ≤ m → Real.log (m : ℝ) - 1 ≤ averageLog m := by
    intro m hm
    unfold averageLog
    rw [← factorialLogIcc m]
    rcases gap1 m hm with ⟨θ, hθpos, hθlt, hstirling⟩
    unfold stirlingFormula at hstirling
    rw [hstirling]
    have hmr : 0 < (m : ℝ) := by exact_mod_cast hm
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_sqrt (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_mul (by positivity) (by positivity)]
    rw [Real.log_pow]
    rw [Real.log_exp]
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlogpi : 0 ≤ Real.log Real.pi :=
      Real.log_nonneg (by nlinarith [Real.pi_gt_three])
    have hlogm : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hm)
    have hbase :
        0 ≤ (Real.log 2 + Real.log Real.pi + Real.log (m : ℝ)) / 2 := by
      positivity
    have hrem : 0 ≤ θ / (12 * (m : ℝ)) := by positivity
    apply (le_div_iff₀ hmr).2
    nlinarith
  have hlog := gap11
  refine tendsto_atTop.2 ?_
  intro b
  have hev : ∀ᶠ n : ℕ in atTop, b + 1 ≤ Real.log (n + 1) :=
    hlog.eventually (eventually_ge_atTop (b + 1))
  filter_upwards [hev] with n hn
  have hlow := hlower (n + 1) (by omega)
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [hcast] at hlow
  linarith

theorem gap13 (a : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    term a n / comparison a n = averageLog n := by
  unfold term comparison averageLog logFactorial
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hnr : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [factorialLogIcc]
  have hpow : Real.rpow n a = Real.rpow n (a - 1) * (n : ℝ) := by
    calc
      Real.rpow n a = Real.rpow n ((a - 1) + 1) := by
        congr 1 <;> ring
      _ = Real.rpow n (a - 1) * (n : ℝ) := by
        exact rpowAddOne (x := (n : ℝ)) (p := a - 1) hnr
  have hrsub0 : Real.rpow n (a - 1) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hnr (a - 1))
  rw [hpow]
  field_simp [hn0, hrsub0] <;> ring

theorem gap14 :
    Tendsto (fun n : ℕ => averageLog (n + 1)) atTop atTop := by
  exact gap12

theorem gap15 (a : ℝ) :
    Tendsto
      (fun n : ℕ => term a (n + 1) / comparison a (n + 1))
      atTop atTop := by
  have hfun :
      (fun n : ℕ => term a (n + 1) / comparison a (n + 1)) =
        (fun n : ℕ => averageLog (n + 1)) := by
    funext n
    apply gap13
    omega
  rw [hfun]
  exact gap14

theorem gap16 (a : ℝ) (ha : a ≤ 2) :
    ¬ Summable (fun n : ℕ => comparison a (n + 1)) := by
  unfold comparison
  intro hs
  have hshift :
      Summable (fun n : ℕ =>
        Real.rpow (((n + 1 : ℕ) : ℝ)) (-(a - 1))) := by
    refine hs.congr ?_
    intro n
    have hx : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
    exact oneDivRpowEq (p := a - 1) hx
  have hall :
      Summable (fun n : ℕ => Real.rpow (n : ℝ) (-(a - 1))) := by
    exact (summable_nat_add_iff 1).1 hshift
  have hexp : -(a - 1) < -1 := Real.summable_nat_rpow.mp hall
  linarith

theorem gap17 (a : ℝ) (ha : a ≤ 2) :
    ¬ converges a := by
  intro hterm
  apply gap16 a ha
  have hratio := gap15 a
  have hev : ∀ᶠ n : ℕ in atTop,
      1 ≤ term a (n + 1) / comparison a (n + 1) :=
    hratio.eventually (eventually_ge_atTop 1)
  have hev' : ∀ᶠ n : ℕ in cofinite,
      1 ≤ term a (n + 1) / comparison a (n + 1) := by
    rw [Nat.cofinite_eq_atTop]
    exact hev
  apply hterm.of_norm_bounded_eventually
  filter_upwards [hev'] with n hn
  have hbase : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hcpos : 0 < comparison a (n + 1) := by
    unfold comparison
    exact one_div_pos.mpr (Real.rpow_pos_of_pos hbase (a - 1))
  have hle : comparison a (n + 1) ≤ term a (n + 1) := by
    have h := (le_div_iff₀ hcpos).mp hn
    simpa only [one_mul] using h
  simpa only [Real.norm_eq_abs, abs_of_pos hcpos] using hle

theorem gap18 (a : ℝ) :
    a ∈ {r : ℝ | 2 < r} ↔ converges a := by
  change 2 < a ↔ converges a
  constructor
  · intro ha
    exact gap10 a ha
  · intro hconv
    by_contra hnot
    have ha : a ≤ 2 := le_of_not_gt hnot
    exact gap17 a ha hconv

end

end ProofGap.Exercise2630
