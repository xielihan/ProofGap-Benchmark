import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2655_3

noncomputable section

open scoped BigOperators

def term (n : ℕ) : ℝ :=
  1 / Nat.factorial (2 * n - 1)

def remainder (N : ℕ) : ℝ :=
  ∑' l : ℕ, term (N + 1 + l)

def stirlingMajorant (n : ℕ) : ℝ :=
  (Real.exp 1 / (2 * n - 1 : ℝ)) ^ (2 * n - 1)

def fixedBaseMajorant (N n : ℕ) : ℝ :=
  (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * n - 1)

private theorem exp_one_lt_three : Real.exp 1 < 3 := by
  have hs : Real.exp (1 / 6 : ℝ) ≤ (6 / 5 : ℝ) := by
    have h := Real.exp_bound_div_one_sub_of_interval
      (show (0 : ℝ) ≤ 1 / 6 by norm_num) (by norm_num)
    norm_num at h ⊢
    exact h
  have hp : (Real.exp (1 / 6 : ℝ)) ^ 6 ≤ (6 / 5 : ℝ) ^ 6 := by
    gcongr
  have heq : Real.exp 1 = (Real.exp (1 / 6 : ℝ)) ^ 6 := by
    convert (Real.exp_nat_mul (1 / 6 : ℝ) 6) using 1 <;> norm_num
  rw [heq]
  exact hp.trans_lt (by norm_num)

private theorem majorant_facts (N : ℕ) (hN : 1 ≤ N) :
    Real.exp 1 / (2 * N + 1 : ℝ) < 1 ∧
    (∀ l : ℕ, stirlingMajorant (N + 1 + l) ≤
      fixedBaseMajorant N (N + 1 + l)) ∧
    Summable (fun l : ℕ => fixedBaseMajorant N (N + 1 + l)) ∧
    Summable (fun l : ℕ => stirlingMajorant (N + 1 + l)) := by
  let q : ℝ := Real.exp 1 / (2 * N + 1 : ℝ)
  have he : Real.exp 1 < 3 := exp_one_lt_three
  have hn : 3 ≤ 2 * N + 1 := by omega
  have hnr : (3 : ℝ) ≤ (2 * N + 1 : ℝ) := by exact_mod_cast hn
  have hdenpos : 0 < (2 * N + 1 : ℝ) := by positivity
  have hq : q < 1 := by
    dsimp [q]
    rw [div_lt_one hdenpos]
    exact he.trans_le hnr
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hq2 : q ^ 2 < 1 := by
    have hmul : q * q < q := by
      simpa using mul_lt_mul_of_pos_left hq hqpos
    exact (by simpa [pow_two] using hmul.trans hq)
  have hnorm : ‖q ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)]
    exact hq2
  have hgeom : Summable (fun l : ℕ => (q ^ 2) ^ l) :=
    summable_geometric_of_norm_lt_one hnorm
  have hfixed : Summable (fun l : ℕ => fixedBaseMajorant N (N + 1 + l)) := by
    have hmul := hgeom.mul_left (q ^ (2 * N + 1))
    refine hmul.congr ?_
    intro l
    unfold fixedBaseMajorant
    dsimp [q]
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  have hpoint : ∀ l : ℕ, stirlingMajorant (N + 1 + l) ≤
      fixedBaseMajorant N (N + 1 + l) := by
    intro l
    let m : ℕ := 2 * (N + 1 + l) - 1
    have hnat : 2 * N + 1 ≤ m := by
      dsimp [m]
      omega
    have hreal : (2 * N + 1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnat
    have hmNat : 0 < m := by
      dsimp [m]
      omega
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hmNat
    have hbase : Real.exp 1 / (m : ℝ) ≤
        Real.exp 1 / (2 * N + 1 : ℝ) := by
      rw [div_le_div_iff₀ hmpos hdenpos]
      nlinarith [Real.exp_pos 1]
    have hp : (Real.exp 1 / (m : ℝ)) ^ m ≤
        (Real.exp 1 / (2 * N + 1 : ℝ)) ^ m := by
      gcongr
    unfold stirlingMajorant fixedBaseMajorant
    simpa [m, Nat.cast_sub (by omega : 1 ≤ 2 * (N + 1 + l))] using hp
  have hstirling_nonneg :
      ∀ l : ℕ, 0 ≤ stirlingMajorant (N + 1 + l) := by
    intro l
    unfold stirlingMajorant
    have harg : (1 : ℝ) ≤ ((N + 1 + l : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ N + 1 + l by omega)
    have hden : (0 : ℝ) <
        2 * ((N + 1 + l : ℕ) : ℝ) - 1 := by
      nlinarith
    exact pow_nonneg
      (div_nonneg (le_of_lt (Real.exp_pos 1)) (le_of_lt hden)) _
  have hstirling : Summable (fun l : ℕ => stirlingMajorant (N + 1 + l)) :=
    Summable.of_nonneg_of_le hstirling_nonneg hpoint hfixed
  exact ⟨by simpa [q] using hq, hpoint, hfixed, hstirling⟩

theorem gap1 :
    ∀ k : ℕ, 1 ≤ k →
      (Nat.factorial k : ℝ) > ((k : ℝ) / Real.exp 1) ^ k := by
  intro k
  induction k with
  | zero =>
      intro hk
      omega
  | succ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k
        have he : (1 : ℝ) < Real.exp 1 := by
          simpa using (Real.exp_lt_exp.mpr (by norm_num : (0 : ℝ) < 1))
        rw [Nat.factorial_one, Nat.cast_one, pow_one]
        exact (div_lt_one (Real.exp_pos 1)).2 he
      · have hkposNat : 1 ≤ k := by omega
        have hkpos : (0 : ℝ) < k := by exact_mod_cast hkposNat
        have hepos : 0 < Real.exp 1 := Real.exp_pos 1
        have hi := ih hkposNat
        have hratio : ((k + 1 : ℕ) : ℝ) / (k : ℝ) ≤
            Real.exp (1 / (k : ℝ)) := by
          calc
            ((k + 1 : ℕ) : ℝ) / (k : ℝ) = 1 / (k : ℝ) + 1 := by
              norm_num only [Nat.cast_add, Nat.cast_one]
              field_simp [ne_of_gt hkpos]
              <;> ring
            _ ≤ Real.exp (1 / (k : ℝ)) := Real.add_one_le_exp _
        have hratioPow :
            (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k ≤ Real.exp 1 := by
          have hp : (((k + 1 : ℕ) : ℝ) / (k : ℝ)) ^ k ≤
              (Real.exp (1 / (k : ℝ))) ^ k := by
            gcongr
          have hexp : (Real.exp (1 / (k : ℝ))) ^ k = Real.exp 1 := by
            rw [← Real.exp_nat_mul]
            congr 1
            field_simp [ne_of_gt hkpos]
          exact hp.trans_eq hexp
        have hpow : (((k + 1 : ℕ) : ℝ) ^ k) ≤
            Real.exp 1 * (k : ℝ) ^ k := by
          rw [div_pow] at hratioPow
          exact (div_le_iff₀ (pow_pos hkpos k)).mp hratioPow
        have hcomp :
            (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) ≤
              ((k + 1 : ℕ) : ℝ) * (((k : ℝ) / Real.exp 1) ^ k) := by
          calc
            (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) =
                (((k + 1 : ℕ) : ℝ) / (Real.exp 1) ^ (k + 1)) *
                  (((k + 1 : ℕ) : ℝ) ^ k) := by
              rw [div_pow, pow_succ]
              field_simp [ne_of_gt hepos]
              <;> ring
            _ ≤ (((k + 1 : ℕ) : ℝ) / (Real.exp 1) ^ (k + 1)) *
                  (Real.exp 1 * (k : ℝ) ^ k) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
            _ = ((k + 1 : ℕ) : ℝ) * (((k : ℝ) / Real.exp 1) ^ k) := by
              rw [div_pow]
              field_simp [ne_of_gt hepos]
              <;> ring
        have hfaclt :
            ((k + 1 : ℕ) : ℝ) * (((k : ℝ) / Real.exp 1) ^ k) <
              ((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ) :=
          mul_lt_mul_of_pos_left hi (by positivity)
        show (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) <
          (Nat.factorial (k + 1) : ℝ)
        calc
          (((k + 1 : ℕ) : ℝ) / Real.exp 1) ^ (k + 1) ≤
              ((k + 1 : ℕ) : ℝ) * (((k : ℝ) / Real.exp 1) ^ k) := hcomp
          _ < ((k + 1 : ℕ) : ℝ) * (Nat.factorial k : ℝ) := hfaclt
          _ = (Nat.factorial (k + 1) : ℝ) := by
            rw [Nat.factorial_succ, Nat.cast_mul]

theorem gap2 (N : ℕ) (hN : 1 ≤ N) :
    remainder N < ∑' l : ℕ, stirlingMajorant (N + 1 + l) := by
  have hstirling := (majorant_facts N hN).2.2.2
  have hpoint : ∀ l : ℕ, term (N + 1 + l) < stirlingMajorant (N + 1 + l) := by
    intro l
    let m : ℕ := 2 * (N + 1 + l) - 1
    have hm : 1 ≤ m := by
      dsimp [m]
      omega
    have hfac := gap1 m hm
    have hmpos : 0 < (m : ℝ) / Real.exp 1 := by positivity
    have hinv : 1 / (Nat.factorial m : ℝ) <
        1 / (((m : ℝ) / Real.exp 1) ^ m) :=
      one_div_lt_one_div_of_lt (pow_pos hmpos m) hfac
    have heq : 1 / (((m : ℝ) / Real.exp 1) ^ m) =
        (Real.exp 1 / (m : ℝ)) ^ m := by
      rw [div_pow, div_pow]
      field_simp [ne_of_gt (show (0 : ℝ) < m by exact_mod_cast hm),
        ne_of_gt (Real.exp_pos 1)]
    have hgeneric : 1 / (Nat.factorial m : ℝ) <
        (Real.exp 1 / (m : ℝ)) ^ m := hinv.trans_eq heq
    unfold term stirlingMajorant
    simpa [m, Nat.cast_sub (by omega : 1 ≤ 2 * (N + 1 + l))] using hgeneric
  have hterm_nonneg : ∀ l : ℕ, 0 ≤ term (N + 1 + l) := by
    intro l
    unfold term
    exact le_of_lt (one_div_pos.mpr (by positivity))
  have hterm : Summable (fun l : ℕ => term (N + 1 + l)) :=
    Summable.of_nonneg_of_le hterm_nonneg
      (fun l => le_of_lt (hpoint l)) hstirling
  unfold remainder
  exact Summable.tsum_lt_tsum
    (fun l => le_of_lt (hpoint l)) (hpoint 0) hterm hstirling

theorem gap3 (N : ℕ) (hN : 1 ≤ N) :
    (∑' l : ℕ, stirlingMajorant (N + 1 + l)) ≤
      ∑' l : ℕ, fixedBaseMajorant N (N + 1 + l) := by
  rcases majorant_facts N hN with ⟨_, hpoint, hfixed, hstirling⟩
  exact Summable.tsum_le_tsum hpoint hstirling hfixed

theorem gap4 (N : ℕ) (hN : 1 ≤ N) :
    (∑' l : ℕ, fixedBaseMajorant N (N + 1 + l)) =
      (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * N + 1) *
        ∑' l : ℕ, (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * l) := by
  rw [← tsum_mul_left]
  apply tsum_congr
  intro l
  unfold fixedBaseMajorant
  rw [← pow_add]
  congr 1
  omega

theorem gap5 (N : ℕ) (hN : 1 ≤ N) :
    remainder N <
      (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * N + 1) *
        ∑' l : ℕ, (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * l) := by
  calc
    remainder N < ∑' l : ℕ, stirlingMajorant (N + 1 + l) := gap2 N hN
    _ ≤ ∑' l : ℕ, fixedBaseMajorant N (N + 1 + l) := gap3 N hN
    _ = (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * N + 1) *
          ∑' l : ℕ, (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * l) :=
      gap4 N hN

theorem gap6 (N : ℕ) :
    1 ≤ N → Real.exp 1 / (2 * N + 1 : ℝ) < 1 := by
  intro hN
  exact (majorant_facts N hN).1

theorem gap7 (N : ℕ) :
    1 ≤ N →
      remainder N <
        (Real.exp 1 / (2 * N + 1 : ℝ)) ^ (2 * N + 1) /
          (1 - (Real.exp 1 / (2 * N + 1 : ℝ)) ^ 2) := by
  intro hN
  let q : ℝ := Real.exp 1 / (2 * N + 1 : ℝ)
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hq : q < 1 := by
    simpa [q] using gap6 N hN
  have hq2 : q ^ 2 < 1 := by
    have hmul : q * q < q := by
      simpa using mul_lt_mul_of_pos_left hq hqpos
    exact (by simpa [pow_two] using hmul.trans hq)
  have hnorm : ‖q ^ 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg q)]
    exact hq2
  have hsum : (∑' l : ℕ, q ^ (2 * l)) = 1 / (1 - q ^ 2) := by
    calc
      (∑' l : ℕ, q ^ (2 * l)) = ∑' l : ℕ, (q ^ 2) ^ l := by
        apply tsum_congr
        intro l
        rw [pow_mul]
      _ = 1 / (1 - q ^ 2) := by
        simpa [div_eq_mul_inv] using
          (hasSum_geometric_of_norm_lt_one hnorm).tsum_eq
  have h := gap5 N hN
  change remainder N < q ^ (2 * N + 1) * ∑' l : ℕ, q ^ (2 * l) at h
  rw [hsum] at h
  simpa [q, div_eq_mul_inv] using h

theorem gap8 :
    ∀ n : ℕ, 1 ≤ n →
      term (n + 1) / term n =
        1 / (((2 * n : ℕ) : ℝ) * (2 * n + 1 : ℝ)) := by
  intro n hn
  have hidx : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have hfac2 : Nat.factorial (2 * n) =
      (2 * n) * Nat.factorial (2 * n - 1) := by
    calc
      Nat.factorial (2 * n) = Nat.factorial ((2 * n - 1) + 1) := by
        congr 1
        omega
      _ = ((2 * n - 1) + 1) * Nat.factorial (2 * n - 1) :=
        Nat.factorial_succ (2 * n - 1)
      _ = (2 * n) * Nat.factorial (2 * n - 1) := by
        rw [show (2 * n - 1) + 1 = 2 * n by omega]
  have hfac : Nat.factorial (2 * n + 1) =
      (2 * n + 1) * (2 * n) * Nat.factorial (2 * n - 1) := by
    calc
      Nat.factorial (2 * n + 1) =
          (2 * n + 1) * Nat.factorial (2 * n) :=
        Nat.factorial_succ (2 * n)
      _ = (2 * n + 1) * ((2 * n) * Nat.factorial (2 * n - 1)) := by
        rw [hfac2]
      _ = (2 * n + 1) * (2 * n) * Nat.factorial (2 * n - 1) := by
        simp only [mul_assoc]
  unfold term
  rw [hidx, hfac]
  have hnpos : (0 : ℝ) < (2 * n : ℕ) := by
    exact_mod_cast (show 0 < 2 * n by omega)
  have hn1pos : (0 : ℝ) < (2 * n + 1 : ℕ) := by positivity
  have hfpos : (0 : ℝ) < Nat.factorial (2 * n - 1) := by positivity
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  field_simp [ne_of_gt hnpos, ne_of_gt hn1pos, ne_of_gt hfpos]
  <;> ring

theorem gap9 :
    ∀ n : ℕ, 6 ≤ n → term (n + 1) ≤ (1 / 156 : ℝ) * term n := by
  intro n hn
  have hn1 : 1 ≤ n := by omega
  have hratio := gap8 n hn1
  have htpos : 0 < term n := by
    unfold term
    exact one_div_pos.mpr (by positivity)
  have htne : term n ≠ 0 := ne_of_gt htpos
  have heq : term (n + 1) =
      (1 / (((2 * n : ℕ) : ℝ) * (2 * n + 1 : ℝ))) * term n :=
    (div_eq_iff htne).mp hratio
  have hnr : (6 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : (156 : ℝ) ≤
      ((2 * n : ℕ) : ℝ) * (2 * n + 1 : ℝ) := by
    norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    nlinarith
  have hcoef :
      1 / (((2 * n : ℕ) : ℝ) * (2 * n + 1 : ℝ)) ≤ (1 / 156 : ℝ) := by
    exact one_div_le_one_div_of_le (by norm_num) hden
  rw [heq]
  exact mul_le_mul_of_nonneg_right hcoef (le_of_lt htpos)

theorem gap10 (N : ℕ) (hN : N = 5) :
    remainder N < (10 : ℝ) ^ (-5 : ℤ) := by
  subst N
  let q : ℝ := Real.exp 1 / 11
  have hr : remainder 5 < q ^ 11 / (1 - q ^ 2) := by
    convert gap7 5 (by norm_num) using 1 <;> norm_num [q]
  have hq0 : 0 ≤ q := by
    dsimp [q]
    positivity
  have hediv := gap6 1 (by norm_num)
  norm_num at hediv
  have he : Real.exp 1 < 3 :=
    (div_lt_one (by norm_num : (0 : ℝ) < 3)).mp hediv
  have hq : q < (1 / 3 : ℝ) := by
    dsimp [q]
    apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 11)).2
    nlinarith
  have hqpow : q ^ 11 < (1 / 3 : ℝ) ^ 11 := by
    gcongr
  have hq2 : q ^ 2 < (1 / 3 : ℝ) ^ 2 := by
    gcongr
  have hden : 0 < 1 - q ^ 2 := by
    norm_num at hq2
    nlinarith
  have hsmall : q ^ 11 / (1 - q ^ 2) < (10 : ℝ) ^ (-5 : ℤ) := by
    apply (div_lt_iff₀ hden).2
    norm_num at hqpow hq2 ⊢
    nlinarith
  exact hr.trans hsmall

theorem gap11 (N : ℕ) (hN : N = 5) :
    5 ≤ N := by
  subst N
  exact le_rfl

end

end ProofGap.Exercise2655_3
