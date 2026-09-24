import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise2729

noncomputable section

def factorialRoot (n : ℕ) : ℝ :=
  Real.rpow (n.factorial : ℝ) (1 / (n : ℝ))

def term (a x : ℝ) (n : ℕ) : ℝ :=
  1 / factorialRoot n * (1 / (1 + a ^ (2 * n) * x ^ 2))

private theorem factorial_lt_pow_self {n : ℕ} (hn : 2 ≤ n) :
    n.factorial < n ^ n := by
  cases n with
  | zero => omega
  | succ n =>
      have hn0 : n ≠ 0 := by omega
      rw [Nat.factorial_succ, pow_succ,
        Nat.mul_comm ((n + 1) ^ n) (n + 1)]
      apply (Nat.mul_lt_mul_left (Nat.succ_pos n)).2
      exact (Nat.factorial_le_pow n).trans_lt
        (Nat.pow_lt_pow_left (Nat.lt_succ_self n) hn0)

private theorem term_pos (a x : ℝ) (n : ℕ) : 0 < term a x n := by
  have hroot : 0 < factorialRoot n := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos n) _
  have haeven : 0 ≤ a ^ (2 * n) := by
    rw [show 2 * n = n + n by omega, pow_add]
    exact mul_self_nonneg _
  have hden : 0 < 1 + a ^ (2 * n) * x ^ 2 := by
    nlinarith [mul_nonneg haeven (sq_nonneg x)]
  unfold term
  exact mul_pos (one_div_pos.mpr hroot) (one_div_pos.mpr hden)

theorem gap1 (a : ℝ) :
    ∀ n : ℕ, 1 ≤ n → term a 0 n = 1 / factorialRoot n := by
  intro n hn
  simp [term]

theorem gap2 :
    ∀ n : ℕ, 2 ≤ n → 1 / factorialRoot n > 1 / (n : ℝ) := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  have hfact : (n.factorial : ℝ) < (n : ℝ) ^ n := by
    exact_mod_cast factorial_lt_pow_self hn
  have hexp : 0 < 1 / (n : ℝ) := by positivity
  have hroot : factorialRoot n < (n : ℝ) := by
    unfold factorialRoot
    calc
      Real.rpow (n.factorial : ℝ) (1 / (n : ℝ)) <
          Real.rpow ((n : ℝ) ^ n) (1 / (n : ℝ)) :=
        Real.rpow_lt_rpow (by positivity) hfact hexp
      _ = (n : ℝ) := by
        simpa [one_div] using
          (Real.pow_rpow_inv_natCast (x := (n : ℝ))
            (n := n) (by positivity) hn0)
  have hrootpos : 0 < factorialRoot n := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos n) _
  exact one_div_lt_one_div_of_lt hrootpos hroot

theorem gap3 :
    ∀ n : ℕ, 1 ≤ n →
      1 / Real.rpow ((n : ℝ) ^ n) (1 / (n : ℝ)) = 1 / n := by
  intro n hn
  have hn0 : n ≠ 0 := by omega
  rw [show Real.rpow ((n : ℝ) ^ n) (1 / (n : ℝ)) = (n : ℝ) by
    simpa [one_div] using
      (Real.pow_rpow_inv_natCast (x := (n : ℝ))
        (n := n) (by positivity) hn0)]

theorem gap4 (a : ℝ) :
    ∀ n : ℕ, 2 ≤ n → term a 0 n > 1 / (n : ℝ) := by
  intro n hn
  rw [gap1 a n (by omega)]
  exact gap2 n hn

theorem gap5 (a : ℝ) :
    ¬ Summable (fun n : ℕ => term a 0 (n + 1)) := by
  intro hterm
  have htail : Summable (fun n : ℕ => term a 0 (n + 2)) := by
    simpa [Nat.add_assoc] using
      ((summable_nat_add_iff
        (f := fun n : ℕ => term a 0 (n + 1)) 1).2 hterm)
  have hharm : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    exact Summable.of_nonneg_of_le (fun _ => by positivity)
      (fun n => (gap4 a (n + 2) (by omega)).le) htail
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff
      (f := fun n : ℕ => 1 / (n : ℝ)) 2).mp hharm)

theorem gap6 (a x : ℝ) (hx : x ≠ 0) (ha : 1 < |a|) :
    ∀ n : ℕ, 1 ≤ n → 0 < term a x n := by
  intro n hn
  exact term_pos a x n

theorem gap7 (a x : ℝ) (hx : x ≠ 0) (ha : 1 < |a|) :
    ∀ n : ℕ, 1 ≤ n → term a x n < 1 / (a ^ (2 * n) * x ^ 2) := by
  intro n hn
  have ha0 : a ≠ 0 := by
    intro h
    subst a
    norm_num at ha
  have hroot : 1 ≤ factorialRoot n := by
    unfold factorialRoot
    apply Real.one_le_rpow
    · exact_mod_cast Nat.factorial_pos n
    · positivity
  have hinv : 1 / factorialRoot n ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one hroot
  have haeven : 0 ≤ a ^ (2 * n) := by
    rw [show 2 * n = n + n by omega, pow_add]
    exact mul_self_nonneg _
  have hapow : 0 < a ^ (2 * n) :=
    lt_of_le_of_ne haeven (Ne.symm (pow_ne_zero _ ha0))
  have hA : 0 < a ^ (2 * n) * x ^ 2 :=
    mul_pos hapow (sq_pos_of_ne_zero hx)
  unfold term
  calc
    1 / factorialRoot n * (1 / (1 + a ^ (2 * n) * x ^ 2)) ≤
        1 * (1 / (1 + a ^ (2 * n) * x ^ 2)) := by
      gcongr
    _ < 1 / (a ^ (2 * n) * x ^ 2) := by
      simpa using one_div_lt_one_div_of_lt hA (by linarith)

theorem gap8 (a x : ℝ) (hx : x ≠ 0) :
    ∀ n : ℕ, 1 ≤ n →
      1 / (a ^ (2 * n) * x ^ 2) =
        (1 / x ^ 2) * (1 / |a|) ^ (2 * n) := by
  intro n hn
  have h2n : 2 * n ≠ 0 := by omega
  by_cases ha0 : a = 0
  · subst a
    simp [h2n]
  · have haeven : 0 ≤ a ^ (2 * n) := by
      rw [show 2 * n = n + n by omega, pow_add]
      exact mul_self_nonneg _
    have habspow : |a| ^ (2 * n) = a ^ (2 * n) := by
      rw [← abs_pow, abs_of_nonneg haeven]
    rw [one_div_pow, habspow]
    field_simp

theorem gap9 (a x : ℝ) (hx : x ≠ 0) (ha : 1 < |a|) :
    ∀ n : ℕ, 1 ≤ n → 0 < (1 / x ^ 2) * (1 / |a|) ^ (2 * n) := by
  intro n hn
  positivity

theorem gap10 (a x : ℝ) (hx : x ≠ 0) (ha : 1 < |a|) :
    Summable (fun n : ℕ => (1 / x ^ 2) * (1 / |a|) ^ (2 * (n + 1))) := by
  have habs : 0 < |a| := zero_lt_one.trans ha
  have hbase : 0 < 1 / |a| := one_div_pos.mpr habs
  have hnorm : ‖1 / |a|‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos hbase]
    exact (div_lt_one habs).2 ha
  have hsquared : ‖(1 / |a|) ^ 2‖ < 1 := by
    rw [norm_pow]
    nlinarith [norm_nonneg (1 / |a|)]
  have hgeom : Summable (fun n : ℕ => ((1 / |a|) ^ 2) ^ n) :=
    summable_geometric_of_norm_lt_one hsquared
  have hscaled := hgeom.mul_left ((1 / x ^ 2) * (1 / |a|) ^ 2)
  convert hscaled using 1
  ext n
  rw [show 2 * (n + 1) = 2 + 2 * n by omega, pow_add, ← pow_mul]
  ring

theorem gap11 (a x : ℝ) (hx : x ≠ 0) (ha : 1 < |a|) :
    Summable (fun n : ℕ => |term a x (n + 1)|) := by
  apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _) ?_ (gap10 a x hx ha)
  intro n
  rw [abs_of_pos (gap6 a x hx ha (n + 1) (by omega))]
  exact (gap7 a x hx ha (n + 1) (by omega)).le.trans_eq
    (gap8 a x hx (n + 1) (by omega))

theorem gap12 (a x : ℝ) (hx : x ≠ 0) (ha : |a| ≤ 1) :
    ∀ n : ℕ, 2 ≤ n →
      |term a x n| > (1 / (1 + x ^ 2)) * (1 / (n : ℝ)) := by
  intro n hn
  have hterm : 0 < term a x n := term_pos a x n
  have hroot : 0 < factorialRoot n := by
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.factorial_pos n) _
  rw [abs_of_pos hterm]
  have haeven : 0 ≤ a ^ (2 * n) := by
    rw [show 2 * n = n + n by omega, pow_add]
    exact mul_self_nonneg _
  have habspow : |a| ^ (2 * n) = a ^ (2 * n) := by
    rw [← abs_pow, abs_of_nonneg haeven]
  have hapow : a ^ (2 * n) ≤ 1 := by
    rw [← habspow]
    exact pow_le_one₀ (abs_nonneg a) ha
  have hden :
      1 / (1 + x ^ 2) ≤ 1 / (1 + a ^ (2 * n) * x ^ 2) := by
    exact one_div_le_one_div_of_le (by positivity)
      (by nlinarith [sq_nonneg x])
  calc
    (1 / (1 + x ^ 2)) * (1 / (n : ℝ)) <
        (1 / (1 + x ^ 2)) * (1 / factorialRoot n) := by
      exact mul_lt_mul_of_pos_left (gap2 n hn) (by positivity)
    _ = (1 / factorialRoot n) * (1 / (1 + x ^ 2)) := by ring
    _ ≤ (1 / factorialRoot n) *
        (1 / (1 + a ^ (2 * n) * x ^ 2)) := by
      apply mul_le_mul_of_nonneg_left hden
      exact (one_div_pos.mpr hroot).le
    _ = term a x n := rfl

theorem gap13 (x : ℝ) :
    ∀ n : ℕ, 2 ≤ n →
      (1 / (1 + x ^ 2)) * (1 / (n : ℝ)) > 0 := by
  intro n hn
  positivity

theorem gap14 (a x : ℝ) (hx : x ≠ 0) (ha : |a| ≤ 1) :
    ∀ n : ℕ, 2 ≤ n →
      |term a x n| > (1 / (1 + x ^ 2)) * (1 / (n : ℝ)) := by
  exact gap12 a x hx ha

theorem gap15 (a x : ℝ) (hx : x ≠ 0) (ha : |a| ≤ 1) :
    ¬ Summable (fun n : ℕ => term a x (n + 1)) := by
  intro hterm
  let c : ℝ := 1 / (1 + x ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  have htail : Summable (fun n : ℕ => term a x (n + 2)) := by
    simpa [Nat.add_assoc] using
      ((summable_nat_add_iff
        (f := fun n : ℕ => term a x (n + 1)) 1).2 hterm)
  have hscaled : Summable
      (fun n : ℕ => c * (1 / ((n + 2 : ℕ) : ℝ))) := by
    apply Summable.of_nonneg_of_le (fun _ => by positivity) ?_ htail
    intro n
    simpa [c, abs_of_pos (term_pos a x (n + 2))] using
      (gap14 a x hx ha (n + 2) (by omega)).le
  have hharm : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    have := hscaled.mul_left (1 / c)
    convert this using 1
    ext n
    field_simp
  exact Real.not_summable_one_div_natCast
    ((summable_nat_add_iff
      (f := fun n : ℕ => 1 / (n : ℝ)) 2).mp hharm)

theorem gap16 (a x : ℝ) :
    Summable (fun n : ℕ => term a x (n + 1)) ↔ x ≠ 0 ∧ 1 < |a| := by
  constructor
  · intro h
    have hx : x ≠ 0 := by
      intro hx
      subst x
      exact gap5 a h
    constructor
    · exact hx
    · by_contra ha
      exact gap15 a x hx (le_of_not_gt ha) h
  · rintro ⟨hx, ha⟩
    have hnorm : Summable (fun n : ℕ => ‖term a x (n + 1)‖) := by
      simpa [Real.norm_eq_abs] using gap11 a x hx ha
    exact hnorm.of_norm

end

end ProofGap.Exercise2729
