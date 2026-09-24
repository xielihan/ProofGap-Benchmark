import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1295

open scoped BigOperators

noncomputable section

def product (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∏ i ∈ Finset.range n, x i

def total (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ i ∈ Finset.range n, x i

def G (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  Real.rpow (product n x) (1 / (n : ℝ))

def A (n : ℕ) (x : ℕ → ℝ) : ℝ :=
  total n x / n

def PositiveTerms (x : ℕ → ℝ) : Prop := ∀ i, 0 < x i

def youngAux (α : ℝ) (z : ℝ) : ℝ :=
  Real.rpow z α - α * z + α - 1

theorem gap1 (n : ℕ) (x : ℕ → ℝ) (hn : 0 < n)
    (hx : PositiveTerms x) :
    G n x ^ n = product n x := by
  have hp : 0 < product n x := by
    unfold product
    exact Finset.prod_pos fun i hi => hx i
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  have hexp : (1 / (n : ℝ)) * (n : ℝ) = 1 := by
    field_simp
  calc
    G n x ^ n = Real.rpow (G n x) (n : ℝ) := by
      symm
      exact Real.rpow_natCast (G n x) n
    _ = Real.rpow (product n x) ((1 / (n : ℝ)) * (n : ℝ)) := by
      unfold G
      exact (Real.rpow_mul (le_of_lt hp) _ _).symm
    _ = product n x := by
      rw [hexp]
      exact Real.rpow_one (product n x)

theorem gap2 (n : ℕ) (x : ℕ → ℝ) (hn : 0 < n) :
    (n : ℝ) * A n x = total n x := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hn
  unfold A
  field_simp

theorem gap3 (x : ℕ → ℝ) (hx : PositiveTerms x) :
    Real.sqrt (x 0 * x 1) ≤ (x 0 + x 1) / 2 := by
  have h0 : 0 ≤ x 0 * x 1 :=
    mul_nonneg (le_of_lt (hx 0)) (le_of_lt (hx 1))
  have hsqrt : 0 ≤ Real.sqrt (x 0 * x 1) := Real.sqrt_nonneg _
  have hmean : 0 ≤ (x 0 + x 1) / 2 := by
    nlinarith [hx 0, hx 1]
  have hsq : (Real.sqrt (x 0 * x 1)) ^ 2 = x 0 * x 1 :=
    Real.sq_sqrt h0
  have hsquares :
      (Real.sqrt (x 0 * x 1)) ^ 2 ≤ ((x 0 + x 1) / 2) ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg (x 0 - x 1)]
  nlinarith

theorem gap4 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k)
    (hx : PositiveTerms x) :
    G (k + 1) x =
      Real.rpow (product (k + 1) x) (1 / (k + 1 : ℝ)) := by
  simpa [G, Nat.cast_add, Nat.cast_one]

theorem gap5 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k)
    (hx : PositiveTerms x) :
    G (k + 1) x ≤
      Real.rpow (G k x) ((k : ℝ) / (k + 1)) *
        Real.rpow (x k) (1 / (k + 1 : ℝ)) := by
  have hpk : 0 < product k x := by
    unfold product
    exact Finset.prod_pos fun i hi => hx i
  have hxk : 0 < x k := hx k
  have hprod : product (k + 1) x = product k x * x k := by
    simp [product, Finset.prod_range_succ]
  have hk0 : (k : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hk
  have hk10 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hpow :
      Real.rpow (G k x) ((k : ℝ) / ((k : ℝ) + 1)) =
        Real.rpow (product k x) (1 / ((k : ℝ) + 1)) := by
    calc
      Real.rpow (G k x) ((k : ℝ) / ((k : ℝ) + 1)) =
          Real.rpow (product k x)
            ((1 / (k : ℝ)) * ((k : ℝ) / ((k : ℝ) + 1))) := by
        unfold G
        exact (Real.rpow_mul (le_of_lt hpk) _ _).symm
      _ = Real.rpow (product k x) (1 / ((k : ℝ) + 1)) := by
        congr 1
        field_simp [hk0, hk10]
  have hmul :
      Real.rpow (product k x * x k) (1 / ((k : ℝ) + 1)) =
        Real.rpow (product k x) (1 / ((k : ℝ) + 1)) *
          Real.rpow (x k) (1 / ((k : ℝ) + 1)) := by
    exact Real.mul_rpow (le_of_lt hpk) (le_of_lt hxk)
  calc
    G (k + 1) x =
        Real.rpow (product k x * x k) (1 / ((k : ℝ) + 1)) := by
      rw [gap4 k x hk hx, hprod]
    _ = Real.rpow (product k x) (1 / ((k : ℝ) + 1)) *
          Real.rpow (x k) (1 / ((k : ℝ) + 1)) := hmul
    _ ≤ Real.rpow (G k x) ((k : ℝ) / ((k : ℝ) + 1)) *
          Real.rpow (x k) (1 / ((k : ℝ) + 1)) := by
      rw [hpow]

theorem gap6 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k)
    (hx : PositiveTerms x) (hind : G k x ≤ A k x) :
    Real.rpow (G k x) ((k : ℝ) / (k + 1)) *
        Real.rpow (x k) (1 / (k + 1 : ℝ)) ≤
      Real.rpow (A k x) ((k : ℝ) / (k + 1)) *
        Real.rpow (x k) (1 / (k + 1 : ℝ)) := by
  have hprod : 0 < product k x := by
    unfold product
    exact Finset.prod_pos fun i hi => hx i
  have hG : 0 ≤ G k x := by
    unfold G
    exact Real.rpow_nonneg (le_of_lt hprod) _
  have he : 0 ≤ (k : ℝ) / (k + 1) := by positivity
  have hr :
      Real.rpow (G k x) ((k : ℝ) / (k + 1)) ≤
        Real.rpow (A k x) ((k : ℝ) / (k + 1)) :=
    Real.rpow_le_rpow hG hind he
  have hfactor : 0 ≤ Real.rpow (x k) (1 / (k + 1 : ℝ)) :=
    Real.rpow_nonneg (le_of_lt (hx k)) _
  exact mul_le_mul_of_nonneg_right hr hfactor

theorem gap7 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k)
    (hx : PositiveTerms x) (hind : G k x ≤ A k x) :
    G (k + 1) x ≤
      Real.rpow (A k x) ((k : ℝ) / (k + 1)) *
        Real.rpow (x k) (1 / (k + 1 : ℝ)) := by
  exact le_trans (gap5 k x hk hx) (gap6 k x hk hx hind)

theorem gap8 (α z : ℝ) (hz : 0 < z) :
    deriv (youngAux α) z =
      α * (Real.rpow z (α - 1) - 1) := by
  have hpow : HasDerivAt (fun t : ℝ => Real.rpow t α)
      (α * Real.rpow z (α - 1)) z :=
    Real.hasDerivAt_rpow_const (p := α) (Or.inl (ne_of_gt hz))
  have hlin : HasDerivAt (fun t : ℝ => α * t) α z := by
    simpa using (hasDerivAt_id z).const_mul α
  have hfull : HasDerivAt (youngAux α)
      (α * Real.rpow z (α - 1) - α) z := by
    simpa [youngAux] using
      (((hpow.sub hlin).add (hasDerivAt_const z α)).sub
        (hasDerivAt_const z 1))
  calc
    deriv (youngAux α) z = α * Real.rpow z (α - 1) - α := hfull.deriv
    _ = α * (Real.rpow z (α - 1) - 1) := by ring

theorem gap9 (a b p q : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hp : 1 < p) (hq : 1 < q) (hconj : 1 / p + 1 / q = 1) :
    Real.rpow a (1 / p) * Real.rpow b (1 / q) ≤
      a / p + b / q := by
  let s : Finset ℕ := {0, 1}
  let w : ℕ → ℝ := fun i => if i = 0 then 1 / p else 1 / q
  let v : ℕ → ℝ := fun i => if i = 0 then a else b
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hpw : 0 ≤ 1 / p := by positivity
  have hqw : 0 ≤ 1 / q := by positivity
  have hpw1 : 1 / p ≤ 1 := by
    rw [div_le_iff₀ hp0]
    linarith
  have hqw1 : 1 / q ≤ 1 := by
    rw [div_le_iff₀ hq0]
    linarith
  have hpwlt : 1 / p < 1 := by
    rw [div_lt_iff₀ hp0]
    linarith
  have hqwlt : 1 / q < 1 := by
    rw [div_lt_iff₀ hq0]
    linarith
  have hconj' : p⁻¹ + q⁻¹ = 1 := by
    simpa [one_div] using hconj
  have hgm :
      (∏ i ∈ s, Real.rpow (v i) (w i)) ≤
        ∑ i ∈ s, w i * v i := by
    apply Real.geom_mean_le_arith_mean_weighted
    all_goals
      simp [s, w, v, hp0.le, hq0.le, hpw, hqw, hpw1, hqw1,
        hpwlt, hqwlt, ha.le, hb.le, hconj']
  simpa [s, w, v, div_eq_mul_inv, mul_comm] using hgm

theorem gap10 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k)
    (hx : PositiveTerms x) :
    Real.rpow (A k x) ((k : ℝ) / (k + 1)) *
        Real.rpow (x k) (1 / (k + 1 : ℝ)) ≤
      (k : ℝ) / (k + 1) * A k x +
        1 / (k + 1 : ℝ) * x k := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have htotal : 0 < total k x := by
    unfold total
    refine Finset.sum_pos' (fun i hi => le_of_lt (hx i)) ?_
    exact ⟨0, Finset.mem_range.mpr hk, hx 0⟩
  have hA : 0 < A k x := by
    unfold A
    exact div_pos htotal hkR
  have hp : 1 < (((k : ℝ) + 1) / (k : ℝ)) := by
    rw [lt_div_iff₀ hkR]
    norm_num
  have hq : 1 < (k : ℝ) + 1 := by linarith
  have hconj :
      1 / (((k : ℝ) + 1) / (k : ℝ)) + 1 / ((k : ℝ) + 1) = 1 := by
    field_simp [ne_of_gt hkR]
  have h := gap9 (A k x) (x k)
    (((k : ℝ) + 1) / (k : ℝ)) ((k : ℝ) + 1)
    hA (hx k) hp hq hconj
  convert h using 1 <;> field_simp [ne_of_gt hkR] <;> ring

theorem gap11 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k)
    (hx : PositiveTerms x) (hind : G k x ≤ A k x) :
    G (k + 1) x ≤
      1 / (k + 1 : ℝ) * (total k x + x k) := by
  calc
    G (k + 1) x ≤
        Real.rpow (A k x) ((k : ℝ) / (k + 1)) *
          Real.rpow (x k) (1 / (k + 1 : ℝ)) :=
      gap7 k x hk hx hind
    _ ≤ (k : ℝ) / (k + 1) * A k x +
          1 / (k + 1 : ℝ) * x k := gap10 k x hk hx
    _ = 1 / (k + 1 : ℝ) * (total k x + x k) := by
      rw [← gap2 k x hk]
      ring

theorem gap12 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k) :
    1 / (k + 1 : ℝ) * (total k x + x k) = A (k + 1) x := by
  unfold A total
  rw [Finset.sum_range_succ]
  simp [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_add, add_mul, mul_comm]

theorem gap13 (k : ℕ) (x : ℕ → ℝ) (hk : 0 < k)
    (hx : PositiveTerms x) (hind : G k x ≤ A k x) :
    G (k + 1) x ≤ A (k + 1) x := by
  rw [← gap12 k x hk]
  exact gap11 k x hk hx hind

theorem gap14 (n : ℕ) (x : ℕ → ℝ) (hn : 0 < n)
    (hx : PositiveTerms x) :
    Real.rpow (product n x) (1 / (n : ℝ)) ≤
      total n x / n := by
  change G n x ≤ A n x
  induction n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        simp [G, A, product, total]
      · have hk : 0 < k := Nat.pos_of_ne_zero hk0
        exact gap13 k x hk hx (ih hk)

theorem gap15 (n : ℕ) (x : ℕ → ℝ) (hn : 0 < n)
    (hx : PositiveTerms x) :
    G n x ≤ A n x := by
  simpa [G, A] using gap14 n x hn hx

end

end ProofGap.Exercise1295
