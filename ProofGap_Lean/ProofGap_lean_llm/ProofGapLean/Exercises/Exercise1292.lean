import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1292

open scoped BigOperators

noncomputable section

def arithmeticTerm (a d : ℝ) (k : ℕ) : ℝ := a + k * d
def geometricTerm (a q : ℝ) (k : ℕ) : ℝ := a * q ^ k

def arithmeticSum (n : ℕ) (a d : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, arithmeticTerm a d k

def geometricSum (n : ℕ) (a q : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, geometricTerm a q k

def endpointStep (n : ℕ) (a q : ℝ) : ℝ :=
  a * (q ^ (n - 1) - 1) / (n - 1 : ℝ)

def closedArithmeticSum (n : ℕ) (a q : ℝ) : ℝ :=
  (n : ℝ) / 2 * a * (1 + q ^ (n - 1))

def phiBelow (n : ℕ) (t : ℝ) : ℝ :=
  (n - 2 : ℝ) * (1 - t ^ n)

def psiBelow (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * t * (1 - t ^ (n - 2))

def phiAbove (n : ℕ) (t : ℝ) : ℝ :=
  (n - 2 : ℝ) * (t ^ n - 1)

def psiAbove (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) * t * (t ^ (n - 2) - 1)

def scaledBelow (n : ℕ) (a q : ℝ) : ℝ :=
  (2 / a) * (1 - q) *
    (closedArithmeticSum n a q - geometricSum n a q)

def scaledAbove (n : ℕ) (a q : ℝ) : ℝ :=
  (2 / a) * (q - 1) *
    (closedArithmeticSum n a q - geometricSum n a q)

private theorem sum_cast_range_formula (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ)) = (n : ℝ) * (n - 1 : ℝ) / 2 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

private theorem algebra_below (n : ℕ) (q : ℝ) (hn : 3 ≤ n) :
    (n : ℝ) * (1 - q) * (1 + q ^ (n - 1)) - 2 * (1 - q ^ n) =
      phiBelow n q - psiBelow n q := by
  have hp1 : q ^ (n - 1) = q ^ (n - 2) * q := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
  have hp2 : q ^ n = q ^ (n - 2) * q ^ 2 := by
    calc
      q ^ n = q ^ ((n - 2) + 2) := by congr 1 <;> omega
      _ = q ^ (n - 2) * q ^ 2 := by rw [pow_add]
  unfold phiBelow psiBelow
  rw [hp1, hp2]
  ring

private theorem algebra_above (n : ℕ) (q : ℝ) (hn : 3 ≤ n) :
    (n : ℝ) * (q - 1) * (1 + q ^ (n - 1)) - 2 * (q ^ n - 1) =
      phiAbove n q - psiAbove n q := by
  have hp1 : q ^ (n - 1) = q ^ (n - 2) * q := by
    rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
  have hp2 : q ^ n = q ^ (n - 2) * q ^ 2 := by
    calc
      q ^ n = q ^ ((n - 2) + 2) := by congr 1 <;> omega
      _ = q ^ (n - 2) * q ^ 2 := by rw [pow_add]
  unfold phiAbove psiAbove
  rw [hp1, hp2]
  ring

private theorem deriv_phiBelow_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (phiBelow n) t = -(n : ℝ) * (n - 2 : ℝ) * t ^ (n - 1) := by
  have h := ((hasDerivAt_const t (1 : ℝ)).sub ((hasDerivAt_id t).pow n)).const_mul (n - 2 : ℝ)
  convert h.deriv using 1 <;>
    simp [phiBelow] <;> ring

private theorem deriv_psiBelow_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (psiBelow n) t = (n : ℝ) * (1 - (n - 1 : ℝ) * t ^ (n - 2)) := by
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have he : n - 1 - 1 = n - 2 := by omega
  rw [show psiBelow n = fun x : ℝ => (n : ℝ) * x - (n : ℝ) * x ^ (n - 1) by
    funext x
    unfold psiBelow
    have hp : x * x ^ (n - 2) = x ^ (n - 1) := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
      ring
    calc
      (n : ℝ) * x * (1 - x ^ (n - 2)) =
          (n : ℝ) * x - (n : ℝ) * (x * x ^ (n - 2)) := by ring
      _ = (n : ℝ) * x - (n : ℝ) * x ^ (n - 1) := by rw [hp]]
  have h := ((hasDerivAt_id t).const_mul (n : ℝ)).sub
    (((hasDerivAt_id t).pow (n - 1)).const_mul (n : ℝ))
  convert h.deriv using 1 <;>
    simp [hc1, he] <;> ring

private theorem second_deriv_phiBelow_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (phiBelow n)) t =
      -(n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) * t ^ (n - 2) := by
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have he : n - 1 - 1 = n - 2 := by omega
  rw [show deriv (phiBelow n) = fun x => -(n : ℝ) * (n - 2 : ℝ) * x ^ (n - 1) by
    funext x
    exact deriv_phiBelow_formula n x hn]
  have h := ((hasDerivAt_id t).pow (n - 1)).const_mul (-(n : ℝ) * (n - 2 : ℝ))
  convert h.deriv using 1 <;>
    simp [hc1, he] <;> ring

private theorem second_deriv_psiBelow_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (psiBelow n)) t =
      -(n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) * t ^ (n - 3) := by
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hc2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have he : n - 2 - 1 = n - 3 := by omega
  rw [show deriv (psiBelow n) = fun x => (n : ℝ) * (1 - (n - 1 : ℝ) * x ^ (n - 2)) by
    funext x
    exact deriv_psiBelow_formula n x hn]
  have h := ((hasDerivAt_const t (1 : ℝ)).sub
    (((hasDerivAt_id t).pow (n - 2)).const_mul (n - 1 : ℝ))).const_mul (n : ℝ)
  convert h.deriv using 1 <;>
    simp [hc1, hc2, he] <;> ring

private theorem deriv_phiAbove_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (phiAbove n) t = (n : ℝ) * (n - 2 : ℝ) * t ^ (n - 1) := by
  have h := (((hasDerivAt_id t).pow n).sub (hasDerivAt_const t (1 : ℝ))).const_mul (n - 2 : ℝ)
  convert h.deriv using 1 <;>
    simp [phiAbove] <;> ring

private theorem deriv_psiAbove_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (psiAbove n) t = (n : ℝ) * ((n - 1 : ℝ) * t ^ (n - 2) - 1) := by
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have he : n - 1 - 1 = n - 2 := by omega
  rw [show psiAbove n = fun x : ℝ => (n : ℝ) * x ^ (n - 1) - (n : ℝ) * x by
    funext x
    unfold psiAbove
    have hp : x * x ^ (n - 2) = x ^ (n - 1) := by
      rw [show n - 1 = (n - 2) + 1 by omega, pow_succ]
      ring
    calc
      (n : ℝ) * x * (x ^ (n - 2) - 1) =
          (n : ℝ) * (x * x ^ (n - 2)) - (n : ℝ) * x := by ring
      _ = (n : ℝ) * x ^ (n - 1) - (n : ℝ) * x := by rw [hp]]
  have h := (((hasDerivAt_id t).pow (n - 1)).const_mul (n : ℝ)).sub
    ((hasDerivAt_id t).const_mul (n : ℝ))
  convert h.deriv using 1 <;>
    simp [hc1, he] <;> ring

private theorem second_deriv_phiAbove_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (phiAbove n)) t =
      (n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) * t ^ (n - 2) := by
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have he : n - 1 - 1 = n - 2 := by omega
  rw [show deriv (phiAbove n) = fun x => (n : ℝ) * (n - 2 : ℝ) * x ^ (n - 1) by
    funext x
    exact deriv_phiAbove_formula n x hn]
  have h := ((hasDerivAt_id t).pow (n - 1)).const_mul ((n : ℝ) * (n - 2 : ℝ))
  convert h.deriv using 1 <;>
    simp [hc1, he] <;> ring

private theorem second_deriv_psiAbove_formula (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (psiAbove n)) t =
      (n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) * t ^ (n - 3) := by
  have hc1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n)]
    norm_num
  have hc2 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]
    norm_num
  have he : n - 2 - 1 = n - 3 := by omega
  rw [show deriv (psiAbove n) = fun x => (n : ℝ) * ((n - 1 : ℝ) * x ^ (n - 2) - 1) by
    funext x
    exact deriv_psiAbove_formula n x hn]
  have h := ((((hasDerivAt_id t).pow (n - 2)).const_mul (n - 1 : ℝ)).sub
    (hasDerivAt_const t (1 : ℝ))).const_mul (n : ℝ)
  convert h.deriv using 1 <;>
    simp [hc1, hc2, he] <;> ring

private theorem hasDerivAt_const_rpow (q x : ℝ) (hq : 0 < q) :
    HasDerivAt (fun y : ℝ => Real.rpow q y)
      (Real.rpow q x * Real.log q) x := by
  have h := (Real.hasDerivAt_exp (x * Real.log q)).comp x
    ((hasDerivAt_id x).mul_const (Real.log q))
  simpa [Function.comp_def, Real.rpow_def_of_pos hq,
    mul_comm, mul_left_comm, mul_assoc] using h

private theorem hasDerivAt_aux_expr (a d q x : ℝ) (hq : 0 < q) :
    HasDerivAt (fun y : ℝ => a + y * d - a * Real.rpow q y)
      (d - a * Real.rpow q x * Real.log q) x := by
  have hr := hasDerivAt_const_rpow q x hq
  have h := ((hasDerivAt_const x a).add ((hasDerivAt_id x).mul_const d)).sub
    (hr.const_mul a)
  convert h using 1 <;> simp <;> ring

private theorem differentiable_aux_expr (a d q : ℝ) (hq : 0 < q) :
    Differentiable ℝ (fun x : ℝ => a + x * d - a * Real.rpow q x) := by
  intro x
  exact (hasDerivAt_aux_expr a d q x hq).differentiableAt

private theorem deriv_aux_expr (a d q x : ℝ) (hq : 0 < q) :
    deriv (fun y : ℝ => a + y * d - a * Real.rpow q y) x =
      d - a * Real.rpow q x * Real.log q := by
  exact (hasDerivAt_aux_expr a d q x hq).deriv

private theorem second_deriv_aux_expr (a d q x : ℝ) (hq : 0 < q) :
    deriv (deriv (fun y : ℝ => a + y * d - a * Real.rpow q y)) x =
      -a * Real.rpow q x * (Real.log q) ^ 2 := by
  rw [show deriv (fun z : ℝ => a + z * d - a * Real.rpow q z) =
      fun y => d - a * Real.rpow q y * Real.log q by
    funext y
    exact deriv_aux_expr a d q y hq]
  have hr := hasDerivAt_const_rpow q x hq
  have h := (hasDerivAt_const x d).sub ((hr.const_mul a).mul_const (Real.log q))
  convert h.deriv using 1 <;> ring

private theorem rpow_nat_eq_pow (q : ℝ) (n : ℕ) :
    Real.rpow q (n : ℝ) = q ^ n := by
  change q ^ (n : ℝ) = q ^ n
  exact Real.rpow_natCast q n

theorem gap1 (n : ℕ) (a : ℝ) (hn : 1 ≤ n) :
    arithmeticSum n a 0 = geometricSum n a 1 := by simp [arithmeticSum, geometricSum, arithmeticTerm, geometricTerm]

theorem gap2 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) :
    a + (n - 1 : ℝ) * endpointStep n a q =
      a * q ^ (n - 1) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n - 1 : ℝ) ≠ 0 := by linarith
  unfold endpointStep
  field_simp [hn0]
  ring

theorem gap3 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) (hq : q < 1) :
    endpointStep n a q =
      -((1 - q ^ (n - 1)) / (n - 1 : ℝ)) * a := by
  unfold endpointStep
  ring

theorem gap4 (n : ℕ) (a q : ℝ) :
    arithmeticSum n a (endpointStep n a q) =
      ∑ k ∈ Finset.range n,
        (a + k * endpointStep n a q) := by rfl

theorem gap5 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) :
    arithmeticSum n a (endpointStep n a q) =
      ∑ k ∈ Finset.range n,
        (a - (k : ℝ) / (n - 1) *
          (1 - q ^ (n - 1)) * a) := by
  unfold arithmeticSum arithmeticTerm
  apply Finset.sum_congr rfl
  intro k hk
  unfold endpointStep
  ring

theorem gap6 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) :
    (∑ k ∈ Finset.range n,
        (a - (k : ℝ) / (n - 1) *
          (1 - q ^ (n - 1)) * a)) =
      a * ((n : ℝ) -
        (1 / (n - 1 : ℝ)) * (1 - q ^ (n - 1)) *
          (∑ k ∈ Finset.range n, (k : ℝ))) := by
  calc
    (∑ k ∈ Finset.range n, (a - (k : ℝ) / (n - 1) * (1 - q ^ (n - 1)) * a)) =
        ∑ k ∈ Finset.range n, a * (1 - (1 / (n - 1 : ℝ)) * (1 - q ^ (n - 1)) * (k : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = a * ∑ k ∈ Finset.range n, (1 - (1 / (n - 1 : ℝ)) * (1 - q ^ (n - 1)) * (k : ℝ)) := by
          rw [Finset.mul_sum]
    _ = a * ((n : ℝ) - (1 / (n - 1 : ℝ)) * (1 - q ^ (n - 1)) * (∑ k ∈ Finset.range n, (k : ℝ))) := by
          congr 1
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
          rw [← Finset.mul_sum]

theorem gap7 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) :
    a * ((n : ℝ) -
        (1 / (n - 1 : ℝ)) * (1 - q ^ (n - 1)) *
          (∑ k ∈ Finset.range n, (k : ℝ))) =
      closedArithmeticSum n a q := by
  rw [sum_cast_range_formula]
  unfold closedArithmeticSum
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n - 1 : ℝ) ≠ 0 := by linarith
  field_simp [hn0]
  ring

theorem gap8 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) :
    arithmeticSum n a (endpointStep n a q) =
      closedArithmeticSum n a q := by
  rw [gap5 n a q hn, gap6 n a q hn, gap7 n a q hn]

theorem gap9 (n : ℕ) (a q : ℝ) :
    geometricSum n a q =
      ∑ k ∈ Finset.range n, a * q ^ k := by rfl

theorem gap10 (n : ℕ) (a q : ℝ) (hq : q < 1) (hq1 : q ≠ 1) :
    geometricSum n a q = a * (1 - q ^ n) / (1 - q) := by
  rw [gap9, ← Finset.mul_sum]
  have hden : 1 - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq1)
  have hg : (∑ k ∈ Finset.range n, q ^ k) * (1 - q) = 1 - q ^ n := by
    nlinarith [geom_sum_mul q n]
  field_simp [hden]
  calc
    (a * ∑ k ∈ Finset.range n, q ^ k) * (1 - q) =
        a * ((∑ k ∈ Finset.range n, q ^ k) * (1 - q)) := by ring
    _ = a * (1 - q ^ n) := by rw [hg]

theorem gap11 (n : ℕ) (a q : ℝ) (hq : q < 1) :
    geometricSum n a q = a * (1 - q ^ n) / (1 - q) := by
  apply gap10 n a q hq
  linarith

theorem gap12 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : a ≠ 0) (hq : 0 < q) (hq1 : q < 1) :
    scaledBelow n a q =
      (n : ℝ) * (1 - q) * (1 + q ^ (n - 1)) -
        2 * (1 - q ^ n) := by
  rw [scaledBelow, closedArithmeticSum, gap11 n a q hq1]
  have hden : 1 - q ≠ 0 := by linarith
  field_simp [ha, hden]

theorem gap13 (n : ℕ) (q : ℝ) (hn : 3 ≤ n) :
    (n : ℝ) * (1 - q) * (1 + q ^ (n - 1)) -
        2 * (1 - q ^ n) =
      phiBelow n q - psiBelow n q := by exact algebra_below n q hn

theorem gap14 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : a ≠ 0) (hq : 0 < q) (hq1 : q < 1) :
    scaledBelow n a q = phiBelow n q - psiBelow n q := by
  rw [gap12 n a q hn ha hq hq1, gap13 n q hn]

theorem gap15 (n : ℕ) : phiBelow n 1 = psiBelow n 1 := by simp [phiBelow, psiBelow]

theorem gap16 (n : ℕ) : psiBelow n 1 = 0 := by simp [psiBelow]

theorem gap17 (n : ℕ) (hn : 3 ≤ n) :
    deriv (phiBelow n) 1 = deriv (psiBelow n) 1 := by
  rw [deriv_phiBelow_formula n 1 hn, deriv_psiBelow_formula n 1 hn]
  norm_num only [one_pow, mul_one]
  ring

theorem gap18 (n : ℕ) (hn : 3 ≤ n) :
    deriv (psiBelow n) 1 = -(n : ℝ) * (n - 2 : ℝ) := by
  rw [deriv_psiBelow_formula n 1 hn]
  norm_num only [one_pow, mul_one]
  ring

theorem gap19 (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (phiBelow n)) t =
      -(n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) *
        t ^ (n - 2) := by exact second_deriv_phiBelow_formula n t hn

theorem gap20 (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (psiBelow n)) t =
      -(n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) *
        t ^ (n - 3) := by exact second_deriv_psiBelow_formula n t hn

theorem gap21 (n : ℕ) (t : ℝ) (hn : 3 ≤ n)
    (ht0 : 0 < t) (ht1 : t < 1) :
    deriv (deriv (psiBelow n)) t <
      deriv (deriv (phiBelow n)) t := by
  rw [gap20 n t hn, gap19 n t hn]
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n - 1 : ℝ) := by linarith
  have hn2 : 0 < (n - 2 : ℝ) := by linarith
  have hC : 0 < (n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) :=
    mul_pos (mul_pos hn0 hn1) hn2
  have hp : 0 < t ^ (n - 3) := pow_pos ht0 _
  have he : t ^ (n - 2) = t ^ (n - 3) * t := by
    rw [show n - 2 = (n - 3) + 1 by omega, pow_succ]
  rw [he]
  have hm := mul_lt_mul_of_pos_left ht1 (mul_pos hC hp)
  nlinarith

theorem gap22 (n : ℕ) (t : ℝ) (hn : 3 ≤ n)
    (ht0 : 0 < t) (ht1 : t < 1) :
    psiBelow n t < phiBelow n t := by
  let f : ℝ → ℝ := fun x => phiBelow n x - psiBelow n x
  have hphi : Differentiable ℝ (phiBelow n) := by
    unfold phiBelow
    fun_prop
  have hpsi : Differentiable ℝ (psiBelow n) := by
    unfold psiBelow
    fun_prop
  have hdf : deriv f = fun x => deriv (phiBelow n) x - deriv (psiBelow n) x := by
    funext x
    dsimp [f]
    simpa only [Pi.sub_apply] using
      (deriv_sub hphi.differentiableAt hpsi.differentiableAt)
  have hdphi : Differentiable ℝ (deriv (phiBelow n)) := by
    rw [show deriv (phiBelow n) = fun x => -(n : ℝ) * (n - 2 : ℝ) * x ^ (n - 1) by
      funext x
      exact deriv_phiBelow_formula n x hn]
    fun_prop
  have hdpsi : Differentiable ℝ (deriv (psiBelow n)) := by
    rw [show deriv (psiBelow n) = fun x => (n : ℝ) * (1 - (n - 1 : ℝ) * x ^ (n - 2)) by
      funext x
      exact deriv_psiBelow_formula n x hn]
    fun_prop
  have hmono : StrictMonoOn (deriv f) (Set.Icc t 1) := by
    refine strictMonoOn_of_deriv_pos (f := deriv f) (convex_Icc t 1) ?_ ?_
    · rw [hdf]
      exact (hdphi.sub hdpsi).continuous.continuousOn
    · intro x hx
      have hx' : x ∈ Set.Ioo t 1 := by simpa [interior_Icc, ht1] using hx
      rw [hdf]
      have hdsub :
          deriv (fun y => deriv (phiBelow n) y - deriv (psiBelow n) y) x =
            deriv (deriv (phiBelow n)) x - deriv (deriv (psiBelow n)) x := by
        simpa only [Pi.sub_apply] using
          (deriv_sub hdphi.differentiableAt hdpsi.differentiableAt)
      rw [hdsub]
      linarith [gap21 n x hn (lt_trans ht0 hx'.1) hx'.2]
  have hdf1 : deriv f 1 = 0 := by
    rw [hdf]
    linarith [gap17 n hn]
  have hanti : StrictAntiOn f (Set.Icc t 1) := by
    refine strictAntiOn_of_deriv_neg (f := f) (convex_Icc t 1) ?_ ?_
    · exact (hphi.sub hpsi).continuous.continuousOn
    · intro x hx
      have hx' : x ∈ Set.Ioo t 1 := by simpa [interior_Icc, ht1] using hx
      have hm := hmono
        (show x ∈ Set.Icc t 1 by exact ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩)
        (show (1 : ℝ) ∈ Set.Icc t 1 by exact ⟨le_of_lt ht1, le_rfl⟩) hx'.2
      linarith
  have hv := hanti
    (show t ∈ Set.Icc t 1 by exact ⟨le_rfl, le_of_lt ht1⟩)
    (show (1 : ℝ) ∈ Set.Icc t 1 by exact ⟨le_of_lt ht1, le_rfl⟩) ht1
  dsimp [f] at hv ⊢
  rw [gap15 n] at hv
  linarith

theorem gap23 (n : ℕ) (q : ℝ) (hn : 3 ≤ n)
    (hq0 : 0 < q) (hq1 : q < 1) :
    psiBelow n q < phiBelow n q := by exact gap22 n q hn hq0 hq1

theorem gap24 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : a ≠ 0) (hq0 : 0 < q) (hq1 : q < 1) :
    scaledBelow n a q = phiBelow n q - psiBelow n q := by exact gap14 n a q hn ha hq0 hq1

theorem gap25 (n : ℕ) (q : ℝ) (hn : 3 ≤ n)
    (hq0 : 0 < q) (hq1 : q < 1) :
    0 < phiBelow n q - psiBelow n q := by linarith [gap23 n q hn hq0 hq1]

theorem gap26 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : 0 < a) (hq0 : 0 < q) (hq1 : q < 1) :
    0 < scaledBelow n a q := by
  rw [gap24 n a q hn ha.ne' hq0 hq1]
  exact gap25 n q hn hq0 hq1

theorem gap27 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : 0 < a) (hq0 : 0 < q) (hq1 : q < 1) :
    geometricSum n a q <
      arithmeticSum n a (endpointStep n a q) := by
  have hs := gap26 n a q hn ha hq0 hq1
  rw [scaledBelow] at hs
  have htwo : 0 < (2 : ℝ) / a := div_pos (by norm_num) ha
  have hone : 0 < 1 - q := sub_pos.mpr hq1
  have hc : 0 < (2 / a) * (1 - q) := mul_pos htwo hone
  have hd : 0 < closedArithmeticSum n a q - geometricSum n a q := by
    rcases (mul_pos_iff.mp hs) with h | h
    · exact h.2
    · exact (not_lt_of_ge (le_of_lt hc) h.1).elim
  rw [← gap8 n a q (by omega)] at hd
  linarith

theorem gap28 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) (hq : 1 < q) :
    endpointStep n a q =
      (q ^ (n - 1) - 1) / (n - 1 : ℝ) * a := by
  unfold endpointStep
  ring

theorem gap29 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n)
    (ha : 0 < a) (hq : 1 < q) :
    0 < (q ^ (n - 1) - 1) / (n - 1 : ℝ) * a := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hden : 0 < (n - 1 : ℝ) := by linarith
  have hp : 1 < q ^ (n - 1) := one_lt_pow₀ hq (by omega)
  exact mul_pos (div_pos (sub_pos.mpr hp) hden) ha

theorem gap30 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n)
    (ha : 0 < a) (hq : 1 < q) :
    0 < endpointStep n a q := by
  rw [gap28 n a q hn hq]
  exact gap29 n a q hn ha hq

theorem gap31 (n : ℕ) (a q : ℝ) :
    arithmeticSum n a (endpointStep n a q) =
      ∑ k ∈ Finset.range n,
        (a + k * endpointStep n a q) := by rfl

theorem gap32 (n : ℕ) (a d : ℝ) :
    arithmeticSum n a d =
      (n : ℝ) * a + (n : ℝ) * (n - 1 : ℝ) / 2 * d := by
  unfold arithmeticSum arithmeticTerm
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← Finset.sum_mul, sum_cast_range_formula]

theorem gap33 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) :
    (n : ℝ) * a +
        (n : ℝ) * (n - 1 : ℝ) / 2 * endpointStep n a q =
      closedArithmeticSum n a q := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n - 1 : ℝ) ≠ 0 := by linarith
  unfold endpointStep closedArithmeticSum
  field_simp [hn0]
  ring

theorem gap34 (n : ℕ) (a q : ℝ) (hn : 2 ≤ n) :
    arithmeticSum n a (endpointStep n a q) =
      closedArithmeticSum n a q := by
  rw [gap32, gap33 n a q hn]

theorem gap35 (n : ℕ) (a q : ℝ) :
    geometricSum n a q =
      ∑ k ∈ Finset.range n, a * q ^ k := by rfl

theorem gap36 (n : ℕ) (a q : ℝ) (hq : 1 < q) :
    geometricSum n a q = a * (q ^ n - 1) / (q - 1) := by
  rw [gap35, ← Finset.mul_sum]
  have hden : q - 1 ≠ 0 := by linarith
  have hg : (∑ k ∈ Finset.range n, q ^ k) * (q - 1) = q ^ n - 1 :=
    geom_sum_mul q n
  field_simp [hden]
  calc
    (a * ∑ k ∈ Finset.range n, q ^ k) * (q - 1) =
        a * ((∑ k ∈ Finset.range n, q ^ k) * (q - 1)) := by ring
    _ = a * (q ^ n - 1) := by rw [hg]

theorem gap37 (n : ℕ) (a q : ℝ) (hq : 1 < q) :
    geometricSum n a q = a * (q ^ n - 1) / (q - 1) := by exact gap36 n a q hq

theorem gap38 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : a ≠ 0) (hq : 1 < q) :
    scaledAbove n a q = phiAbove n q - psiAbove n q := by
  rw [scaledAbove, closedArithmeticSum, gap37 n a q hq]
  have hden : q - 1 ≠ 0 := by linarith
  field_simp [ha, hden]
  simpa [mul_comm, mul_left_comm, mul_assoc] using algebra_above n q hn

theorem gap39 (n : ℕ) : phiAbove n 1 = psiAbove n 1 := by simp [phiAbove, psiAbove]

theorem gap40 (n : ℕ) : psiAbove n 1 = 0 := by simp [psiAbove]

theorem gap41 (n : ℕ) (hn : 3 ≤ n) :
    deriv (phiAbove n) 1 = deriv (psiAbove n) 1 := by
  rw [deriv_phiAbove_formula n 1 hn, deriv_psiAbove_formula n 1 hn]
  norm_num only [one_pow, mul_one]
  ring

theorem gap42 (n : ℕ) (hn : 3 ≤ n) :
    deriv (psiAbove n) 1 = (n : ℝ) * (n - 2 : ℝ) := by
  rw [deriv_psiAbove_formula n 1 hn]
  norm_num only [one_pow, mul_one]
  ring

theorem gap43 (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (phiAbove n)) t =
      (n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) *
        t ^ (n - 2) := by exact second_deriv_phiAbove_formula n t hn

theorem gap44 (n : ℕ) (t : ℝ) (hn : 3 ≤ n) :
    deriv (deriv (psiAbove n)) t =
      (n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) *
        t ^ (n - 3) := by exact second_deriv_psiAbove_formula n t hn

theorem gap45 (n : ℕ) (t : ℝ) (hn : 3 ≤ n) (ht : 1 < t) :
    deriv (deriv (psiAbove n)) t <
      deriv (deriv (phiAbove n)) t := by
  rw [gap44 n t hn, gap43 n t hn]
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n : ℝ) := by linarith
  have hn1 : 0 < (n - 1 : ℝ) := by linarith
  have hn2 : 0 < (n - 2 : ℝ) := by linarith
  have hC : 0 < (n : ℝ) * (n - 1 : ℝ) * (n - 2 : ℝ) :=
    mul_pos (mul_pos hn0 hn1) hn2
  have hp : 0 < t ^ (n - 3) := pow_pos (lt_trans zero_lt_one ht) _
  have he : t ^ (n - 2) = t ^ (n - 3) * t := by
    rw [show n - 2 = (n - 3) + 1 by omega, pow_succ]
  rw [he]
  have hm := mul_lt_mul_of_pos_left ht (mul_pos hC hp)
  simpa [mul_assoc] using hm

theorem gap46 (n : ℕ) (t : ℝ) (hn : 3 ≤ n) (ht : 1 < t) :
    psiAbove n t < phiAbove n t := by
  let f : ℝ → ℝ := fun x => phiAbove n x - psiAbove n x
  have hphi : Differentiable ℝ (phiAbove n) := by
    unfold phiAbove
    fun_prop
  have hpsi : Differentiable ℝ (psiAbove n) := by
    unfold psiAbove
    fun_prop
  have hdf : deriv f = fun x => deriv (phiAbove n) x - deriv (psiAbove n) x := by
    funext x
    dsimp [f]
    simpa only [Pi.sub_apply] using
      (deriv_sub hphi.differentiableAt hpsi.differentiableAt)
  have hdphi : Differentiable ℝ (deriv (phiAbove n)) := by
    rw [show deriv (phiAbove n) = fun x => (n : ℝ) * (n - 2 : ℝ) * x ^ (n - 1) by
      funext x
      exact deriv_phiAbove_formula n x hn]
    fun_prop
  have hdpsi : Differentiable ℝ (deriv (psiAbove n)) := by
    rw [show deriv (psiAbove n) = fun x => (n : ℝ) * ((n - 1 : ℝ) * x ^ (n - 2) - 1) by
      funext x
      exact deriv_psiAbove_formula n x hn]
    fun_prop
  have hmono : StrictMonoOn (deriv f) (Set.Icc 1 t) := by
    refine strictMonoOn_of_deriv_pos (f := deriv f) (convex_Icc 1 t) ?_ ?_
    · rw [hdf]
      exact (hdphi.sub hdpsi).continuous.continuousOn
    · intro x hx
      have hx' : x ∈ Set.Ioo 1 t := by simpa [interior_Icc, ht] using hx
      rw [hdf]
      have hdsub :
          deriv (fun y => deriv (phiAbove n) y - deriv (psiAbove n) y) x =
            deriv (deriv (phiAbove n)) x - deriv (deriv (psiAbove n)) x := by
        simpa only [Pi.sub_apply] using
          (deriv_sub hdphi.differentiableAt hdpsi.differentiableAt)
      rw [hdsub]
      linarith [gap45 n x hn hx'.1]
  have hdf1 : deriv f 1 = 0 := by
    rw [hdf]
    linarith [gap41 n hn]
  have hinc : StrictMonoOn f (Set.Icc 1 t) := by
    refine strictMonoOn_of_deriv_pos (f := f) (convex_Icc 1 t) ?_ ?_
    · exact (hphi.sub hpsi).continuous.continuousOn
    · intro x hx
      have hx' : x ∈ Set.Ioo 1 t := by simpa [interior_Icc, ht] using hx
      have hm := hmono
        (show (1 : ℝ) ∈ Set.Icc 1 t by exact ⟨le_rfl, le_of_lt ht⟩)
        (show x ∈ Set.Icc 1 t by exact ⟨le_of_lt hx'.1, le_of_lt hx'.2⟩) hx'.1
      linarith
  have hv := hinc
    (show (1 : ℝ) ∈ Set.Icc 1 t by exact ⟨le_rfl, le_of_lt ht⟩)
    (show t ∈ Set.Icc 1 t by exact ⟨le_of_lt ht, le_rfl⟩) ht
  dsimp [f] at hv ⊢
  rw [gap39 n] at hv
  linarith

theorem gap47 (n : ℕ) (q : ℝ) (hn : 3 ≤ n) (hq : 1 < q) :
    psiAbove n q < phiAbove n q := by exact gap46 n q hn hq

theorem gap48 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : a ≠ 0) (hq : 1 < q) :
    scaledAbove n a q = phiAbove n q - psiAbove n q := by exact gap38 n a q hn ha hq

theorem gap49 (n : ℕ) (q : ℝ) (hn : 3 ≤ n) (hq : 1 < q) :
    0 < phiAbove n q - psiAbove n q := by linarith [gap47 n q hn hq]

theorem gap50 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : 0 < a) (hq : 1 < q) :
    0 < scaledAbove n a q := by
  rw [gap48 n a q hn ha.ne' hq]
  exact gap49 n q hn hq

theorem gap51 (n : ℕ) (a q : ℝ) (hn : 3 ≤ n)
    (ha : 0 < a) (hq : 1 < q) :
    geometricSum n a q <
      arithmeticSum n a (endpointStep n a q) := by
  have hs := gap50 n a q hn ha hq
  rw [scaledAbove] at hs
  have htwo : 0 < (2 : ℝ) / a := div_pos (by norm_num) ha
  have hone : 0 < q - 1 := sub_pos.mpr hq
  have hc : 0 < (2 / a) * (q - 1) := mul_pos htwo hone
  have hd : 0 < closedArithmeticSum n a q - geometricSum n a q := by
    rcases (mul_pos_iff.mp hs) with h | h
    · exact h.2
    · exact (not_lt_of_ge (le_of_lt hc) h.1).elim
  rw [← gap34 n a q (by omega)] at hd
  linarith

theorem gap52 (n : ℕ) (a : ℝ) :
    arithmeticSum n a 0 = geometricSum n a 1 := by simp [arithmeticSum, geometricSum, arithmeticTerm, geometricTerm]

def aux (a d q x : ℝ) : ℝ :=
  a + x * d - a * Real.rpow q x

theorem gap53 (n : ℕ) (a d q : ℝ) (hn : 1 ≤ n)
    (ha : 0 < a) (hd : 0 < d) (hfirst : 0 < a * q)
    (hend : a + (n : ℝ) * d = a * q ^ n) :
    0 < q := by
  exact pos_of_mul_pos_right hfirst (le_of_lt ha)

theorem gap54 (n : ℕ) (a d q : ℝ)
    (hend : a + (n : ℝ) * d = a * q ^ n) :
    a + (n : ℝ) * d = a * q ^ n := by exact hend

theorem gap55 (n : ℕ) (a d q : ℝ) (hq : 0 < q)
    (hend : a + (n : ℝ) * d = a * q ^ n) :
    aux a d q 0 = aux a d q n := by
  have h0 : aux a d q 0 = 0 := by
    simp [aux]
  have hr : Real.rpow q (n : ℝ) = q ^ n := rpow_nat_eq_pow q n
  have hn : aux a d q n = 0 := by
    unfold aux
    rw [hr]
    linarith
  exact h0.trans hn.symm

theorem gap56 (n : ℕ) (a d q : ℝ) (hq : 0 < q)
    (hend : a + (n : ℝ) * d = a * q ^ n) :
    aux a d q n = 0 := by
  have hr : Real.rpow q (n : ℝ) = q ^ n := rpow_nat_eq_pow q n
  unfold aux
  rw [hr]
  linarith

theorem gap57 (a d q : ℝ) (hq : 0 < q) :
    aux a d q 0 = 0 := by
  simp [aux]

theorem gap58 (n : ℕ) (a d q : ℝ) (hn : 0 < n)
    (hq : 0 < q)
    (hend : a + (n : ℝ) * d = a * q ^ n) :
    ∃ c ∈ Set.Ioo (0 : ℝ) n, deriv (aux a d q) c = 0 := by
  have hlt : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdiffAll : Differentiable ℝ (aux a d q) := by
    unfold aux
    exact differentiable_aux_expr a d q hq
  have hcont : ContinuousOn (aux a d q) (Set.Icc (0 : ℝ) n) :=
    hdiffAll.continuous.continuousOn
  have heq := gap55 n a d q hq hend
  exact exists_deriv_eq_zero hlt hcont heq

theorem gap59 (a d q x : ℝ) (hq : 0 < q) :
    deriv (deriv (aux a d q)) x =
      -a * Real.rpow q x * (Real.log q) ^ 2 := by
  unfold aux
  exact second_deriv_aux_expr a d q x hq

theorem gap60 (a d q x : ℝ) (ha : 0 < a)
    (hq : 0 < q) (hq1 : q ≠ 1) :
    -a * Real.rpow q x * (Real.log q) ^ 2 < 0 := by
  have hr : 0 < Real.rpow q x := Real.rpow_pos_of_pos hq x
  rcases lt_or_gt_of_ne hq1 with hqLt | hqGt
  · have hl : Real.log q < 0 := Real.log_neg hq hqLt
    have hs : 0 < (Real.log q) ^ 2 := sq_pos_of_neg hl
    have hp : 0 < a * Real.rpow q x * (Real.log q) ^ 2 :=
      mul_pos (mul_pos ha hr) hs
    calc
      -a * Real.rpow q x * (Real.log q) ^ 2 =
          -(a * Real.rpow q x * (Real.log q) ^ 2) := by ring
      _ < 0 := by linarith
  · have hl : 0 < Real.log q := Real.log_pos hqGt
    have hs : 0 < (Real.log q) ^ 2 := sq_pos_of_pos hl
    have hp : 0 < a * Real.rpow q x * (Real.log q) ^ 2 :=
      mul_pos (mul_pos ha hr) hs
    calc
      -a * Real.rpow q x * (Real.log q) ^ 2 =
          -(a * Real.rpow q x * (Real.log q) ^ 2) := by ring
      _ < 0 := by linarith

theorem gap61 (a d q x : ℝ) (ha : 0 < a)
    (hq : 0 < q) (hq1 : q ≠ 1) :
    deriv (deriv (aux a d q)) x < 0 := by
  rw [gap59 a d q x hq]
  exact gap60 a d q x ha hq hq1

theorem gap62 (a d q x : ℝ) (hq : 0 < q) :
    deriv (aux a d q) x =
      d - a * Real.rpow q x * Real.log q := by
  unfold aux
  exact deriv_aux_expr a d q x hq

theorem gap63 (a d q : ℝ) (ha : 0 < a)
    (hq : 0 < q) (hq1 : q ≠ 1) :
    StrictAnti (deriv (aux a d q)) := by
  apply strictAnti_of_deriv_neg
  intro x
  exact gap61 a d q x ha hq hq1

theorem gap64 (a d q c x : ℝ)
    (hanti : StrictAnti (deriv (aux a d q)))
    (hc : deriv (aux a d q) c = 0) (hx : x < c) :
    0 < deriv (aux a d q) x := by
  have h := hanti hx
  rw [hc] at h
  exact h

theorem gap65 (a d q c x : ℝ)
    (hanti : StrictAnti (deriv (aux a d q)))
    (hc : deriv (aux a d q) c = 0) (hx : c < x) :
    deriv (aux a d q) x < 0 := by
  have h := hanti hx
  rw [hc] at h
  exact h

theorem gap66 (n : ℕ) (a d q x : ℝ) (hn : 0 < n)
    (ha : 0 < a) (hq : 0 < q) (hq1 : q ≠ 1)
    (hend : a + (n : ℝ) * d = a * q ^ n)
    (hx : x ∈ Set.Icc (0 : ℝ) n) :
    0 ≤ aux a d q x := by
  obtain ⟨c, hcI, hc⟩ := gap58 n a d q hn hq hend
  have hanti := gap63 a d q ha hq hq1
  have hdiffAll : Differentiable ℝ (aux a d q) := by
    unfold aux
    exact differentiable_aux_expr a d q hq
  by_cases hxc : x ≤ c
  · have hmono : MonotoneOn (aux a d q) (Set.Icc 0 c) := by
      refine monotoneOn_of_deriv_nonneg (f := aux a d q) (convex_Icc 0 c)
        hdiffAll.continuous.continuousOn hdiffAll.differentiableOn ?_
      intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) c := by simpa [interior_Icc, hcI.1] using hy
      exact le_of_lt (gap64 a d q c y hanti hc hy'.2)
    have hx' : x ∈ Set.Icc (0 : ℝ) c := ⟨hx.1, hxc⟩
    have hz := hmono
      (show (0 : ℝ) ∈ Set.Icc 0 c by exact ⟨le_rfl, le_of_lt hcI.1⟩) hx' hx.1
    rw [gap57 a d q hq] at hz
    exact hz
  · have hcx : c ≤ x := le_of_not_ge hxc
    have hdec : AntitoneOn (aux a d q) (Set.Icc c n) := by
      refine antitoneOn_of_deriv_nonpos (f := aux a d q) (convex_Icc c n)
        hdiffAll.continuous.continuousOn hdiffAll.differentiableOn ?_
      intro y hy
      have hy' : y ∈ Set.Ioo c (n : ℝ) := by simpa [interior_Icc, hcI.2] using hy
      exact le_of_lt (gap65 a d q c y hanti hc hy'.1)
    have hx' : x ∈ Set.Icc c (n : ℝ) := ⟨hcx, hx.2⟩
    have hz := hdec hx'
      (show (n : ℝ) ∈ Set.Icc c n by exact ⟨le_of_lt hcI.2, le_rfl⟩) hx.2
    rw [gap56 n a d q hq hend] at hz
    exact hz

theorem gap67 (a d q : ℝ) (k : ℕ) :
    aux a d q k = a + k * d - a * Real.rpow q k := by rfl

theorem gap68 (n k : ℕ) (a d q : ℝ) (hn : 2 ≤ n)
    (ha : 0 < a) (hq : 0 < q) (hq1 : q ≠ 1)
    (hend : a + (n : ℝ) * d = a * q ^ n)
    (hk0 : 0 < k) (hkn : k < n) :
    0 < aux a d q k := by
  obtain ⟨c, hcI, hc⟩ := gap58 n a d q (by omega) hq hend
  have hanti := gap63 a d q ha hq hq1
  have hdiffAll : Differentiable ℝ (aux a d q) := by
    unfold aux
    exact differentiable_aux_expr a d q hq
  have hk0R : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hknR : (k : ℝ) < (n : ℝ) := by exact_mod_cast hkn
  by_cases hkc : (k : ℝ) < c
  · have hmono : StrictMonoOn (aux a d q) (Set.Icc 0 c) := by
      refine strictMonoOn_of_deriv_pos (f := aux a d q) (convex_Icc 0 c)
        hdiffAll.continuous.continuousOn ?_
      intro y hy
      have hy' : y ∈ Set.Ioo (0 : ℝ) c := by simpa [interior_Icc, hcI.1] using hy
      exact gap64 a d q c y hanti hc hy'.2
    have hz := hmono
      (show (0 : ℝ) ∈ Set.Icc 0 c by exact ⟨le_rfl, le_of_lt hcI.1⟩)
      (show (k : ℝ) ∈ Set.Icc 0 c by exact ⟨le_of_lt hk0R, le_of_lt hkc⟩) hk0R
    rw [gap57 a d q hq] at hz
    exact hz
  · have hck : c ≤ (k : ℝ) := le_of_not_gt hkc
    have hdec : StrictAntiOn (aux a d q) (Set.Icc c n) := by
      refine strictAntiOn_of_deriv_neg (f := aux a d q) (convex_Icc c n)
        hdiffAll.continuous.continuousOn ?_
      intro y hy
      have hy' : y ∈ Set.Ioo c (n : ℝ) := by simpa [interior_Icc, hcI.2] using hy
      exact gap65 a d q c y hanti hc hy'.1
    have hz := hdec
      (show (k : ℝ) ∈ Set.Icc c n by exact ⟨hck, le_of_lt hknR⟩)
      (show (n : ℝ) ∈ Set.Icc c n by exact ⟨le_of_lt hcI.2, le_rfl⟩) hknR
    rw [gap56 n a d q hq hend] at hz
    exact hz

theorem gap69 (n k : ℕ) (a d q : ℝ) (hn : 2 ≤ n)
    (ha : 0 < a) (hq : 0 < q) (hq1 : q ≠ 1)
    (hend : a + (n : ℝ) * d = a * q ^ n)
    (hk0 : 0 < k) (hkn : k < n) :
    0 < aux a d q k := by exact gap68 n k a d q hn ha hq hq1 hend hk0 hkn

theorem gap70 (n k : ℕ) (a d q : ℝ) (hn : 2 ≤ n)
    (ha : 0 < a) (hq : 0 < q) (hq1 : q ≠ 1)
    (hend : a + (n : ℝ) * d = a * q ^ n)
    (hk0 : 0 < k) (hkn : k < n) :
    a * q ^ k < a + k * d := by
  have h := gap69 n k a d q hn ha hq hq1 hend hk0 hkn
  change 0 < a + (k : ℝ) * d - a * Real.rpow q (k : ℝ) at h
  rw [rpow_nat_eq_pow q k] at h
  linarith

theorem gap71 (n : ℕ) (a d q : ℝ) (hn : 2 ≤ n)
    (ha : 0 < a) (hq : 0 < q) (hq1 : q ≠ 1)
    (hend : a + (n : ℝ) * d = a * q ^ n) :
    (∑ k ∈ Finset.range (n + 1), a * q ^ k) <
      ∑ k ∈ Finset.range (n + 1), (a + k * d) := by
  have hle : ∀ k ∈ Finset.range (n + 1), a * q ^ k ≤ a + k * d := by
    intro k hk
    have hkn : k ≤ n := by simpa using hk
    have hkR : (0 : ℝ) ≤ (k : ℝ) := by positivity
    have hknR : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have haux := gap66 n a d q k (by omega) ha hq hq1 hend ⟨hkR, hknR⟩
    rw [gap67] at haux
    have hr : Real.rpow q (k : ℝ) = q ^ k := rpow_nat_eq_pow q k
    rw [hr] at haux
    linarith
  apply Finset.sum_lt_sum hle
  refine ⟨1, ?_, ?_⟩
  · exact Finset.mem_range.mpr (by omega)
  · exact gap70 n 1 a d q hn ha hq hq1 hend (by omega) (by omega)

theorem gap72 (n : ℕ) (a d q : ℝ) (hn : 1 ≤ n)
    (ha : 0 < a) (hq : 0 < q)
    (hend : a + (n : ℝ) * d = a * q ^ n) :
    (∑ k ∈ Finset.range (n + 1), a * q ^ k) ≤
      ∑ k ∈ Finset.range (n + 1), (a + k * d) := by
  by_cases hn2 : 2 ≤ n
  · by_cases hq1 : q = 1
    · subst q
      have hn0 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (by omega : n ≠ 0)
      have hend' : a + (n : ℝ) * d = a := by simpa using hend
      have hnd : (n : ℝ) * d = 0 := by linarith
      have hd : d = 0 := (mul_eq_zero.mp hnd).resolve_left hn0
      subst d
      simp
    · exact le_of_lt (gap71 n a d q hn2 ha hq hq1 hend)
  · have hne : n = 1 := by omega
    subst n
    norm_num [Finset.sum_range_succ] at hend ⊢
    linarith

def SequenceData (n : ℕ) (u v : ℕ → ℝ) : Prop :=
  ∃ a d q : ℝ, 0 < a ∧ 0 < q ∧
    (∀ k < n, u k = a + k * d) ∧
    (∀ k < n, v k = a * q ^ k) ∧
    u (n - 1) = v (n - 1)

theorem gap73 (n : ℕ) (u v : ℕ → ℝ) (hn : 2 ≤ n)
    (hdata : SequenceData n u v) :
    (∑ k ∈ Finset.range n, v k) ≤
      ∑ k ∈ Finset.range n, u k := by
  rcases hdata with ⟨a, d, q, ha, hq, hu, hv, henduv⟩
  have hm : 1 ≤ n - 1 := by omega
  have hend : a + ((n - 1 : ℕ) : ℝ) * d = a * q ^ (n - 1) := by
    calc
      a + ((n - 1 : ℕ) : ℝ) * d = u (n - 1) :=
        (hu (n - 1) (by omega)).symm
      _ = v (n - 1) := henduv
      _ = a * q ^ (n - 1) := hv (n - 1) (by omega)
  have hs := gap72 (n - 1) a d q hm ha hq hend
  have hr : n - 1 + 1 = n := by omega
  rw [hr] at hs
  calc
    (∑ k ∈ Finset.range n, v k) = ∑ k ∈ Finset.range n, a * q ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hv k (by simpa using hk)
    _ ≤ ∑ k ∈ Finset.range n, (a + k * d) := hs
    _ = ∑ k ∈ Finset.range n, u k := by
      apply Finset.sum_congr rfl
      intro k hk
      symm
      exact hu k (by simpa using hk)

end

end ProofGap.Exercise1292
