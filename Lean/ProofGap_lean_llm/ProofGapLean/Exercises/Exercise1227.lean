import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Choose.Cast

namespace ProofGap.Exercise1227

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (m : ℕ) (x : ℝ) : ℝ := (x ^ 2 - 1) ^ m
def P (m : ℕ) (x : ℝ) : ℝ :=
  iterDeriv m (y m) x / ((2 : ℝ) ^ m * (Nat.factorial m : ℝ))

theorem gap1 (m : ℕ) (x : ℝ) :
    deriv (y m) x = 2 * (m : ℝ) * x * (x ^ 2 - 1) ^ (m - 1) := by
  unfold y
  have hbase : HasDerivAt (fun z : ℝ => z ^ 2 - 1) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).sub_const 1 using 1 <;>
      simp [id] <;> ring
  convert (hbase.pow m).deriv using 1 <;> ring

theorem gap2 (m : ℕ) (x : ℝ) :
    (x ^ 2 - 1) * deriv (y m) x = 2 * (m : ℝ) * x * y m x := by
  rw [gap1]
  unfold y
  rcases m with _ | m
  · norm_num
  · rw [Nat.succ_sub_one, pow_succ]
    ring

private theorem iteratedDeriv_quadratic (i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun z : ℝ => z ^ 2 - 1) x =
      if i = 0 then x ^ 2 - 1 else if i = 1 then 2 * x else if i = 2 then 2 else 0 := by
  rw [iteratedDeriv_fun_sub (n := i) (by fun_prop) (by fun_prop)]
  simp only [iteratedDeriv_pow, iteratedDeriv_const]
  by_cases h0 : i = 0
  · subst i
    norm_num
  by_cases h1 : i = 1
  · subst i
    norm_num
  by_cases h2 : i = 2
  · subst i
    norm_num
  simp [h0, h1, h2, Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : 2 < i)]

private theorem sum_quadratic (n : ℕ) (hn : 2 ≤ n) (x : ℝ) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) *
        (if i = 0 then x ^ 2 - 1
          else if i = 1 then 2 * x else if i = 2 then 2 else 0) *
        G (n - i)) =
      (x ^ 2 - 1) * G n + 2 * (n : ℝ) * x * G (n - 1) +
        (n : ℝ) * (n - 1 : ℕ) * G (n - 2) := by
  have hsummand (i : ℕ) :
      (Nat.choose n i : ℝ) *
          (if i = 0 then x ^ 2 - 1
            else if i = 1 then 2 * x else if i = 2 then 2 else 0) *
          G (n - i) =
        (if i = 0 then (x ^ 2 - 1) * G n else 0) +
        (if i = 1 then (n : ℝ) * 2 * x * G (n - 1) else 0) +
        (if i = 2 then (Nat.choose n 2 : ℝ) * 2 * G (n - 2) else 0) := by
    by_cases h0 : i = 0
    · subst i
      simp
    by_cases h1 : i = 1
    · subst i
      simp [h0, Nat.choose_one_right]
      left
      ring
    by_cases h2 : i = 2
    · subst i
      simp
    simp [h0, h1, h2]
  simp_rw [hsummand]
  simp only [Finset.sum_add_distrib]
  simp [Finset.mem_range, hn]
  rw [if_pos (by omega : 0 < n)]
  rw [Nat.cast_choose_two ℝ]
  push_cast
  rw [Nat.cast_sub (by omega : 1 ≤ n)]
  ring

private theorem sum_linear (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) *
        (if i = 0 then x else if i = 1 then 1 else 0) *
        G (n - i)) =
      x * G n + (n : ℝ) * G (n - 1) := by
  have hsummand (i : ℕ) :
      (Nat.choose n i : ℝ) *
          (if i = 0 then x else if i = 1 then 1 else 0) *
          G (n - i) =
        (if i = 0 then x * G n else 0) +
        (if i = 1 then (n : ℝ) * G (n - 1) else 0) := by
    by_cases h0 : i = 0
    · subst i
      simp
    by_cases h1 : i = 1
    · subst i
      simp [h0, Nat.choose_one_right]
    simp [h0, h1]
  simp_rw [hsummand]
  simp only [Finset.sum_add_distrib]
  simp [Finset.mem_range]
  omega

theorem gap3 (m : ℕ) (x : ℝ) :
    (x ^ 2 - 1) * iterDeriv (m + 2) (y m) x +
        2 * (m + 1 : ℕ) * x * iterDeriv (m + 1) (y m) x +
        (m : ℝ) * (m + 1 : ℕ) * iterDeriv m (y m) x =
      2 * (m : ℝ) * x * iterDeriv (m + 1) (y m) x +
        2 * (m : ℝ) * (m + 1 : ℕ) * iterDeriv m (y m) x := by
  rcases m with _ | m
  · have hzero : deriv (y 0) = fun _ => 0 := by
      funext z
      simpa using gap1 0 z
    simp [iterDeriv, Function.iterate_succ_apply', hzero]
  · have heq :
        (fun z : ℝ => (z ^ 2 - 1) * deriv (y (m + 1)) z) =
          fun z => 2 * (m + 1 : ℕ) * z * y (m + 1) z := by
      funext z
      exact gap2 (m + 1) z
    have hy : ContDiff ℝ (m + 2) (y (m + 1)) := by
      unfold y
      fun_prop
    have hyd : ContDiff ℝ (m + 2) (deriv (y (m + 1))) := by
      apply ContDiff.deriv'
      unfold y
      fun_prop
    have hd := congrArg
      (fun f : ℝ → ℝ => iteratedDeriv (m + 2) f x) heq
    change iteratedDeriv (m + 2)
        (fun z : ℝ => (z ^ 2 - 1) * deriv (y (m + 1)) z) x =
      iteratedDeriv (m + 2)
        (fun z : ℝ => 2 * (m + 1 : ℕ) * z * y (m + 1) z) x at hd
    rw [iteratedDeriv_fun_mul (n := m + 2)
      (f := fun z : ℝ => z ^ 2 - 1) (g := deriv (y (m + 1)))
      (by fun_prop) hyd.contDiffAt] at hd
    rw [show (fun z : ℝ => 2 * (m + 1 : ℕ) * z * y (m + 1) z) =
        fun z => (2 * (m + 1 : ℕ) : ℝ) * (z * y (m + 1) z) by
          funext z
          push_cast
          ring,
      iteratedDeriv_const_mul_field,
      iteratedDeriv_fun_mul (n := m + 2)
        (f := fun z : ℝ => z) (g := y (m + 1))
        (by fun_prop) hy.contDiffAt] at hd
    rw [show
        (∑ i ∈ Finset.range (m + 2 + 1),
          (Nat.choose (m + 2) i : ℝ) *
            iteratedDeriv i (fun z : ℝ => z ^ 2 - 1) x *
            iteratedDeriv (m + 2 - i) (deriv (y (m + 1))) x) =
          (x ^ 2 - 1) * iteratedDeriv (m + 2) (deriv (y (m + 1))) x +
            2 * (m + 2 : ℝ) * x *
              iteratedDeriv (m + 2 - 1) (deriv (y (m + 1))) x +
            (m + 2 : ℝ) * (m + 2 - 1 : ℕ) *
              iteratedDeriv (m + 2 - 2) (deriv (y (m + 1))) x by
          rw [show (∑ i ∈ Finset.range (m + 2 + 1),
              (Nat.choose (m + 2) i : ℝ) *
                iteratedDeriv i (fun z : ℝ => z ^ 2 - 1) x *
                iteratedDeriv (m + 2 - i) (deriv (y (m + 1))) x) =
            ∑ i ∈ Finset.range (m + 2 + 1),
              (Nat.choose (m + 2) i : ℝ) *
                (if i = 0 then x ^ 2 - 1
                  else if i = 1 then 2 * x else if i = 2 then 2 else 0) *
                iteratedDeriv (m + 2 - i) (deriv (y (m + 1))) x by
              apply Finset.sum_congr rfl
              intro i hi
              rw [iteratedDeriv_quadratic]]
          simpa only [Nat.cast_add, Nat.cast_ofNat] using
            (sum_quadratic (m + 2) (by omega) x
              (fun j => iteratedDeriv j (deriv (y (m + 1))) x)),
        show
          (∑ i ∈ Finset.range (m + 2 + 1),
            (Nat.choose (m + 2) i : ℝ) *
              iteratedDeriv i (fun z : ℝ => z) x *
              iteratedDeriv (m + 2 - i) (y (m + 1)) x) =
            x * iteratedDeriv (m + 2) (y (m + 1)) x +
              (m + 2 : ℝ) * iteratedDeriv (m + 2 - 1) (y (m + 1)) x by
          rw [show (∑ i ∈ Finset.range (m + 2 + 1),
              (Nat.choose (m + 2) i : ℝ) *
                iteratedDeriv i (fun z : ℝ => z) x *
                iteratedDeriv (m + 2 - i) (y (m + 1)) x) =
            ∑ i ∈ Finset.range (m + 2 + 1),
              (Nat.choose (m + 2) i : ℝ) *
                (if i = 0 then x else if i = 1 then 1 else 0) *
                iteratedDeriv (m + 2 - i) (y (m + 1)) x by
              apply Finset.sum_congr rfl
              intro i hi
              rw [iteratedDeriv_fun_id]]
          simpa only [Nat.cast_add, Nat.cast_ofNat] using
            (sum_linear (m + 2) (by omega) x
              (fun j => iteratedDeriv j (y (m + 1)) x))] at hd
    simp only [← iteratedDeriv_succ'] at hd
    simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
    convert hd using 1 <;> push_cast <;> ring

theorem gap4 (m : ℕ) (x : ℝ) :
    (x ^ 2 - 1) * iterDeriv (m + 2) (y m) x +
        2 * x * iterDeriv (m + 1) (y m) x -
        (m : ℝ) * (m + 1 : ℕ) * iterDeriv m (y m) x = 0 := by
  have h := gap3 m x
  push_cast at h ⊢
  linarith

theorem gap5 (m : ℕ) (x : ℝ) :
    (x ^ 2 - 1) * iterDeriv 2 (P m) x +
        2 * x * deriv (P m) x -
        (m : ℝ) * (m + 1 : ℕ) * P m x = 0 := by
  let D : ℝ := (2 : ℝ) ^ m * (Nat.factorial m : ℝ)
  have hD : D ≠ 0 := by
    dsimp [D]
    positivity
  have hP : P m = fun z => (1 / D) * iterDeriv m (y m) z := by
    funext z
    simp only [P]
    dsimp [D]
    field_simp
  have hP1 : deriv (P m) =
      fun z => (1 / D) * iterDeriv (m + 1) (y m) z := by
    rw [hP, deriv_const_mul_field']
    funext z
    simp [iterDeriv, Function.iterate_succ_apply']
  have hP2 : iterDeriv 2 (P m) =
      fun z => (1 / D) * iterDeriv (m + 2) (y m) z := by
    rw [show iterDeriv 2 (P m) = deriv (deriv (P m)) by
      funext z
      simp [iterDeriv, Function.iterate_succ_apply']]
    rw [hP1, deriv_const_mul_field']
    funext z
    simp [iterDeriv, Function.iterate_succ_apply']
  rw [hP2, hP1, hP]
  have h := gap4 m x
  dsimp [D]
  field_simp [hD]
  nlinarith

theorem gap6 (m : ℕ) (x : ℝ) :
    (1 - x ^ 2) * iterDeriv 2 (P m) x -
        2 * x * deriv (P m) x +
        (m : ℝ) * (m + 1 : ℕ) * P m x = 0 := by
  have h := gap5 m x
  linarith

theorem gap7 (m : ℕ) (x : ℝ) :
    (1 - x ^ 2) * iterDeriv 2 (P m) x -
        2 * x * deriv (P m) x +
        (m : ℝ) * (m + 1 : ℕ) * P m x = 0 := by
  exact gap6 m x

end

end ProofGap.Exercise1227
