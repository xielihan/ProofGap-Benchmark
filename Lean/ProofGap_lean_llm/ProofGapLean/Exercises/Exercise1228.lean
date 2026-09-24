import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1228

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (m : ℕ) (x : ℝ) : ℝ := x ^ m * Real.exp (-x)
def z (m : ℕ) : ℝ → ℝ := iterDeriv m (y m)
def L (m : ℕ) (x : ℝ) : ℝ := Real.exp x * z m x

def polynomialExpansion (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℝ) ^ j * (Nat.choose m j : ℝ) *
      (Nat.factorial m : ℝ) / (Nat.factorial j : ℝ) * x ^ j

def exponentialExpansion (m : ℕ) (x : ℝ) : ℝ :=
  Real.exp (-x) * polynomialExpansion m x

theorem gap1 (m : ℕ) (x : ℝ) :
    L m x = Real.exp x * exponentialExpansion m x := by
  have hcoeff (j : ℕ) (hj : j ∈ Finset.range (m + 1)) :
      (m.descFactorial (m - j) : ℝ) =
        (Nat.factorial m : ℝ) / (Nat.factorial j : ℝ) := by
    have hjm : j ≤ m := by
      have := Finset.mem_range.mp hj
      omega
    have hnat := Nat.factorial_mul_descFactorial (Nat.sub_le m j)
    have hsub : m - (m - j) = j := by omega
    rw [hsub] at hnat
    apply (eq_div_iff (by positivity : (Nat.factorial j : ℝ) ≠ 0)).2
    norm_cast
    simpa [mul_comm] using hnat
  unfold L z exponentialExpansion
  rw [show y m = fun t : ℝ => Real.exp ((-1 : ℝ) * t) * t ^ m by
    funext t
    simp [y]
    ring]
  rw [iterDeriv, ← iteratedDeriv_eq_iterate]
  change Real.exp x *
      iteratedDeriv m (fun t : ℝ => Real.exp ((-1 : ℝ) * t) * t ^ m) x =
    Real.exp x * (Real.exp (-x) * polynomialExpansion m x)
  rw [iteratedDeriv_fun_mul (n := m) (by fun_prop) (by fun_prop)]
  simp_rw [iteratedDeriv_exp_const_mul, iteratedDeriv_pow]
  unfold polynomialExpansion
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [hcoeff j hj]
  have hjm : j ≤ m := by
    have := Finset.mem_range.mp hj
    omega
  have he : m - (m - j) = j := by omega
  rw [he]
  ring

theorem gap2 (m : ℕ) (x : ℝ) :
    L m x = polynomialExpansion m x := by
  rw [gap1, exponentialExpansion]
  rw [show Real.exp x * (Real.exp (-x) * polynomialExpansion m x) =
      (Real.exp x * Real.exp (-x)) * polynomialExpansion m x by ring,
    ← Real.exp_add]
  simp

theorem gap3 (m : ℕ) (x : ℝ) :
    L m x = (-1 : ℝ) ^ m *
      ((-1 : ℝ) ^ m * polynomialExpansion m x) := by
  rw [gap2]
  rw [← mul_assoc, ← pow_add]
  have he : (-1 : ℝ) ^ (m + m) = 1 := by
    rw [← two_mul, pow_mul]
    norm_num
  rw [he, one_mul]

theorem gap4 (m : ℕ) (x : ℝ) :
    deriv (y m) x =
      (m : ℝ) * x ^ (m - 1) * Real.exp (-x) - x ^ m * Real.exp (-x) := by
  have hp := (hasDerivAt_id x).pow m
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) x := by
    convert (hasDerivAt_id x).neg using 1 <;> simp [id]
  have he := (Real.hasDerivAt_exp (-x)).comp x hn
  unfold y
  convert hp.mul he |>.deriv using 1 <;> simp [id] <;> ring

theorem gap5 (m : ℕ) (x : ℝ) :
    x * deriv (y m) x + (x - m) * y m x = 0 := by
  rw [gap4]
  unfold y
  rcases m with _ | m
  · norm_num
  · rw [Nat.succ_sub_one, pow_succ]
    push_cast
    ring

private theorem iteratedDeriv_affine (i : ℕ) (c x : ℝ) :
    iteratedDeriv i (fun t : ℝ => t - c) x =
      if i = 0 then x - c else if i = 1 then 1 else 0 := by
  rw [iteratedDeriv_fun_sub (n := i) (by fun_prop) (by fun_prop)]
  simp [iteratedDeriv_fun_id, iteratedDeriv_const]
  by_cases h0 : i = 0
  · subst i
    simp
  by_cases h1 : i = 1
  · subst i
    simp
  simp [h0, h1]

private theorem sum_linear (n : ℕ) (hn : 1 ≤ n)
    (a : ℝ) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) *
        (if i = 0 then a else if i = 1 then 1 else 0) *
        G (n - i)) =
      a * G n + (n : ℝ) * G (n - 1) := by
  have hsummand (i : ℕ) :
      (Nat.choose n i : ℝ) *
          (if i = 0 then a else if i = 1 then 1 else 0) *
          G (n - i) =
        (if i = 0 then a * G n else 0) +
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

private theorem iteratedDeriv_affine_mul (n : ℕ) (hn : 1 ≤ n)
    (c x : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun t => (t - c) * f t) x =
      (x - c) * iteratedDeriv n f x +
        (n : ℝ) * iteratedDeriv (n - 1) f x := by
  rw [iteratedDeriv_fun_mul (n := n) (by fun_prop) hf]
  rw [show
      (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          iteratedDeriv i (fun t : ℝ => t - c) x *
          iteratedDeriv (n - i) f x) =
        ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) *
            (if i = 0 then x - c else if i = 1 then 1 else 0) *
            iteratedDeriv (n - i) f x by
        apply Finset.sum_congr rfl
        intro i hi
        rw [iteratedDeriv_affine]]
  exact sum_linear n hn (x - c) (fun j => iteratedDeriv j f x)

theorem gap6 (m : ℕ) (x : ℝ) :
    x * iterDeriv (m + 2) (y m) x +
        (m + 1 : ℕ) * iterDeriv (m + 1) (y m) x +
        (x - m) * iterDeriv (m + 1) (y m) x +
        (m + 1 : ℕ) * iterDeriv m (y m) x = 0 := by
  have heq :
      (fun t : ℝ => t * deriv (y m) t + (t - m) * y m t) =
        fun _ => 0 := by
    funext t
    exact gap5 m t
  have hy : ContDiff ℝ (m + 1) (y m) := by
    unfold y
    fun_prop
  have hyd : ContDiff ℝ (m + 1) (deriv (y m)) := by
    apply ContDiff.deriv'
    unfold y
    fun_prop
  have hfirst : ContDiffAt ℝ (m + 1)
      (fun t : ℝ => (t - 0) * deriv (y m) t) x :=
    (by fun_prop)
  have hsecond : ContDiffAt ℝ (m + 1)
      (fun t : ℝ => (t - (m : ℝ)) * y m t) x :=
    (by fun_prop)
  have hd := congrArg
    (fun f : ℝ → ℝ => iteratedDeriv (m + 1) f x) heq
  change iteratedDeriv (m + 1)
      (fun t : ℝ => t * deriv (y m) t +
        (t - (m : ℝ)) * y m t) x =
    iteratedDeriv (m + 1) (fun _ : ℝ => 0) x at hd
  rw [show (fun t : ℝ => t * deriv (y m) t +
        (t - (m : ℝ)) * y m t) =
      fun t => (t - 0) * deriv (y m) t +
        (t - (m : ℝ)) * y m t by
      funext t
      ring] at hd
  rw [iteratedDeriv_fun_add hfirst hsecond,
    iteratedDeriv_affine_mul (m + 1) (by omega) 0 x
      (deriv (y m)) hyd.contDiffAt,
    iteratedDeriv_affine_mul (m + 1) (by omega) (m : ℝ) x
      (y m) hy.contDiffAt,
    iteratedDeriv_const] at hd
  simp only [← iteratedDeriv_succ'] at hd
  simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
  convert hd using 1 <;> push_cast <;> ring

theorem gap7 (m : ℕ) (x : ℝ) :
    x * iterDeriv (m + 2) (y m) x +
        (1 + x) * iterDeriv (m + 1) (y m) x +
        (m + 1 : ℕ) * iterDeriv m (y m) x = 0 := by
  have h := gap6 m x
  push_cast at h ⊢
  linarith

theorem gap8 (m : ℕ) (x : ℝ) :
    x * iterDeriv 2 (z m) x + (1 + x) * deriv (z m) x +
        (m + 1 : ℕ) * z m x = 0 := by
  simpa [z, iterDeriv, Function.iterate_succ_apply',
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using gap7 m x

theorem gap9 (m : ℕ) (x : ℝ) :
    L m x = Real.exp x * z m x := by
  rfl

theorem gap10 (m : ℕ) (x : ℝ) :
    deriv (L m) x = Real.exp x * (z m x + deriv (z m) x) := by
  have hy : ContDiff ℝ (m + 1) (y m) := by
    unfold y
    fun_prop
  have hz : DifferentiableAt ℝ (z m) x := by
    unfold z iterDeriv
    rw [← iteratedDeriv_eq_iterate]
    exact (hy.differentiable_iteratedDeriv' m) x
  have h := (Real.hasDerivAt_exp x).mul hz.hasDerivAt
  unfold L
  convert h.deriv using 1 <;> ring

theorem gap11 (m : ℕ) (x : ℝ) :
    iterDeriv 2 (L m) x =
      Real.exp x * (z m x + 2 * deriv (z m) x + iterDeriv 2 (z m) x) := by
  have hy : ContDiff ℝ (m + 2) (y m) := by
    unfold y
    fun_prop
  have hz : DifferentiableAt ℝ (z m) x := by
    have hy1 : ContDiff ℝ (m + 1) (y m) := by
      unfold y
      fun_prop
    unfold z iterDeriv
    rw [← iteratedDeriv_eq_iterate]
    exact hy1.differentiable_iteratedDeriv' m x
  have hdz : DifferentiableAt ℝ (deriv (z m)) x := by
    unfold z iterDeriv
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_succ]
    exact hy.differentiable_iteratedDeriv' (m + 1) x
  have heq : deriv (L m) =
      fun t => Real.exp t * (z m t + deriv (z m) t) := by
    funext t
    exact gap10 m t
  rw [show iterDeriv 2 (L m) x = deriv (deriv (L m)) x by
    simp [iterDeriv, Function.iterate_succ_apply'], heq]
  have hinner := hz.hasDerivAt.add hdz.hasDerivAt
  have h := (Real.hasDerivAt_exp x).mul hinner
  convert h.deriv using 1 <;>
    simp [iterDeriv, Function.iterate_succ_apply'] <;> ring

theorem gap12 (m : ℕ) (x : ℝ) :
    x * iterDeriv 2 (L m) x + (1 - x) * deriv (L m) x + (m : ℝ) * L m x =
      Real.exp x * (x * (z m x + 2 * deriv (z m) x + iterDeriv 2 (z m) x) +
        (1 - x) * (z m x + deriv (z m) x) + (m : ℝ) * z m x) := by
  rw [gap9, gap10, gap11]
  ring

theorem gap13 (m : ℕ) (x : ℝ) :
    x * iterDeriv 2 (L m) x + (1 - x) * deriv (L m) x + (m : ℝ) * L m x =
      Real.exp x * (x * iterDeriv 2 (z m) x + (x + 1) * deriv (z m) x +
        (m + 1 : ℕ) * z m x) := by
  rw [gap12]
  push_cast
  ring

theorem gap14 (m : ℕ) (x : ℝ) :
    x * iterDeriv 2 (L m) x + (1 - x) * deriv (L m) x +
        (m : ℝ) * L m x = 0 := by
  rw [gap13]
  rw [show x + 1 = 1 + x by ring, gap8]
  ring

theorem gap15 (m : ℕ) (x : ℝ) :
    L m x = polynomialExpansion m x ∧
      x * iterDeriv 2 (L m) x + (1 - x) * deriv (L m) x +
        (m : ℝ) * L m x = 0 := by
  exact ⟨gap2 m x, gap14 m x⟩

end

end ProofGap.Exercise1228
