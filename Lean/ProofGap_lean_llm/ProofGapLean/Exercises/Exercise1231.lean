import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.RingTheory.Polynomial.Hermite.Gaussian

namespace ProofGap.Exercise1231

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (x : ℝ) : ℝ := Real.exp (-x ^ 2)
def z (m : ℕ) : ℝ → ℝ := iterDeriv m y
def H (m : ℕ) (x : ℝ) : ℝ := (-1 : ℝ) ^ m * Real.exp (x ^ 2) * z m x

def polynomialExpansion (m : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m / 2 + 1),
    (-1 : ℝ) ^ k * (Nat.factorial m : ℝ) /
      ((Nat.factorial k : ℝ) * (Nat.factorial (m - 2 * k) : ℝ)) *
      (2 * x) ^ (m - 2 * k)

private theorem even_factorial (k : ℕ) :
    Nat.factorial (2 * k) =
      2 ^ k * Nat.factorial k * (2 * k - 1).doubleFactorial := by
  cases k with
  | zero => norm_num
  | succ k =>
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
      rw [Nat.factorial_eq_mul_doubleFactorial]
      rw [show (2 * k + 1 + 1) = 2 * (k + 1) by omega,
        Nat.doubleFactorial_two_mul]

private theorem sqrt_two_pow_term (k j : ℕ) (x : ℝ) :
    (Real.sqrt 2) ^ (2 * k + j) *
        (((Polynomial.hermite (2 * k + j)).coeff j : ℤ) : ℝ) *
        (Real.sqrt 2 * x) ^ j =
      (-1 : ℝ) ^ k * (Nat.factorial (2 * k + j) : ℝ) /
          ((Nat.factorial k : ℝ) * (Nat.factorial j : ℝ)) *
          (2 * x) ^ j := by
  rw [Polynomial.coeff_hermite_explicit]
  push_cast
  have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hsj : Real.sqrt 2 ^ j * Real.sqrt 2 ^ j = 2 ^ j := by
    rw [← mul_pow, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hpow :
      Real.sqrt 2 ^ (2 * k + j) * (Real.sqrt 2 * x) ^ j =
        (2 : ℝ) ^ k * 2 ^ j * x ^ j := by
    rw [pow_add, pow_mul, hs, mul_pow]
    rw [show
        2 ^ k * Real.sqrt 2 ^ j * (Real.sqrt 2 ^ j * x ^ j) =
          2 ^ k * (Real.sqrt 2 ^ j * Real.sqrt 2 ^ j) * x ^ j by ring,
      hsj]
  rw [show
      Real.sqrt 2 ^ (2 * k + j) *
          ((-1 : ℝ) ^ k * ↑(2 * k - 1).doubleFactorial *
            ↑((2 * k + j).choose j)) *
          (Real.sqrt 2 * x) ^ j =
        (-1 : ℝ) ^ k * ↑(2 * k - 1).doubleFactorial *
          ↑((2 * k + j).choose j) *
          (Real.sqrt 2 ^ (2 * k + j) * (Real.sqrt 2 * x) ^ j) by ring,
    hpow, mul_pow]
  have hchoose := Nat.choose_mul_factorial_mul_factorial
    (show j ≤ 2 * k + j by omega)
  rw [show 2 * k + j - j = 2 * k by omega] at hchoose
  have hfac := even_factorial k
  rw [hfac] at hchoose
  have hnat :
      (2 * k - 1).doubleFactorial * (2 * k + j).choose j *
          2 ^ k * Nat.factorial k * Nat.factorial j =
        Nat.factorial (2 * k + j) := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hchoose
  field_simp
  have hreal :
      (↑(2 * k - 1).doubleFactorial : ℝ) *
          ↑((2 * k + j).choose j) *
          (2 : ℝ) ^ k * ↑(Nat.factorial k) * ↑(Nat.factorial j) =
        ↑(Nat.factorial (2 * k + j)) := by
    exact_mod_cast hnat
  calc
    (↑(2 * k - 1).doubleFactorial : ℝ) *
          ↑((2 * k + j).choose j) *
          2 ^ k * x ^ j * ↑(Nat.factorial k) * ↑(Nat.factorial j) =
        x ^ j * ((↑(2 * k - 1).doubleFactorial : ℝ) *
          ↑((2 * k + j).choose j) *
          2 ^ k * ↑(Nat.factorial k) * ↑(Nat.factorial j)) := by ring
    _ = x ^ j * ↑(Nat.factorial (2 * k + j)) := by rw [hreal]

private theorem scaled_hermite_eq_expansion (m : ℕ) (x : ℝ) :
    Real.sqrt 2 ^ m *
        Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m) =
      polynomialExpansion m x := by
  rw [Polynomial.aeval_eq_sum_range, Polynomial.natDegree_hermite]
  simp only [Finset.mul_sum]
  simp_rw [← Int.cast_smul_eq_zsmul ℝ, smul_eq_mul]
  let term : ℕ → ℝ := fun j =>
    Real.sqrt 2 ^ m *
      (↑((Polynomial.hermite m).coeff j) * (Real.sqrt 2 * x) ^ j)
  let relevant := (Finset.range (m + 1)).filter fun j => Even (m + j)
  have hzero (j : ℕ) (hj : j ∈ Finset.range (m + 1))
      (hjr : j ∉ relevant) : term j = 0 := by
    have hne : ¬Even (m + j) := by
      simpa [relevant, Finset.mem_filter, hj] using hjr
    simp [term, Polynomial.coeff_hermite, hne]
  have hsubset : relevant ⊆ Finset.range (m + 1) := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hfilter :
      ∑ j ∈ relevant, term j =
        ∑ j ∈ Finset.range (m + 1), term j :=
    Finset.sum_subset hsubset hzero
  have hreindex :
      (∑ k ∈ Finset.range (m / 2 + 1),
        (-1 : ℝ) ^ k * (Nat.factorial m : ℝ) /
          ((Nat.factorial k : ℝ) * (Nat.factorial (m - 2 * k) : ℝ)) *
          (2 * x) ^ (m - 2 * k)) =
        ∑ j ∈ relevant, term j := by
    refine Finset.sum_bij (fun k _ => m - 2 * k) ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_range] at hk
      have hkm : 2 * k ≤ m := by omega
      simp only [relevant, Finset.mem_filter, Finset.mem_range]
      constructor
      · omega
      · use m - k
        omega
    · intro a ha b hb hab
      simp only [Finset.mem_range] at ha hb
      have ham : 2 * a ≤ m := by omega
      have hbm : 2 * b ≤ m := by omega
      change m - 2 * a = m - 2 * b at hab
      omega
    · intro j hj
      simp only [relevant, Finset.mem_filter, Finset.mem_range] at hj
      rcases hj with ⟨hjm, heven⟩
      have hjle : j ≤ m := by omega
      have hdiff : Even (m - j) := by
        rw [Nat.even_add, ← Nat.even_sub hjle] at heven
        exact heven
      rcases hdiff with ⟨q, hq⟩
      refine ⟨(m - j) / 2, ?_, ?_⟩
      · simp only [Finset.mem_range]
        omega
      · change m - 2 * ((m - j) / 2) = j
        omega
    · intro k hk
      simp only [Finset.mem_range] at hk
      have hkm : 2 * k ≤ m := by omega
      have hm : m = 2 * k + (m - 2 * k) := by omega
      dsimp only [term]
      rw [hm]
      have hsub : 2 * k + (m - 2 * k) - 2 * k = m - 2 * k := by omega
      rw [hsub]
      simpa only [mul_assoc] using (sqrt_two_pow_term k (m - 2 * k) x).symm
  change ∑ j ∈ Finset.range (m + 1), term j = _
  unfold polynomialExpansion
  rw [← hfilter, ← hreindex]

theorem gap1 (x : ℝ) :
    deriv y x = -2 * x * Real.exp (-x ^ 2) := by
  unfold y
  have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).neg using 1 <;>
      simp only [id_eq] <;> ring
  convert ((Real.hasDerivAt_exp (-x ^ 2)).comp x hsq).deriv using 1 <;> ring

theorem gap2 (x : ℝ) :
    -2 * x * Real.exp (-x ^ 2) =
      (-1 : ℝ) ^ 1 * (2 * x) ^ 1 * Real.exp (-x ^ 2) := by
  ring

theorem gap3 (x : ℝ) :
    deriv y x = (-1 : ℝ) ^ 1 * (2 * x) ^ 1 * Real.exp (-x ^ 2) := by
  rw [gap1, gap2]

theorem gap4 (x : ℝ) :
    iterDeriv 2 y x = Real.exp (-x ^ 2) * ((-2 * x) ^ 2 - 2) := by
  have heq : deriv y = fun t : ℝ => -2 * t * Real.exp (-t ^ 2) := by
    funext t
    exact gap1 t
  rw [show iterDeriv 2 y x = deriv (deriv y) x by
    simp [iterDeriv, Function.iterate_succ_apply']]
  rw [heq]
  have hlin : HasDerivAt (fun t : ℝ => -2 * t) (-2) x := by
    convert (hasDerivAt_id x).const_mul (-2) using 1 <;> ring
  have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).neg using 1 <;>
      simp only [id_eq] <;> ring
  have hexp := (Real.hasDerivAt_exp (-x ^ 2)).comp x hsq
  convert (hlin.mul hexp).deriv using 1 <;>
    simp only [Function.comp_apply] <;> ring

theorem gap5 (x : ℝ) :
    Real.exp (-x ^ 2) * ((-2 * x) ^ 2 - 2) =
      (((-1 : ℝ) ^ 2 * (2 * x) ^ 2) - 2) * Real.exp (-x ^ 2) := by
  ring

theorem gap6 (x : ℝ) :
    iterDeriv 2 y x =
      (((-1 : ℝ) ^ 2 * (2 * x) ^ 2) - 2) * Real.exp (-x ^ 2) := by
  rw [gap4, gap5]

theorem gap7 (m : ℕ) (x : ℝ) :
    iterDeriv m y x = (-1 : ℝ) ^ m * polynomialExpansion m x * Real.exp (-x ^ 2) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2 / 2))
  have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
  have hy : y = fun t => g (Real.sqrt 2 * t) := by
    funext t
    unfold y g
    congr 1
    rw [mul_pow, hs]
    ring
  have hg : ContDiff ℝ m g := by
    unfold g
    fun_prop
  rw [iterDeriv, ← iteratedDeriv_eq_iterate, hy,
    iteratedDeriv_comp_const_mul hg (Real.sqrt 2)]
  unfold g
  simp only [Function.comp_apply]
  rw [iteratedDeriv_eq_iterate]
  rw [Polynomial.deriv_gaussian_eq_hermite_mul_gaussian]
  have hpoly := scaled_hermite_eq_expansion m x
  have hexp :
      Real.exp (-((Real.sqrt 2 * x) ^ 2 / 2)) =
        Real.exp (-x ^ 2) := by
    congr 1
    rw [mul_pow, hs]
    ring
  rw [hexp]
  calc
    Real.sqrt 2 ^ m *
        ((-1 : ℝ) ^ m *
          Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m) *
          Real.exp (-x ^ 2)) =
      (-1 : ℝ) ^ m *
        (Real.sqrt 2 ^ m *
          Polynomial.aeval (Real.sqrt 2 * x) (Polynomial.hermite m)) *
        Real.exp (-x ^ 2) := by ring
    _ = (-1 : ℝ) ^ m * polynomialExpansion m x * Real.exp (-x ^ 2) := by
      rw [hpoly]

theorem gap8 (m : ℕ) (x : ℝ) :
    H m x = (-1 : ℝ) ^ m * Real.exp (x ^ 2) * iterDeriv m y x := by
  rfl

theorem gap9 (m : ℕ) (x : ℝ) :
    (-1 : ℝ) ^ m * Real.exp (x ^ 2) * iterDeriv m y x =
      polynomialExpansion m x := by
  rw [gap7]
  have hsign : (-1 : ℝ) ^ m * (-1 : ℝ) ^ m = 1 := by
    rw [← pow_add, ← two_mul m, pow_mul]
    norm_num
  have hexp : Real.exp (x ^ 2) * Real.exp (-x ^ 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  rw [show
      (-1 : ℝ) ^ m * Real.exp (x ^ 2) *
          ((-1 : ℝ) ^ m * polynomialExpansion m x * Real.exp (-x ^ 2)) =
        ((-1 : ℝ) ^ m * (-1 : ℝ) ^ m) *
          polynomialExpansion m x *
          (Real.exp (x ^ 2) * Real.exp (-x ^ 2)) by ring,
    hsign, hexp]
  ring

theorem gap10 (m : ℕ) (x : ℝ) :
    H m x = polynomialExpansion m x := by
  rw [gap8, gap9]

theorem gap11 (x : ℝ) :
    deriv y x + 2 * x * y x = 0 := by
  rw [gap1]
  unfold y
  ring

private theorem iteratedDeriv_two_mul_id (i : ℕ) (x : ℝ) :
    iteratedDeriv i (fun t : ℝ => 2 * t) x =
      if i = 0 then 2 * x else if i = 1 then 2 else 0 := by
  rw [iteratedDeriv_const_mul_field]
  by_cases h0 : i = 0
  · subst i
    simp
  by_cases h1 : i = 1
  · subst i
    simp [iteratedDeriv_one]
  simp [h0, h1, iteratedDeriv_fun_id]

private theorem sum_two_mul_id (n : ℕ) (hn : 1 ≤ n)
    (a : ℝ) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) *
        (if i = 0 then a else if i = 1 then 2 else 0) *
        G (n - i)) =
      a * G n + 2 * (n : ℝ) * G (n - 1) := by
  have hsummand (i : ℕ) :
      (Nat.choose n i : ℝ) *
          (if i = 0 then a else if i = 1 then 2 else 0) *
          G (n - i) =
        (if i = 0 then a * G n else 0) +
        (if i = 1 then 2 * (n : ℝ) * G (n - 1) else 0) := by
    by_cases h0 : i = 0
    · subst i
      simp
    by_cases h1 : i = 1
    · subst i
      norm_num only [Nat.one_ne_zero, ↓reduceIte, Nat.choose_one_right]
      push_cast
      ring
    simp [h0, h1]
  simp_rw [hsummand]
  simp only [Finset.sum_add_distrib]
  simp [Finset.mem_range]
  omega

private theorem iteratedDeriv_two_mul_id_mul (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (f : ℝ → ℝ) (hf : ContDiffAt ℝ n f x) :
    iteratedDeriv n (fun t => 2 * t * f t) x =
      2 * x * iteratedDeriv n f x +
        2 * (n : ℝ) * iteratedDeriv (n - 1) f x := by
  rw [iteratedDeriv_fun_mul (n := n) (by fun_prop) hf]
  rw [show
      (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          iteratedDeriv i (fun t : ℝ => 2 * t) x *
          iteratedDeriv (n - i) f x) =
        ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) *
            (if i = 0 then 2 * x else if i = 1 then 2 else 0) *
            iteratedDeriv (n - i) f x by
        apply Finset.sum_congr rfl
        intro i hi
        rw [iteratedDeriv_two_mul_id]]
  exact sum_two_mul_id n hn (2 * x) (fun j => iteratedDeriv j f x)

theorem gap12 (m : ℕ) (x : ℝ) :
    iterDeriv (m + 2) y x + 2 * x * iterDeriv (m + 1) y x +
        2 * (m + 1 : ℕ) * iterDeriv m y x = 0 := by
  have hy : ContDiff ℝ (m + 2) y := by
    unfold y
    fun_prop
  have hy1 : ContDiff ℝ (m + 1) y := by
    unfold y
    fun_prop
  have hdy : ContDiffAt ℝ (m + 1) (deriv y) x := by
    rw [show deriv y = fun t : ℝ => -2 * t * Real.exp (-t ^ 2) by
      funext t
      exact gap1 t]
    fun_prop
  have heq : (fun t : ℝ => deriv y t + 2 * t * y t) = fun _ => 0 := by
    funext t
    exact gap11 t
  have hd := congrArg (fun f : ℝ → ℝ => iteratedDeriv (m + 1) f x) heq
  change iteratedDeriv (m + 1) (fun t : ℝ => deriv y t + 2 * t * y t) x =
    iteratedDeriv (m + 1) (fun _ : ℝ => 0) x at hd
  rw [iteratedDeriv_fun_add
      hdy
      (show ContDiffAt ℝ (m + 1) (fun t : ℝ => 2 * t * y t) x by
        exact (by fun_prop : ContDiffAt ℝ (m + 1) (fun t : ℝ => 2 * t) x)
          |>.mul hy1.contDiffAt),
    iteratedDeriv_two_mul_id_mul (m + 1) (by omega) x y hy1.contDiffAt,
    iteratedDeriv_const] at hd
  simp only [← iteratedDeriv_succ'] at hd
  simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
  convert hd using 1 <;> push_cast <;> ring

theorem gap13 (m : ℕ) (x : ℝ) :
    iterDeriv 2 (z m) x + 2 * x * deriv (z m) x +
        2 * (m + 1 : ℕ) * z m x = 0 := by
  simpa [z, iterDeriv, Function.iterate_succ_apply', Nat.add_assoc,
    Nat.add_comm, Nat.add_left_comm] using gap12 m x

theorem gap14 (m : ℕ) (x : ℝ) :
    H m x = (-1 : ℝ) ^ m * Real.exp (x ^ 2) * z m x := by
  rfl

theorem gap15 (m : ℕ) (x : ℝ) :
    deriv (H m) x =
      (-1 : ℝ) ^ m * Real.exp (x ^ 2) * (2 * x * z m x + deriv (z m) x) := by
  have hy : ContDiff ℝ (m + 1) y := by
    unfold y
    fun_prop
  have hz : DifferentiableAt ℝ (z m) x := by
    unfold z iterDeriv
    rw [← iteratedDeriv_eq_iterate]
    exact (hy.differentiable_iteratedDeriv' m) x
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hexp := (Real.hasDerivAt_exp (x ^ 2)).comp x hsq
  have hc : HasDerivAt (fun _ : ℝ => (-1 : ℝ) ^ m) 0 x :=
    hasDerivAt_const x _
  have h := (hc.mul hexp).mul hz.hasDerivAt
  unfold H
  convert h.deriv using 1 <;>
    simp only [Function.comp_apply, Pi.mul_apply] <;> ring

theorem gap16 (m : ℕ) (x : ℝ) :
    iterDeriv 2 (H m) x =
      (-1 : ℝ) ^ m * Real.exp (x ^ 2) *
        ((4 * x ^ 2 + 2) * z m x + 4 * x * deriv (z m) x + iterDeriv 2 (z m) x) := by
  have hy : ContDiff ℝ (m + 2) y := by
    unfold y
    fun_prop
  have hy1 : ContDiff ℝ (m + 1) y := by
    unfold y
    fun_prop
  have hz : DifferentiableAt ℝ (z m) x := by
    unfold z iterDeriv
    rw [← iteratedDeriv_eq_iterate]
    exact (hy1.differentiable_iteratedDeriv' m) x
  have hdz : DifferentiableAt ℝ (deriv (z m)) x := by
    unfold z iterDeriv
    rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_succ]
    exact hy.differentiable_iteratedDeriv' (m + 1) x
  have heq : deriv (H m) = fun t =>
      ((-1 : ℝ) ^ m * Real.exp (t ^ 2)) *
        (2 * t * z m t + deriv (z m) t) := by
    funext t
    exact gap15 m t
  rw [show iterDeriv 2 (H m) x = deriv (deriv (H m)) x by
    simp [iterDeriv, Function.iterate_succ_apply'], heq]
  have hsq : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    convert (hasDerivAt_id x).pow 2 using 1 <;>
      simp only [id_eq] <;> ring
  have hexp := (Real.hasDerivAt_exp (x ^ 2)).comp x hsq
  have htwo : HasDerivAt (fun t : ℝ => 2 * t) 2 x := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id x).const_mul 2
  have hinner := (htwo.mul hz.hasDerivAt).add hdz.hasDerivAt
  have hc : HasDerivAt (fun _ : ℝ => (-1 : ℝ) ^ m) 0 x :=
    hasDerivAt_const x _
  have h := (hc.mul hexp).mul hinner
  convert h.deriv using 1 <;>
    simp [iterDeriv, Function.iterate_succ_apply', Function.comp_apply,
      Pi.mul_apply, Pi.add_apply] <;> ring

theorem gap17 (m : ℕ) (x : ℝ) :
    iterDeriv 2 (H m) x - 2 * x * deriv (H m) x + 2 * (m : ℝ) * H m x =
      (-1 : ℝ) ^ m * Real.exp (x ^ 2) *
        ((4 * x ^ 2 + 2) * z m x + 4 * x * deriv (z m) x +
          iterDeriv 2 (z m) x - 4 * x ^ 2 * z m x -
          2 * x * deriv (z m) x + 2 * (m : ℝ) * z m x) := by
  rw [gap14, gap15, gap16]
  ring

theorem gap18 (m : ℕ) (x : ℝ) :
    iterDeriv 2 (H m) x - 2 * x * deriv (H m) x + 2 * (m : ℝ) * H m x =
      (-1 : ℝ) ^ m * Real.exp (x ^ 2) *
        (iterDeriv 2 (z m) x + 2 * x * deriv (z m) x +
          2 * (m + 1 : ℕ) * z m x) := by
  rw [gap17]
  push_cast
  ring

theorem gap19 (m : ℕ) (x : ℝ) :
    iterDeriv 2 (H m) x - 2 * x * deriv (H m) x +
        2 * (m : ℝ) * H m x = 0 := by
  rw [gap18, gap13]
  ring

theorem gap20 (m : ℕ) (x : ℝ) :
    H m x = polynomialExpansion m x ∧
      iterDeriv 2 (H m) x - 2 * x * deriv (H m) x +
        2 * (m : ℝ) * H m x = 0 := by
  exact ⟨gap10 m x, gap19 m x⟩

end

end ProofGap.Exercise1231
