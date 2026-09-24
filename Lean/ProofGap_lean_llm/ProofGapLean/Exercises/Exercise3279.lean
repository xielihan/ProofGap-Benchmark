import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3279

noncomputable section

structure MonomialData where
  coefficient : ℝ
  xDegree : ℕ
  yDegree : ℕ
  zDegree : ℕ
  totalDegree : ℕ
  degree_eq : xDegree + yDegree + zDegree = totalDegree

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def nthDifferential₁ (n : ℕ) (f : ℝ → ℝ)
    (x dx : ℝ) : ℝ :=
  iterDeriv n (fun t => f (x + t * dx)) 0

def nthDifferential₂ (n : ℕ) (f : ℝ → ℝ → ℝ)
    (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun t => f (x + t * dx) (y + t * dy)) 0

def nthDifferential₃ (n : ℕ) (f : ℝ → ℝ → ℝ → ℝ)
    (x y z dx dy dz : ℝ) : ℝ :=
  iterDeriv n
    (fun t => f (x + t * dx) (y + t * dy) (z + t * dz)) 0

def degreeTriples (n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (n + 1)).product
      ((Finset.range (n + 1)).product (Finset.range (n + 1)))).filter
    (fun t => t.1 + t.2.1 + t.2.2 = n)

def monomial (p q r : ℕ) (x y z : ℝ) : ℝ :=
  x ^ p * y ^ q * z ^ r

def dataMonomial (m : MonomialData) (x y z : ℝ) : ℝ :=
  m.coefficient * monomial m.xDegree m.yDegree m.zDegree x y z

def P (A : ℝ) (n : ℕ) (x y z : ℝ) : ℝ :=
  ∑ t ∈ degreeTriples n,
    A * monomial t.1 t.2.1 t.2.2 x y z

def multinomialCoefficient (n p q r : ℕ) : ℝ :=
  (Nat.choose n r : ℝ) * (Nat.choose (p + q) q : ℝ)

private def linePolynomial (p q r : ℕ)
    (x y z dx dy dz : ℝ) : Polynomial ℝ :=
  (Polynomial.C x + Polynomial.C dx * Polynomial.X) ^ p *
    (Polynomial.C y + Polynomial.C dy * Polynomial.X) ^ q *
    (Polynomial.C z + Polynomial.C dz * Polynomial.X) ^ r

private theorem iteratePolynomialDerivative_add (n : ℕ)
    (f g : Polynomial ℝ) :
    (Polynomial.derivative^[n]) (f + g) =
      (Polynomial.derivative^[n]) f + (Polynomial.derivative^[n]) g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, Polynomial.derivative_add]
      exact ih f.derivative g.derivative

private theorem iteratePolynomialDerivative_C_mul (n : ℕ) (a : ℝ)
    (f : Polynomial ℝ) :
    (Polynomial.derivative^[n]) (Polynomial.C a * f) =
      Polynomial.C a * (Polynomial.derivative^[n]) f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      simp only [Polynomial.derivative_mul, Polynomial.derivative_C,
        zero_mul, zero_add]
      exact ih f.derivative

private theorem iteratePolynomialDerivative_sum {ι : Type*} (n : ℕ)
    (s : Finset ι) (f : ι → Polynomial ℝ) :
    (Polynomial.derivative^[n]) (s.sum f) =
      s.sum (fun i => (Polynomial.derivative^[n]) (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, ih]

private theorem linePolynomialDerivative (p q r : ℕ)
    (x y z dx dy dz : ℝ) :
    (linePolynomial p q r x y z dx dy dz).derivative =
      Polynomial.C ((p : ℝ) * dx) *
          linePolynomial (p - 1) q r x y z dx dy dz +
        Polynomial.C ((q : ℝ) * dy) *
          linePolynomial p (q - 1) r x y z dx dy dz +
        Polynomial.C ((r : ℝ) * dz) *
          linePolynomial p q (r - 1) x y z dx dy dz := by
  simp [linePolynomial, Polynomial.derivative_mul,
    Polynomial.derivative_pow]
  ring

private theorem linePolynomialTopDerivative (n p q r : ℕ)
    (hdegree : p + q + r = n) (x y z dx dy dz : ℝ) :
    ((Polynomial.derivative^[n])
        (linePolynomial p q r x y z dx dy dz)).eval 0 =
      (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r := by
  induction n using Nat.strong_induction_on generalizing p q r with
  | h n ih =>
      cases n with
      | zero =>
          have hp : p = 0 := by omega
          have hq : q = 0 := by omega
          have hr : r = 0 := by omega
          subst p
          subst q
          subst r
          simp [linePolynomial]
      | succ n =>
          rw [Function.iterate_succ_apply,
            linePolynomialDerivative,
            iteratePolynomialDerivative_add,
            iteratePolynomialDerivative_add,
            iteratePolynomialDerivative_C_mul,
            iteratePolynomialDerivative_C_mul,
            iteratePolynomialDerivative_C_mul]
          simp only [Polynomial.eval_add, Polynomial.eval_mul,
            Polynomial.eval_C]
          have hpterm :
              (p : ℝ) * dx *
                  ((Polynomial.derivative^[n])
                    (linePolynomial (p - 1) q r x y z dx dy dz)).eval 0 =
                (p : ℝ) * (Nat.factorial n : ℝ) *
                  dx ^ p * dy ^ q * dz ^ r := by
            by_cases hp : p = 0
            · simp [hp]
            · have hs : p - 1 + q + r = n := by omega
              rw [ih n (Nat.lt_succ_self n) (p - 1) q r hs]
              obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hp
              simp [pow_succ]
              ring
          have hqterm :
              (q : ℝ) * dy *
                  ((Polynomial.derivative^[n])
                    (linePolynomial p (q - 1) r x y z dx dy dz)).eval 0 =
                (q : ℝ) * (Nat.factorial n : ℝ) *
                  dx ^ p * dy ^ q * dz ^ r := by
            by_cases hq : q = 0
            · simp [hq]
            · have hs : p + (q - 1) + r = n := by omega
              rw [ih n (Nat.lt_succ_self n) p (q - 1) r hs]
              obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq
              simp [pow_succ]
              ring
          have hrterm :
              (r : ℝ) * dz *
                  ((Polynomial.derivative^[n])
                    (linePolynomial p q (r - 1) x y z dx dy dz)).eval 0 =
                (r : ℝ) * (Nat.factorial n : ℝ) *
                  dx ^ p * dy ^ q * dz ^ r := by
            by_cases hr : r = 0
            · simp [hr]
            · have hs : p + q + (r - 1) = n := by omega
              rw [ih n (Nat.lt_succ_self n) p q (r - 1) hs]
              obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
              simp [pow_succ]
              ring
          rw [hpterm, hqterm, hrterm]
          have hcast :
              (p : ℝ) + (q : ℝ) + (r : ℝ) = (n : ℝ) + 1 := by
            exact_mod_cast hdegree
          rw [Nat.factorial_succ]
          simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          calc
            (p : ℝ) * (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r +
                (q : ℝ) * (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r +
                (r : ℝ) * (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r =
              ((p : ℝ) + (q : ℝ) + (r : ℝ)) *
                (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r := by ring
            _ = ((n : ℝ) + 1) * (Nat.factorial n : ℝ) *
                dx ^ p * dy ^ q * dz ^ r := by rw [hcast]

private theorem iterDerivPolynomialEval (n : ℕ) (f : Polynomial ℝ) :
    iterDeriv n (fun t : ℝ => f.eval t) 0 =
      ((Polynomial.derivative^[n]) f).eval 0 := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
      simp only [iterDeriv, Function.iterate_succ_apply]
      have hderiv :
          deriv (fun t : ℝ => f.eval t) =
            fun t : ℝ => f.derivative.eval t := by
        funext t
        exact (f.hasDerivAt t).deriv
      rw [hderiv]
      simpa [iterDeriv] using ih f.derivative

private theorem monomialDifferential (n p q r : ℕ)
    (hdegree : p + q + r = n) (x y z dx dy dz : ℝ) :
    nthDifferential₃ n (monomial p q r) x y z dx dy dz =
      (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r := by
  unfold nthDifferential₃
  rw [show
    (fun t : ℝ => monomial p q r
      (x + t * dx) (y + t * dy) (z + t * dz)) =
      fun t : ℝ =>
        (linePolynomial p q r x y z dx dy dz).eval t by
          funext t
          simp [linePolynomial, monomial]
          ring]
  rw [iterDerivPolynomialEval]
  exact linePolynomialTopDerivative n p q r hdegree x y z dx dy dz

private theorem oneVariablePowerDifferential (p : ℕ) (x dx : ℝ) :
    nthDifferential₁ p (fun a : ℝ => a ^ p) x dx =
      (Nat.factorial p : ℝ) * dx ^ p := by
  simpa [nthDifferential₁, nthDifferential₃, monomial] using
    monomialDifferential p p 0 0 (by omega) x 0 0 dx 0 0

private theorem twoVariablePowerDifferential (p q : ℕ)
    (x y dx dy : ℝ) :
    nthDifferential₂ (p + q) (fun a b : ℝ => a ^ p * b ^ q)
        x y dx dy =
      (Nat.factorial (p + q) : ℝ) * dx ^ p * dy ^ q := by
  simpa [nthDifferential₂, nthDifferential₃, monomial] using
    monomialDifferential (p + q) p q 0 (by omega) x y 0 dx dy 0

private theorem chooseFactorialReal (n k m : ℕ) (hkm : k + m = n) :
    (Nat.choose n k : ℝ) * (Nat.factorial k : ℝ) *
        (Nat.factorial m : ℝ) =
      (Nat.factorial n : ℝ) := by
  have hk : k ≤ n := by omega
  have hsub : n - k = m := by omega
  have hnat :
      Nat.choose n k * Nat.factorial k * Nat.factorial m =
        Nat.factorial n := by
    simpa [hsub] using Nat.choose_mul_factorial_mul_factorial hk
  exact_mod_cast hnat

private theorem homogeneousMonomialSumDifferential
    (s : Finset (ℕ × ℕ × ℕ)) (n : ℕ)
    (hdegrees : ∀ t ∈ s, t.1 + t.2.1 + t.2.2 = n)
    (A x y z dx dy dz : ℝ) :
    nthDifferential₃ n
        (fun a b c => s.sum (fun t =>
          A * monomial t.1 t.2.1 t.2.2 a b c))
        x y z dx dy dz =
      (Nat.factorial n : ℝ) *
        s.sum (fun t => A * dx ^ t.1 * dy ^ t.2.1 * dz ^ t.2.2) := by
  unfold nthDifferential₃
  rw [show
    (fun u : ℝ => s.sum (fun t =>
      A * monomial t.1 t.2.1 t.2.2
        (x + u * dx) (y + u * dy) (z + u * dz))) =
      fun u : ℝ =>
        (s.sum (fun t => Polynomial.C A *
          linePolynomial t.1 t.2.1 t.2.2 x y z dx dy dz)).eval u by
          funext u
          change
            s.sum (fun t =>
              A * monomial t.1 t.2.1 t.2.2
                (x + u * dx) (y + u * dy) (z + u * dz)) =
              (Polynomial.evalRingHom u)
                (s.sum (fun t => Polynomial.C A *
                  linePolynomial t.1 t.2.1 t.2.2 x y z dx dy dz))
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro t ht
          simp [linePolynomial, monomial]
          left
          ring]
  rw [iterDerivPolynomialEval]
  calc
    ((Polynomial.derivative^[n])
        (s.sum (fun t => Polynomial.C A *
          linePolynomial t.1 t.2.1 t.2.2 x y z dx dy dz))).eval 0 =
      s.sum (fun t => A *
        ((Polynomial.derivative^[n])
          (linePolynomial t.1 t.2.1 t.2.2 x y z dx dy dz)).eval 0) := by
            rw [iteratePolynomialDerivative_sum]
            change
              (Polynomial.evalRingHom 0)
                  (s.sum (fun t =>
                    (Polynomial.derivative^[n])
                      (Polynomial.C A *
                        linePolynomial t.1 t.2.1 t.2.2
                          x y z dx dy dz))) =
                s.sum (fun t => A *
                  ((Polynomial.derivative^[n])
                    (linePolynomial t.1 t.2.1 t.2.2
                      x y z dx dy dz)).eval 0)
            rw [map_sum]
            apply Finset.sum_congr rfl
            intro t ht
            rw [iteratePolynomialDerivative_C_mul]
            simp
    _ = s.sum (fun t => A *
        ((Nat.factorial n : ℝ) * dx ^ t.1 * dy ^ t.2.1 * dz ^ t.2.2)) := by
          apply Finset.sum_congr rfl
          intro t ht
          rw [linePolynomialTopDerivative n t.1 t.2.1 t.2.2
            (hdegrees t ht)]
    _ = (Nat.factorial n : ℝ) *
        s.sum (fun t => A * dx ^ t.1 * dy ^ t.2.1 * dz ^ t.2.2) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          ring

theorem gap1 (A : ℝ) (n : ℕ) (x y z : ℝ) :
    P A n x y z =
      ∑ t ∈ degreeTriples n,
        A * monomial t.1 t.2.1 t.2.2 x y z := by
  rfl

theorem gap2 (m : MonomialData) :
    dataMonomial m 1 1 1 = m.coefficient := by
  simp [dataMonomial, monomial]

theorem gap3 (m : MonomialData) :
    m.xDegree ≤ m.totalDegree := by
  rw [← m.degree_eq]
  omega

theorem gap4 (m : MonomialData) :
    m.yDegree ≤ m.totalDegree := by
  rw [← m.degree_eq]
  omega

theorem gap5 (m : MonomialData) :
    m.zDegree ≤ m.totalDegree := by
  rw [← m.degree_eq]
  omega

theorem gap6 (m : MonomialData) :
    m.xDegree + m.yDegree + m.zDegree = m.totalDegree := by
  exact m.degree_eq

theorem gap7 (A : ℝ) (n : ℕ) (x y z dx dy dz : ℝ) :
    nthDifferential₃ n (P A n) x y z dx dy dz =
      (Nat.factorial n : ℝ) * P A n dx dy dz := by
  have hP : P A n = fun a b c =>
      ∑ t ∈ degreeTriples n,
        A * monomial t.1 t.2.1 t.2.2 a b c := by
    funext a b c
    exact gap1 A n a b c
  rw [hP]
  have hdegrees : ∀ t ∈ degreeTriples n,
      t.1 + t.2.1 + t.2.2 = n := by
    intro t ht
    exact (Finset.mem_filter.mp ht).2
  simpa [monomial, mul_assoc] using
    homogeneousMonomialSumDifferential (degreeTriples n) n hdegrees A
      x y z dx dy dz

theorem gap8 (n p q r : ℕ) (hdegree : p + q + r = n)
    (x y z dx dy dz : ℝ) :
    nthDifferential₃ n (monomial p q r) x y z dx dy dz =
      (Nat.choose n r : ℝ) *
        nthDifferential₂ (p + q) (fun a b => a ^ p * b ^ q)
          x y dx dy *
        nthDifferential₁ r (fun c => c ^ r) z dz := by
  rw [monomialDifferential n p q r hdegree,
    twoVariablePowerDifferential, oneVariablePowerDifferential]
  have hc := chooseFactorialReal n r (p + q) (by omega)
  calc
    (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r =
        ((Nat.choose n r : ℝ) * (Nat.factorial r : ℝ) *
          (Nat.factorial (p + q) : ℝ)) * dx ^ p * dy ^ q * dz ^ r := by
            rw [hc]
    _ = (Nat.choose n r : ℝ) *
          ((Nat.factorial (p + q) : ℝ) * dx ^ p * dy ^ q) *
          ((Nat.factorial r : ℝ) * dz ^ r) := by ring

theorem gap9 (n p q r : ℕ) (hdegree : p + q + r = n)
    (x y z dx dy dz : ℝ) :
    (Nat.choose n r : ℝ) *
          nthDifferential₂ (p + q) (fun a b => a ^ p * b ^ q)
            x y dx dy *
          nthDifferential₁ r (fun c => c ^ r) z dz =
      multinomialCoefficient n p q r *
        nthDifferential₁ p (fun a => a ^ p) x dx *
        nthDifferential₁ q (fun b => b ^ q) y dy *
        nthDifferential₁ r (fun c => c ^ r) z dz := by
  rw [twoVariablePowerDifferential,
    oneVariablePowerDifferential, oneVariablePowerDifferential,
    oneVariablePowerDifferential]
  unfold multinomialCoefficient
  have hc := chooseFactorialReal (p + q) q p (by omega)
  calc
    (Nat.choose n r : ℝ) *
          ((Nat.factorial (p + q) : ℝ) * dx ^ p * dy ^ q) *
          ((Nat.factorial r : ℝ) * dz ^ r) =
        (Nat.choose n r : ℝ) *
          ((Nat.choose (p + q) q : ℝ) * (Nat.factorial q : ℝ) *
            (Nat.factorial p : ℝ)) * dx ^ p * dy ^ q *
          ((Nat.factorial r : ℝ) * dz ^ r) := by
            rw [hc]
            ring
    _ = (Nat.choose n r : ℝ) * (Nat.choose (p + q) q : ℝ) *
          ((Nat.factorial p : ℝ) * dx ^ p) *
          ((Nat.factorial q : ℝ) * dy ^ q) *
          ((Nat.factorial r : ℝ) * dz ^ r) := by ring

theorem gap10 (n p q r : ℕ) (hdegree : p + q + r = n)
    (x y z dx dy dz : ℝ) :
    nthDifferential₃ n (monomial p q r) x y z dx dy dz =
      multinomialCoefficient n p q r *
        nthDifferential₁ p (fun a => a ^ p) x dx *
        nthDifferential₁ q (fun b => b ^ q) y dy *
        nthDifferential₁ r (fun c => c ^ r) z dz := by
  rw [gap8 n p q r hdegree x y z dx dy dz]
  exact gap9 n p q r hdegree x y z dx dy dz

theorem gap11 (n p q r : ℕ) (hdegree : p + q + r = n)
    (x y z dx dy dz : ℝ) :
    multinomialCoefficient n p q r *
          nthDifferential₁ p (fun a => a ^ p) x dx *
          nthDifferential₁ q (fun b => b ^ q) y dy *
          nthDifferential₁ r (fun c => c ^ r) z dz =
      multinomialCoefficient n p q r *
        (Nat.factorial p : ℝ) * (Nat.factorial q : ℝ) *
        (Nat.factorial r : ℝ) * dx ^ p * dy ^ q * dz ^ r := by
  rw [oneVariablePowerDifferential,
    oneVariablePowerDifferential, oneVariablePowerDifferential]
  ring

theorem gap12 (n p q r : ℕ) (hdegree : p + q + r = n) :
    multinomialCoefficient n p q r *
        (Nat.factorial p : ℝ) * (Nat.factorial q : ℝ) *
        (Nat.factorial r : ℝ) =
      (Nat.factorial n : ℝ) := by
  unfold multinomialCoefficient
  have hinner := chooseFactorialReal (p + q) q p (by omega)
  have houter := chooseFactorialReal n r (p + q) (by omega)
  calc
    (Nat.choose n r : ℝ) * (Nat.choose (p + q) q : ℝ) *
          (Nat.factorial p : ℝ) * (Nat.factorial q : ℝ) *
          (Nat.factorial r : ℝ) =
        (Nat.choose n r : ℝ) * (Nat.factorial r : ℝ) *
          ((Nat.choose (p + q) q : ℝ) * (Nat.factorial q : ℝ) *
            (Nat.factorial p : ℝ)) := by ring
    _ = (Nat.choose n r : ℝ) * (Nat.factorial r : ℝ) *
          (Nat.factorial (p + q) : ℝ) := by rw [hinner]
    _ = (Nat.factorial n : ℝ) := houter

theorem gap13 (n p q r : ℕ) (hdegree : p + q + r = n)
    (x y z dx dy dz : ℝ) :
    nthDifferential₃ n (monomial p q r) x y z dx dy dz =
      (Nat.factorial n : ℝ) * dx ^ p * dy ^ q * dz ^ r := by
  exact monomialDifferential n p q r hdegree x y z dx dy dz

theorem gap14 (n : ℕ) (t : ℕ × ℕ × ℕ)
    (ht : t ∈ degreeTriples n) (x y z dx dy dz : ℝ) :
    nthDifferential₃ n (monomial t.1 t.2.1 t.2.2)
        x y z dx dy dz =
      (Nat.factorial n : ℝ) *
        dx ^ t.1 * dy ^ t.2.1 * dz ^ t.2.2 := by
  apply monomialDifferential n t.1 t.2.1 t.2.2
  exact (Finset.mem_filter.mp ht).2

end

end ProofGap.Exercise3279
