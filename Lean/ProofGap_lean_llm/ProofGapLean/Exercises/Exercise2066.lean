import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2066
noncomputable section

def peval (P : Polynomial ℝ) (x : ℝ) := P.eval x
def pd (P : Polynomial ℝ) (k : ℕ) (x : ℝ) :=
  ((Polynomial.derivative^[k]) P).eval x
def integrand (P : Polynomial ℝ) (a x : ℝ) := peval P x * Real.exp (a * x)
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def ByExpDerivative (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family (fun x => peval P x * deriv (fun y => Real.exp (a * y)) x),
    ∃ C, ∀ x, F x = (1 / a) * G x + C}
def FirstParts (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family (fun x => Real.exp (a * x) * pd P 1 x),
    ∃ C, ∀ x, F x = peval P x * Real.exp (a * x) / a - G x / a + C}
def SecondParts (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family (fun x => Real.exp (a * x) * pd P 2 x),
    ∃ C, ∀ x, F x = peval P x * Real.exp (a * x) / a -
      pd P 1 x * Real.exp (a * x) / a ^ 2 + G x / a ^ 2 + C}
def expPrimitive (P : Polynomial ℝ) (a : ℝ) (x : ℝ) :=
  Real.exp (a * x) *
    ∑ k ∈ Finset.range (P.natDegree + 1), (-1 : ℝ) ^ k * pd P k x / a ^ (k + 1)
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private lemma hasDerivAt_exp_mul (a x : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (a * y))
      (a * Real.exp (a * x)) x := by
  simpa [mul_comm] using
    (Real.hasDerivAt_exp (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x))

private lemma deriv_exp_mul (a x : ℝ) :
    deriv (fun y : ℝ => Real.exp (a * y)) x =
      a * Real.exp (a * x) :=
  (hasDerivAt_exp_mul a x).deriv

private lemma hasDerivAt_pd (P : Polynomial ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (pd P k) (pd P (k + 1) x) x := by
  simpa [pd, Function.iterate_succ_apply'] using
    (((Polynomial.derivative^[k]) P).hasDerivAt x)

private lemma hasDerivAt_peval (P : Polynomial ℝ) (x : ℝ) :
    HasDerivAt (peval P) (pd P 1 x) x := by
  simpa [peval, pd] using hasDerivAt_pd P 0 x

private lemma derivative_iterate_eq_zero_of_natDegree_lt
    (P : Polynomial ℝ) (k : ℕ) (h : P.natDegree < k) :
    (Polynomial.derivative^[k]) P = 0 := by
  induction k generalizing P with
  | zero =>
      exact (Nat.not_lt_zero _ h).elim
  | succ k ih =>
      rw [Function.iterate_succ_apply]
      by_cases hn : P.natDegree = 0
      · have hP : P = Polynomial.C (P.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hn
        have hd : Polynomial.derivative P = 0 := by
          calc
            Polynomial.derivative P =
                Polynomial.derivative (Polynomial.C (P.coeff 0)) :=
              congrArg Polynomial.derivative hP
            _ = 0 := by simp
        simp [hd]
      · apply ih
        exact lt_of_lt_of_le (Polynomial.natDegree_derivative_lt hn)
          (Nat.le_of_lt_succ h)

private lemma pd_eq_zero_of_natDegree_lt (P : Polynomial ℝ) (k : ℕ)
    (h : P.natDegree < k) (x : ℝ) : pd P k x = 0 := by
  have hz : (Polynomial.derivative^[k]) P = 0 :=
    derivative_iterate_eq_zero_of_natDegree_lt P k h
  simp [pd, hz]

private lemma family_eq_firstParts (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) = FirstParts P a := by
  ext F
  simp only [Family, FirstParts, Set.mem_setOf_eq]
  constructor
  · intro hF
    let G := fun y =>
      peval P y * Real.exp (a * y) - a * F y
    refine ⟨G, ?_, 0, ?_⟩
    · intro x
      have hprod := (hasDerivAt_peval P x).mul (hasDerivAt_exp_mul a x)
      convert hprod.sub ((hF x).const_mul a) using 1
      simp only [integrand]
      ring
    · intro x
      dsimp [G]
      field_simp [ha] <;> ring
  · rintro ⟨G, hG, C, hF⟩
    have hfun : F = fun x =>
        peval P x * Real.exp (a * x) / a - G x / a + C := funext hF
    rw [hfun]
    intro x
    have hprod := (hasDerivAt_peval P x).mul (hasDerivAt_exp_mul a x)
    convert ((hprod.div_const a).sub ((hG x).div_const a)).add_const C using 1
    simp only [integrand]
    field_simp [ha] <;> ring

private lemma family_eq_scaledFirst (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) =
      {F : ℝ → ℝ | ∃ G ∈ Family
        (fun x => pd P 1 x * deriv (fun y => Real.exp (a * y)) x),
        ∃ C, ∀ x, F x = peval P x * Real.exp (a * x) / a - G x / a ^ 2 + C} := by
  ext F
  simp only [Family, Set.mem_setOf_eq]
  constructor
  · intro hF
    let G := fun y => a *
      (peval P y * Real.exp (a * y) - a * F y)
    refine ⟨G, ?_, 0, ?_⟩
    · intro x
      have hprod := (hasDerivAt_peval P x).mul (hasDerivAt_exp_mul a x)
      have hbase := hprod.sub ((hF x).const_mul a)
      convert hbase.const_mul a using 1
      rw [deriv_exp_mul]
      simp only [integrand]
      ring
    · intro x
      dsimp [G]
      field_simp [ha] <;> ring
  · rintro ⟨G, hG, C, hF⟩
    have hfun : F = fun x =>
        peval P x * Real.exp (a * x) / a - G x / a ^ 2 + C := funext hF
    rw [hfun]
    intro x
    have hprod := (hasDerivAt_peval P x).mul (hasDerivAt_exp_mul a x)
    convert ((hprod.div_const a).sub ((hG x).div_const (a ^ 2))).add_const C using 1
    rw [deriv_exp_mul]
    simp only [integrand]
    field_simp [ha] <;> ring

private lemma family_eq_secondParts (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) = SecondParts P a := by
  ext F
  simp only [Family, SecondParts, Set.mem_setOf_eq]
  constructor
  · intro hF
    let G := fun y =>
      a ^ 2 * F y - a * (peval P y * Real.exp (a * y)) +
        pd P 1 y * Real.exp (a * y)
    refine ⟨G, ?_, 0, ?_⟩
    · intro x
      have hprod0 := (hasDerivAt_peval P x).mul (hasDerivAt_exp_mul a x)
      have hprod1 := (hasDerivAt_pd P 1 x).mul (hasDerivAt_exp_mul a x)
      have hder :=
        (((hF x).const_mul (a ^ 2)).sub (hprod0.const_mul a)).add hprod1
      convert hder using 1
      simp only [integrand]
      ring
    · intro x
      dsimp [G]
      field_simp [ha] <;> ring
  · rintro ⟨G, hG, C, hF⟩
    have hfun : F = fun x =>
        peval P x * Real.exp (a * x) / a -
          pd P 1 x * Real.exp (a * x) / a ^ 2 +
          G x / a ^ 2 + C := funext hF
    rw [hfun]
    intro x
    have hprod0 := (hasDerivAt_peval P x).mul (hasDerivAt_exp_mul a x)
    have hprod1 := (hasDerivAt_pd P 1 x).mul (hasDerivAt_exp_mul a x)
    have hder :=
      (((hprod0.div_const a).sub (hprod1.div_const (a ^ 2))).add
        ((hG x).div_const (a ^ 2))).add_const C
    convert hder using 1
    simp only [integrand]
    field_simp [ha] <;> ring

private lemma alternating_pd_sum (a : ℝ) (ha : a ≠ 0)
    (u : ℕ → ℝ) (n : ℕ) :
    a * (∑ k ∈ Finset.range (n + 1),
      (-1 : ℝ) ^ k * u k / a ^ (k + 1)) +
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * u (k + 1) / a ^ (k + 1)) =
      u 0 + (-1 : ℝ) ^ n * u (n + 1) / a ^ (n + 1) := by
  induction n with
  | zero =>
      simp only [Nat.zero_add, Finset.range_one, Finset.sum_singleton,
        pow_zero, one_mul, pow_one]
      field_simp [ha] <;> ring
  | succ n ih =>
      have hS :
          (∑ k ∈ Finset.range (n + 2),
            (-1 : ℝ) ^ k * u k / a ^ (k + 1)) =
          (∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ k * u k / a ^ (k + 1)) +
            (-1 : ℝ) ^ (n + 1) * u (n + 1) / a ^ (n + 2) := by
        simpa only using
          (Finset.sum_range_succ
            (fun k => (-1 : ℝ) ^ k * u k / a ^ (k + 1)) (n + 1))
      have hT :
          (∑ k ∈ Finset.range (n + 2),
            (-1 : ℝ) ^ k * u (k + 1) / a ^ (k + 1)) =
          (∑ k ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ k * u (k + 1) / a ^ (k + 1)) +
            (-1 : ℝ) ^ (n + 1) * u (n + 2) / a ^ (n + 2) := by
        simpa only using
          (Finset.sum_range_succ
            (fun k => (-1 : ℝ) ^ k * u (k + 1) / a ^ (k + 1)) (n + 1))
      rw [hS, hT]
      let S : ℝ := ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * u k / a ^ (k + 1)
      let T : ℝ := ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * u (k + 1) / a ^ (k + 1)
      change
        a * (S + (-1 : ℝ) ^ (n + 1) * u (n + 1) / a ^ (n + 2)) +
          (T + (-1 : ℝ) ^ (n + 1) * u (n + 2) / a ^ (n + 2)) =
        u 0 + (-1 : ℝ) ^ (n + 1) * u (n + 2) / a ^ (n + 2)
      calc
        _ = (a * S + T) +
            (a * ((-1 : ℝ) ^ (n + 1) * u (n + 1) / a ^ (n + 2)) +
             (-1 : ℝ) ^ (n + 1) * u (n + 2) / a ^ (n + 2)) := by ring
        _ = (u 0 + (-1 : ℝ) ^ n * u (n + 1) / a ^ (n + 1)) +
            (a * ((-1 : ℝ) ^ (n + 1) * u (n + 1) / a ^ (n + 2)) +
             (-1 : ℝ) ^ (n + 1) * u (n + 2) / a ^ (n + 2)) := by rw [ih]
        _ = u 0 + (-1 : ℝ) ^ (n + 1) * u (n + 2) / a ^ (n + 2) := by
          field_simp [ha, pow_succ] <;> ring

private lemma hasDerivAt_pd_sum (P : Polynomial ℝ) (a : ℝ)
    (n : ℕ) (x : ℝ) :
    HasDerivAt
      (fun y => ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * pd P k y / a ^ (k + 1))
      (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * pd P (k + 1) x / a ^ (k + 1)) x := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      HasDerivAt
        (fun y => (-1 : ℝ) ^ k * pd P k y / a ^ (k + 1))
        ((-1 : ℝ) ^ k * pd P (k + 1) x / a ^ (k + 1)) x := by
    intro k hk
    simpa only using
      ((hasDerivAt_pd P k x).const_mul ((-1 : ℝ) ^ k)).div_const
        (a ^ (k + 1))
  have hsum := HasDerivAt.sum hterm
  have hfun :
      (∑ k ∈ Finset.range (n + 1),
        fun y => (-1 : ℝ) ^ k * pd P k y / a ^ (k + 1)) =
      (fun y => ∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ k * pd P k y / a ^ (k + 1)) := by
    funext y
    simp only [Finset.sum_apply]
  rw [← hfun]
  exact hsum

private lemma hasDerivAt_expPrimitive (P : Polynomial ℝ) (a : ℝ)
    (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (expPrimitive P a) (integrand P a x) x := by
  let S : ℝ := ∑ k ∈ Finset.range (P.natDegree + 1),
    (-1 : ℝ) ^ k * pd P k x / a ^ (k + 1)
  let T : ℝ := ∑ k ∈ Finset.range (P.natDegree + 1),
    (-1 : ℝ) ^ k * pd P (k + 1) x / a ^ (k + 1)
  have hzero : pd P (P.natDegree + 1) x = 0 :=
    pd_eq_zero_of_natDegree_lt P (P.natDegree + 1)
      (Nat.lt_succ_self P.natDegree) x
  have htel : a * S + T = pd P 0 x := by
    have h := alternating_pd_sum a ha (fun k => pd P k x) P.natDegree
    rw [hzero] at h
    simpa [S, T] using h
  have hsum := hasDerivAt_pd_sum P a P.natDegree x
  have hprod := (hasDerivAt_exp_mul a x).mul hsum
  have hderiv :
      (a * Real.exp (a * x)) * S + Real.exp (a * x) * T =
        integrand P a x := by
    rw [show (a * Real.exp (a * x)) * S + Real.exp (a * x) * T =
      Real.exp (a * x) * (a * S + T) by ring, htel]
    simp [integrand, peval, pd, mul_comm]
  rw [hderiv] at hprod
  simpa only [expPrimitive, S, T] using hprod

private lemma family_eq_translates_of_primitive
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hz : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      simpa only [Pi.sub_apply, sub_self] using (hF x).sub (hp x)
    have hconst : ∀ x y, F x - p x = F y - p y := fun x y =>
      is_const_of_deriv_eq_zero
        (fun z => (hz z).differentiableAt)
        (fun z => (hz z).deriv) x y
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    linarith [hconst x 0]
  · rintro ⟨C, hF⟩
    have hfun : F = fun x => p x + C := funext hF
    rw [hfun]
    intro x
    exact (hp x).add_const C

theorem gap1 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) = ByExpDerivative P a := by
  ext F
  simp only [Family, ByExpDerivative, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨fun x => a * F x, ?_, 0, ?_⟩
    · intro x
      convert (hF x).const_mul a using 1
      rw [deriv_exp_mul]
      simp only [integrand]
      ring
    · intro x
      field_simp [ha] <;> ring
  · rintro ⟨G, hG, C, hF⟩
    have hfun : F = fun x => (1 / a) * G x + C := funext hF
    rw [hfun]
    intro x
    convert ((hG x).const_mul (1 / a)).add_const C using 1
    rw [deriv_exp_mul]
    simp only [integrand]
    field_simp [ha] <;> ring
theorem gap2 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    ByExpDerivative P a = FirstParts P a := by
  calc
    ByExpDerivative P a = Family (integrand P a) := (gap1 P a ha).symm
    _ = FirstParts P a := family_eq_firstParts P a ha
theorem gap3 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) = FirstParts P a := by
  exact (gap1 P a ha).trans (gap2 P a ha)
theorem gap4 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) =
      {F : ℝ → ℝ | ∃ G ∈ Family
        (fun x => pd P 1 x * deriv (fun y => Real.exp (a * y)) x),
        ∃ C, ∀ x, F x = peval P x * Real.exp (a * x) / a - G x / a ^ 2 + C} := by
  exact family_eq_scaledFirst P a ha
theorem gap5 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    {F : ℝ → ℝ | ∃ G ∈ Family
      (fun x => pd P 1 x * deriv (fun y => Real.exp (a * y)) x),
      ∃ C, ∀ x, F x = peval P x * Real.exp (a * x) / a - G x / a ^ 2 + C} =
      SecondParts P a := by
  calc
    {F : ℝ → ℝ | ∃ G ∈ Family
      (fun x => pd P 1 x * deriv (fun y => Real.exp (a * y)) x),
      ∃ C, ∀ x, F x = peval P x * Real.exp (a * x) / a - G x / a ^ 2 + C} =
        Family (integrand P a) := (gap4 P a ha).symm
    _ = SecondParts P a := family_eq_secondParts P a ha
theorem gap6 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) = SecondParts P a := by
  exact (gap4 P a ha).trans (gap5 P a ha)
theorem gap7 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (integrand P a) = Translates (expPrimitive P a) := by
  apply family_eq_translates_of_primitive
  intro x
  exact hasDerivAt_expPrimitive P a ha x
theorem gap8 (P : Polynomial ℝ) (n : ℕ) (hdeg : P.natDegree ≤ n) :
    ∀ x, pd P (n + 1) x = 0 := by
  intro x
  apply pd_eq_zero_of_natDegree_lt
  exact Nat.lt_succ_iff.mpr hdeg
theorem gap9 (P : Polynomial ℝ) :
    ∀ a : ℝ, a ≠ 0 →
      Family (integrand P a) = Translates (expPrimitive P a) := by
  intro a ha
  exact gap7 P a ha

end
end ProofGap.Exercise2066
