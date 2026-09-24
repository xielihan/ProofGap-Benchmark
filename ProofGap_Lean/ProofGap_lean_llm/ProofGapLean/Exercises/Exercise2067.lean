import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2067
noncomputable section

def peval (P : Polynomial ℝ) (x : ℝ) := P.eval x
def pd (P : Polynomial ℝ) (k : ℕ) (x : ℝ) :=
  ((Polynomial.derivative^[k]) P).eval x
def cosIntegrand (P : Polynomial ℝ) (a x : ℝ) := peval P x * Real.cos (a * x)
def sinIntegrand (P : Polynomial ℝ) (a x : ℝ) := peval P x * Real.sin (a * x)
def Family (f : ℝ → ℝ) := {F : ℝ → ℝ | ∀ x, HasDerivAt F (f x) x}
def CosDerivativeStep (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family
    (fun x => peval P x * deriv (fun y => Real.sin (a * y)) x),
    ∃ C, ∀ x, F x = G x / a + C}
def CosFirstParts (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family (fun x => pd P 1 x * Real.sin (a * x)),
    ∃ C, ∀ x, F x = peval P x * Real.sin (a * x) / a - G x / a + C}
def CosSecondParts (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family (fun x => pd P 2 x * Real.cos (a * x)),
    ∃ C, ∀ x, F x = peval P x * Real.sin (a * x) / a +
      pd P 1 x * Real.cos (a * x) / a ^ 2 - G x / a ^ 2 + C}
def SinDerivativeStep (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family
    (fun x => peval P x * deriv (fun y => Real.cos (a * y)) x),
    ∃ C, ∀ x, F x = -G x / a + C}
def SinFirstParts (P : Polynomial ℝ) (a : ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family (fun x => pd P 1 x * Real.cos (a * x)),
    ∃ C, ∀ x, F x = -peval P x * Real.cos (a * x) / a + G x / a + C}
def evenSeries (P : Polynomial ℝ) (a x : ℝ) :=
  ∑ k ∈ Finset.range (P.natDegree / 2 + 1),
    (-1 : ℝ) ^ k * pd P (2 * k) x / a ^ (2 * k)
def oddSeries (P : Polynomial ℝ) (a x : ℝ) :=
  ∑ k ∈ Finset.range ((P.natDegree + 1) / 2),
    (-1 : ℝ) ^ k * pd P (2 * k + 1) x / a ^ (2 * k)
def cosPrimitive (P : Polynomial ℝ) (a x : ℝ) :=
  Real.sin (a * x) / a * evenSeries P a x +
    Real.cos (a * x) / a ^ 2 * oddSeries P a x
def sinPrimitive (P : Polynomial ℝ) (a x : ℝ) :=
  -Real.cos (a * x) / a * evenSeries P a x +
    Real.sin (a * x) / a ^ 2 * oddSeries P a x
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C, ∀ x, F x = p x + C}

private theorem polynomial_derivative_eq_zero_of_natDegree_eq_zero
    (P : Polynomial ℝ) (hP : P.natDegree = 0) : P.derivative = 0 := by
  ext k
  rw [Polynomial.coeff_derivative]
  have hk : P.coeff (k + 1) = 0 :=
    P.coeff_eq_zero_of_natDegree_lt (by omega)
  simp [hk]

private theorem derivative_iterate_vanish
    (P : Polynomial ℝ) (n : ℕ) (hdeg : P.natDegree ≤ n) :
    (Polynomial.derivative^[n + 1]) P = 0 := by
  induction n generalizing P with
  | zero =>
      simp only [Nat.zero_add, Function.iterate_one]
      exact polynomial_derivative_eq_zero_of_natDegree_eq_zero P
        (Nat.le_zero.mp hdeg)
  | succ n ih =>
      change (Polynomial.derivative^[n + 1]) P.derivative = 0
      apply ih P.derivative
      by_cases hzero : P.natDegree = 0
      · have hd := polynomial_derivative_eq_zero_of_natDegree_eq_zero P hzero
        simp [hd]
      · have hlt := P.natDegree_derivative_lt hzero
        omega

private theorem Polynomial.derivative_iterate_eq_zero
    {P : Polynomial ℝ} {n : ℕ} (hdeg : P.natDegree ≤ n) :
    (Polynomial.derivative^[n + 1]) P = 0 :=
  derivative_iterate_vanish P n hdeg

private theorem hasDerivAt_pd
    (P : Polynomial ℝ) (k : ℕ) (x : ℝ) :
    HasDerivAt (pd P k) (pd P (k + 1) x) x := by
  simpa [pd, Function.iterate_succ_apply'] using
    (((Polynomial.derivative^[k]) P).hasDerivAt x)

private theorem hasDerivAt_evenSeries
    (P : Polynomial ℝ) (a x : ℝ) :
    HasDerivAt (evenSeries P a) (oddSeries P a x) x := by
  have hsum :
      HasDerivAt
        (fun y => ∑ k ∈ Finset.range (P.natDegree / 2 + 1),
          (-1 : ℝ) ^ k * pd P (2 * k) y / a ^ (2 * k))
        (∑ k ∈ Finset.range (P.natDegree / 2 + 1),
          (-1 : ℝ) ^ k * pd P (2 * k + 1) x / a ^ (2 * k)) x := by
    have hterms :
        ∀ k ∈ Finset.range (P.natDegree / 2 + 1),
          HasDerivAt
            (fun y => (-1 : ℝ) ^ k * pd P (2 * k) y / a ^ (2 * k))
            ((-1 : ℝ) ^ k * pd P (2 * k + 1) x / a ^ (2 * k)) x := by
      intro k hk
      convert ((hasDerivAt_pd P (2 * k) x).const_mul ((-1 : ℝ) ^ k)).div_const
        (a ^ (2 * k)) using 1 <;> ring
    have hraw := HasDerivAt.sum hterms
    have hfun :
        (Finset.range (P.natDegree / 2 + 1)).sum
          (fun k => fun y : ℝ =>
            (-1 : ℝ) ^ k * pd P (2 * k) y / a ^ (2 * k)) =
          (fun y : ℝ =>
            (Finset.range (P.natDegree / 2 + 1)).sum
              (fun k =>
                (-1 : ℝ) ^ k * pd P (2 * k) y / a ^ (2 * k))) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hfun] at hraw
    exact hraw
  unfold evenSeries oddSeries
  by_cases heven : P.natDegree % 2 = 0
  · have hr : (P.natDegree + 1) / 2 = P.natDegree / 2 := by omega
    have hdeg : P.natDegree ≤ 2 * (P.natDegree / 2) := by omega
    have hz : pd P (2 * (P.natDegree / 2) + 1) x = 0 := by
      have h := derivative_iterate_vanish P (2 * (P.natDegree / 2)) hdeg
      simpa [pd] using congrArg (fun Q : Polynomial ℝ => Q.eval x) h
    simpa [hr, Finset.sum_range_succ, hz] using hsum
  · have hr : (P.natDegree + 1) / 2 = P.natDegree / 2 + 1 := by omega
    simpa [hr] using hsum

private theorem hasDerivAt_oddSeries
    (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) (x : ℝ) :
    HasDerivAt (oddSeries P a)
      (a ^ 2 * (peval P x - evenSeries P a x)) x := by
  let m := P.natDegree / 2
  let e : ℕ → ℝ := fun k =>
    (-1 : ℝ) ^ k * pd P (2 * k) x / a ^ (2 * k)
  let o : ℕ → ℝ := fun k =>
    (-1 : ℝ) ^ k * pd P (2 * k + 2) x / a ^ (2 * k)
  have hsum :
      HasDerivAt
        (fun y => ∑ k ∈ Finset.range ((P.natDegree + 1) / 2),
          (-1 : ℝ) ^ k * pd P (2 * k + 1) y / a ^ (2 * k))
        (∑ k ∈ Finset.range ((P.natDegree + 1) / 2), o k) x := by
    have hterms :
        ∀ k ∈ Finset.range ((P.natDegree + 1) / 2),
          HasDerivAt
            (fun y => (-1 : ℝ) ^ k * pd P (2 * k + 1) y / a ^ (2 * k))
            (o k) x := by
      intro k hk
      simp only [o]
      convert ((hasDerivAt_pd P (2 * k + 1) x).const_mul ((-1 : ℝ) ^ k)).div_const
        (a ^ (2 * k)) using 1 <;> ring
    have hraw := HasDerivAt.sum hterms
    have hfun :
        (Finset.range ((P.natDegree + 1) / 2)).sum
          (fun k => fun y : ℝ =>
            (-1 : ℝ) ^ k * pd P (2 * k + 1) y / a ^ (2 * k)) =
          (fun y : ℝ =>
            (Finset.range ((P.natDegree + 1) / 2)).sum
              (fun k =>
                (-1 : ℝ) ^ k * pd P (2 * k + 1) y / a ^ (2 * k))) := by
      funext y
      simp only [Finset.sum_apply]
    rw [hfun] at hraw
    exact hraw
  have hsplit :
      (∑ k ∈ Finset.range (m + 1), e k) =
        e 0 + ∑ k ∈ Finset.range m, e (k + 1) := by
    induction m with
    | zero => simp
    | succ m ih =>
        rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
        ring
  have htail :
      (∑ k ∈ Finset.range m, o k) =
        -(a ^ 2) * ∑ k ∈ Finset.range m, e (k + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hpow : a ^ (2 * (k + 1)) = a ^ (2 * k) * a ^ 2 := by
      rw [show 2 * (k + 1) = 2 * k + 2 by omega, pow_add]
    simp only [e, o]
    rw [hpow, pow_succ]
    field_simp [ha] <;> ring
  have hOD :
      (∑ k ∈ Finset.range ((P.natDegree + 1) / 2), o k) =
        ∑ k ∈ Finset.range m, o k := by
    by_cases heven : P.natDegree % 2 = 0
    · have hr : (P.natDegree + 1) / 2 = m := by
        simp only [m]
        omega
      rw [hr]
    · have hr : (P.natDegree + 1) / 2 = m + 1 := by
        simp only [m]
        omega
      have hdeg : P.natDegree ≤ 2 * m + 1 := by
        simp only [m]
        omega
      have hz : pd P (2 * m + 2) x = 0 := by
        have h := derivative_iterate_vanish P (2 * m + 1) hdeg
        simpa [pd] using congrArg (fun Q : Polynomial ℝ => Q.eval x) h
      rw [hr, Finset.sum_range_succ]
      simp [o, hz]
  have hhead : e 0 = peval P x := by
    simp [e, pd, peval]
  have hval :
      (∑ k ∈ Finset.range ((P.natDegree + 1) / 2), o k) =
        a ^ 2 * (peval P x - ∑ k ∈ Finset.range (P.natDegree / 2 + 1), e k) := by
    rw [hOD, htail]
    change -(a ^ 2) * (∑ k ∈ Finset.range m, e (k + 1)) =
      a ^ 2 * (peval P x - ∑ k ∈ Finset.range (m + 1), e k)
    rw [hsplit, hhead]
    ring
  unfold oddSeries evenSeries
  change HasDerivAt
    (fun y => ∑ k ∈ Finset.range ((P.natDegree + 1) / 2),
      (-1 : ℝ) ^ k * pd P (2 * k + 1) y / a ^ (2 * k))
    (a ^ 2 *
      (peval P x - ∑ k ∈ Finset.range (P.natDegree / 2 + 1), e k)) x
  simpa only [hval] using hsum

private theorem family_eq_translates_of_hasDerivAt
    (f p : ℝ → ℝ) (hp : ∀ x, HasDerivAt p (f x) x) :
    Family f = Translates p := by
  ext F
  simp only [Family, Translates, Set.mem_setOf_eq]
  constructor
  · intro hF
    have hzero : ∀ x, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x
      simpa using (hF x).sub (hp x)
    refine ⟨F 0 - p 0, ?_⟩
    intro x
    have hc := is_const_of_deriv_eq_zero
      (fun z => (hzero z).differentiableAt)
      (fun z => (hzero z).deriv) x 0
    linarith
  · rintro ⟨C, hFC⟩
    have hfun : F = fun x => p x + C := funext hFC
    rw [hfun]
    intro x
    exact (hp x).add_const C

theorem gap1 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (cosIntegrand P a) = CosDerivativeStep P a := by
  ext F
  simp only [Family, CosDerivativeStep, Set.mem_setOf_eq]
  have hsin (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (a * Real.cos (a * x)) x := by
    convert (Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  constructor
  · intro hF
    refine ⟨fun x => a * F x, ?_, 0, ?_⟩
    · intro x
      convert (hF x).const_mul a using 1 <;>
        simp [cosIntegrand, (hsin x).deriv] <;> ring
    · intro x
      simp [ha]
  · rintro ⟨G, hG, C, hFC⟩
    have hfun : F = fun x => G x / a + C := funext hFC
    rw [hfun]
    intro x
    convert ((hG x).div_const a).add_const C using 1 <;>
      simp [cosIntegrand, (hsin x).deriv, ha] <;> field_simp <;> ring
theorem gap2 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    CosDerivativeStep P a = CosFirstParts P a := by
  ext F
  simp only [CosDerivativeStep, CosFirstParts, Family, Set.mem_setOf_eq]
  have hp (x : ℝ) : HasDerivAt (peval P) (pd P 1 x) x := by
    simpa [peval, pd] using P.hasDerivAt x
  have hs (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (a * Real.cos (a * x)) x := by
    convert (Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  constructor
  · rintro ⟨G, hG, C, hFG⟩
    refine ⟨fun x => peval P x * Real.sin (a * x) - G x, ?_, C, ?_⟩
    · intro x
      convert ((hp x).mul (hs x)).sub (hG x) using 1 <;>
        simp [(hs x).deriv] <;> ring
    · intro x
      rw [hFG x]
      field_simp [ha] <;> ring
  · rintro ⟨H, hH, C, hFH⟩
    refine ⟨fun x => peval P x * Real.sin (a * x) - H x, ?_, C, ?_⟩
    · intro x
      convert ((hp x).mul (hs x)).sub (hH x) using 1 <;>
        simp [(hs x).deriv] <;> ring
    · intro x
      rw [hFH x]
      field_simp [ha] <;> ring
theorem gap3 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (cosIntegrand P a) = CosFirstParts P a := by
  exact (gap1 P a ha).trans (gap2 P a ha)
theorem gap4 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (cosIntegrand P a) =
      {F : ℝ → ℝ | ∃ G ∈ Family
        (fun x => pd P 1 x * deriv (fun y => Real.cos (a * y)) x),
        ∃ C, ∀ x, F x = peval P x * Real.sin (a * x) / a + G x / a ^ 2 + C} := by
  rw [gap3 P a ha]
  ext F
  simp only [CosFirstParts, Family, Set.mem_setOf_eq]
  have hc (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-a * Real.sin (a * x)) x := by
    convert (Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  constructor
  · rintro ⟨H, hH, C, hFH⟩
    refine ⟨fun x => -a * H x, ?_, C, ?_⟩
    · intro x
      convert (hH x).const_mul (-a) using 1 <;>
        simp [(hc x).deriv] <;> ring
    · intro x
      rw [hFH x]
      field_simp [ha]
      ring
  · rintro ⟨G, hG, C, hFG⟩
    refine ⟨fun x => -G x / a, ?_, C, ?_⟩
    · intro x
      convert (hG x).neg.div_const a using 1 <;>
        simp [(hc x).deriv, ha] <;> field_simp <;> ring
    · intro x
      rw [hFG x]
      field_simp [ha]
      ring
theorem gap5 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    {F : ℝ → ℝ | ∃ G ∈ Family
      (fun x => pd P 1 x * deriv (fun y => Real.cos (a * y)) x),
      ∃ C, ∀ x, F x = peval P x * Real.sin (a * x) / a + G x / a ^ 2 + C} =
      CosSecondParts P a := by
  ext F
  simp only [CosSecondParts, Family, Set.mem_setOf_eq]
  have hp (x : ℝ) : HasDerivAt (pd P 1) (pd P 2 x) x := by
    simpa [pd, Function.iterate_succ_apply'] using
      (((Polynomial.derivative^[1]) P).hasDerivAt x)
  have hc (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-a * Real.sin (a * x)) x := by
    convert (Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  constructor
  · rintro ⟨G, hG, C, hFG⟩
    refine ⟨fun x => pd P 1 x * Real.cos (a * x) - G x, ?_, C, ?_⟩
    · intro x
      convert ((hp x).mul (hc x)).sub (hG x) using 1 <;>
        simp [(hc x).deriv] <;> ring
    · intro x
      rw [hFG x]
      field_simp [ha]
      ring
  · rintro ⟨H, hH, C, hFH⟩
    refine ⟨fun x => pd P 1 x * Real.cos (a * x) - H x, ?_, C, ?_⟩
    · intro x
      convert ((hp x).mul (hc x)).sub (hH x) using 1 <;>
        simp [(hc x).deriv] <;> ring
    · intro x
      rw [hFH x]
      field_simp [ha]
      ring
theorem gap6 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (cosIntegrand P a) = CosSecondParts P a := by
  exact (gap4 P a ha).trans (gap5 P a ha)
theorem gap7 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (cosIntegrand P a) = Translates (cosPrimitive P a) := by
  apply family_eq_translates_of_hasDerivAt
  intro x
  have hs :
      HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (a * Real.cos (a * x)) x := by
    convert (Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  have hc :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-a * Real.sin (a * x)) x := by
    convert (Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  have he := hasDerivAt_evenSeries P a x
  have ho := hasDerivAt_oddSeries P a ha x
  unfold cosPrimitive cosIntegrand
  convert ((hs.div_const a).mul he).add
    ((hc.div_const (a ^ 2)).mul ho) using 1 <;>
      field_simp [ha] <;> ring
theorem gap8 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (sinIntegrand P a) = SinDerivativeStep P a := by
  ext F
  simp only [Family, SinDerivativeStep, Set.mem_setOf_eq]
  have hc (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-a * Real.sin (a * x)) x := by
    convert (Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  constructor
  · intro hF
    refine ⟨fun x => -a * F x, ?_, 0, ?_⟩
    · intro x
      convert (hF x).const_mul (-a) using 1 <;>
        simp [sinIntegrand, (hc x).deriv] <;> ring
    · intro x
      field_simp [ha]
      ring
  · rintro ⟨G, hG, C, hFG⟩
    have hfun : F = fun x => -G x / a + C := funext hFG
    rw [hfun]
    intro x
    convert (hG x).neg.div_const a |>.add_const C using 1 <;>
      simp [sinIntegrand, (hc x).deriv, ha] <;> field_simp <;> ring
theorem gap9 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    SinDerivativeStep P a = SinFirstParts P a := by
  ext F
  simp only [SinDerivativeStep, SinFirstParts, Family, Set.mem_setOf_eq]
  have hp (x : ℝ) : HasDerivAt (peval P) (pd P 1 x) x := by
    simpa [peval, pd] using P.hasDerivAt x
  have hc (x : ℝ) :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-a * Real.sin (a * x)) x := by
    convert (Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  constructor
  · rintro ⟨G, hG, C, hFG⟩
    refine ⟨fun x => peval P x * Real.cos (a * x) - G x, ?_, C, ?_⟩
    · intro x
      convert ((hp x).mul (hc x)).sub (hG x) using 1 <;>
        simp [(hc x).deriv] <;> ring
    · intro x
      rw [hFG x]
      field_simp [ha]
      ring
  · rintro ⟨H, hH, C, hFH⟩
    refine ⟨fun x => peval P x * Real.cos (a * x) - H x, ?_, C, ?_⟩
    · intro x
      convert ((hp x).mul (hc x)).sub (hH x) using 1 <;>
        simp [(hc x).deriv] <;> ring
    · intro x
      rw [hFH x]
      field_simp [ha]
      ring
theorem gap10 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (sinIntegrand P a) = SinFirstParts P a := by
  exact (gap8 P a ha).trans (gap9 P a ha)
theorem gap11 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (sinIntegrand P a) = Translates (sinPrimitive P a) := by
  apply family_eq_translates_of_hasDerivAt
  intro x
  have hs :
      HasDerivAt (fun y : ℝ => Real.sin (a * y))
        (a * Real.cos (a * x)) x := by
    convert (Real.hasDerivAt_sin (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  have hc :
      HasDerivAt (fun y : ℝ => Real.cos (a * y))
        (-a * Real.sin (a * x)) x := by
    convert (Real.hasDerivAt_cos (a * x)).comp x
      ((hasDerivAt_const x a).mul (hasDerivAt_id x)) using 1 <;> ring
  have he := hasDerivAt_evenSeries P a x
  have ho := hasDerivAt_oddSeries P a ha x
  unfold sinPrimitive sinIntegrand
  convert ((hc.neg.div_const a).mul he).add
    ((hs.div_const (a ^ 2)).mul ho) using 1 <;>
      simp only [Pi.neg_apply] <;> field_simp [ha] <;> ring
theorem gap12 (P : Polynomial ℝ) (n : ℕ) (hdeg : P.natDegree ≤ n) :
    ∀ x, pd P (n + 1) x = 0 := by
  intro x
  have hz : (Polynomial.derivative^[n + 1]) P = 0 :=
    Polynomial.derivative_iterate_eq_zero (by omega)
  simp [pd, hz]
theorem gap13 (P : Polynomial ℝ) (a : ℝ) (ha : a ≠ 0) :
    Family (cosIntegrand P a) = Translates (cosPrimitive P a) ∧
      Family (sinIntegrand P a) = Translates (sinPrimitive P a) := by
  exact ⟨gap7 P a ha, gap11 P a ha⟩

end
end ProofGap.Exercise2067
