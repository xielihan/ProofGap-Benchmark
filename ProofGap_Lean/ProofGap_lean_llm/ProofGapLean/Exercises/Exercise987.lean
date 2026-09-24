import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise987

noncomputable section

def detFn {n : ℕ} (A : Fin n → Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  Matrix.det (fun i j => A i j x)

def leibnizExpansion {n : ℕ} (A : Fin n → Fin n → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ σ : Equiv.Perm (Fin n),
    ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A i (σ i) x

def rowDerivativeMatrix {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ)
    (i : Fin n) (x : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun r c => if r = i then A' r c x else A r c x

def rowDerivativeDet {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ)
    (i : Fin n) (x : ℝ) : ℝ :=
  Matrix.det (rowDerivativeMatrix A A' i x)

def derivativeSum {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ)
    (x : ℝ) : ℝ :=
  ∑ i, rowDerivativeDet A A' i x

private theorem hasDerivAt_finset_sum
    {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (f' : ι → ℝ) (x : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt (fun y => s.sum fun i => f i y) (s.sum f') x := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using (hasDerivAt_const x (0 : ℝ))
  | @insert a s ha ih =>
      intro h
      have ha' : HasDerivAt (f a) (f' a) x := h a (by simp)
      have hs' : HasDerivAt (fun y => s.sum fun i => f i y)
          (s.sum f') x :=
        ih (fun i hi => h i (by simp [hi]))
      convert ha'.add hs' using 1
      · funext y
        change (insert a s).sum (fun i => f i y) =
          f a y + s.sum (fun i => f i y)
        exact Finset.sum_insert ha
      · exact Finset.sum_insert ha

private theorem hasDerivAt_finset_prod_replacing
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ → ℝ)
    (f' : ι → ℝ) (x : ℝ)
    (h : ∀ i ∈ s, HasDerivAt (f i) (f' i) x) :
    HasDerivAt
      (fun y => s.prod fun i => f i y)
      (s.sum fun i => s.prod fun j => if j = i then f' j else f j x) x := by
  classical
  revert h
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa using (hasDerivAt_const x (1 : ℝ))
  | @insert a s ha ih =>
      intro h
      have ha' : HasDerivAt (f a) (f' a) x := h a (by simp)
      have hs' : HasDerivAt
          (fun y => s.prod fun i => f i y)
          (s.sum fun i => s.prod fun j => if j = i then f' j else f j x) x :=
        ih (fun i hi => h i (by simp [hi]))
      convert ha'.mul hs' using 1
      · funext y
        change (insert a s).prod (fun i => f i y) =
          f a y * s.prod (fun i => f i y)
        exact Finset.prod_insert ha
      · rw [Finset.sum_insert ha]
        congr 1
        · calc
            (∏ j ∈ insert a s, if j = a then f' j else f j x) =
                f' a * ∏ j ∈ s, if j = a then f' j else f j x := by
                  rw [Finset.prod_insert ha]
                  simp only [if_pos]
            _ = f' a * ∏ j ∈ s, f j x := by
                  congr 1
                  apply Finset.prod_congr rfl
                  intro j hj
                  have hja : j ≠ a := by
                    intro hja
                    apply ha
                    exact hja ▸ hj
                  simp [hja]
        · rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i hi
          have hai : a ≠ i := by
            intro hai
            apply ha
            exact hai.symm ▸ hi
          rw [Finset.prod_insert ha]
          simp [hai]

theorem gap1 {n : ℕ} (A : Fin n → Fin n → ℝ → ℝ) (x : ℝ) :
    detFn A x = leibnizExpansion A x := by
  classical
  unfold detFn leibnizExpansion
  calc
    Matrix.det (fun i j => A i j x) =
        Matrix.det (fun i j => A j i x) := by
      symm
      simpa only using
        (Matrix.det_transpose (fun i j : Fin n => A i j x))
    _ = ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A i (σ i) x := by
      simpa using
        (Matrix.det_apply' (fun i j : Fin n => A j i x))

theorem gap2 {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (A i j) (A' i j x) x) :
    HasDerivAt (detFn A) (derivativeSum A A' x) x := by
  classical
  have hprod : ∀ σ : Equiv.Perm (Fin n),
      HasDerivAt
        (fun y => ∏ i : Fin n, A i (σ i) y)
        (∑ r : Fin n, ∏ j : Fin n,
          if j = r then A' j (σ j) x else A j (σ j) x) x := by
    intro σ
    exact
      hasDerivAt_finset_prod_replacing
        (s := Finset.univ)
        (f := fun i y => A i (σ i) y)
        (f' := fun i => A' i (σ i) x)
        (x := x)
        (fun i _ => hA i (σ i))
  have hterm : ∀ σ : Equiv.Perm (Fin n),
      HasDerivAt
        (fun y => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i : Fin n, A i (σ i) y)
        (((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ r : Fin n, ∏ j : Fin n,
            if j = r then A' j (σ j) x else A j (σ j) x) x := by
    intro σ
    simpa using
      (hasDerivAt_const x ((Equiv.Perm.sign σ : ℤ) : ℝ)).mul (hprod σ)
  have hsum : HasDerivAt (leibnizExpansion A)
      (∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ r : Fin n, ∏ j : Fin n,
            if j = r then A' j (σ j) x else A j (σ j) x) x := by
    simpa [leibnizExpansion] using
      (hasDerivAt_finset_sum
        (s := Finset.univ)
        (f := fun σ y => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∏ i : Fin n, A i (σ i) y)
        (f' := fun σ => ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ r : Fin n, ∏ j : Fin n,
            if j = r then A' j (σ j) x else A j (σ j) x)
        (x := x)
        (fun σ _ => hterm σ))
  have hrow (r : Fin n) :
      Matrix.det (rowDerivativeMatrix A A' r x) =
        ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ j : Fin n,
              if j = r then A' j (σ j) x else A j (σ j) x := by
    simpa [detFn, leibnizExpansion, rowDerivativeMatrix] using
      (gap1
        (A := fun i j y => if i = r then A' i j y else A i j y)
        (x := x))
  have hvalue :
      (∑ σ : Equiv.Perm (Fin n),
        ((Equiv.Perm.sign σ : ℤ) : ℝ) *
          ∑ r : Fin n, ∏ j : Fin n,
            if j = r then A' j (σ j) x else A j (σ j) x) =
        derivativeSum A A' x := by
    calc
      _ = ∑ σ : Equiv.Perm (Fin n), ∑ r : Fin n,
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ j : Fin n,
              if j = r then A' j (σ j) x else A j (σ j) x := by
            apply Finset.sum_congr rfl
            intro σ _
            rw [Finset.mul_sum]
      _ = ∑ r : Fin n, ∑ σ : Equiv.Perm (Fin n),
          ((Equiv.Perm.sign σ : ℤ) : ℝ) *
            ∏ j : Fin n,
              if j = r then A' j (σ j) x else A j (σ j) x := by
            rw [Finset.sum_comm]
      _ = derivativeSum A A' x := by
            unfold derivativeSum rowDerivativeDet
            apply Finset.sum_congr rfl
            intro r _
            exact (hrow r).symm
  rw [hvalue] at hsum
  have hfun : leibnizExpansion A = detFn A := by
    funext y
    exact (gap1 (A := A) (x := y)).symm
  rw [hfun] at hsum
  exact hsum

theorem gap3 {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (A i j) (A' i j x) x) :
    HasDerivAt (leibnizExpansion A) (derivativeSum A A' x) x := by
  have hfun : leibnizExpansion A = detFn A := by
    funext y
    exact (gap1 (A := A) (x := y)).symm
  rw [hfun]
  exact gap2 (A := A) (A' := A') (x := x) hA

theorem gap4 {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (A i j) (A' i j x) x) :
    HasDerivAt (detFn A)
      (∑ i, Matrix.det (rowDerivativeMatrix A A' i x)) x := by
  simpa [derivativeSum, rowDerivativeDet] using
    (gap2 (A := A) (A' := A') (x := x) hA)

theorem gap5 {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ) (x : ℝ) :
    (∑ i, Matrix.det (rowDerivativeMatrix A A' i x)) =
      derivativeSum A A' x := by
  rfl

theorem gap6 {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (A i j) (A' i j x) x) :
    HasDerivAt (detFn A) (∑ i, rowDerivativeDet A A' i x) x := by
  simpa [derivativeSum] using
    (gap2 (A := A) (A' := A') (x := x) hA)

theorem gap7 {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (A i j) (A' i j x) x) :
    HasDerivAt (detFn A) (derivativeSum A A' x) x := by
  exact gap2 (A := A) (A' := A') (x := x) hA

theorem gap8 {n : ℕ} (A A' : Fin n → Fin n → ℝ → ℝ) (x : ℝ)
    (hA : ∀ i j, HasDerivAt (A i j) (A' i j x) x) :
    HasDerivAt (detFn A) (derivativeSum A A' x) x := by
  exact gap7 (A := A) (A' := A') (x := x) hA

end

end ProofGap.Exercise987
