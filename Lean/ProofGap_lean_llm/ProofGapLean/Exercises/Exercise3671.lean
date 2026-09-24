import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3671

noncomputable section

open scoped BigOperators

def quadraticForm {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * ∑ j, A i j * x j

def unitVector {n : ℕ} (x : Fin n → ℝ) : Prop :=
  ∑ i, x i ^ 2 = 1

def IsEigenvector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ i, ∑ j, A i j * x j = lambda * x i

def characteristicDeterminant {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ) : ℝ :=
  Matrix.det (fun i j => A i j - if i = j then lambda else 0)

def CompleteOrderedEigenSystem {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : Fin n → ℝ) (eigenvector : Fin n → Fin n → ℝ) : Prop :=
  (∀ k, unitVector (eigenvector k) ∧
    IsEigenvector A (eigenvalue k) (eigenvector k)) ∧
  Antitone eigenvalue ∧
  ∀ lambda x, unitVector x → IsEigenvector A lambda x →
    ∃ k, lambda = eigenvalue k

def sphere {n : ℕ} : Set (Fin n → ℝ) :=
  {x | unitVector x}

def maximizers {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ sphere ∧
    ∀ y ∈ sphere, quadraticForm A y ≤ quadraticForm A x}

def minimizers {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ sphere ∧
    ∀ y ∈ sphere, quadraticForm A x ≤ quadraticForm A y}

private theorem unitVector_ne_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : unitVector x) : x ≠ 0 := by
  intro hzero
  subst x
  simp [unitVector] at hx

private theorem quadraticForm_of_eigenvector {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (lambda : ℝ)
    (x : Fin n → ℝ) (hx : unitVector x)
    (heig : IsEigenvector A lambda x) :
    quadraticForm A x = lambda := by
  unfold IsEigenvector at heig
  unfold quadraticForm
  simp_rw [heig]
  calc
    ∑ i, x i * (lambda * x i) =
        lambda * ∑ i, x i ^ 2 := by
      simp_rw [pow_two]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = lambda := by rw [hx, mul_one]

theorem gap1 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (lambda : ℝ) (x : Fin n → ℝ)
    (hx : unitVector x) (heig : IsEigenvector A lambda x) :
    characteristicDeterminant A lambda = 0 := by
  let M : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => A i j - if i = j then lambda else 0
  unfold IsEigenvector at heig
  have hMx : M.mulVec x = 0 := by
    funext i
    change (∑ j, (A i j - if i = j then lambda else 0) * x j) = 0
    calc
      (∑ j, (A i j - if i = j then lambda else 0) * x j) =
          (∑ j, A i j * x j) -
            ∑ j, (if i = j then lambda else 0) * x j := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = lambda * x i - lambda * x i := by rw [heig i]; simp
      _ = 0 := sub_self _
  by_contra hdet
  have hunitDet : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  have hunitM : IsUnit M := M.isUnit_iff_isUnit_det.mpr hunitDet
  have hinj : Function.Injective M.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunitM
  have hxzero : x = 0 := by
    apply hinj
    simpa using hMx
  exact unitVector_ne_zero hx hxzero

theorem gap2 {n : ℕ} (A : Matrix (Fin (n + 2)) (Fin (n + 2)) ℝ)
    (eigenvalue : Fin (n + 2) → ℝ)
    (eigenvector : Fin (n + 2) → Fin (n + 2) → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    eigenvalue 0 ≥ eigenvalue 1 := by
  exact hsys.2.1 (by simp)

theorem gap3 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : Fin n → ℝ) (eigenvector : Fin n → Fin n → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    Antitone eigenvalue := by
  exact hsys.2.1

theorem gap4 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalue : Fin (n + 1) → ℝ)
    (eigenvector : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ i, eigenvalue i ≥ eigenvalue (Fin.last n) := by
  intro i
  exact hsys.2.1 (Fin.le_last i)

theorem gap5 {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalue : Fin (n + 1) → ℝ)
    (eigenvector : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    eigenvalue 0 ≥ eigenvalue (Fin.last n) := by
  exact gap4 A eigenvalue eigenvector hsys 0

theorem gap6 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : Fin n → ℝ) (eigenvector : Fin n → Fin n → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ k i, ∑ j, A i j * eigenvector k j =
      eigenvalue k * eigenvector k i := by
  intro k i
  exact (hsys.1 k).2 i

theorem gap7 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : Fin n → ℝ) (eigenvector : Fin n → Fin n → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    {lambda | ∃ x, unitVector x ∧ IsEigenvector A lambda x} =
      Set.range eigenvalue := by
  ext lambda
  constructor
  · rintro ⟨x, hx, heig⟩
    rcases hsys.2.2 lambda x hx heig with ⟨k, hk⟩
    exact ⟨k, hk.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨eigenvector k, (hsys.1 k).1, (hsys.1 k).2⟩

theorem gap8 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) :
    quadraticForm A x = ∑ i, x i * ∑ j, A i j * x j := by
  rfl

theorem gap9 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : Fin n → ℝ) (eigenvector : Fin n → Fin n → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ k, quadraticForm A (eigenvector k) =
      ∑ i, eigenvalue k * eigenvector k i ^ 2 := by
  intro k
  have heig := (hsys.1 k).2
  unfold IsEigenvector at heig
  unfold quadraticForm
  simp_rw [heig]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem gap10 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : Fin n → ℝ) (eigenvector : Fin n → Fin n → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ k, (∑ i, eigenvalue k * eigenvector k i ^ 2) =
      eigenvalue k := by
  intro k
  rw [← Finset.mul_sum, (hsys.1 k).1, mul_one]

theorem gap11 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (eigenvalue : Fin n → ℝ) (eigenvector : Fin n → Fin n → ℝ)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ k, quadraticForm A (eigenvector k) = eigenvalue k := by
  intro k
  exact quadraticForm_of_eigenvector A (eigenvalue k) (eigenvector k)
    (hsys.1 k).1 (hsys.1 k).2

private theorem symmetric_isHermitian {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℝ}
    (hsym : ∀ i j, A i j = A j i) : A.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  exact (hsym i j).symm

private theorem norm_toLp_eq_one {n : ℕ} {x : Fin n → ℝ}
    (hx : unitVector x) :
    ‖WithLp.toLp 2 x‖ = 1 := by
  have hs := EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)
  change ‖WithLp.toLp 2 x‖ ^ 2 = ∑ i, x i ^ 2 at hs
  rw [hx] at hs
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

private theorem quadraticForm_eq_reApplyInnerSelf {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.toEuclideanLin.IsSymmetric) (x : Fin n → ℝ) :
    quadraticForm A x =
      (hA.toSelfAdjoint : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)).reApplyInnerSelf (WithLp.toLp 2 x) := by
  change (∑ i, x i * ∑ j, A i j * x j) =
    RCLike.re (inner ℝ
      (A.toEuclideanLin (WithLp.toLp 2 x))
      (WithLp.toLp 2 x))
  rw [Matrix.toEuclideanLin_apply_piLp_toLp]
  change (∑ i, x i * ∑ j, A i j * x j) =
    ∑ i, x i * (A.mulVec x) i
  rfl

private theorem isEigenvector_of_isMaxOn {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (x : Fin n → ℝ) (hx : unitVector x)
    (hmax : ∀ y, unitVector y →
      quadraticForm A y ≤ quadraticForm A x) :
    IsEigenvector A (quadraticForm A x) x := by
  have hherm := symmetric_isHermitian hsym
  have hlin : A.toEuclideanLin.IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hherm
  let T := hlin.toSelfAdjoint
  let X : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 x
  have hnorm : ‖X‖ = 1 := norm_toLp_eq_one hx
  have hmaxE :
      IsMaxOn
        (T : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)).reApplyInnerSelf
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) ‖X‖) X := by
    intro Y hY
    let y : Fin n → ℝ := WithLp.ofLp Y
    have hyNorm : ‖Y‖ = 1 := by
      simpa [Metric.mem_sphere, dist_eq_norm, hnorm] using hY
    have hy : unitVector y := by
      unfold unitVector
      have hs := EuclideanSpace.real_norm_sq_eq Y
      change ‖Y‖ ^ 2 = ∑ i, y i ^ 2 at hs
      nlinarith
    have hq := hmax y hy
    rw [quadraticForm_eq_reApplyInnerSelf A hlin] at hq
    have hYX : WithLp.toLp 2 y = Y := WithLp.toLp_ofLp 2 Y
    simpa [T, X, hYX] using hq
  have heq :
      (T : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)) X =
        (T : EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n)).rayleighQuotient X • X :=
    T.prop.eq_smul_self_of_isLocalExtrOn (Or.inr hmaxE.localize)
  have hray :
      (T : EuclideanSpace ℝ (Fin n) →L[ℝ]
        EuclideanSpace ℝ (Fin n)).rayleighQuotient X =
        quadraticForm A x := by
    unfold ContinuousLinearMap.rayleighQuotient
    rw [← quadraticForm_eq_reApplyInnerSelf A hlin]
    rw [hnorm]
    norm_num
  rw [hray] at heq
  change A.toEuclideanLin (WithLp.toLp 2 x) =
      quadraticForm A x • WithLp.toLp 2 x at heq
  rw [Matrix.toEuclideanLin_apply_piLp_toLp] at heq
  change WithLp.toLp 2 (A.mulVec x) =
      WithLp.toLp 2 (quadraticForm A x • x) at heq
  have hfun : A.mulVec x = quadraticForm A x • x :=
    WithLp.toLp_injective 2 heq
  intro i
  simpa [Pi.smul_apply, smul_eq_mul] using congrFun hfun i

private theorem quadraticForm_neg {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    quadraticForm (-A) x = -quadraticForm A x := by
  unfold quadraticForm
  simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem isEigenvector_of_isMinOn {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (x : Fin n → ℝ) (hx : unitVector x)
    (hmin : ∀ y, unitVector y →
      quadraticForm A x ≤ quadraticForm A y) :
    IsEigenvector A (quadraticForm A x) x := by
  have hsymNeg : ∀ i j, (-A) i j = (-A) j i := by
    intro i j
    simp only [Matrix.neg_apply]
    exact congrArg Neg.neg (hsym i j)
  have hmaxNeg : ∀ y, unitVector y →
      quadraticForm (-A) y ≤ quadraticForm (-A) x := by
    intro y hy
    rw [quadraticForm_neg, quadraticForm_neg]
    exact neg_le_neg (hmin y hy)
  have heig := isEigenvector_of_isMaxOn (-A) hsymNeg x hx hmaxNeg
  unfold IsEigenvector at heig ⊢
  intro i
  have hi := heig i
  rw [quadraticForm_neg] at hi
  simp only [Matrix.neg_apply, neg_mul, Finset.sum_neg_distrib] at hi
  linarith

private theorem exists_maximizer {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsym : ∀ i j, A i j = A j i) :
    ∃ x : Fin (n + 1) → ℝ, unitVector x ∧
      ∀ y, unitVector y → quadraticForm A y ≤ quadraticForm A x := by
  have hherm := symmetric_isHermitian hsym
  have hlin : A.toEuclideanLin.IsSymmetric :=
    Matrix.isHermitian_iff_isSymmetric.mp hherm
  let T := hlin.toSelfAdjoint
  let E := EuclideanSpace ℝ (Fin (n + 1))
  have hcompact : IsCompact (Metric.sphere (0 : E) 1) :=
    isCompact_sphere _ _
  let e : Fin (n + 1) → ℝ := fun i => if i = 0 then 1 else 0
  have heUnit : unitVector e := by
    unfold unitVector e
    simp
  have heNorm : ‖WithLp.toLp 2 e‖ = 1 := norm_toLp_eq_one heUnit
  have hnonempty : (Metric.sphere (0 : E) 1).Nonempty := by
    refine ⟨WithLp.toLp 2 e, ?_⟩
    simp [Metric.mem_sphere, heNorm]
  obtain ⟨X, hXsphere, hXmax⟩ :=
    hcompact.exists_isMaxOn hnonempty
      (T : E →L[ℝ] E).reApplyInnerSelf_continuous.continuousOn
  let x : Fin (n + 1) → ℝ := WithLp.ofLp X
  have hXnorm : ‖X‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hXsphere
  have hx : unitVector x := by
    unfold unitVector
    have hs := EuclideanSpace.real_norm_sq_eq X
    change ‖X‖ ^ 2 = ∑ i, x i ^ 2 at hs
    nlinarith
  refine ⟨x, hx, ?_⟩
  intro y hy
  have hyNorm : ‖WithLp.toLp 2 y‖ = 1 := norm_toLp_eq_one hy
  have hySphere : WithLp.toLp 2 y ∈ Metric.sphere (0 : E) 1 := by
    simp [hyNorm]
  have hle := hXmax hySphere
  rw [quadraticForm_eq_reApplyInnerSelf A hlin,
    quadraticForm_eq_reApplyInnerSelf A hlin]
  have hxToLp : WithLp.toLp 2 x = X := WithLp.toLp_ofLp 2 X
  simpa [T, x, hxToLp] using hle

private theorem exists_minimizer {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (hsym : ∀ i j, A i j = A j i) :
    ∃ x : Fin (n + 1) → ℝ, unitVector x ∧
      ∀ y, unitVector y → quadraticForm A x ≤ quadraticForm A y := by
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := -A
  have hsymB : ∀ i j, B i j = B j i := by
    intro i j
    simp only [B, Matrix.neg_apply]
    exact congrArg Neg.neg (hsym i j)
  rcases exists_maximizer B hsymB with ⟨x, hx, hmax⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  have h := hmax y hy
  dsimp [B] at h
  rw [quadraticForm_neg, quadraticForm_neg] at h
  exact neg_le_neg_iff.mp h

theorem gap12 {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalue : Fin (n + 1) → ℝ)
    (eigenvector : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    maximizers A =
      {x | unitVector x ∧ IsEigenvector A (eigenvalue 0) x} := by
  ext x
  constructor
  · rintro ⟨hx, hmax⟩
    have heigQ := isEigenvector_of_isMaxOn A hsym x hx hmax
    rcases hsys.2.2 (quadraticForm A x) x hx heigQ with ⟨k, hk⟩
    have hle : quadraticForm A x ≤ eigenvalue 0 := by
      rw [hk]
      exact hsys.2.1 (Fin.zero_le k)
    have hge : eigenvalue 0 ≤ quadraticForm A x := by
      calc
        eigenvalue 0 = quadraticForm A (eigenvector 0) :=
          (quadraticForm_of_eigenvector A (eigenvalue 0) (eigenvector 0)
            (hsys.1 0).1 (hsys.1 0).2).symm
        _ ≤ quadraticForm A x := hmax (eigenvector 0) (hsys.1 0).1
    have heq : quadraticForm A x = eigenvalue 0 :=
      le_antisymm hle hge
    exact ⟨hx, by simpa [heq] using heigQ⟩
  · rintro ⟨hx, heigTop⟩
    refine ⟨hx, ?_⟩
    intro y hy
    rcases exists_maximizer A hsym with ⟨z, hz, hzmax⟩
    have heigZ := isEigenvector_of_isMaxOn A hsym z hz hzmax
    rcases hsys.2.2 (quadraticForm A z) z hz heigZ with ⟨k, hk⟩
    have hzle : quadraticForm A z ≤ eigenvalue 0 := by
      rw [hk]
      exact hsys.2.1 (Fin.zero_le k)
    have hyle : quadraticForm A y ≤ quadraticForm A z := hzmax y hy
    have hxval : quadraticForm A x = eigenvalue 0 :=
      quadraticForm_of_eigenvector A (eigenvalue 0) x hx heigTop
    linarith

theorem gap13 {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalue : Fin (n + 1) → ℝ)
    (eigenvector : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    minimizers A =
      {x | unitVector x ∧
        IsEigenvector A (eigenvalue (Fin.last n)) x} := by
  ext x
  constructor
  · rintro ⟨hx, hmin⟩
    have heigQ := isEigenvector_of_isMinOn A hsym x hx hmin
    rcases hsys.2.2 (quadraticForm A x) x hx heigQ with ⟨k, hk⟩
    have hge : eigenvalue (Fin.last n) ≤ quadraticForm A x := by
      rw [hk]
      exact hsys.2.1 (Fin.le_last k)
    have hle : quadraticForm A x ≤ eigenvalue (Fin.last n) := by
      calc
        quadraticForm A x ≤ quadraticForm A (eigenvector (Fin.last n)) :=
          hmin (eigenvector (Fin.last n)) (hsys.1 (Fin.last n)).1
        _ = eigenvalue (Fin.last n) :=
          quadraticForm_of_eigenvector A (eigenvalue (Fin.last n))
            (eigenvector (Fin.last n)) (hsys.1 (Fin.last n)).1
            (hsys.1 (Fin.last n)).2
    have heq : quadraticForm A x = eigenvalue (Fin.last n) :=
      le_antisymm hle hge
    exact ⟨hx, by simpa [heq] using heigQ⟩
  · rintro ⟨hx, heigBottom⟩
    refine ⟨hx, ?_⟩
    intro y hy
    rcases exists_minimizer A hsym with ⟨z, hz, hzmin⟩
    have heigZ := isEigenvector_of_isMinOn A hsym z hz hzmin
    rcases hsys.2.2 (quadraticForm A z) z hz heigZ with ⟨k, hk⟩
    have hzge : eigenvalue (Fin.last n) ≤ quadraticForm A z := by
      rw [hk]
      exact hsys.2.1 (Fin.le_last k)
    have hzle : quadraticForm A z ≤ quadraticForm A y := hzmin y hy
    have hxval : quadraticForm A x = eigenvalue (Fin.last n) :=
      quadraticForm_of_eigenvector A (eigenvalue (Fin.last n)) x hx
        heigBottom
    linarith

theorem gap14 {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalue : Fin (n + 1) → ℝ)
    (eigenvector : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ x ∈ maximizers A, quadraticForm A x = eigenvalue 0 := by
  intro x hx
  rw [gap12 A eigenvalue eigenvector hsym hsys] at hx
  exact quadraticForm_of_eigenvector A (eigenvalue 0) x hx.1 hx.2

theorem gap15 {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalue : Fin (n + 1) → ℝ)
    (eigenvector : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ x ∈ minimizers A,
      quadraticForm A x = eigenvalue (Fin.last n) := by
  intro x hx
  rw [gap13 A eigenvalue eigenvector hsym hsys] at hx
  exact quadraticForm_of_eigenvector A (eigenvalue (Fin.last n)) x hx.1 hx.2

theorem gap16 {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (eigenvalue : Fin (n + 1) → ℝ)
    (eigenvector : Fin (n + 1) → Fin (n + 1) → ℝ)
    (hsym : ∀ i j, A i j = A j i)
    (hsys : CompleteOrderedEigenSystem A eigenvalue eigenvector) :
    ∀ k, eigenvalue k ≠ eigenvalue 0 →
      eigenvalue k ≠ eigenvalue (Fin.last n) →
      eigenvector k ∉ maximizers A ∧ eigenvector k ∉ minimizers A := by
  intro k hkTop hkBottom
  constructor
  · intro hk
    have hmaxval := gap14 A eigenvalue eigenvector hsym hsys
      (eigenvector k) hk
    have heigval := quadraticForm_of_eigenvector A (eigenvalue k)
      (eigenvector k) (hsys.1 k).1 (hsys.1 k).2
    exact hkTop (heigval.symm.trans hmaxval)
  · intro hk
    have hminval := gap15 A eigenvalue eigenvector hsym hsys
      (eigenvector k) hk
    have heigval := quadraticForm_of_eigenvector A (eigenvalue k)
      (eigenvector k) (hsys.1 k).1 (hsys.1 k).2
    exact hkBottom (heigval.symm.trans hminval)

end

end ProofGap.Exercise3671
