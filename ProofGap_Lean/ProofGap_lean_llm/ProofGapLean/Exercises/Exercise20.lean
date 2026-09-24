import ProofGapLean.Prelude.Core
import Mathlib.Data.Real.Archimedean

/-!
# Exercise 20

Semantic formalization of Exercise 20, gaps 1,...,14.
The two operand sets are arbitrary nonempty bounded sets of nonnegative reals;
they are not the whole nonnegative ray.  The product set is their pointwise
product.
-/

namespace ProofGap.Exercise20

def productSet (X Y : Set ℝ) : Set ℝ :=
  {z | ∃ x ∈ X, ∃ y ∈ Y, z = x * y}

def NonnegativeSet (X : Set ℝ) : Prop :=
  ∀ x ∈ X, 0 ≤ x

def AdmissiblePair (X Y : Set ℝ) : Prop :=
  X.Nonempty ∧ Y.Nonempty ∧
    BddBelow X ∧ BddBelow Y ∧ BddAbove X ∧ BddAbove Y ∧
    NonnegativeSet X ∧ NonnegativeSet Y

def XInfLowerBound (X Y : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, sInf X ≤ x

def XInfNonnegative (X Y : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ sInf X

def YInfLowerBound (X Y : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, sInf Y ≤ y

def YInfNonnegative (X Y : Set ℝ) : Prop :=
  ∀ x ∈ X, ∀ y ∈ Y, 0 ≤ sInf Y

def SeparateInfApproximations (X Y : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ x ∈ X, ∃ y ∈ Y,
      0 ≤ x ∧ x < sInf X + ε ∧
      0 ≤ y ∧ y < sInf Y + ε

def ProductLowerBound (X Y : Set ℝ) : Prop :=
  ∀ z ∈ productSet X Y, sInf X * sInf Y ≤ z

/--
The source's `ε'` must depend on `ε`; its displayed value is recorded
explicitly here.
-/
def ProductPerturbationWitness (X Y : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ ε' : ℝ, ∃ x ∈ X, ∃ y ∈ Y,
      x * y ∈ productSet X Y ∧
      0 ≤ x * y ∧
      x * y < (sInf X + ε) * (sInf Y + ε) ∧
      (sInf X + ε) * (sInf Y + ε) =
        sInf X * sInf Y + ε' ∧
      ε' = (sInf X + sInf Y) * ε + ε ^ 2

def PerturbationFormula (X Y : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ ε' : ℝ, ε' = (sInf X + sInf Y) * ε + ε ^ 2

/-- Exercise 20, gap 1. -/
theorem gap1
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y) :
    0 ≤ sInf X := by
  rcases hXY with
    ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove, hXnonneg, hYnonneg⟩
  exact (isGLB_csInf hX hXbelow).2 hXnonneg

/-- Exercise 20, gap 2. -/
theorem gap2
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h1 : 0 ≤ sInf X) :
    0 ≤ sInf Y := by
  rcases hXY with
    ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove, hXnonneg, hYnonneg⟩
  exact (isGLB_csInf hY hYbelow).2 hYnonneg

/-- Exercise 20, gap 3. -/
theorem gap3
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h1 : 0 ≤ sInf X)
    (h2 : 0 ≤ sInf Y) :
    XInfLowerBound X Y := by
  rcases hXY with
    ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove, hXnonneg, hYnonneg⟩
  intro x hx y hy
  exact (isGLB_csInf hX hXbelow).1 hx

/-- Exercise 20, gap 4. -/
theorem gap4
    (X Y : Set ℝ)
    (h3 : XInfLowerBound X Y)
    (h1 : 0 ≤ sInf X) :
    XInfNonnegative X Y := by
  intro x hx y hy
  exact h1

/-- Exercise 20, gap 5. -/
theorem gap5
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h2 : 0 ≤ sInf Y) :
    YInfLowerBound X Y := by
  rcases hXY with
    ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove, hXnonneg, hYnonneg⟩
  intro x hx y hy
  exact (isGLB_csInf hY hYbelow).1 hy

/-- Exercise 20, gap 6. -/
theorem gap6
    (X Y : Set ℝ)
    (h5 : YInfLowerBound X Y)
    (h2 : 0 ≤ sInf Y) :
    YInfNonnegative X Y := by
  intro x hx y hy
  exact h2

/-- Exercise 20, gap 7. -/
theorem gap7
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h3 : XInfLowerBound X Y)
    (h5 : YInfLowerBound X Y) :
    SeparateInfApproximations X Y := by
  rcases hXY with
    ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove, hXnonneg, hYnonneg⟩
  intro ε hε
  rcases exists_lt_of_csInf_lt hX (lt_add_of_pos_right _ hε) with
    ⟨x, hx, hxlt⟩
  rcases exists_lt_of_csInf_lt hY (lt_add_of_pos_right _ hε) with
    ⟨y, hy, hylt⟩
  exact ⟨x, hx, y, hy, hXnonneg x hx, hxlt, hYnonneg y hy, hylt⟩

/-- Exercise 20, gap 8. -/
theorem gap8
    (X Y : Set ℝ)
    (h1 : 0 ≤ sInf X)
    (h2 : 0 ≤ sInf Y)
    (h3 : XInfLowerBound X Y)
    (h5 : YInfLowerBound X Y) :
    ProductLowerBound X Y := by
  intro z hz
  rcases hz with ⟨x, hx, y, hy, rfl⟩
  have hxl := h3 x hx y hy
  have hyl := h5 x hx y hy
  exact mul_le_mul hxl hyl h2 (h1.trans hxl)

/-- Exercise 20, gap 9; the `ε'` quantifier is repaired. -/
theorem gap9
    (X Y : Set ℝ)
    (h7 : SeparateInfApproximations X Y) :
    ProductPerturbationWitness X Y := by
  intro ε hε
  rcases h7 ε hε with
    ⟨x, hx, y, hy, hxnonneg, hxlt, hynonneg, hylt⟩
  refine ⟨(sInf X + sInf Y) * ε + ε ^ 2,
    x, hx, y, hy, ?_, ?_, ?_, ?_, rfl⟩
  · exact ⟨x, hx, y, hy, rfl⟩
  · positivity
  · calc
      x * y ≤ (sInf X + ε) * y :=
        mul_le_mul_of_nonneg_right hxlt.le hynonneg
      _ < (sInf X + ε) * (sInf Y + ε) :=
        mul_lt_mul_of_pos_left hylt (by linarith)
  · ring

/-- Exercise 20, gap 10; the `ε'` quantifier is repaired. -/
theorem gap10
    (X Y : Set ℝ)
    (h9 : ProductPerturbationWitness X Y) :
    PerturbationFormula X Y := by
  intro ε hε
  exact ⟨(sInf X + sInf Y) * ε + ε ^ 2, rfl⟩

/-- Exercise 20, gap 11. -/
theorem gap11
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h8 : ProductLowerBound X Y)
    (h9 : ProductPerturbationWitness X Y)
    (h10 : PerturbationFormula X Y) :
    sInf X * sInf Y = sInf (productSet X Y) := by
  rcases hXY with
    ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove, hXnonneg, hYnonneg⟩
  have hsum_nonneg : 0 ≤ sInf X + sInf Y := by
    have hix : 0 ≤ sInf X := (isGLB_csInf hX hXbelow).2 hXnonneg
    have hiy : 0 ≤ sInf Y := (isGLB_csInf hY hYbelow).2 hYnonneg
    linarith
  have hprod : (productSet X Y).Nonempty := by
    rcases hX with ⟨x, hx⟩
    rcases hY with ⟨y, hy⟩
    exact ⟨x * y, x, hx, y, hy, rfl⟩
  have hglb : IsGLB (productSet X Y) (sInf X * sInf Y) := by
    constructor
    · exact h8
    · intro M hM
      by_contra hnot
      let δ : ℝ := M - sInf X * sInf Y
      have hδ : 0 < δ := by
        dsimp [δ]
        linarith [lt_of_not_ge hnot]
      let ε : ℝ := min 1 (δ / (2 * (sInf X + sInf Y + 1)))
      have hden : 0 < 2 * (sInf X + sInf Y + 1) := by linarith
      have hε : 0 < ε := by
        dsimp [ε]
        exact lt_min zero_lt_one (div_pos hδ hden)
      have hεle : ε ≤ 1 := by
        dsimp [ε]
        exact min_le_left _ _
      have hεfrac :
          ε ≤ δ / (2 * (sInf X + sInf Y + 1)) := by
        dsimp [ε]
        exact min_le_right _ _
      have hscaled :
          (sInf X + sInf Y + 1) * ε ≤ δ / 2 := by
        have hmul := mul_le_mul_of_nonneg_left hεfrac
          (by linarith : 0 ≤ sInf X + sInf Y + 1)
        have heq :
            (sInf X + sInf Y + 1) *
                (δ / (2 * (sInf X + sInf Y + 1))) = δ / 2 := by
          field_simp [ne_of_gt (by linarith : 0 < sInf X + sInf Y + 1)]
        rwa [heq] at hmul
      rcases h9 ε hε with
        ⟨ε', x, hx, y, hy, hzmem, hznonneg, hzlt, hformula, hε'⟩
      have hε'small : ε' < δ := by
        rw [hε']
        have hepssq : ε ^ 2 ≤ ε := by
          nlinarith [mul_nonneg hε.le (sub_nonneg.mpr hεle)]
        nlinarith
      have hzlt' : x * y < sInf X * sInf Y + ε' := by
        linarith [hzlt, hformula]
      have hMle := hM hzmem
      dsimp [δ] at hε'small
      linarith
  exact (hglb.csInf_eq hprod).symm

/-- Exercise 20, gap 12. -/
theorem gap12
    (X Y : Set ℝ)
    (h11 : sInf X * sInf Y = sInf (productSet X Y)) :
    sInf (productSet X Y) = sInf X * sInf Y := by
  exact h11.symm

/-- Exercise 20, gap 13. -/
theorem gap13
    (X Y : Set ℝ)
    (hXY : AdmissiblePair X Y)
    (h12 : sInf (productSet X Y) = sInf X * sInf Y) :
    sSup (productSet X Y) = sSup X * sSup Y := by
  rcases hXY with
    ⟨hX, hY, hXbelow, hYbelow, hXabove, hYabove, hXnonneg, hYnonneg⟩
  have hSXnonneg : 0 ≤ sSup X := by
    rcases hX with ⟨x, hx⟩
    exact (hXnonneg x hx).trans ((isLUB_csSup ⟨x, hx⟩ hXabove).1 hx)
  have hSYnonneg : 0 ≤ sSup Y := by
    rcases hY with ⟨y, hy⟩
    exact (hYnonneg y hy).trans ((isLUB_csSup ⟨y, hy⟩ hYabove).1 hy)
  have hprod : (productSet X Y).Nonempty := by
    rcases hX with ⟨x, hx⟩
    rcases hY with ⟨y, hy⟩
    exact ⟨x * y, x, hx, y, hy, rfl⟩
  have hlub : IsLUB (productSet X Y) (sSup X * sSup Y) := by
    constructor
    · intro z hz
      rcases hz with ⟨x, hx, y, hy, rfl⟩
      have hxl := (isLUB_csSup hX hXabove).1 hx
      have hyl := (isLUB_csSup hY hYabove).1 hy
      exact mul_le_mul hxl hyl (hYnonneg y hy) hSXnonneg
    · intro M hM
      by_contra hnot
      have hMP : M < sSup X * sSup Y := lt_of_not_ge hnot
      by_cases hSXpos : 0 < sSup X
      · by_cases hSYpos : 0 < sSup Y
        · have hthreshold : max 0 (M / sSup Y) < sSup X := by
            apply max_lt hSXpos
            exact (div_lt_iff₀ hSYpos).2 hMP
          rcases exists_lt_of_lt_csSup hX hthreshold with
            ⟨x, hx, hxgt⟩
          have hxpos : 0 < x :=
            (le_max_left 0 (M / sSup Y)).trans_lt hxgt
          have hMxSY : M < x * sSup Y := by
            apply (div_lt_iff₀ hSYpos).mp
            exact (le_max_right 0 (M / sSup Y)).trans_lt hxgt
          have hythreshold : M / x < sSup Y :=
            (div_lt_iff₀ hxpos).2 (by simpa [mul_comm] using hMxSY)
          rcases exists_lt_of_lt_csSup hY hythreshold with
            ⟨y, hy, hygt⟩
          have hMxy : M < x * y := by
            simpa [mul_comm] using (div_lt_iff₀ hxpos).mp hygt
          exact (not_lt_of_ge (hM ⟨x, hx, y, hy, rfl⟩)) hMxy
        · have hSYzero : sSup Y = 0 := le_antisymm (le_of_not_gt hSYpos) hSYnonneg
          rcases hX with ⟨x, hx⟩
          rcases hY with ⟨y, hy⟩
          have hxy : 0 ≤ x * y := mul_nonneg (hXnonneg x hx) (hYnonneg y hy)
          rw [hSYzero, mul_zero] at hMP
          exact (not_lt_of_ge (hM ⟨x, hx, y, hy, rfl⟩)) (hMP.trans_le hxy)
      · have hSXzero : sSup X = 0 := le_antisymm (le_of_not_gt hSXpos) hSXnonneg
        rcases hX with ⟨x, hx⟩
        rcases hY with ⟨y, hy⟩
        have hxy : 0 ≤ x * y := mul_nonneg (hXnonneg x hx) (hYnonneg y hy)
        rw [hSXzero, zero_mul] at hMP
        exact (not_lt_of_ge (hM ⟨x, hx, y, hy, rfl⟩)) (hMP.trans_le hxy)
  exact hlub.csSup_eq hprod

/-- Exercise 20, gap 14. -/
theorem gap14
    (X Y : Set ℝ)
    (h12 : sInf (productSet X Y) = sInf X * sInf Y)
    (h13 : sSup (productSet X Y) = sSup X * sSup Y) :
    sInf (productSet X Y) = sInf X * sInf Y ∧
      sSup (productSet X Y) = sSup X * sSup Y := by
  exact ⟨h12, h13⟩

end ProofGap.Exercise20
