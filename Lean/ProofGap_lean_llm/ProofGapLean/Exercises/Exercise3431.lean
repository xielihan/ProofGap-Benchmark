import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise3431

noncomputable section

def d1 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv f x

def d2 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x

def d3 (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv (deriv f)) x

def reciprocalSlope (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  1 / d1 g y

def inverseSecondFormula (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  -d2 g y / (d1 g y) ^ 3

def inverseThirdFormula (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  (3 * (d2 g y) ^ 2 - d1 g y * d3 g y) / (d1 g y) ^ 5

theorem gap1 (g h : ℝ → ℝ)
    (hInverse : Function.LeftInverse g h)
    (hg : Differentiable ℝ g)
    (hh : Differentiable ℝ h)
    (hNonzero : ∀ x, d1 g (h x) ≠ 0) :
    ∀ x, d1 h x = reciprocalSlope g (h x) := by
  intro x
  have hcomp :=
    (hg (h x)).hasDerivAt.comp x (hh x).hasDerivAt
  have heq : g ∘ h = id := by
    funext t
    exact hInverse t
  have hd := hcomp.deriv
  rw [heq] at hd
  simp only [deriv_id] at hd
  unfold d1 reciprocalSlope
  have hn := hNonzero x
  unfold d1 at hn
  apply (eq_div_iff hn).mpr
  linarith

theorem gap2 (h : ℝ → ℝ) :
    ∀ x, d2 h x = d2 h x := by
  intro x
  rfl

theorem gap3 (g h : ℝ → ℝ)
    (hFirst : ∀ x, d1 h x = reciprocalSlope g (h x))
    (hNonzero : ∀ x, d1 g (h x) ≠ 0)
    (hg : ContDiff ℝ 2 g)
    (hh : ContDiff ℝ 2 h) :
    ∀ x,
      d2 h x =
        deriv (reciprocalSlope g) (h x) * d1 h x := by
  intro x
  have hgd : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hrecip :
      DifferentiableAt ℝ (reciprocalSlope g) (h x) := by
    unfold reciprocalSlope d1
    simp only [one_div]
    exact (hgd.differentiable (by decide) (h x)).inv (hNonzero x)
  have hh1 : Differentiable ℝ h := hh.differentiable (by decide)
  have hcomp :=
    hrecip.hasDerivAt.comp x (hh1 x).hasDerivAt
  unfold d2
  rw [show deriv h = fun t => reciprocalSlope g (h t) by
    funext t
    exact hFirst t]
  simpa [d1] using hcomp.deriv

theorem gap4 (g h : ℝ → ℝ)
    (hChain :
      ∀ x,
        d2 h x =
          deriv (reciprocalSlope g) (h x) * d1 h x)
    (hFirst : ∀ x, d1 h x = reciprocalSlope g (h x))
    (hNonzero : ∀ x, d1 g (h x) ≠ 0)
    (hg : ContDiff ℝ 2 g) :
    ∀ x,
      deriv (reciprocalSlope g) (h x) * d1 h x =
        (-d2 g (h x) / (d1 g (h x)) ^ 2) *
          (1 / d1 g (h x)) := by
  intro x
  have hgd : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hA :
      HasDerivAt (deriv g) (deriv (deriv g) (h x)) (h x) :=
    (hgd.differentiable (by decide) (h x)).hasDerivAt
  have hrecip :
      deriv (reciprocalSlope g) (h x) =
        -d2 g (h x) / (d1 g (h x)) ^ 2 := by
    have hi := hA.inv (hNonzero x)
    unfold reciprocalSlope d1 d2
    simp only [one_div]
    convert hi.deriv using 1
  rw [hrecip, hFirst]
  rfl

theorem gap5 (g h : ℝ → ℝ)
    (hNonzero : ∀ x, d1 g (h x) ≠ 0) :
    ∀ x,
      (-d2 g (h x) / (d1 g (h x)) ^ 2) *
          (1 / d1 g (h x)) =
        inverseSecondFormula g (h x) := by
  intro x
  unfold inverseSecondFormula
  have hn := hNonzero x
  field_simp [hn]

theorem gap6 (g h : ℝ → ℝ)
    (hChain :
      ∀ x,
        d2 h x =
          deriv (reciprocalSlope g) (h x) * d1 h x)
    (hExpand :
      ∀ x,
        deriv (reciprocalSlope g) (h x) * d1 h x =
          (-d2 g (h x) / (d1 g (h x)) ^ 2) *
            (1 / d1 g (h x)))
    (hCollect :
      ∀ x,
        (-d2 g (h x) / (d1 g (h x)) ^ 2) *
            (1 / d1 g (h x)) =
          inverseSecondFormula g (h x)) :
    ∀ x, d2 h x = inverseSecondFormula g (h x) := by
  intro x
  rw [hChain x, hExpand x, hCollect x]

theorem gap7 (h : ℝ → ℝ) :
    ∀ x, d3 h x = d3 h x := by
  intro x
  rfl

theorem gap8 (g h : ℝ → ℝ)
    (hSecond : ∀ x, d2 h x = inverseSecondFormula g (h x))
    (hNonzero : ∀ x, d1 g (h x) ≠ 0)
    (hg : ContDiff ℝ 3 g)
    (hh : ContDiff ℝ 3 h) :
    ∀ x,
      d3 h x =
        deriv (inverseSecondFormula g) (h x) * d1 h x := by
  intro x
  have hgd : ContDiff ℝ 2 (deriv g) := hg.deriv'
  have hgdd : ContDiff ℝ 1 (deriv (deriv g)) := hgd.deriv'
  have hform :
      DifferentiableAt ℝ (inverseSecondFormula g) (h x) := by
    have hA :=
      (hgd.differentiable (by decide) (h x)).hasDerivAt
    have hB :=
      (hgdd.differentiable (by decide) (h x)).hasDerivAt
    have hq := hB.neg.div (hA.pow 3)
      (pow_ne_zero 3 (hNonzero x))
    simpa [inverseSecondFormula, d1, d2] using hq.differentiableAt
  have hh1 : Differentiable ℝ h := hh.differentiable (by decide)
  have hcomp := hform.hasDerivAt.comp x (hh1 x).hasDerivAt
  unfold d3
  rw [show deriv (deriv h) =
      fun t => inverseSecondFormula g (h t) by
    funext t
    exact hSecond t]
  simpa [d1] using hcomp.deriv

theorem gap9 (g h : ℝ → ℝ)
    (hChain :
      ∀ x,
        d3 h x =
          deriv (inverseSecondFormula g) (h x) * d1 h x)
    (hFirst : ∀ x, d1 h x = reciprocalSlope g (h x))
    (hNonzero : ∀ x, d1 g (h x) ≠ 0)
    (hg : ContDiff ℝ 3 g) :
    ∀ x,
      deriv (inverseSecondFormula g) (h x) * d1 h x =
        inverseThirdFormula g (h x) := by
  intro x
  have hgd : ContDiff ℝ 2 (deriv g) := hg.deriv'
  have hgdd : ContDiff ℝ 1 (deriv (deriv g)) := hgd.deriv'
  have hA :=
    (hgd.differentiable (by decide) (h x)).hasDerivAt
  have hB :=
    (hgdd.differentiable (by decide) (h x)).hasDerivAt
  have hform := hB.neg.div (hA.pow 3)
    (pow_ne_zero 3 (hNonzero x))
  have hd := hform.deriv
  rw [hFirst]
  unfold reciprocalSlope inverseSecondFormula inverseThirdFormula d1 d2 d3 at *
  simp only [one_div] at *
  rw [show (fun y => -deriv (deriv g) y / deriv g y ^ 3) =
      -deriv (deriv g) / deriv g ^ 3 by
    funext y
    rfl]
  rw [hd]
  simp only [Pi.pow_apply, Pi.neg_apply, Nat.cast_ofNat, Nat.reduceSub]
  field_simp [hNonzero x]
  ring

theorem gap10 (g h : ℝ → ℝ)
    (hChain :
      ∀ x,
        d3 h x =
          deriv (inverseSecondFormula g) (h x) * d1 h x)
    (hExpand :
      ∀ x,
        deriv (inverseSecondFormula g) (h x) * d1 h x =
          inverseThirdFormula g (h x)) :
    ∀ x, d3 h x = inverseThirdFormula g (h x) := by
  intro x
  rw [hChain x, hExpand x]

theorem gap11 (g h : ℝ → ℝ)
    (hInverse : Function.RightInverse g h)
    (hODE : ∀ x, d1 h x * d3 h x - 3 * (d2 h x) ^ 2 = x)
    (hFirst : ∀ x, d1 h x = reciprocalSlope g (h x))
    (hSecond : ∀ x, d2 h x = inverseSecondFormula g (h x))
    (hThird : ∀ x, d3 h x = inverseThirdFormula g (h x))
    (hNonzero : ∀ y, d1 g y ≠ 0) :
    ∀ y, d3 g y + g y * (d1 g y) ^ 5 = 0 := by
  intro y
  have h := hODE (g y)
  rw [hFirst, hSecond, hThird, hInverse y] at h
  unfold reciprocalSlope inverseSecondFormula inverseThirdFormula at h
  have hn := hNonzero y
  field_simp [hn] at h ⊢
  have hm :
      d1 g y * (d3 g y + g y * (d1 g y) ^ 5) = 0 := by
    calc
      d1 g y * (d3 g y + g y * (d1 g y) ^ 5) =
          d1 g y * d3 g y + (d1 g y) ^ 6 * g y := by ring
      _ = 0 := by linarith
  simpa [mul_comm] using (mul_eq_zero.mp hm).resolve_left hn

end

end ProofGap.Exercise3431
