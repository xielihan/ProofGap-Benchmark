import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1581

noncomputable section

def circumference (R x : ℝ) := R * x
def baseRadius (R x : ℝ) := R * x / (2 * Real.pi)
def height (R x : ℝ) := Real.sqrt (R ^ 2 - baseRadius R x ^ 2)
def volume (R x : ℝ) :=
  (1 / 3 : ℝ) * Real.pi * baseRadius R x ^ 2 * height R x
def volumeFormula (R x : ℝ) :=
  R ^ 3 / (24 * Real.pi ^ 2) * x ^ 2 *
    Real.sqrt (4 * Real.pi ^ 2 - x ^ 2)
def proxy (x : ℝ) := x ^ 4 * (4 * Real.pi ^ 2 - x ^ 2)
def optimizer : ℝ := 2 * Real.pi * Real.sqrt (2 / 3)
def Optimal (R x : ℝ) : Prop :=
  x ∈ Set.Ioo 0 (2 * Real.pi) ∧
    ∀ x₁ ∈ Set.Ioo 0 (2 * Real.pi), volumeFormula R x₁ ≤ volumeFormula R x

private lemma sqrt_ratio_pos : 0 < Real.sqrt (2 / 3 : ℝ) := by positivity

private lemma sqrt_ratio_sq : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = 2 / 3 := by
  rw [Real.sq_sqrt]
  norm_num

private lemma optimizer_pos : 0 < optimizer := by
  unfold optimizer
  positivity

private lemma optimizer_lt : optimizer < 2 * Real.pi := by
  have hq : Real.sqrt (2 / 3 : ℝ) < 1 := by
    nlinarith [sqrt_ratio_sq, Real.sqrt_nonneg (2 / 3 : ℝ)]
  unfold optimizer
  nlinarith [Real.pi_pos]

private lemma optimizer_mem : optimizer ∈ Set.Ioo 0 (2 * Real.pi) :=
  ⟨optimizer_pos, optimizer_lt⟩

private lemma optimizer_sq : optimizer ^ 2 = 8 * Real.pi ^ 2 / 3 := by
  unfold optimizer
  rw [mul_pow, sqrt_ratio_sq]
  ring

private lemma proxy_max (x : ℝ) : proxy x ≤ proxy optimizer := by
  have hn : 0 ≤ (x ^ 2 - 8 * Real.pi ^ 2 / 3) ^ 2 *
      (x ^ 2 + 4 * Real.pi ^ 2 / 3) := by positivity
  have ho4 : optimizer ^ 4 = (8 * Real.pi ^ 2 / 3) ^ 2 := by
    calc
      optimizer ^ 4 = (optimizer ^ 2) ^ 2 := by ring
      _ = (8 * Real.pi ^ 2 / 3) ^ 2 := by rw [optimizer_sq]
  have hdiff : proxy optimizer - proxy x =
      (x ^ 2 - 8 * Real.pi ^ 2 / 3) ^ 2 *
        (x ^ 2 + 4 * Real.pi ^ 2 / 3) := by
    rw [proxy, proxy, ho4, optimizer_sq]
    ring
  linarith

private lemma radicand_pos {x : ℝ} (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    0 < 4 * Real.pi ^ 2 - x ^ 2 := by
  rcases hx with ⟨hx0, hxpi⟩
  nlinarith [mul_pos (sub_pos.mpr hxpi) (add_pos_of_pos_of_nonneg
    (by positivity : 0 < 2 * Real.pi) hx0.le)]

private lemma shape_sq (x : ℝ) (hrad : 0 ≤ 4 * Real.pi ^ 2 - x ^ 2) :
    (x ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2)) ^ 2 = proxy x := by
  unfold proxy
  rw [mul_pow, Real.sq_sqrt hrad]
  ring

private lemma volume_max (R x : ℝ) (hR : 0 < R)
    (hx : x ∈ Set.Ioo 0 (2 * Real.pi)) :
    volumeFormula R x ≤ volumeFormula R optimizer := by
  have hradx := (radicand_pos hx).le
  have hrado := (radicand_pos optimizer_mem).le
  have hsx := shape_sq x hradx
  have hso := shape_sq optimizer hrado
  have hp := proxy_max x
  have hshape :
      x ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2) ≤
        optimizer ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - optimizer ^ 2) := by
    by_contra hn
    have hlt : optimizer ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - optimizer ^ 2) <
        x ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2) := lt_of_not_ge hn
    have hsum : 0 <
        x ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2) +
        optimizer ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - optimizer ^ 2) := by
      have hnonneg : 0 ≤ optimizer ^ 2 *
          Real.sqrt (4 * Real.pi ^ 2 - optimizer ^ 2) :=
        mul_nonneg (sq_nonneg optimizer) (Real.sqrt_nonneg _)
      linarith
    have hmul := mul_pos (sub_pos.mpr hlt) hsum
    nlinarith
  unfold volumeFormula
  have hc : 0 < R ^ 3 / (24 * Real.pi ^ 2) := by positivity
  nlinarith

private lemma optimizer_unique (R x : ℝ) (hR : 0 < R)
    (hx : x ∈ Set.Ioo 0 (2 * Real.pi))
    (hle : volumeFormula R optimizer ≤ volumeFormula R x) :
    x = optimizer := by
  have hmax := volume_max R x hR hx
  have hvol : volumeFormula R x = volumeFormula R optimizer :=
    le_antisymm hmax hle
  have hradx := (radicand_pos hx).le
  have hrado := (radicand_pos optimizer_mem).le
  have hsx := shape_sq x hradx
  have hso := shape_sq optimizer hrado
  have hc : 0 < R ^ 3 / (24 * Real.pi ^ 2) := by positivity
  have hshape :
      x ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2) =
        optimizer ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - optimizer ^ 2) := by
    unfold volumeFormula at hvol
    nlinarith
  have hp : proxy x = proxy optimizer := by
    calc
      proxy x = (x ^ 2 * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2)) ^ 2 := hsx.symm
      _ = (optimizer ^ 2 *
          Real.sqrt (4 * Real.pi ^ 2 - optimizer ^ 2)) ^ 2 := by rw [hshape]
      _ = proxy optimizer := hso
  have ho4 : optimizer ^ 4 = (8 * Real.pi ^ 2 / 3) ^ 2 := by
    calc
      optimizer ^ 4 = (optimizer ^ 2) ^ 2 := by ring
      _ = (8 * Real.pi ^ 2 / 3) ^ 2 := by rw [optimizer_sq]
  have hfactor : proxy optimizer - proxy x =
      (x ^ 2 - 8 * Real.pi ^ 2 / 3) ^ 2 *
        (x ^ 2 + 4 * Real.pi ^ 2 / 3) := by
    rw [proxy, proxy, ho4, optimizer_sq]
    ring
  have hsecond : 0 < x ^ 2 + 4 * Real.pi ^ 2 / 3 := by positivity
  have hx2 : x ^ 2 = 8 * Real.pi ^ 2 / 3 := by
    have hmulzero :
        (x ^ 2 - 8 * Real.pi ^ 2 / 3) ^ 2 *
          (x ^ 2 + 4 * Real.pi ^ 2 / 3) = 0 := by
      linarith
    have hz : (x ^ 2 - 8 * Real.pi ^ 2 / 3) ^ 2 = 0 := by
      exact (mul_eq_zero.mp hmulzero).resolve_right hsecond.ne'
    nlinarith
  have ho2 := optimizer_sq
  nlinarith [hx.1, optimizer_pos, sq_nonneg (x + optimizer)]

theorem gap1 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    circumference R x = R * x := by rfl
theorem gap2 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    baseRadius R x = R * x / (2 * Real.pi) := by rfl
theorem gap3 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    height R x = Real.sqrt (R ^ 2 - (R * x / (2 * Real.pi)) ^ 2) := by rfl
theorem gap4 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    Real.sqrt (R ^ 2 - (R * x / (2 * Real.pi)) ^ 2) =
      R / (2 * Real.pi) * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2) := by
  have hfactor :
      R ^ 2 - (R * x / (2 * Real.pi)) ^ 2 =
        (R / (2 * Real.pi)) ^ 2 * (4 * Real.pi ^ 2 - x ^ 2) := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg (R / (2 * Real.pi))),
    Real.sqrt_sq_eq_abs, abs_of_pos (by positivity)]
theorem gap5 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    height R x =
      R / (2 * Real.pi) * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2) := by
  rw [gap3 R x hR h, gap4 R x hR h]
theorem gap6 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    volume R x =
      (1 / 3 : ℝ) * Real.pi * (R * x / (2 * Real.pi)) ^ 2 *
        (R / (2 * Real.pi) * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2)) := by
  unfold volume
  rw [gap2 R x hR h, gap5 R x hR h]
theorem gap7 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    (1 / 3 : ℝ) * Real.pi * (R * x / (2 * Real.pi)) ^ 2 *
        (R / (2 * Real.pi) * Real.sqrt (4 * Real.pi ^ 2 - x ^ 2)) =
      volumeFormula R x := by
  unfold volumeFormula
  field_simp [Real.pi_ne_zero]
  ring
theorem gap8 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    volume R x = volumeFormula R x := by
  rw [gap6 R x hR h, gap7 R x hR h]
theorem gap9 (x : ℝ) : deriv proxy x = 16 * Real.pi ^ 2 * x ^ 3 - 6 * x ^ 5 := by
  unfold proxy
  have h := ((hasDerivAt_id x).pow 4).mul
    ((hasDerivAt_const x (4 * Real.pi ^ 2 : ℝ)).sub ((hasDerivAt_id x).pow 2))
  convert h.deriv using 1 <;> simp [id] <;> ring
theorem gap10 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) : x ≠ 0 := by
  exact h.1.1.ne'
theorem gap11 (R x : ℝ) (hR : 0 < R) (h : Optimal R x) :
    x = optimizer := by
  exact optimizer_unique R x hR h.1 (h.2 optimizer optimizer_mem)
theorem gap12 (R : ℝ) (hR : 0 < R) :
    IsMaxOn (volumeFormula R) (Set.Ioo 0 (2 * Real.pi)) optimizer := by
  intro x hx
  exact volume_max R x hR hx
theorem gap13 (R x : ℝ) (hR : 0 < R) :
    x = optimizer ↔ Optimal R x := by
  constructor
  · intro hx
    subst x
    exact ⟨optimizer_mem, fun x hx => volume_max R x hR hx⟩
  · intro h
    exact gap11 R x hR h

end
end ProofGap.Exercise1581
