import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1572

noncomputable section

def height (l r : ℝ) : ℝ := Real.sqrt (l ^ 2 - r ^ 2)
def volume (l r : ℝ) : ℝ :=
  (1 / 3 : ℝ) * Real.pi * r ^ 2 * height l r
def squaredObjective (l r : ℝ) : ℝ := r ^ 4 * (l ^ 2 - r ^ 2)
def optimalRadius (l : ℝ) : ℝ := Real.sqrt (2 / 3) * l
def optimalHeight (l : ℝ) : ℝ := l / Real.sqrt 3

def Feasible (l r h : ℝ) : Prop :=
  0 < r ∧ 0 < h ∧ h = height l r

def IsOptimal (l r h : ℝ) : Prop :=
  Feasible l r h ∧ ∀ r₁ h₁, Feasible l r₁ h₁ →
    (1 / 3 : ℝ) * Real.pi * r₁ ^ 2 * h₁ ≤
      (1 / 3 : ℝ) * Real.pi * r ^ 2 * h

theorem gap1 (l r h : ℝ) (hfeas : Feasible l r h) :
    h = height l r := by
  exact hfeas.2.2

theorem gap2 (l r h : ℝ) (hh : h = height l r) :
    (1 / 3 : ℝ) * Real.pi * r ^ 2 * h = volume l r := by
  simpa [volume, hh]

theorem gap3 (l r : ℝ) :
    deriv (squaredObjective l) r = 4 * l ^ 2 * r ^ 3 - 6 * r ^ 5 := by
  have hx : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id r
  have hx2 : HasDerivAt (fun x : ℝ => x ^ 2) (2 * r) r := by
    convert hx.mul hx using 1
    · funext x
      change x ^ 2 = x * x
      ring
    · ring
  have hx4 : HasDerivAt (fun x : ℝ => x ^ 4) (4 * r ^ 3) r := by
    convert hx2.mul hx2 using 1
    · funext x
      change x ^ 4 = x ^ 2 * x ^ 2
      ring
    · ring
  have hdiff :
      HasDerivAt (fun x : ℝ => l ^ 2 - x ^ 2) (-2 * r) r := by
    convert (hasDerivAt_const r (l ^ 2)).sub hx2 using 1 <;> ring
  have hderiv :
      HasDerivAt (squaredObjective l)
        (4 * r ^ 3 * (l ^ 2 - r ^ 2) + r ^ 4 * (-2 * r)) r := by
    simpa [squaredObjective] using hx4.mul hdiff
  rw [hderiv.deriv]
  ring

theorem gap4 (l r : ℝ) (hl : 0 < l) (hr : 0 < r)
    (hrl : r < l) (hcrit : deriv (squaredObjective l) r = 0) :
    r = optimalRadius l := by
  rw [gap3] at hcrit
  have hfactor : r ^ 3 * (4 * l ^ 2 - 6 * r ^ 2) = 0 := by
    nlinarith
  have hr3 : r ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hr)
  have hquad : 4 * l ^ 2 - 6 * r ^ 2 = 0 :=
    (mul_eq_zero.mp hfactor).resolve_left hr3
  have hs_sq : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = (2 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hcand_sq :
      (Real.sqrt (2 / 3 : ℝ) * l) ^ 2 = (2 / 3 : ℝ) * l ^ 2 := by
    rw [mul_pow, hs_sq]
  have hcand_pos : 0 < Real.sqrt (2 / 3 : ℝ) * l :=
    mul_pos (Real.sqrt_pos.2 (by norm_num)) hl
  rw [optimalRadius]
  nlinarith

theorem gap5 (l : ℝ) (hl : 0 < l) :
    height l (optimalRadius l) = optimalHeight l := by
  have hs_sq : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = (2 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hrad : l ^ 2 - (optimalRadius l) ^ 2 = l ^ 2 / 3 := by
    rw [optimalRadius, mul_pow, hs_sq]
    ring
  have hs3_sq : (Real.sqrt 3) ^ 2 = (3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hs3_pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hrad_nonneg : 0 ≤ l ^ 2 / 3 := by
    nlinarith [sq_nonneg l]
  have hleft_sq : (Real.sqrt (l ^ 2 / 3)) ^ 2 = l ^ 2 / 3 :=
    Real.sq_sqrt hrad_nonneg
  have hright_sq : (l / Real.sqrt 3) ^ 2 = l ^ 2 / 3 := by
    rw [div_pow, hs3_sq]
  have hleft_nonneg : 0 ≤ Real.sqrt (l ^ 2 / 3) := Real.sqrt_nonneg _
  have hright_pos : 0 < l / Real.sqrt 3 := div_pos hl hs3_pos
  rw [height, optimalHeight, hrad]
  nlinarith

theorem gap6 (l : ℝ) (hl : 0 < l) :
    ∀ r ∈ Set.Ioo 0 l, volume l r ≤ volume l (optimalRadius l) := by
  intro r hrange
  rcases hrange with ⟨hr, hrl⟩
  have hsum_nonneg : 0 ≤ l + r := by linarith
  have hrad : 0 ≤ l ^ 2 - r ^ 2 := by
    have hp : 0 ≤ (l - r) * (l + r) :=
      mul_nonneg (le_of_lt (sub_pos.mpr hrl)) hsum_nonneg
    nlinarith
  have hs_sq : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = (2 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hro_sq :
      (optimalRadius l) ^ 2 = (2 / 3 : ℝ) * l ^ 2 := by
    rw [optimalRadius, mul_pow, hs_sq]
  have hro_four :
      (optimalRadius l) ^ 4 = (4 / 9 : ℝ) * l ^ 4 := by
    calc
      (optimalRadius l) ^ 4 = ((optimalRadius l) ^ 2) ^ 2 := by ring
      _ = ((2 / 3 : ℝ) * l ^ 2) ^ 2 := by rw [hro_sq]
      _ = (4 / 9 : ℝ) * l ^ 4 := by ring
  have hopt_rad : 0 ≤ l ^ 2 - (optimalRadius l) ^ 2 := by
    rw [hro_sq]
    nlinarith [sq_nonneg l]
  have hfactor_nonneg :
      0 ≤ (r ^ 2 - (2 / 3 : ℝ) * l ^ 2) ^ 2 *
        (r ^ 2 + (1 / 3 : ℝ) * l ^ 2) := by
    exact mul_nonneg (sq_nonneg _)
      (by nlinarith [sq_nonneg r, sq_nonneg l])
  have hidentity :
      squaredObjective l (optimalRadius l) - squaredObjective l r =
        (r ^ 2 - (2 / 3 : ℝ) * l ^ 2) ^ 2 *
          (r ^ 2 + (1 / 3 : ℝ) * l ^ 2) := by
    rw [squaredObjective, squaredObjective, hro_four, hro_sq]
    ring
  have hobj :
      squaredObjective l r ≤ squaredObjective l (optimalRadius l) := by
    nlinarith
  have hh_sq : (height l r) ^ 2 = l ^ 2 - r ^ 2 := by
    simpa [height] using Real.sq_sqrt hrad
  have hopt_h_sq :
      (height l (optimalRadius l)) ^ 2 =
        l ^ 2 - (optimalRadius l) ^ 2 := by
    simpa [height] using Real.sq_sqrt hopt_rad
  have hterm_sq :
      (r ^ 2 * height l r) ^ 2 = squaredObjective l r := by
    rw [mul_pow, hh_sq]
    unfold squaredObjective
    ring
  have hopt_term_sq :
      ((optimalRadius l) ^ 2 * height l (optimalRadius l)) ^ 2 =
        squaredObjective l (optimalRadius l) := by
    rw [mul_pow, hopt_h_sq]
    unfold squaredObjective
    ring
  have hterm_nonneg : 0 ≤ r ^ 2 * height l r :=
    mul_nonneg (sq_nonneg r) (Real.sqrt_nonneg _)
  have hopt_term_nonneg :
      0 ≤ (optimalRadius l) ^ 2 * height l (optimalRadius l) :=
    mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hbase :
      r ^ 2 * height l r ≤
        (optimalRadius l) ^ 2 * height l (optimalRadius l) := by
    nlinarith
  have hc : 0 ≤ (1 / 3 : ℝ) * Real.pi :=
    mul_nonneg (by norm_num) (le_of_lt Real.pi_pos)
  have hm := mul_le_mul_of_nonneg_left hbase hc
  simpa [volume, mul_assoc] using hm

theorem gap7 (l : ℝ) (hl : 0 < l) :
    volume l (optimalRadius l) =
      2 * Real.pi * l ^ 3 / (9 * Real.sqrt 3) := by
  have hs_sq : (Real.sqrt (2 / 3 : ℝ)) ^ 2 = (2 / 3 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  unfold volume
  rw [gap5 l hl, optimalRadius, mul_pow, hs_sq]
  unfold optimalHeight
  ring

theorem gap8 (l : ℝ) (hl : 0 < l) :
    IsOptimal l (optimalRadius l) (optimalHeight l) := by
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · exact mul_pos (Real.sqrt_pos.2 (by norm_num)) hl
    · exact div_pos hl (Real.sqrt_pos.2 (by norm_num))
    · exact (gap5 l hl).symm
  · intro r₁ h₁ hfeas
    have hh_pos : 0 < height l r₁ := by
      rw [← hfeas.2.2]
      exact hfeas.2.1
    have hrad_pos : 0 < l ^ 2 - r₁ ^ 2 := by
      exact Real.sqrt_pos.mp (by simpa [height] using hh_pos)
    have hrlt : r₁ < l := by
      by_contra hnot
      have hp : 0 ≤ (r₁ - l) * (r₁ + l) :=
        mul_nonneg (sub_nonneg.mpr (le_of_not_gt hnot))
          (by linarith [hfeas.1, hl])
      nlinarith
    have hv := gap6 l hl r₁ ⟨hfeas.1, hrlt⟩
    simpa [volume, hfeas.2.2, gap5 l hl] using hv

end

end ProofGap.Exercise1572
