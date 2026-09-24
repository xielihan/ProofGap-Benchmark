import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

namespace ProofGap.Exercise1567

noncomputable section

def reduced (d b : ℝ) : ℝ := b * (d ^ 2 - b ^ 2)

def Feasible (d b h : ℝ) : Prop :=
  0 < b ∧ 0 < h ∧ b ^ 2 + h ^ 2 = d ^ 2

def IsOptimal (d b h : ℝ) : Prop :=
  Feasible d b h ∧ ∀ b₁ h₁, Feasible d b₁ h₁ → b₁ * h₁ ^ 2 ≤ b * h ^ 2

def optimalBase (d : ℝ) : ℝ := d / Real.sqrt 3
def optimalHeight (d : ℝ) : ℝ := d * Real.sqrt (2 / 3)

private theorem canonicalFeasible (d : ℝ) (hd : 0 < d) :
    Feasible d (optimalBase d) (optimalHeight d) := by
  have hs3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs3_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hs23 : 0 < Real.sqrt ((2 : ℝ) / 3) :=
    Real.sqrt_pos.2 (by norm_num)
  have hs23_sq : (Real.sqrt ((2 : ℝ) / 3)) ^ 2 = (2 : ℝ) / 3 :=
    Real.sq_sqrt (by norm_num)
  unfold Feasible
  refine ⟨?_, ?_, ?_⟩
  · simpa [optimalBase] using div_pos hd hs3
  · simpa [optimalHeight] using mul_pos hd hs23
  · simp only [optimalBase, optimalHeight]
    rw [div_pow, hs3_sq, mul_pow, hs23_sq]
    ring

private theorem reduced_optimal_sub (d b : ℝ) :
    reduced d (optimalBase d) - reduced d b =
      (b - optimalBase d) ^ 2 * (b + 2 * optimalBase d) := by
  have hs3_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  have hd_sq : d ^ 2 = 3 * (optimalBase d) ^ 2 := by
    unfold optimalBase
    rw [div_pow, hs3_sq]
    ring
  unfold reduced
  rw [hd_sq]
  ring

private theorem reduced_le_optimal (d b : ℝ) (hd : 0 < d) (hb : 0 < b) :
    reduced d b ≤ reduced d (optimalBase d) := by
  have hs3 : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have ha : 0 < optimalBase d := by
    simpa [optimalBase] using div_pos hd hs3
  have hsum : 0 ≤ b + 2 * optimalBase d := by
    nlinarith
  have hnonneg :
      0 ≤ (b - optimalBase d) ^ 2 * (b + 2 * optimalBase d) :=
    mul_nonneg (sq_nonneg _) hsum
  have hdiff : 0 ≤ reduced d (optimalBase d) - reduced d b := by
    rw [reduced_optimal_sub d b]
    exact hnonneg
  linarith

theorem gap1 (d b h : ℝ) (hfeas : Feasible d b h) :
    h ^ 2 = d ^ 2 - b ^ 2 := by
  rcases hfeas with ⟨hb, hh, heq⟩
  nlinarith

theorem gap2 (d b : ℝ) :
    deriv (reduced d) b = d ^ 2 - 3 * b ^ 2 := by
  have hderiv :
      HasDerivAt (reduced d) (d ^ 2 - 3 * b ^ 2) b := by
    convert
      (hasDerivAt_id b).mul
        ((hasDerivAt_const b (d ^ 2)).sub
          ((hasDerivAt_id b).mul (hasDerivAt_id b))) using 1
    · funext x
      simp [reduced, pow_two] <;> ring
    · simp [pow_two] <;> ring
  exact hderiv.deriv

theorem gap3 (d b : ℝ) (hd : 0 < d) (hb : 0 < b)
    (hcrit : deriv (reduced d) b = 0) :
    b = optimalBase d := by
  rw [gap2 d b] at hcrit
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hs_sq : (Real.sqrt (3 : ℝ)) ^ 2 = 3 :=
    Real.sq_sqrt (by norm_num)
  unfold optimalBase
  apply (eq_div_iff (ne_of_gt hs)).2
  have hsq : (b * Real.sqrt (3 : ℝ)) ^ 2 = d ^ 2 := by
    rw [mul_pow, hs_sq]
    nlinarith
  have hsum : 0 < b * Real.sqrt (3 : ℝ) + d :=
    add_pos (mul_pos hb hs) hd
  have hfac :
      (b * Real.sqrt (3 : ℝ) - d) *
          (b * Real.sqrt (3 : ℝ) + d) = 0 := by
    nlinarith [hsq]
  have hdiff : b * Real.sqrt (3 : ℝ) - d = 0 :=
    (mul_eq_zero.mp hfac).resolve_right (ne_of_gt hsum)
  nlinarith

theorem gap4 (d b h : ℝ) (hd : 0 < d) (hopt : IsOptimal d b h) :
    b = optimalBase d ∧ h = optimalHeight d := by
  rcases hopt with ⟨hfeas, hmax⟩
  have hcan := canonicalFeasible d hd
  have hle : reduced d b ≤ reduced d (optimalBase d) :=
    reduced_le_optimal d b hd hfeas.1
  have hrev : reduced d (optimalBase d) ≤ reduced d b := by
    calc
      reduced d (optimalBase d) =
          optimalBase d * optimalHeight d ^ 2 := by
            rw [gap1 d (optimalBase d) (optimalHeight d) hcan]
            rfl
      _ ≤ b * h ^ 2 := hmax (optimalBase d) (optimalHeight d) hcan
      _ = reduced d b := by
            rw [gap1 d b h hfeas]
            rfl
  have heq : reduced d b = reduced d (optimalBase d) :=
    le_antisymm hle hrev
  have hprod :
      (b - optimalBase d) ^ 2 * (b + 2 * optimalBase d) = 0 := by
    calc
      (b - optimalBase d) ^ 2 * (b + 2 * optimalBase d) =
          reduced d (optimalBase d) - reduced d b :=
            (reduced_optimal_sub d b).symm
      _ = 0 := by rw [heq]; ring
  have ha : 0 < optimalBase d := by
    have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.2 (by norm_num)
    simpa [optimalBase] using div_pos hd hs
  have hsum : 0 < b + 2 * optimalBase d := by
    nlinarith [hfeas.1, ha]
  have hsq : (b - optimalBase d) ^ 2 = 0 :=
    (mul_eq_zero.mp hprod).resolve_right (ne_of_gt hsum)
  have hb : b = optimalBase d := by
    nlinarith [hsq]
  refine ⟨hb, ?_⟩
  have hh_sq := gap1 d b h hfeas
  have hH_sq := gap1 d (optimalBase d) (optimalHeight d) hcan
  rw [hb] at hh_sq
  have hsqeq : h ^ 2 = optimalHeight d ^ 2 := by
    nlinarith [hh_sq, hH_sq]
  have hheight_sum : 0 < h + optimalHeight d :=
    add_pos hfeas.2.1 hcan.2.1
  have hheight_fac :
      (h - optimalHeight d) * (h + optimalHeight d) = 0 := by
    nlinarith [hsqeq]
  have hheight_diff : h - optimalHeight d = 0 :=
    (mul_eq_zero.mp hheight_fac).resolve_right (ne_of_gt hheight_sum)
  nlinarith

theorem gap5 (d b : ℝ) :
    deriv (deriv (reduced d)) b = -6 * b := by
  have hfun : deriv (reduced d) = fun x : ℝ => d ^ 2 - 3 * x ^ 2 := by
    funext x
    exact gap2 d x
  rw [hfun]
  have hderiv :
      HasDerivAt (fun x : ℝ => d ^ 2 - 3 * x ^ 2) (-6 * b) b := by
    convert
      (hasDerivAt_const b (d ^ 2)).sub
        ((hasDerivAt_const b (3 : ℝ)).mul
          ((hasDerivAt_id b).mul (hasDerivAt_id b))) using 1
    · funext x
      simp [pow_two] <;> ring
    · simp [pow_two] <;> ring
  exact hderiv.deriv

theorem gap6 (b : ℝ) (hb : 0 < b) :
    -6 * b < 0 := by
  nlinarith

theorem gap7 (d b : ℝ) (hb : 0 < b) :
    deriv (deriv (reduced d)) b < 0 := by
  rw [gap5 d b]
  exact gap6 b hb

theorem gap8 (d : ℝ) (hd : 0 < d) :
    ∀ b ∈ Set.Ioo 0 d, reduced d b ≤ reduced d (optimalBase d) := by
  intro b hb
  exact reduced_le_optimal d b hd hb.1

theorem gap9 (d : ℝ) (hd : 0 < d) :
    IsOptimal d (optimalBase d) (optimalHeight d) := by
  have hcan := canonicalFeasible d hd
  refine ⟨hcan, ?_⟩
  intro b₁ h₁ hfeas
  calc
    b₁ * h₁ ^ 2 = reduced d b₁ := by
      rw [gap1 d b₁ h₁ hfeas]
      rfl
    _ ≤ reduced d (optimalBase d) :=
      reduced_le_optimal d b₁ hd hfeas.1
    _ = optimalBase d * optimalHeight d ^ 2 := by
      rw [gap1 d (optimalBase d) (optimalHeight d) hcan]
      rfl

end

end ProofGap.Exercise1567
