import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3634

noncomputable section

open Filter Topology

def linearPart (p : ℝ × ℝ) : ℝ :=
  5 * p.1 + 7 * p.2 - 25

def quadraticPart (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.1 * p.2 + p.2 ^ 2

def z (p : ℝ × ℝ) : ℝ :=
  linearPart p * Real.exp (-quadraticPart p)

def partialX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => g (x, p.2)) p.1

def partialY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => g (p.1, y)) p.2

def partialXX (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => partialX g (x, p.2)) p.1

def partialXY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialX g (p.1, y)) p.2

def partialYY (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun y => partialY g (p.1, y)) p.2

def IsCriticalPoint (p : ℝ × ℝ) : Prop :=
  partialX z p = 0 ∧ partialY z p = 0

def p₀ : ℝ × ℝ :=
  (1, 3)

def p₁ : ℝ × ℝ :=
  (-(1 / 26 : ℝ), -(3 / 26 : ℝ))

def criticalPoints : Set (ℝ × ℝ) :=
  {p₀, p₁}

def hessianA (p : ℝ × ℝ) : ℝ :=
  partialXX z p

def hessianB (p : ℝ × ℝ) : ℝ :=
  partialXY z p

def hessianC (p : ℝ × ℝ) : ℝ :=
  partialYY z p

def hessianDiscriminant (p : ℝ × ℝ) : ℝ :=
  hessianA p * hessianC p - hessianB p ^ 2

def IsUniqueGlobalMaximum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  (∀ q, g q ≤ g p) ∧ (∀ q, g q = g p → q = p)

def IsUniqueGlobalMinimum
    (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : Prop :=
  (∀ q, g p ≤ g q) ∧ (∀ q, g q = g p → q = p)

def Approx (a b ε : ℝ) : Prop :=
  |a - b| < ε

private theorem partialX_formula (p : ℝ × ℝ) :
    partialX z p =
      (5 - linearPart p * (2 * p.1 + p.2)) *
        Real.exp (-quadraticPart p) := by
  have hL :
      HasDerivAt
        (fun x : ℝ => 5 * x + 7 * p.2 - 25) 5 p.1 := by
    convert (((hasDerivAt_id p.1).const_mul 5).add_const
      (7 * p.2)).sub_const 25 using 1 <;> ring
  have hQ :
      HasDerivAt
        (fun x : ℝ => -(x ^ 2 + x * p.2 + p.2 ^ 2))
          (-(2 * p.1 + p.2)) p.1 := by
    convert
      (((hasDerivAt_id p.1).pow 2).add
        ((hasDerivAt_id p.1).mul_const p.2) |>.add_const (p.2 ^ 2)).neg
        using 1 <;> simp only [id] <;> ring
  unfold partialX z linearPart quadraticPart
  convert (hL.mul hQ.exp).deriv using 1 <;> ring

private theorem partialY_formula (p : ℝ × ℝ) :
    partialY z p =
      (7 - linearPart p * (p.1 + 2 * p.2)) *
        Real.exp (-quadraticPart p) := by
  have hL :
      HasDerivAt
        (fun y : ℝ => 5 * p.1 + 7 * y - 25) 7 p.2 := by
    convert (((hasDerivAt_id p.2).const_mul 7).const_add
      (5 * p.1)).sub_const 25 using 1 <;> ring
  have hQ :
      HasDerivAt
        (fun y : ℝ => -(p.1 ^ 2 + p.1 * y + y ^ 2))
          (-(p.1 + 2 * p.2)) p.2 := by
    convert
      (((hasDerivAt_const p.2 (p.1 ^ 2)).add
        ((hasDerivAt_id p.2).const_mul p.1)).add
          ((hasDerivAt_id p.2).pow 2)).neg using 1 <;>
      simp only [id] <;> ring
  unfold partialY z linearPart quadraticPart
  convert (hL.mul hQ.exp).deriv using 1 <;> ring

private theorem partialXX_formula (p : ℝ × ℝ) :
    partialXX z p =
      (-5 * (2 * p.1 + p.2) - 2 * linearPart p -
          (5 - linearPart p * (2 * p.1 + p.2)) *
            (2 * p.1 + p.2)) *
        Real.exp (-quadraticPart p) := by
  have hfun :
      (fun x : ℝ => partialX z (x, p.2)) =
        fun x =>
          (5 - linearPart (x, p.2) * (2 * x + p.2)) *
            Real.exp (-quadraticPart (x, p.2)) := by
    funext x
    exact partialX_formula (x, p.2)
  have hL :
      HasDerivAt (fun x : ℝ => linearPart (x, p.2)) 5 p.1 := by
    unfold linearPart
    convert (((hasDerivAt_id p.1).const_mul 5).add_const
      (7 * p.2)).sub_const 25 using 1 <;> ring
  have hM :
      HasDerivAt (fun x : ℝ => 2 * x + p.2) 2 p.1 := by
    convert ((hasDerivAt_id p.1).const_mul 2).add_const p.2 using 1 <;> ring
  have hB :
      HasDerivAt
        (fun x : ℝ =>
          5 - linearPart (x, p.2) * (2 * x + p.2))
        (-5 * (2 * p.1 + p.2) - 2 * linearPart p) p.1 := by
    convert (hL.mul hM).const_sub 5 using 1 <;>
      simp [linearPart] <;> ring
  have hQ :
      HasDerivAt
        (fun x : ℝ => -quadraticPart (x, p.2))
          (-(2 * p.1 + p.2)) p.1 := by
    unfold quadraticPart
    convert
      (((hasDerivAt_id p.1).pow 2).add
        ((hasDerivAt_id p.1).mul_const p.2) |>.add_const (p.2 ^ 2)).neg
        using 1 <;> simp only [id] <;> ring
  unfold partialXX
  rw [hfun]
  convert (hB.mul hQ.exp).deriv using 1 <;>
    simp [linearPart, quadraticPart] <;> ring

private theorem partialXY_formula (p : ℝ × ℝ) :
    partialXY z p =
      (-7 * (2 * p.1 + p.2) - linearPart p -
          (5 - linearPart p * (2 * p.1 + p.2)) *
            (p.1 + 2 * p.2)) *
        Real.exp (-quadraticPart p) := by
  have hfun :
      (fun y : ℝ => partialX z (p.1, y)) =
        fun y =>
          (5 - linearPart (p.1, y) * (2 * p.1 + y)) *
            Real.exp (-quadraticPart (p.1, y)) := by
    funext y
    exact partialX_formula (p.1, y)
  have hL :
      HasDerivAt (fun y : ℝ => linearPart (p.1, y)) 7 p.2 := by
    unfold linearPart
    convert (((hasDerivAt_id p.2).const_mul 7).const_add
      (5 * p.1)).sub_const 25 using 1 <;> ring
  have hM :
      HasDerivAt (fun y : ℝ => 2 * p.1 + y) 1 p.2 := by
    convert (hasDerivAt_id p.2).const_add (2 * p.1) using 1 <;> ring
  have hB :
      HasDerivAt
        (fun y : ℝ =>
          5 - linearPart (p.1, y) * (2 * p.1 + y))
        (-7 * (2 * p.1 + p.2) - linearPart p) p.2 := by
    convert (hL.mul hM).const_sub 5 using 1 <;>
      simp [linearPart] <;> ring
  have hQ :
      HasDerivAt
        (fun y : ℝ => -quadraticPart (p.1, y))
          (-(p.1 + 2 * p.2)) p.2 := by
    unfold quadraticPart
    convert
      (((hasDerivAt_const p.2 (p.1 ^ 2)).add
        ((hasDerivAt_id p.2).const_mul p.1)).add
          ((hasDerivAt_id p.2).pow 2)).neg using 1 <;>
      simp only [id] <;> ring
  unfold partialXY
  rw [hfun]
  convert (hB.mul hQ.exp).deriv using 1 <;>
    simp [linearPart, quadraticPart] <;> ring

private theorem partialYY_formula (p : ℝ × ℝ) :
    partialYY z p =
      (-7 * (p.1 + 2 * p.2) - 2 * linearPart p -
          (7 - linearPart p * (p.1 + 2 * p.2)) *
            (p.1 + 2 * p.2)) *
        Real.exp (-quadraticPart p) := by
  have hfun :
      (fun y : ℝ => partialY z (p.1, y)) =
        fun y =>
          (7 - linearPart (p.1, y) * (p.1 + 2 * y)) *
            Real.exp (-quadraticPart (p.1, y)) := by
    funext y
    exact partialY_formula (p.1, y)
  have hL :
      HasDerivAt (fun y : ℝ => linearPart (p.1, y)) 7 p.2 := by
    unfold linearPart
    convert (((hasDerivAt_id p.2).const_mul 7).const_add
      (5 * p.1)).sub_const 25 using 1 <;> ring
  have hM :
      HasDerivAt (fun y : ℝ => p.1 + 2 * y) 2 p.2 := by
    convert ((hasDerivAt_id p.2).const_mul 2).const_add p.1 using 1 <;> ring
  have hB :
      HasDerivAt
        (fun y : ℝ =>
          7 - linearPart (p.1, y) * (p.1 + 2 * y))
        (-7 * (p.1 + 2 * p.2) - 2 * linearPart p) p.2 := by
    convert (hL.mul hM).const_sub 7 using 1 <;>
      simp [linearPart] <;> ring
  have hQ :
      HasDerivAt
        (fun y : ℝ => -quadraticPart (p.1, y))
          (-(p.1 + 2 * p.2)) p.2 := by
    unfold quadraticPart
    convert
      (((hasDerivAt_const p.2 (p.1 ^ 2)).add
        ((hasDerivAt_id p.2).const_mul p.1)).add
          ((hasDerivAt_id p.2).pow 2)).neg using 1 <;>
      simp only [id] <;> ring
  unfold partialYY
  rw [hfun]
  convert (hB.mul hQ.exp).deriv using 1 <;>
    simp [linearPart, quadraticPart] <;> ring

private theorem critical_equations (p : ℝ × ℝ)
    (hp : IsCriticalPoint p) :
    5 - linearPart p * (2 * p.1 + p.2) = 0 ∧
      7 - linearPart p * (p.1 + 2 * p.2) = 0 := by
  unfold IsCriticalPoint at hp
  constructor
  · rw [partialX_formula] at hp
    exact (mul_eq_zero.mp hp.1).resolve_right (Real.exp_ne_zero _)
  · rw [partialY_formula] at hp
    exact (mul_eq_zero.mp hp.2).resolve_right (Real.exp_ne_zero _)

theorem gap1 :
    ∀ p : ℝ × ℝ, IsCriticalPoint p →
      3 * linearPart p * (3 * p.1 - p.2) = 0 := by
  intro p hp
  obtain ⟨hx, hy⟩ := critical_equations p hp
  nlinarith

theorem gap2 :
    ∀ p : ℝ × ℝ, IsCriticalPoint p →
      linearPart p ≠ 0 := by
  intro p hp hzero
  obtain ⟨hx, hy⟩ := critical_equations p hp
  rw [hzero] at hx
  norm_num at hx

theorem gap3 :
    ∀ p : ℝ × ℝ, IsCriticalPoint p →
      p.2 = 3 * p.1 := by
  intro p hp
  have hprod := gap1 p hp
  have hn := gap2 p hp
  rcases mul_eq_zero.mp hprod with hthree | hrest
  · have hlin : linearPart p = 0 := by nlinarith
    exact False.elim (hn hlin)
  · nlinarith

theorem gap4 :
    ∀ p : ℝ × ℝ, IsCriticalPoint p →
      26 * p.1 ^ 2 - 25 * p.1 - 1 = 0 := by
  intro p hp
  obtain ⟨hx, hy⟩ := critical_equations p hp
  have hp2 := gap3 p hp
  unfold linearPart at hx
  nlinarith

theorem gap5 :
    ∀ p : ℝ × ℝ, p ∈ criticalPoints →
      partialX z p =
          5 * Real.exp (-quadraticPart p) -
            linearPart p * (2 * p.1 + p.2) *
              Real.exp (-quadraticPart p) ∧
      5 * Real.exp (-quadraticPart p) -
          linearPart p * (2 * p.1 + p.2) *
            Real.exp (-quadraticPart p) = 0 ∧
      partialY z p =
          7 * Real.exp (-quadraticPart p) -
            linearPart p * (p.1 + 2 * p.2) *
              Real.exp (-quadraticPart p) ∧
      7 * Real.exp (-quadraticPart p) -
          linearPart p * (p.1 + 2 * p.2) *
            Real.exp (-quadraticPart p) = 0 := by
  intro p hp
  simp only [criticalPoints, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl
  · constructor
    · rw [partialX_formula]
      ring
    constructor
    · norm_num [p₀, linearPart, quadraticPart]
    constructor
    · rw [partialY_formula]
      ring
    · norm_num [p₀, linearPart, quadraticPart]
  · constructor
    · rw [partialX_formula]
      ring
    constructor
    · norm_num [p₁, linearPart, quadraticPart]
    constructor
    · rw [partialY_formula]
      ring
    · norm_num [p₁, linearPart, quadraticPart]

theorem gap6 :
    p₀ = (1, 3) := by
  rfl

theorem gap7 :
    p₁ = (-(1 / 26 : ℝ), -(3 / 26 : ℝ)) := by
  rfl

theorem gap8 :
    hessianA p₀ = -27 * Real.exp (-13) := by
  unfold hessianA
  rw [partialXX_formula]
  norm_num [p₀, linearPart, quadraticPart]

theorem gap9 :
    hessianB p₀ = -36 * Real.exp (-13) := by
  unfold hessianB
  rw [partialXY_formula]
  norm_num [p₀, linearPart, quadraticPart]

theorem gap10 :
    hessianC p₀ = -51 * Real.exp (-13) := by
  unfold hessianC
  rw [partialYY_formula]
  norm_num [p₀, linearPart, quadraticPart]

theorem gap11 :
    hessianDiscriminant p₀ = 81 * Real.exp (-26) := by
  unfold hessianDiscriminant
  rw [gap8, gap9, gap10]
  rw [show Real.exp (-26) = Real.exp (-13) * Real.exp (-13) by
    rw [← Real.exp_add]
    norm_num]
  ring

theorem gap12 :
    81 * Real.exp (-26) > 0 := by
  positivity

theorem gap13 :
    hessianDiscriminant p₀ > 0 := by
  rw [gap11]
  exact gap12

private theorem quadratic_form_nonnegative (x y : ℝ) :
    0 ≤ x ^ 2 + x * y + y ^ 2 := by
  nlinarith [sq_nonneg (2 * x + y), sq_nonneg y]

private theorem z_p₀ :
    z p₀ = Real.exp (-13) := by
  norm_num [z, p₀, linearPart, quadraticPart]

private theorem z_p₁ :
    z p₁ = -26 * Real.exp (-(1 / 52 : ℝ)) := by
  norm_num [z, p₁, linearPart, quadraticPart]

private theorem z_le_p₀ (q : ℝ × ℝ) :
    z q ≤ z p₀ := by
  let d : ℝ :=
    (q.1 - 1) ^ 2 + (q.1 - 1) * (q.2 - 3) + (q.2 - 3) ^ 2
  have hd : 0 ≤ d := quadratic_form_nonnegative (q.1 - 1) (q.2 - 3)
  have hdecomp :
      quadraticPart q = linearPart q + 12 + d := by
    unfold quadraticPart linearPart d
    ring
  by_cases hL : linearPart q ≤ 0
  · have hz : z q ≤ 0 := by
      unfold z
      exact mul_nonpos_of_nonpos_of_nonneg hL (Real.exp_pos _).le
    exact hz.trans (by rw [z_p₀]; exact (Real.exp_pos _).le)
  · have hLpos : 0 < linearPart q := lt_of_not_ge hL
    have hDexp : Real.exp (-d) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hmain :
        linearPart q * Real.exp (-linearPart q) ≤ Real.exp (-1) :=
      Real.mul_exp_neg_le_exp_neg_one _
    have hmain_nonneg :
        0 ≤ linearPart q * Real.exp (-linearPart q) :=
      mul_nonneg hLpos.le (Real.exp_pos _).le
    calc
      z q =
          Real.exp (-12) *
            (linearPart q * Real.exp (-linearPart q)) *
              Real.exp (-d) := by
        unfold z
        rw [hdecomp]
        rw [show -(linearPart q + 12 + d) =
          -12 + (-linearPart q) + (-d) by ring,
          Real.exp_add, Real.exp_add]
        ring
      _ ≤ Real.exp (-12) * Real.exp (-1) * 1 := by
        gcongr
      _ = Real.exp (-13) := by
        rw [← Real.exp_add]
        norm_num
      _ = z p₀ := z_p₀.symm

private theorem p₁_le_z (q : ℝ × ℝ) :
    z p₁ ≤ z q := by
  let d : ℝ :=
    (q.1 + 1 / 26) ^ 2 +
      (q.1 + 1 / 26) * (q.2 + 3 / 26) +
      (q.2 + 3 / 26) ^ 2
  let v : ℝ := -linearPart q / 26
  have hd : 0 ≤ d :=
    quadratic_form_nonnegative (q.1 + 1 / 26) (q.2 + 3 / 26)
  have hdecomp :
      quadraticPart q = -(51 / 52 : ℝ) + v + d := by
    unfold quadraticPart d v linearPart
    ring
  by_cases hL : 0 ≤ linearPart q
  · have hz : 0 ≤ z q := by
      unfold z
      exact mul_nonneg hL (Real.exp_pos _).le
    have hzneg : z p₁ < 0 := by
      rw [z_p₁]
      nlinarith [Real.exp_pos (-(1 / 52 : ℝ))]
    exact hzneg.le.trans hz
  · have hv : 0 < v := by
      unfold v
      have : linearPart q < 0 := lt_of_not_ge hL
      nlinarith
    have hDexp : Real.exp (-d) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    have hmain :
        v * Real.exp (-v) ≤ Real.exp (-1) :=
      Real.mul_exp_neg_le_exp_neg_one _
    have hmain_nonneg : 0 ≤ v * Real.exp (-v) :=
      mul_nonneg hv.le (Real.exp_pos _).le
    have hproduct :
        (v * Real.exp (-v)) * Real.exp (-d) ≤ Real.exp (-1) := by
      calc
        (v * Real.exp (-v)) * Real.exp (-d) ≤
            (v * Real.exp (-v)) * 1 :=
          mul_le_mul_of_nonneg_left hDexp hmain_nonneg
        _ ≤ Real.exp (-1) := by simpa using hmain
    have hpref : -26 * Real.exp (51 / 52 : ℝ) ≤ 0 := by
      have := Real.exp_pos (51 / 52 : ℝ)
      nlinarith
    calc
      z p₁ =
          (-26 * Real.exp (51 / 52 : ℝ)) * Real.exp (-1) := by
        rw [z_p₁]
        rw [mul_assoc]
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ (-26 * Real.exp (51 / 52 : ℝ)) *
          ((v * Real.exp (-v)) * Real.exp (-d)) :=
        mul_le_mul_of_nonpos_left hproduct hpref
      _ = z q := by
        unfold z v
        rw [hdecomp]
        rw [show -(-(51 / 52 : ℝ) + (-linearPart q / 26) + d) =
          51 / 52 + (-(-linearPart q / 26)) + (-d) by ring,
          Real.exp_add, Real.exp_add]
        ring

private theorem critical_point_eq_p₀_or_p₁ (q : ℝ × ℝ)
    (hq : IsCriticalPoint q) :
    q = p₀ ∨ q = p₁ := by
  have hy := gap3 q hq
  have hpoly := gap4 q hq
  have hfactor : (q.1 - 1) * (26 * q.1 + 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hfactor with hx | hx
  · left
    apply Prod.ext
    · simp [p₀]
      linarith
    · simp [p₀]
      nlinarith
  · right
    apply Prod.ext
    · simp [p₁]
      linarith
    · simp [p₁]
      nlinarith

theorem gap14 :
    IsUniqueGlobalMaximum z p₀ := by
  constructor
  · exact z_le_p₀
  · intro q heq
    have hxLocal : IsLocalMax (fun x : ℝ => z (x, q.2)) q.1 := by
      filter_upwards [] with x
      calc
        z (x, q.2) ≤ z p₀ := z_le_p₀ _
        _ = z q := heq.symm
    have hyLocal : IsLocalMax (fun y : ℝ => z (q.1, y)) q.2 := by
      filter_upwards [] with y
      calc
        z (q.1, y) ≤ z p₀ := z_le_p₀ _
        _ = z q := heq.symm
    have hcrit : IsCriticalPoint q := by
      exact ⟨hxLocal.deriv_eq_zero, hyLocal.deriv_eq_zero⟩
    rcases critical_point_eq_p₀_or_p₁ q hcrit with hq | hq
    · exact hq
    · have hneg : z q < 0 := by
        rw [hq, z_p₁]
        nlinarith [Real.exp_pos (-(1 / 52 : ℝ))]
      have hpos : 0 < z p₀ := by
        rw [z_p₀]
        positivity
      nlinarith

theorem gap15 :
    z p₀ = Real.exp (-13) :=
  z_p₀

theorem gap16 :
    Approx (Real.exp (-13)) (2.26 * 10 ^ (-6 : ℤ))
      (1 / 1000000000 : ℝ) := by
  unfold Approx
  have heq : Real.exp (-13) = Real.exp (-1) ^ 13 := by
    rw [show (-13 : ℝ) = (13 : ℕ) * (-1 : ℝ) by norm_num,
      Real.exp_nat_mul]
  have hlo :
      (0.36787944116 : ℝ) ^ 13 < Real.exp (-13) := by
    rw [heq]
    exact pow_lt_pow_left₀ Real.exp_neg_one_gt_d9 (by norm_num) (by norm_num)
  have hhi :
      Real.exp (-13) < (0.3678794412 : ℝ) ^ 13 := by
    rw [heq]
    exact pow_lt_pow_left₀ Real.exp_neg_one_lt_d9
      (Real.exp_pos _).le (by norm_num)
  rw [abs_lt]
  constructor
  · calc
      -(1 / 1000000000 : ℝ) <
          (0.36787944116 : ℝ) ^ 13 - 2.26 * 10 ^ (-6 : ℤ) := by
        norm_num
      _ < Real.exp (-13) - 2.26 * 10 ^ (-6 : ℤ) := by
        linarith
  · calc
      Real.exp (-13) - 2.26 * 10 ^ (-6 : ℤ) <
          (0.3678794412 : ℝ) ^ 13 - 2.26 * 10 ^ (-6 : ℤ) := by
        linarith
      _ < (1 / 1000000000 : ℝ) := by
        norm_num

theorem gap17 :
    IsUniqueGlobalMinimum z p₁ := by
  constructor
  · exact p₁_le_z
  · intro q heq
    have hxLocal : IsLocalMin (fun x : ℝ => z (x, q.2)) q.1 := by
      filter_upwards [] with x
      calc
        z q = z p₁ := heq
        _ ≤ z (x, q.2) := p₁_le_z _
    have hyLocal : IsLocalMin (fun y : ℝ => z (q.1, y)) q.2 := by
      filter_upwards [] with y
      calc
        z q = z p₁ := heq
        _ ≤ z (q.1, y) := p₁_le_z _
    have hcrit : IsCriticalPoint q := by
      exact ⟨hxLocal.deriv_eq_zero, hyLocal.deriv_eq_zero⟩
    rcases critical_point_eq_p₀_or_p₁ q hcrit with hq | hq
    · have hpos : 0 < z q := by
        rw [hq, z_p₀]
        positivity
      have hneg : z p₁ < 0 := by
        rw [z_p₁]
        nlinarith [Real.exp_pos (-(1 / 52 : ℝ))]
      nlinarith
    · exact hq

theorem gap18 :
    z p₁ = -26 * Real.exp (-(1 / 52 : ℝ)) :=
  z_p₁

theorem gap19 :
    Approx (-26 * Real.exp (-(1 / 52 : ℝ))) (-25.50)
      (1 / 100 : ℝ) := by
  unfold Approx
  have hnorm : ‖-(1 / 52 : ℝ)‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_neg]
    norm_num
  have h := Real.norm_exp_sub_one_sub_id_le hnorm
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hscaled :
      26 * |Real.exp (-(1 / 52 : ℝ)) - 1 - (-(1 / 52 : ℝ))|
        ≤ 26 * |-(1 / 52 : ℝ)| ^ 2 :=
    mul_le_mul_of_nonneg_left h (by norm_num)
  calc
    |-26 * Real.exp (-(1 / 52 : ℝ)) - (-25.50)| =
        26 * |Real.exp (-(1 / 52 : ℝ)) - 1 -
          (-(1 / 52 : ℝ))| := by
      rw [show -26 * Real.exp (-(1 / 52 : ℝ)) - (-25.50) =
        -26 * (Real.exp (-(1 / 52 : ℝ)) - 1 -
          (-(1 / 52 : ℝ))) by ring]
      rw [abs_mul]
      norm_num
    _ ≤ 26 * |-(1 / 52 : ℝ)| ^ 2 := hscaled
    _ < (1 / 100 : ℝ) := by norm_num

end

end ProofGap.Exercise3634
