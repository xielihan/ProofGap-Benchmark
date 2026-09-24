import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise4302

noncomputable section

open MeasureTheory
open scoped Interval

def P (x y : ℝ) : ℝ := (x + y) ^ 2

def Q (x y : ℝ) : ℝ := -(x - y) ^ 2

def curl (x y : ℝ) : ℝ :=
  deriv (fun t => Q t y) x - deriv (fun t => P x t) y

def linePath (t : ℝ) : ℝ × ℝ :=
  (t, 5 * t - 4)

def parabolaPath (t : ℝ) : ℝ × ℝ :=
  (t, 2 * t ^ 2 - t)

def pathIntegral (γ : ℝ → ℝ × ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..2,
    P (γ t).1 (γ t).2 * deriv (fun s => (γ s).1) t +
      Q (γ t).1 (γ t).2 * deriv (fun s => (γ s).2) t

def I₁ : ℝ := pathIntegral linePath

def I₂ : ℝ := pathIntegral parabolaPath

def enclosedRegion : Set (ℝ × ℝ) :=
  {z |
    z.1 ∈ Set.Icc (1 : ℝ) 2 ∧
      2 * z.1 ^ 2 - z.1 ≤ z.2 ∧
      z.2 ≤ 5 * z.1 - 4}

def boundaryIntegral : ℝ := I₂ - I₁

def areaIntegral : ℝ :=
  ∫ z in enclosedRegion, curl z.1 z.2

def primitive (x : ℝ) : ℝ :=
  2 * x ^ 4 - 8 * x ^ 3 + 8 * x ^ 2

theorem gap1 (x y : ℝ) :
    curl x y =
      -2 * (x - y) - 2 * (x + y) := by
  have hQ :
      HasDerivAt (fun t : ℝ => Q t y) (-2 * (x - y)) x := by
    convert (((hasDerivAt_id x).sub_const y).pow 2).neg using 1 <;>
      simp [Q] <;> ring
  have hP :
      HasDerivAt (fun t : ℝ => P x t) (2 * (x + y)) y := by
    convert (((hasDerivAt_const (x := y) x).add (hasDerivAt_id y)).pow 2) using 1 <;>
      simp [P] <;> ring
  unfold curl
  rw [hQ.deriv, hP.deriv]

theorem gap2 (x y : ℝ) :
    -2 * (x - y) - 2 * (x + y) = -4 * x := by
  ring

theorem gap3 (x y : ℝ) :
    curl x y = -4 * x := by
  rw [gap1, gap2]

theorem gap4 :
    I₂ - I₁ = boundaryIntegral := by
  rfl

theorem gap5 :
    boundaryIntegral =
      ∫ x in (1 : ℝ)..2,
        ∫ y in (2 * x ^ 2 - x)..(5 * x - 4), -4 * x := by
  have hp1 (t : ℝ) :
      deriv (fun s => (parabolaPath s).1) t = 1 := by
    simpa [parabolaPath] using (hasDerivAt_id t).deriv
  have hp2 (t : ℝ) :
      deriv (fun s => (parabolaPath s).2) t = 4 * t - 1 := by
    have h :=
      ((((hasDerivAt_id t).pow 2).const_mul 2).sub
        (hasDerivAt_id t)).deriv
    convert h using 1 <;> simp [parabolaPath] <;> ring
  have hl1 (t : ℝ) :
      deriv (fun s => (linePath s).1) t = 1 := by
    simpa [linePath] using (hasDerivAt_id t).deriv
  have hl2 (t : ℝ) :
      deriv (fun s => (linePath s).2) t = 5 := by
    have h :=
      (((hasDerivAt_id t).const_mul 5).sub_const 4).deriv
    convert h using 1 <;> simp [linePath] <;> ring
  have hi2 :
      IntervalIntegrable
        (fun t : ℝ =>
          P (parabolaPath t).1 (parabolaPath t).2 * 1 +
            Q (parabolaPath t).1 (parabolaPath t).2 * (4 * t - 1))
        volume 1 2 := by
    apply Continuous.intervalIntegrable
    simp only [P, Q, parabolaPath, Prod.fst, Prod.snd]
    fun_prop
  have hi1 :
      IntervalIntegrable
        (fun t : ℝ =>
          P (linePath t).1 (linePath t).2 * 1 +
            Q (linePath t).1 (linePath t).2 * 5)
        volume 1 2 := by
    apply Continuous.intervalIntegrable
    simp only [P, Q, linePath, Prod.fst, Prod.snd]
    fun_prop
  let leftPrimitive : ℝ → ℝ := fun t =>
    64 * t - 56 * t ^ 2 + 16 * t ^ 3 - 6 * t ^ 4 +
      8 * t ^ 5 - (8 / 3 : ℝ) * t ^ 6
  have hleft (x : ℝ) :
      HasDerivAt leftPrimitive
        ((P (parabolaPath x).1 (parabolaPath x).2 * 1 +
            Q (parabolaPath x).1 (parabolaPath x).2 * (4 * x - 1)) -
          (P (linePath x).1 (linePath x).2 * 1 +
            Q (linePath x).1 (linePath x).2 * 5)) x := by
    have h64 := (hasDerivAt_id x).const_mul (64 : ℝ)
    have h56 := ((hasDerivAt_id x).pow 2).const_mul (56 : ℝ)
    have h16 := ((hasDerivAt_id x).pow 3).const_mul (16 : ℝ)
    have h6 := ((hasDerivAt_id x).pow 4).const_mul (6 : ℝ)
    have h8 := ((hasDerivAt_id x).pow 5).const_mul (8 : ℝ)
    have hfrac :=
      ((hasDerivAt_id x).pow 6).const_mul (8 / 3 : ℝ)
    convert (((((h64.sub h56).add h16).sub h6).add h8).sub hfrac) using 1 <;>
      simp [leftPrimitive, P, Q, parabolaPath, linePath] <;> ring
  have hprim (x : ℝ) :
      HasDerivAt primitive (-(4 * x * (-2 * x ^ 2 + 6 * x - 4))) x := by
    unfold primitive
    convert
      (((((hasDerivAt_id x).pow 4).const_mul 2).sub
          (((hasDerivAt_id x).pow 3).const_mul 8)).add
        (((hasDerivAt_id x).pow 2).const_mul 8)) using 1 <;>
      simp only [id_eq] <;> ring
  simp only [boundaryIntegral, I₂, I₁, pathIntegral, hp1, hp2, hl1, hl2]
  calc
    _ = ∫ t in (1 : ℝ)..2,
          (P (parabolaPath t).1 (parabolaPath t).2 * 1 +
              Q (parabolaPath t).1 (parabolaPath t).2 * (4 * t - 1)) -
            (P (linePath t).1 (linePath t).2 * 1 +
              Q (linePath t).1 (linePath t).2 * 5) :=
      (intervalIntegral.integral_sub hi2 hi1).symm
    _ = leftPrimitive 2 - leftPrimitive 1 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x
        intro hx
        exact hleft x
      · exact hi2.sub hi1
    _ = primitive 2 - primitive 1 := by
      norm_num [leftPrimitive, primitive]
    _ = ∫ x in (1 : ℝ)..2,
          ∫ y in (2 * x ^ 2 - x)..(5 * x - 4), -4 * x := by
      symm
      calc
        _ = ∫ x in (1 : ℝ)..2,
              -(4 * x * (-2 * x ^ 2 + 6 * x - 4)) := by
          refine intervalIntegral.integral_congr (fun x _ => ?_)
          rw [intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
        _ = primitive 2 - primitive 1 := by
          apply intervalIntegral.integral_eq_sub_of_hasDerivAt
          · intro x
            intro hx
            exact hprim x
          · apply Continuous.intervalIntegrable
            fun_prop

theorem gap6 :
    I₂ - I₁ =
      ∫ x in (1 : ℝ)..2,
        ∫ y in (2 * x ^ 2 - x)..(5 * x - 4), -4 * x := by
  rw [gap4, gap5]

theorem gap7 :
    I₂ - I₁ =
      -(∫ x in (1 : ℝ)..2,
        4 * x * (-2 * x ^ 2 + 6 * x - 4)) := by
  rw [gap6]
  calc
    _ = ∫ x in (1 : ℝ)..2,
          -(4 * x * (-2 * x ^ 2 + 6 * x - 4)) := by
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      ring
    _ = -(∫ x in (1 : ℝ)..2,
          4 * x * (-2 * x ^ 2 + 6 * x - 4)) :=
      intervalIntegral.integral_neg

theorem gap8 :
    -(∫ x in (1 : ℝ)..2,
        4 * x * (-2 * x ^ 2 + 6 * x - 4)) =
      primitive 2 - primitive 1 := by
  have hprim (x : ℝ) :
      HasDerivAt primitive (-(4 * x * (-2 * x ^ 2 + 6 * x - 4))) x := by
    unfold primitive
    convert
      (((((hasDerivAt_id x).pow 4).const_mul 2).sub
          (((hasDerivAt_id x).pow 3).const_mul 8)).add
        (((hasDerivAt_id x).pow 2).const_mul 8)) using 1 <;>
      simp only [id_eq] <;> ring
  calc
    _ = ∫ x in (1 : ℝ)..2,
          -(4 * x * (-2 * x ^ 2 + 6 * x - 4)) :=
      (intervalIntegral.integral_neg).symm
    _ = primitive 2 - primitive 1 := by
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      · intro x
        intro hx
        exact hprim x
      · apply Continuous.intervalIntegrable
        fun_prop

theorem gap9 :
    primitive 2 - primitive 1 = -2 := by
  norm_num [primitive]

theorem gap10 :
    I₂ - I₁ = -2 := by
  rw [gap7, gap8, gap9]

theorem gap11 :
    I₁ - I₂ = 2 := by
  calc
    I₁ - I₂ = -(I₂ - I₁) := by ring
    _ = -(-2) := by rw [gap10]
    _ = 2 := by norm_num

end

end ProofGap.Exercise4302
