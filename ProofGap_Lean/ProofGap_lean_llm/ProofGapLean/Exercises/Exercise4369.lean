import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4369

noncomputable section

open MeasureTheory
open scoped Interval

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def cross (p q : Vec3) : Vec3 :=
  (p.2.1 * q.2.2 - p.2.2 * q.2.1,
    p.2.2 * q.1 - p.1 * q.2.2,
    p.1 * q.2.1 - p.2.1 * q.1)

def derivative (γ : ℝ → Vec3) (t : ℝ) : Vec3 :=
  (deriv (fun s => (γ s).1) t,
    deriv (fun s => (γ s).2.1) t,
    deriv (fun s => (γ s).2.2) t)

def curl (F : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  (deriv (fun y => (F (p.1, y, p.2.2)).2.2) p.2.1 -
      deriv (fun z => (F (p.1, p.2.1, z)).2.1) p.2.2,
    deriv (fun z => (F (p.1, p.2.1, z)).1) p.2.2 -
      deriv (fun x => (F (x, p.2.1, p.2.2)).2.2) p.1,
    deriv (fun x => (F (x, p.2.1, p.2.2)).2.1) p.1 -
      deriv (fun y => (F (p.1, y, p.2.2)).1) p.2.1)

structure OrientedSurface where
  boundary : ℝ → Vec3
  boundaryStart : ℝ
  boundaryEnd : ℝ
  param : ℝ → ℝ → Vec3
  s₀ : ℝ
  s₁ : ℝ
  t₀ : ℝ
  t₁ : ℝ

def boundaryIntegral
    (S : OrientedSurface) (F : Vec3 → Vec3) : ℝ :=
  ∫ t in S.boundaryStart..S.boundaryEnd,
    dot (F (S.boundary t)) (derivative S.boundary t)

def surfaceAreaVector (S : OrientedSurface) (s t : ℝ) : Vec3 :=
  cross (derivative (fun u => S.param u t) s)
    (derivative (S.param s) t)

def surfaceFlux
    (S : OrientedSurface) (F : Vec3 → Vec3) : ℝ :=
  ∫ s in S.s₀..S.s₁,
    ∫ t in S.t₀..S.t₁,
      dot (F (S.param s t)) (surfaceAreaVector S s t)

def SatisfiesStokes (S : OrientedSurface) : Prop :=
  ∀ F : Vec3 → Vec3, ContDiff ℝ 1 F →
    boundaryIntegral S F = surfaceFlux S (curl F)

def normalSquare (n : Vec3) : ℝ :=
  dot n n

def planarField (n p : Vec3) : Vec3 :=
  (p.2.2 * n.2.1 - p.2.1 * n.2.2,
    p.1 * n.2.2 - p.2.2 * n.1,
    p.2.1 * n.1 - p.1 * n.2.1)

def expandedBoundaryIntegral (S : OrientedSurface) (n : Vec3) : ℝ :=
  boundaryIntegral S (planarField n)

def stokesSurfaceIntegral (S : OrientedSurface) (n : Vec3) : ℝ :=
  surfaceFlux S (fun _p => n)

def orientedArea (S : OrientedSurface) (n : Vec3) : ℝ :=
  stokesSurfaceIntegral S n

private theorem deriv_linear_curl_component
    (a b c x y : ℝ) :
    deriv (fun u : ℝ => u * a - b) x -
        deriv (fun u : ℝ => c - u * a) y = 2 * a := by
  have hleft : HasDerivAt (fun u : ℝ => u * a - b) a x := by
    simpa using (((hasDerivAt_id x).mul_const a).sub_const b)
  have hright : HasDerivAt (fun u : ℝ => c - u * a) (-a) y := by
    simpa using
      ((hasDerivAt_const y c).sub ((hasDerivAt_id y).mul_const a))
  rw [hleft.deriv, hright.deriv]
  ring

theorem gap1 (S : OrientedSurface) (n : Vec3) :
    boundaryIntegral S (planarField n) =
      expandedBoundaryIntegral S n := by
  rfl

theorem gap2 (S : OrientedSurface) (n : Vec3)
    (hStokes : SatisfiesStokes S) :
    boundaryIntegral S (planarField n) =
      2 * stokesSurfaceIntegral S n := by
  have hfield : ContDiff ℝ 1 (planarField n) := by
    unfold planarField
    fun_prop
  rw [hStokes (planarField n) hfield]
  have hcurl :
      curl (planarField n) =
        fun _p => (2 * n.1, 2 * n.2.1, 2 * n.2.2) := by
    funext p
    apply Prod.ext
    · change
        deriv (fun y : ℝ => y * n.1 - p.1 * n.2.1) p.2.1 -
            deriv (fun z : ℝ => p.1 * n.2.2 - z * n.1) p.2.2 =
          2 * n.1
      exact deriv_linear_curl_component
        n.1 (p.1 * n.2.1) (p.1 * n.2.2) p.2.1 p.2.2
    · apply Prod.ext
      · change
          deriv (fun z : ℝ => z * n.2.1 - p.2.1 * n.2.2) p.2.2 -
              deriv (fun x : ℝ => p.2.1 * n.1 - x * n.2.1) p.1 =
            2 * n.2.1
        exact deriv_linear_curl_component
          n.2.1 (p.2.1 * n.2.2) (p.2.1 * n.1) p.2.2 p.1
      · change
          deriv (fun x : ℝ => x * n.2.2 - p.2.2 * n.1) p.1 -
              deriv (fun y : ℝ => p.2.2 * n.2.1 - y * n.2.2) p.2.1 =
            2 * n.2.2
        exact deriv_linear_curl_component
          n.2.2 (p.2.2 * n.1) (p.2.2 * n.2.1) p.1 p.2.1
  rw [hcurl]
  unfold stokesSurfaceIntegral surfaceFlux
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _hs
  change
    (∫ t in S.t₀..S.t₁,
        dot (2 * n.1, 2 * n.2.1, 2 * n.2.2)
          (surfaceAreaVector S s t)) =
      2 * ∫ t in S.t₀..S.t₁,
        dot n (surfaceAreaVector S s t)
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _ht
  unfold dot
  ring

theorem gap3 (n : Vec3) (hn : normalSquare n = 1) :
    n.1 ^ 2 + n.2.1 ^ 2 + n.2.2 ^ 2 = 1 := by
  simpa [normalSquare, dot, pow_two] using hn

theorem gap4 (S : OrientedSurface) (n : Vec3)
    (hn : normalSquare n = 1)
    (hStokes : SatisfiesStokes S) :
    boundaryIntegral S (planarField n) =
      2 * orientedArea S n := by
  simpa [orientedArea] using gap2 S n hStokes

end

end ProofGap.Exercise4369
