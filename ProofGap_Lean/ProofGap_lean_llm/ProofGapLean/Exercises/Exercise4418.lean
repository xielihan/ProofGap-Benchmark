import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4418

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def normalizedGradient (v : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  ((gradient v p).1 / norm3 (gradient v p),
    (gradient v p).2.1 / norm3 (gradient v p),
    (gradient v p).2.2 / norm3 (gradient v p))

def directionalDerivative (u : Vec3 → ℝ) (p l : Vec3) : ℝ :=
  dot (gradient u p) l

def GradientsOrthogonal (u v : Vec3 → ℝ) (p : Vec3) : Prop :=
  dot (gradient u p) (gradient v p) = 0

theorem gap1 (u v : Vec3 → ℝ) (p : Vec3)
    (hv : gradient v p ≠ (0, 0, 0)) :
    directionalDerivative u p (normalizedGradient v p) =
      dot (gradient u p) (normalizedGradient v p) := by
  rfl

theorem gap2 (u v : Vec3 → ℝ) (p : Vec3)
    (hv : gradient v p ≠ (0, 0, 0)) :
    dot (gradient u p) (normalizedGradient v p) =
      dot (gradient u p) (gradient v p) / norm3 (gradient v p) := by
  unfold normalizedGradient dot
  ring

theorem gap3 (u v : Vec3 → ℝ) (p : Vec3)
    (hv : gradient v p ≠ (0, 0, 0)) :
    directionalDerivative u p (normalizedGradient v p) =
      dot (gradient u p) (gradient v p) / norm3 (gradient v p) := by
  calc
    directionalDerivative u p (normalizedGradient v p) =
        dot (gradient u p) (normalizedGradient v p) := gap1 u v p hv
    _ = dot (gradient u p) (gradient v p) / norm3 (gradient v p) :=
      gap2 u v p hv

theorem gap4 (u v : Vec3 → ℝ) (p : Vec3)
    (hv : gradient v p ≠ (0, 0, 0))
    (hOrthogonal : GradientsOrthogonal u v p) :
    directionalDerivative u p (normalizedGradient v p) = 0 := by
  have hdot : dot (gradient u p) (gradient v p) = 0 := by
    exact hOrthogonal
  rw [gap3 u v p hv, hdot]
  simp

theorem gap5 (u v : Vec3 → ℝ) (p : Vec3)
    (hv : gradient v p ≠ (0, 0, 0))
    (hOrthogonal : dot (gradient u p) (gradient v p) = 0) :
    directionalDerivative u p (normalizedGradient v p) = 0 := by
  rw [gap3 u v p hv, hOrthogonal]
  simp

theorem gap6 (u v : Vec3 → ℝ) (p : Vec3)
    (hOrthogonal : GradientsOrthogonal u v p) :
    dot (gradient u p) (gradient v p) = 0 := by
  exact hOrthogonal

end

end ProofGap.Exercise4418
