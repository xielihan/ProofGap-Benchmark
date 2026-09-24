import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4424_2

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

def divergence (a : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (a q).1) p +
    partialY (fun q => (a q).2.1) p +
      partialZ (fun q => (a q).2.2) p

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def scalarTimesConstant (u : Vec3 → ℝ) (c : Vec3) (p : Vec3) : Vec3 :=
  (u p * c.1, u p * c.2.1, u p * c.2.2)

def CoordinateDifferentiable (u : Vec3 → ℝ) (p : Vec3) : Prop :=
  DifferentiableAt ℝ (fun x => u (x, p.2.1, p.2.2)) p.1 ∧
    DifferentiableAt ℝ (fun y => u (p.1, y, p.2.2)) p.2.1 ∧
      DifferentiableAt ℝ (fun z => u (p.1, p.2.1, z)) p.2.2

theorem gap1 (u : Vec3 → ℝ) (c p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialX (fun q => u q * c.1) p = c.1 * partialX u p := by
  unfold partialX
  simpa [mul_comm] using (hu.1.hasDerivAt.mul_const c.1).deriv

theorem gap2 (u : Vec3 → ℝ) (c p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialY (fun q => u q * c.2.1) p = c.2.1 * partialY u p := by
  unfold partialY
  simpa [mul_comm] using (hu.2.1.hasDerivAt.mul_const c.2.1).deriv

theorem gap3 (u : Vec3 → ℝ) (c p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialZ (fun q => u q * c.2.2) p = c.2.2 * partialZ u p := by
  unfold partialZ
  simpa [mul_comm] using (hu.2.2.hasDerivAt.mul_const c.2.2).deriv

theorem gap4 (u : Vec3 → ℝ) (c p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    divergence (scalarTimesConstant u c) p = dot c (gradient u p) := by
  change
    partialX (fun q => u q * c.1) p +
          partialY (fun q => u q * c.2.1) p +
        partialZ (fun q => u q * c.2.2) p =
      c.1 * partialX u p +
          c.2.1 * partialY u p +
        c.2.2 * partialZ u p
  rw [gap1 u c p hu, gap2 u c p hu, gap3 u c p hu]

theorem gap5 (u : Vec3 → ℝ) (c : Vec3)
    (hu : ∀ p, CoordinateDifferentiable u p) :
    ∀ p, divergence (scalarTimesConstant u c) p =
      dot c (gradient u p) := by
  intro p
  exact gap4 u c p (hu p)

end

end ProofGap.Exercise4424_2
