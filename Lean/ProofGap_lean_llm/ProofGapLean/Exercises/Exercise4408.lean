import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4408

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

def addVec (a b : Vec3) : Vec3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def scaleVec (c : ℝ) (v : Vec3) : Vec3 :=
  (c * v.1, c * v.2.1, c * v.2.2)

def CoordinateDifferentiable (u : Vec3 → ℝ) (p : Vec3) : Prop :=
  DifferentiableAt ℝ (fun x => u (x, p.2.1, p.2.2)) p.1 ∧
    DifferentiableAt ℝ (fun y => u (p.1, y, p.2.2)) p.2.1 ∧
      DifferentiableAt ℝ (fun z => u (p.1, p.2.1, z)) p.2.2

theorem gap1 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialX (fun q => u q + c) p = partialX u p := by
  unfold partialX
  simpa using (hu.1.hasDerivAt.add_const c).deriv

theorem gap2 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialY (fun q => u q + c) p = partialY u p := by
  unfold partialY
  simpa using (hu.2.1.hasDerivAt.add_const c).deriv

theorem gap3 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialZ (fun q => u q + c) p = partialZ u p := by
  unfold partialZ
  simpa using (hu.2.2.hasDerivAt.add_const c).deriv

theorem gap4 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    gradient (fun q => u q + c) p = gradient u p := by
  unfold gradient
  rw [gap1 c u p hu, gap2 c u p hu, gap3 c u p hu]

theorem gap5 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialX (fun q => c * u q) p = c * partialX u p := by
  unfold partialX
  simpa using (hu.1.hasDerivAt.const_mul c).deriv

theorem gap6 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialY (fun q => c * u q) p = c * partialY u p := by
  unfold partialY
  simpa using (hu.2.1.hasDerivAt.const_mul c).deriv

theorem gap7 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    partialZ (fun q => c * u q) p = c * partialZ u p := by
  unfold partialZ
  simpa using (hu.2.2.hasDerivAt.const_mul c).deriv

theorem gap8 (c : ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    gradient (fun q => c * u q) p = scaleVec c (gradient u p) := by
  unfold gradient scaleVec
  rw [gap5 c u p hu, gap6 c u p hu, gap7 c u p hu]

theorem gap9 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialX (fun q => u q + v q) p = partialX u p + partialX v p := by
  unfold partialX
  simpa using (hu.1.hasDerivAt.add hv.1.hasDerivAt).deriv

theorem gap10 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialY (fun q => u q + v q) p = partialY u p + partialY v p := by
  unfold partialY
  simpa using (hu.2.1.hasDerivAt.add hv.2.1.hasDerivAt).deriv

theorem gap11 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialZ (fun q => u q + v q) p = partialZ u p + partialZ v p := by
  unfold partialZ
  simpa using (hu.2.2.hasDerivAt.add hv.2.2.hasDerivAt).deriv

theorem gap12 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    gradient (fun q => u q + v q) p =
      addVec (gradient u p) (gradient v p) := by
  unfold gradient addVec
  rw [gap9 u v p hu hv, gap10 u v p hu hv, gap11 u v p hu hv]

theorem gap13 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialX (fun q => u q * v q) p =
      u p * partialX v p + v p * partialX u p := by
  unfold partialX
  simpa [mul_comm, add_comm] using
    (hu.1.hasDerivAt.mul hv.1.hasDerivAt).deriv

theorem gap14 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialY (fun q => u q * v q) p =
      u p * partialY v p + v p * partialY u p := by
  unfold partialY
  simpa [mul_comm, add_comm] using
    (hu.2.1.hasDerivAt.mul hv.2.1.hasDerivAt).deriv

theorem gap15 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialZ (fun q => u q * v q) p =
      u p * partialZ v p + v p * partialZ u p := by
  unfold partialZ
  simpa [mul_comm, add_comm] using
    (hu.2.2.hasDerivAt.mul hv.2.2.hasDerivAt).deriv

theorem gap16 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    gradient (fun q => u q * v q) p =
      addVec (scaleVec (u p) (gradient v p))
        (scaleVec (v p) (gradient u p)) := by
  unfold gradient addVec scaleVec
  rw [gap13 u v p hu hv, gap14 u v p hu hv, gap15 u v p hu hv]

theorem gap17 (u : Vec3 → ℝ) (p : Vec3)
    (hu : CoordinateDifferentiable u p) :
    gradient (fun q => u q ^ 2) p =
      scaleVec (2 * u p) (gradient u p) := by
  simpa [pow_two, gradient, addVec, scaleVec, two_mul, add_mul] using
    (gap16 u u p hu hu)

theorem gap18 (f : ℝ → ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p))
    (hu : CoordinateDifferentiable u p) :
    partialX (fun q => f (u q)) p =
      deriv f (u p) * partialX u p := by
  unfold partialX
  have hcomp := hf.hasDerivAt.comp p.1 hu.1.hasDerivAt
  simpa [Function.comp_def, mul_comm] using hcomp.deriv

theorem gap19 (f : ℝ → ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p))
    (hu : CoordinateDifferentiable u p) :
    partialY (fun q => f (u q)) p =
      deriv f (u p) * partialY u p := by
  unfold partialY
  have hcomp := hf.hasDerivAt.comp p.2.1 hu.2.1.hasDerivAt
  simpa [Function.comp_def, mul_comm] using hcomp.deriv

theorem gap20 (f : ℝ → ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p))
    (hu : CoordinateDifferentiable u p) :
    partialZ (fun q => f (u q)) p =
      deriv f (u p) * partialZ u p := by
  unfold partialZ
  have hcomp := hf.hasDerivAt.comp p.2.2 hu.2.2.hasDerivAt
  simpa [Function.comp_def, mul_comm] using hcomp.deriv

theorem gap21 (f : ℝ → ℝ) (u : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p))
    (hu : CoordinateDifferentiable u p) :
    gradient (fun q => f (u q)) p =
      scaleVec (deriv f (u p)) (gradient u p) := by
  unfold gradient scaleVec
  rw [gap18 f u p hf hu, gap19 f u p hf hu, gap20 f u p hf hu]

theorem gap22 (c : ℝ) (f : ℝ → ℝ) (u v : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p))
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    gradient (fun q => u q + c) p = gradient u p ∧
      gradient (fun q => c * u q) p = scaleVec c (gradient u p) ∧
      gradient (fun q => u q + v q) p =
        addVec (gradient u p) (gradient v p) ∧
      gradient (fun q => u q * v q) p =
        addVec (scaleVec (v p) (gradient u p))
          (scaleVec (u p) (gradient v p)) ∧
      gradient (fun q => u q ^ 2) p =
        scaleVec (2 * u p) (gradient u p) ∧
      gradient (fun q => f (u q)) p =
        scaleVec (deriv f (u p)) (gradient u p) := by
  constructor
  · exact gap4 c u p hu
  constructor
  · exact gap8 c u p hu
  constructor
  · exact gap12 u v p hu hv
  constructor
  · simpa [mul_comm] using (gap16 v u p hv hu)
  constructor
  · exact gap17 u p hu
  · exact gap21 f u p hf hu

end

end ProofGap.Exercise4408
