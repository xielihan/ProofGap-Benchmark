import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

namespace ProofGap.Exercise4413

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ
abbrev Pair := ℝ × ℝ

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def gradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def partialFirst (f : Pair → ℝ) (q : Pair) : ℝ :=
  deriv (fun s => f (s, q.2)) q.1

def partialSecond (f : Pair → ℝ) (q : Pair) : ℝ :=
  deriv (fun t => f (q.1, t)) q.2

def CoordinateDifferentiable (u : Vec3 → ℝ) (p : Vec3) : Prop :=
  DifferentiableAt ℝ (fun x => u (x, p.2.1, p.2.2)) p.1 ∧
    DifferentiableAt ℝ (fun y => u (p.1, y, p.2.2)) p.2.1 ∧
      DifferentiableAt ℝ (fun z => u (p.1, p.2.1, z)) p.2.2

def addVec (a b : Vec3) : Vec3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def scaleVec (s : ℝ) (v : Vec3) : Vec3 :=
  (s * v.1, s * v.2.1, s * v.2.2)

def composeTwo (f : Pair → ℝ) (u v : Vec3 → ℝ) (p : Vec3) : ℝ :=
  f (u p, v p)

private theorem chainRulePairCoordinates
    (f : Pair → ℝ) (a b : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f (a x, b x))
    (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    deriv (fun y => f (a y, b y)) x =
      partialFirst f (a x, b x) * deriv a x +
        partialSecond f (a x, b x) * deriv b x := by
  let L := fderiv ℝ f (a x, b x)
  have hab : HasDerivAt (fun y => (a y, b y))
      (deriv a x, deriv b x) x := by
    exact ha.hasDerivAt.prodMk hb.hasDerivAt
  have hcomp : HasDerivAt (fun y => f (a y, b y))
      (L (deriv a x, deriv b x)) x := by
    exact hf.hasFDerivAt.comp_hasDerivAt x hab
  have hfirstLine : HasDerivAt (fun y : ℝ => (y, b x)) (1, 0) (a x) := by
    exact (hasDerivAt_id (a x)).prodMk (hasDerivAt_const (a x) (b x))
  have hsecondLine : HasDerivAt (fun y : ℝ => (a x, y)) (0, 1) (b x) := by
    exact (hasDerivAt_const (b x) (a x)).prodMk (hasDerivAt_id (b x))
  have hfirst : partialFirst f (a x, b x) = L (1, 0) := by
    unfold partialFirst
    exact (hf.hasFDerivAt.comp_hasDerivAt (a x) hfirstLine).deriv
  have hsecond : partialSecond f (a x, b x) = L (0, 1) := by
    unfold partialSecond
    exact (hf.hasFDerivAt.comp_hasDerivAt (b x) hsecondLine).deriv
  calc
    deriv (fun y => f (a y, b y)) x =
        L (deriv a x, deriv b x) := hcomp.deriv
    _ = L (deriv a x • (1, 0) + deriv b x • (0, 1)) := by
      apply congrArg L
      apply Prod.ext
      · simp
      · simp
    _ = deriv a x • L (1, 0) + deriv b x • L (0, 1) := by
      rw [map_add, map_smul, map_smul]
    _ = partialFirst f (a x, b x) * deriv a x +
        partialSecond f (a x, b x) * deriv b x := by
      rw [← hfirst, ← hsecond]
      simp [smul_eq_mul, mul_comm]

theorem gap1 (f : Pair → ℝ) (u v : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p, v p))
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialX (composeTwo f u v) p =
      partialFirst f (u p, v p) * partialX u p +
        partialSecond f (u p, v p) * partialX v p := by
  unfold partialX composeTwo
  simpa only [Prod.eta] using
    (chainRulePairCoordinates f
      (fun x => u (x, p.2.1, p.2.2))
      (fun x => v (x, p.2.1, p.2.2)) p.1
      (by simpa only [Prod.eta] using hf) hu.1 hv.1)

theorem gap2 (f : Pair → ℝ) (u v : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p, v p))
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialY (composeTwo f u v) p =
      partialFirst f (u p, v p) * partialY u p +
        partialSecond f (u p, v p) * partialY v p := by
  unfold partialY composeTwo
  simpa only [Prod.eta] using
    (chainRulePairCoordinates f
      (fun y => u (p.1, y, p.2.2))
      (fun y => v (p.1, y, p.2.2)) p.2.1
      (by simpa only [Prod.eta] using hf) hu.2.1 hv.2.1)

theorem gap3 (f : Pair → ℝ) (u v : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p, v p))
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    partialZ (composeTwo f u v) p =
      partialFirst f (u p, v p) * partialZ u p +
        partialSecond f (u p, v p) * partialZ v p := by
  unfold partialZ composeTwo
  simpa only [Prod.eta] using
    (chainRulePairCoordinates f
      (fun z => u (p.1, p.2.1, z))
      (fun z => v (p.1, p.2.1, z)) p.2.2
      (by simpa only [Prod.eta] using hf) hu.2.2 hv.2.2)

theorem gap4 (f : Pair → ℝ) (u v : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p, v p))
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    gradient (composeTwo f u v) p =
      (partialFirst f (u p, v p) * partialX u p +
          partialSecond f (u p, v p) * partialX v p,
        partialFirst f (u p, v p) * partialY u p +
          partialSecond f (u p, v p) * partialY v p,
        partialFirst f (u p, v p) * partialZ u p +
          partialSecond f (u p, v p) * partialZ v p) := by
  change
    (partialX (composeTwo f u v) p,
      partialY (composeTwo f u v) p,
      partialZ (composeTwo f u v) p) = _
  rw [gap1 f u v p hf hu hv, gap2 f u v p hf hu hv,
    gap3 f u v p hf hu hv]

theorem gap5 (f : Pair → ℝ) (u v : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p, v p))
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    gradient (composeTwo f u v) p =
      addVec (scaleVec (partialFirst f (u p, v p)) (gradient u p))
        (scaleVec (partialSecond f (u p, v p)) (gradient v p)) := by
  simpa [addVec, scaleVec, gradient] using gap4 f u v p hf hu hv

theorem gap6 (f : Pair → ℝ) (u v : Vec3 → ℝ) (p : Vec3)
    (hf : DifferentiableAt ℝ f (u p, v p))
    (hu : CoordinateDifferentiable u p)
    (hv : CoordinateDifferentiable v p) :
    gradient (composeTwo f u v) p =
      addVec (scaleVec (partialFirst f (u p, v p)) (gradient u p))
        (scaleVec (partialSecond f (u p, v p)) (gradient v p)) := by
  exact gap5 f u v p hf hu hv

end

end ProofGap.Exercise4413
