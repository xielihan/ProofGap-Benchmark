import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4424_3

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

def scalarFieldMul (u : Vec3 → ℝ) (a : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  (u p * (a p).1, u p * (a p).2.1, u p * (a p).2.2)

def CoordinateDifferentiable (u : Vec3 → ℝ) (p : Vec3) : Prop :=
  DifferentiableAt ℝ (fun x => u (x, p.2.1, p.2.2)) p.1 ∧
    DifferentiableAt ℝ (fun y => u (p.1, y, p.2.2)) p.2.1 ∧
      DifferentiableAt ℝ (fun z => u (p.1, p.2.1, z)) p.2.2

def FieldDifferentiableAt (a : Vec3 → Vec3) (p : Vec3) : Prop :=
  DifferentiableAt ℝ a p

theorem gap1 (u : Vec3 → ℝ) (a : Vec3 → Vec3) (p : Vec3)
    (hu : CoordinateDifferentiable u p) (ha : FieldDifferentiableAt a p) :
    partialX (fun q => u q * (a q).1) p =
      u p * partialX (fun q => (a q).1) p + (a p).1 * partialX u p := by
  have hcurve :
      DifferentiableAt ℝ (fun x : ℝ => (x, p.2.1, p.2.2)) p.1 :=
    differentiableAt_id.prodMk
      ((differentiableAt_const (c := p.2.1)).prodMk
        (differentiableAt_const (c := p.2.2)))
  have ha' : DifferentiableAt ℝ a p := ha
  have hax :
      DifferentiableAt ℝ (fun x : ℝ => (a (x, p.2.1, p.2.2)).1) p.1 :=
    (ha'.comp p.1 hcurve).fst
  have hux :
      DifferentiableAt ℝ (fun x : ℝ => u (x, p.2.1, p.2.2)) p.1 :=
    hu.1
  have hprod := hux.hasDerivAt.mul hax.hasDerivAt
  simpa [partialX, mul_comm, add_comm] using hprod.deriv

theorem gap2 (u : Vec3 → ℝ) (a : Vec3 → Vec3) (p : Vec3)
    (hu : CoordinateDifferentiable u p) (ha : FieldDifferentiableAt a p) :
    partialY (fun q => u q * (a q).2.1) p =
      u p * partialY (fun q => (a q).2.1) p +
        (a p).2.1 * partialY u p := by
  have hcurve :
      DifferentiableAt ℝ (fun y : ℝ => (p.1, y, p.2.2)) p.2.1 :=
    (differentiableAt_const (c := p.1)).prodMk
      (differentiableAt_id.prodMk
        (differentiableAt_const (c := p.2.2)))
  have ha' : DifferentiableAt ℝ a p := ha
  have hay :
      DifferentiableAt ℝ (fun y : ℝ => (a (p.1, y, p.2.2)).2.1) p.2.1 :=
    (ha'.comp p.2.1 hcurve).snd.fst
  have huy :
      DifferentiableAt ℝ (fun y : ℝ => u (p.1, y, p.2.2)) p.2.1 :=
    hu.2.1
  have hprod := huy.hasDerivAt.mul hay.hasDerivAt
  simpa [partialY, mul_comm, add_comm] using hprod.deriv

theorem gap3 (u : Vec3 → ℝ) (a : Vec3 → Vec3) (p : Vec3)
    (hu : CoordinateDifferentiable u p) (ha : FieldDifferentiableAt a p) :
    partialZ (fun q => u q * (a q).2.2) p =
      u p * partialZ (fun q => (a q).2.2) p +
        (a p).2.2 * partialZ u p := by
  have hcurve :
      DifferentiableAt ℝ (fun z : ℝ => (p.1, p.2.1, z)) p.2.2 :=
    (differentiableAt_const (c := p.1)).prodMk
      ((differentiableAt_const (c := p.2.1)).prodMk
        differentiableAt_id)
  have ha' : DifferentiableAt ℝ a p := ha
  have haz :
      DifferentiableAt ℝ (fun z : ℝ => (a (p.1, p.2.1, z)).2.2) p.2.2 :=
    (ha'.comp p.2.2 hcurve).snd.snd
  have huz :
      DifferentiableAt ℝ (fun z : ℝ => u (p.1, p.2.1, z)) p.2.2 :=
    hu.2.2
  have hprod := huz.hasDerivAt.mul haz.hasDerivAt
  simpa [partialZ, mul_comm, add_comm] using hprod.deriv

theorem gap4 (u : Vec3 → ℝ) (a : Vec3 → Vec3) (p : Vec3)
    (hu : CoordinateDifferentiable u p) (ha : FieldDifferentiableAt a p) :
    divergence (scalarFieldMul u a) p =
      u p * divergence a p + dot (a p) (gradient u p) := by
  simp only [divergence, scalarFieldMul, dot, gradient]
  rw [gap1 u a p hu ha, gap2 u a p hu ha, gap3 u a p hu ha]
  ring

theorem gap5 (u : Vec3 → ℝ) (a : Vec3 → Vec3)
    (hu : ∀ p, CoordinateDifferentiable u p)
    (ha : Differentiable ℝ a) :
    ∀ p, divergence (scalarFieldMul u a) p =
      u p * divergence a p + dot (a p) (gradient u p) := by
  intro p
  exact gap4 u a p (hu p) (ha p)

end

end ProofGap.Exercise4424_3
