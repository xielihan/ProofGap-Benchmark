import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4424_1

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (a : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (a q).1) p +
    partialY (fun q => (a q).2.1) p +
      partialZ (fun q => (a q).2.2) p

def addField (a b : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  ((a p).1 + (b p).1,
    (a p).2.1 + (b p).2.1,
    (a p).2.2 + (b p).2.2)

def FieldDifferentiableAt (a : Vec3 → Vec3) (p : Vec3) : Prop :=
  DifferentiableAt ℝ a p

theorem gap1 (a b : Vec3 → Vec3) (p : Vec3)
    (ha : FieldDifferentiableAt a p) (hb : FieldDifferentiableAt b p) :
    partialX (fun q => (a q).1 + (b q).1) p =
      partialX (fun q => (a q).1) p + partialX (fun q => (b q).1) p := by
  unfold partialX
  unfold FieldDifferentiableAt at ha hb
  have hx :
      HasFDerivAt (fun x : ℝ => x)
        (ContinuousLinearMap.id ℝ ℝ) p.1 :=
    hasFDerivAt_id p.1
  have hy :
      HasFDerivAt (fun _ : ℝ => p.2.1)
        (0 : ℝ →L[ℝ] ℝ) p.1 :=
    hasFDerivAt_const (x := p.1) p.2.1
  have hz :
      HasFDerivAt (fun _ : ℝ => p.2.2)
        (0 : ℝ →L[ℝ] ℝ) p.1 :=
    hasFDerivAt_const (x := p.1) p.2.2
  have hline :
      DifferentiableAt ℝ (fun x : ℝ => (x, p.2.1, p.2.2)) p.1 :=
    (hx.prodMk (hy.prodMk hz)).differentiableAt
  have haX :
      DifferentiableAt ℝ (fun x : ℝ => (a (x, p.2.1, p.2.2)).1) p.1 :=
    (ha.comp p.1 hline).fst
  have hbX :
      DifferentiableAt ℝ (fun x : ℝ => (b (x, p.2.1, p.2.2)).1) p.1 :=
    (hb.comp p.1 hline).fst
  change
    deriv (fun x : ℝ => (a (x, p.2.1, p.2.2)).1 + (b (x, p.2.1, p.2.2)).1) p.1 =
      deriv (fun x : ℝ => (a (x, p.2.1, p.2.2)).1) p.1 +
        deriv (fun x : ℝ => (b (x, p.2.1, p.2.2)).1) p.1
  exact (haX.hasDerivAt.add hbX.hasDerivAt).deriv

theorem gap2 (a b : Vec3 → Vec3) (p : Vec3)
    (ha : FieldDifferentiableAt a p) (hb : FieldDifferentiableAt b p) :
    partialY (fun q => (a q).2.1 + (b q).2.1) p =
      partialY (fun q => (a q).2.1) p + partialY (fun q => (b q).2.1) p := by
  unfold partialY
  unfold FieldDifferentiableAt at ha hb
  have hx :
      HasFDerivAt (fun _ : ℝ => p.1)
        (0 : ℝ →L[ℝ] ℝ) p.2.1 :=
    hasFDerivAt_const (x := p.2.1) p.1
  have hy :
      HasFDerivAt (fun y : ℝ => y)
        (ContinuousLinearMap.id ℝ ℝ) p.2.1 :=
    hasFDerivAt_id p.2.1
  have hz :
      HasFDerivAt (fun _ : ℝ => p.2.2)
        (0 : ℝ →L[ℝ] ℝ) p.2.1 :=
    hasFDerivAt_const (x := p.2.1) p.2.2
  have hline :
      DifferentiableAt ℝ (fun y : ℝ => (p.1, y, p.2.2)) p.2.1 :=
    (hx.prodMk (hy.prodMk hz)).differentiableAt
  have haY :
      DifferentiableAt ℝ (fun y : ℝ => (a (p.1, y, p.2.2)).2.1) p.2.1 :=
    (ha.comp p.2.1 hline).snd.fst
  have hbY :
      DifferentiableAt ℝ (fun y : ℝ => (b (p.1, y, p.2.2)).2.1) p.2.1 :=
    (hb.comp p.2.1 hline).snd.fst
  change
    deriv (fun y : ℝ => (a (p.1, y, p.2.2)).2.1 + (b (p.1, y, p.2.2)).2.1) p.2.1 =
      deriv (fun y : ℝ => (a (p.1, y, p.2.2)).2.1) p.2.1 +
        deriv (fun y : ℝ => (b (p.1, y, p.2.2)).2.1) p.2.1
  exact (haY.hasDerivAt.add hbY.hasDerivAt).deriv

theorem gap3 (a b : Vec3 → Vec3) (p : Vec3)
    (ha : FieldDifferentiableAt a p) (hb : FieldDifferentiableAt b p) :
    partialZ (fun q => (a q).2.2 + (b q).2.2) p =
      partialZ (fun q => (a q).2.2) p + partialZ (fun q => (b q).2.2) p := by
  unfold partialZ
  unfold FieldDifferentiableAt at ha hb
  have hx :
      HasFDerivAt (fun _ : ℝ => p.1)
        (0 : ℝ →L[ℝ] ℝ) p.2.2 :=
    hasFDerivAt_const (x := p.2.2) p.1
  have hy :
      HasFDerivAt (fun _ : ℝ => p.2.1)
        (0 : ℝ →L[ℝ] ℝ) p.2.2 :=
    hasFDerivAt_const (x := p.2.2) p.2.1
  have hz :
      HasFDerivAt (fun z : ℝ => z)
        (ContinuousLinearMap.id ℝ ℝ) p.2.2 :=
    hasFDerivAt_id p.2.2
  have hline :
      DifferentiableAt ℝ (fun z : ℝ => (p.1, p.2.1, z)) p.2.2 :=
    (hx.prodMk (hy.prodMk hz)).differentiableAt
  have haZ :
      DifferentiableAt ℝ (fun z : ℝ => (a (p.1, p.2.1, z)).2.2) p.2.2 :=
    (ha.comp p.2.2 hline).snd.snd
  have hbZ :
      DifferentiableAt ℝ (fun z : ℝ => (b (p.1, p.2.1, z)).2.2) p.2.2 :=
    (hb.comp p.2.2 hline).snd.snd
  change
    deriv (fun z : ℝ => (a (p.1, p.2.1, z)).2.2 + (b (p.1, p.2.1, z)).2.2) p.2.2 =
      deriv (fun z : ℝ => (a (p.1, p.2.1, z)).2.2) p.2.2 +
        deriv (fun z : ℝ => (b (p.1, p.2.1, z)).2.2) p.2.2
  exact (haZ.hasDerivAt.add hbZ.hasDerivAt).deriv

theorem gap4 (a b : Vec3 → Vec3) (p : Vec3)
    (ha : FieldDifferentiableAt a p) (hb : FieldDifferentiableAt b p) :
    divergence (addField a b) p = divergence a p + divergence b p := by
  simp only [divergence, addField]
  rw [gap1 a b p ha hb, gap2 a b p ha hb, gap3 a b p ha hb]
  ring

theorem gap5 (a b : Vec3 → Vec3)
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    ∀ p, divergence (addField a b) p = divergence a p + divergence b p := by
  intro p
  exact gap4 a b p (ha p) (hb p)

end

end ProofGap.Exercise4424_1
