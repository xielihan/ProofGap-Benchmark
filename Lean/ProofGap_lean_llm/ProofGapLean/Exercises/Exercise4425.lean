import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise4425

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

def secondX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  partialX (partialX u) p

def secondY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  partialY (partialY u) p

def secondZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  partialZ (partialZ u) p

def laplacian (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  secondX u p + secondY u p + secondZ u p

theorem gap1 (u : Vec3 → ℝ) (p : Vec3) :
    divergence (gradient u) p =
      partialX (partialX u) p +
        partialY (partialY u) p +
          partialZ (partialZ u) p := by
  rfl

theorem gap2 (u : Vec3 → ℝ) (p : Vec3) :
    partialX (partialX u) p +
        partialY (partialY u) p +
          partialZ (partialZ u) p =
      secondX u p + secondY u p + secondZ u p := by
  rfl

theorem gap3 (u : Vec3 → ℝ) (p : Vec3) :
    secondX u p + secondY u p + secondZ u p =
      divergence (gradient u) p := by
  simpa [secondX, secondY, secondZ] using (gap1 u p).symm

theorem gap4 (u : Vec3 → ℝ) (p : Vec3) :
    laplacian u p = divergence (gradient u) p := by
  simpa [laplacian] using gap3 u p

end

end ProofGap.Exercise4425
