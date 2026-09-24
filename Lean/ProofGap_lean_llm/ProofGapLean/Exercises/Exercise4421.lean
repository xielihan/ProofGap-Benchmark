import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

namespace ProofGap.Exercise4421

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

structure Frame where
  e₁ : Vec3
  e₂ : Vec3
  e₃ : Vec3

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def IsOrthonormal (F : Frame) : Prop :=
  dot F.e₁ F.e₁ = 1 ∧ dot F.e₂ F.e₂ = 1 ∧ dot F.e₃ F.e₃ = 1 ∧
    dot F.e₁ F.e₂ = 0 ∧ dot F.e₁ F.e₃ = 0 ∧ dot F.e₂ F.e₃ = 0

def subVec (a b : Vec3) : Vec3 :=
  (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

def scaleVec (s : ℝ) (v : Vec3) : Vec3 :=
  (s * v.1, s * v.2.1, s * v.2.2)

def addVec (a b : Vec3) : Vec3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def rotatedCoordinates (F : Frame) (origin p : Vec3) : Vec3 :=
  (dot (subVec p origin) F.e₁,
    dot (subVec p origin) F.e₂,
    dot (subVec p origin) F.e₃)

def fromComponents (F : Frame) (v : Vec3) : Vec3 :=
  addVec (scaleVec v.1 F.e₁)
    (addVec (scaleVec v.2.1 F.e₂) (scaleVec v.2.2 F.e₃))

def transformedField (F : Frame) (origin : Vec3)
    (A' : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  fromComponents F (A' (rotatedCoordinates F origin p))

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (A : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (A q).1) p +
    partialY (fun q => (A q).2.1) p +
      partialZ (fun q => (A q).2.2) p

def DifferentiableFieldAt (A : Vec3 → Vec3) (p : Vec3) : Prop :=
  DifferentiableAt ℝ A p

def diagonalXExpansion (F : Frame) (A' : Vec3 → Vec3) (q : Vec3) : ℝ :=
  (F.e₁.1 * partialX (fun s => (A' s).1) q +
      F.e₂.1 * partialX (fun s => (A' s).2.1) q +
      F.e₃.1 * partialX (fun s => (A' s).2.2) q) * F.e₁.1 +
    (F.e₁.1 * partialY (fun s => (A' s).1) q +
      F.e₂.1 * partialY (fun s => (A' s).2.1) q +
      F.e₃.1 * partialY (fun s => (A' s).2.2) q) * F.e₂.1 +
    (F.e₁.1 * partialZ (fun s => (A' s).1) q +
      F.e₂.1 * partialZ (fun s => (A' s).2.1) q +
      F.e₃.1 * partialZ (fun s => (A' s).2.2) q) * F.e₃.1

def diagonalYExpansion (F : Frame) (A' : Vec3 → Vec3) (q : Vec3) : ℝ :=
  (F.e₁.2.1 * partialX (fun s => (A' s).1) q +
      F.e₂.2.1 * partialX (fun s => (A' s).2.1) q +
      F.e₃.2.1 * partialX (fun s => (A' s).2.2) q) * F.e₁.2.1 +
    (F.e₁.2.1 * partialY (fun s => (A' s).1) q +
      F.e₂.2.1 * partialY (fun s => (A' s).2.1) q +
      F.e₃.2.1 * partialY (fun s => (A' s).2.2) q) * F.e₂.2.1 +
    (F.e₁.2.1 * partialZ (fun s => (A' s).1) q +
      F.e₂.2.1 * partialZ (fun s => (A' s).2.1) q +
      F.e₃.2.1 * partialZ (fun s => (A' s).2.2) q) * F.e₃.2.1

def diagonalZExpansion (F : Frame) (A' : Vec3 → Vec3) (q : Vec3) : ℝ :=
  (F.e₁.2.2 * partialX (fun s => (A' s).1) q +
      F.e₂.2.2 * partialX (fun s => (A' s).2.1) q +
      F.e₃.2.2 * partialX (fun s => (A' s).2.2) q) * F.e₁.2.2 +
    (F.e₁.2.2 * partialY (fun s => (A' s).1) q +
      F.e₂.2.2 * partialY (fun s => (A' s).2.1) q +
      F.e₃.2.2 * partialY (fun s => (A' s).2.2) q) * F.e₂.2.2 +
    (F.e₁.2.2 * partialZ (fun s => (A' s).1) q +
      F.e₂.2.2 * partialZ (fun s => (A' s).2.1) q +
      F.e₃.2.2 * partialZ (fun s => (A' s).2.2) q) * F.e₃.2.2

private theorem hasFDerivAt_smul_add_vec3 (d c : Vec3) (x : ℝ) :
    HasFDerivAt (fun t : ℝ => t • d + c)
      (ContinuousLinearMap.toSpanSingleton ℝ d) x := by
  simpa using
    (ContinuousLinearMap.toSpanSingleton ℝ d).hasFDerivAt.add_const c

private theorem partialX_eq_fderiv (u : Vec3 → ℝ) (q : Vec3)
    (hu : DifferentiableAt ℝ u q) :
    partialX u q = fderiv ℝ u q (1, 0, 0) := by
  unfold partialX
  have hpath :
      (fun x : ℝ => (x, q.2.1, q.2.2)) =
        (fun x : ℝ => x • ((1, 0, 0) : Vec3) +
          ((0, q.2.1, q.2.2) : Vec3)) := by
    funext x
    apply Prod.ext
    · simp [smul_eq_mul]
    · apply Prod.ext
      · simp [smul_eq_mul]
      · simp [smul_eq_mul]
  have hp : HasFDerivAt (fun x : ℝ => (x, q.2.1, q.2.2))
      (ContinuousLinearMap.toSpanSingleton ℝ ((1, 0, 0) : Vec3)) q.1 := by
    rw [hpath]
    exact hasFDerivAt_smul_add_vec3 ((1, 0, 0) : Vec3)
      ((0, q.2.1, q.2.2) : Vec3) q.1
  simpa using (hu.hasFDerivAt.comp q.1 hp).hasDerivAt.deriv

private theorem partialY_eq_fderiv (u : Vec3 → ℝ) (q : Vec3)
    (hu : DifferentiableAt ℝ u q) :
    partialY u q = fderiv ℝ u q (0, 1, 0) := by
  unfold partialY
  have hpath :
      (fun y : ℝ => (q.1, y, q.2.2)) =
        (fun y : ℝ => y • ((0, 1, 0) : Vec3) +
          ((q.1, 0, q.2.2) : Vec3)) := by
    funext y
    apply Prod.ext
    · simp [smul_eq_mul]
    · apply Prod.ext
      · simp [smul_eq_mul]
      · simp [smul_eq_mul]
  have hp : HasFDerivAt (fun y : ℝ => (q.1, y, q.2.2))
      (ContinuousLinearMap.toSpanSingleton ℝ ((0, 1, 0) : Vec3)) q.2.1 := by
    rw [hpath]
    exact hasFDerivAt_smul_add_vec3 ((0, 1, 0) : Vec3)
      ((q.1, 0, q.2.2) : Vec3) q.2.1
  simpa using (hu.hasFDerivAt.comp q.2.1 hp).hasDerivAt.deriv

private theorem partialZ_eq_fderiv (u : Vec3 → ℝ) (q : Vec3)
    (hu : DifferentiableAt ℝ u q) :
    partialZ u q = fderiv ℝ u q (0, 0, 1) := by
  unfold partialZ
  have hpath :
      (fun z : ℝ => (q.1, q.2.1, z)) =
        (fun z : ℝ => z • ((0, 0, 1) : Vec3) +
          ((q.1, q.2.1, 0) : Vec3)) := by
    funext z
    apply Prod.ext
    · simp [smul_eq_mul]
    · apply Prod.ext
      · simp [smul_eq_mul]
      · simp [smul_eq_mul]
  have hp : HasFDerivAt (fun z : ℝ => (q.1, q.2.1, z))
      (ContinuousLinearMap.toSpanSingleton ℝ ((0, 0, 1) : Vec3)) q.2.2 := by
    rw [hpath]
    exact hasFDerivAt_smul_add_vec3 ((0, 0, 1) : Vec3)
      ((q.1, q.2.1, 0) : Vec3) q.2.2
  simpa using (hu.hasFDerivAt.comp q.2.2 hp).hasDerivAt.deriv

private theorem fderiv_eq_coordinate_partials (u : Vec3 → ℝ) (q d : Vec3)
    (hu : DifferentiableAt ℝ u q) :
    fderiv ℝ u q d =
      d.1 * partialX u q + d.2.1 * partialY u q + d.2.2 * partialZ u q := by
  rw [partialX_eq_fderiv u q hu, partialY_eq_fderiv u q hu,
    partialZ_eq_fderiv u q hu]
  let L := fderiv ℝ u q
  change L d = d.1 * L (1, 0, 0) + d.2.1 * L (0, 1, 0) +
    d.2.2 * L (0, 0, 1)
  have hd : d = d.1 • (1, 0, 0) + d.2.1 • (0, 1, 0) +
      d.2.2 • (0, 0, 1) := by
    ext <;> simp
  calc
    L d = L (d.1 • (1, 0, 0) + d.2.1 • (0, 1, 0) +
        d.2.2 • (0, 0, 1)) := congrArg L hd
    _ = d.1 * L (1, 0, 0) + d.2.1 * L (0, 1, 0) +
        d.2.2 * L (0, 0, 1) := by
      simp only [map_add, map_smul, smul_eq_mul]

private theorem hasDerivAt_comp_vec3 (u : Vec3 → ℝ) (g : ℝ → Vec3)
    (x : ℝ) {g' : ℝ →L[ℝ] Vec3} (hu : DifferentiableAt ℝ u (g x))
    (hg : HasFDerivAt g g' x) :
    HasDerivAt (fun t => u (g t))
      ((g' 1).1 * partialX u (g x) +
        (g' 1).2.1 * partialY u (g x) +
        (g' 1).2.2 * partialZ u (g x)) x := by
  simpa [fderiv_eq_coordinate_partials u (g x) (g' 1) hu] using
    (hu.hasFDerivAt.comp x hg).hasDerivAt

theorem gap1 (F : Frame) (origin p : Vec3) :
    (rotatedCoordinates F origin p).1 = dot (subVec p origin) F.e₁ := by
  rfl

theorem gap2 (F : Frame) (origin p : Vec3) :
    (rotatedCoordinates F origin p).2.1 = dot (subVec p origin) F.e₂ := by
  rfl

theorem gap3 (F : Frame) (origin p : Vec3) :
    (rotatedCoordinates F origin p).2.2 = dot (subVec p origin) F.e₃ := by
  rfl

theorem gap4 (F : Frame) (v : Vec3) :
    fromComponents F v =
      addVec (scaleVec v.1 F.e₁)
        (addVec (scaleVec v.2.1 F.e₂) (scaleVec v.2.2 F.e₃)) := by
  rfl

theorem gap5 (F : Frame) (v : Vec3) :
    (fromComponents F v).1 =
      v.1 * F.e₁.1 + v.2.1 * F.e₂.1 + v.2.2 * F.e₃.1 := by
  simp [fromComponents, addVec, scaleVec, add_assoc]

theorem gap6 (F : Frame) (v : Vec3) :
    (fromComponents F v).2.1 =
      v.1 * F.e₁.2.1 + v.2.1 * F.e₂.2.1 + v.2.2 * F.e₃.2.1 := by
  simp [fromComponents, addVec, scaleVec, add_assoc]

theorem gap7 (F : Frame) (v : Vec3) :
    (fromComponents F v).2.2 =
      v.1 * F.e₁.2.2 + v.2.1 * F.e₂.2.2 + v.2.2 * F.e₃.2.2 := by
  simp [fromComponents, addVec, scaleVec, add_assoc]

theorem gap8 (F : Frame) (origin p : Vec3) (A' : Vec3 → Vec3)
    (hDiff : DifferentiableFieldAt A' (rotatedCoordinates F origin p)) :
    partialX (fun s => (transformedField F origin A' s).1) p =
      diagonalXExpansion F A' (rotatedCoordinates F origin p) := by
  let q := rotatedCoordinates F origin p
  let d : Vec3 := (F.e₁.1, F.e₂.1, F.e₃.1)
  let c : Vec3 := rotatedCoordinates F origin (0, p.2.1, p.2.2)
  have hpath :
      (fun x : ℝ => rotatedCoordinates F origin (x, p.2.1, p.2.2)) =
        (fun x : ℝ => x • d + c) := by
    funext x
    ext <;>
      simp [d, c, rotatedCoordinates, dot, subVec, smul_eq_mul] <;>
      ring
  have hq : HasFDerivAt
      (fun x : ℝ => rotatedCoordinates F origin (x, p.2.1, p.2.2))
      (ContinuousLinearMap.toSpanSingleton ℝ d) p.1 := by
    rw [hpath]
    exact hasFDerivAt_smul_add_vec3 d c p.1
  have hA1 : HasDerivAt
      (fun x : ℝ => (A' (rotatedCoordinates F origin (x, p.2.1, p.2.2))).1)
      (F.e₁.1 * partialX (fun s => (A' s).1) q +
        F.e₂.1 * partialY (fun s => (A' s).1) q +
        F.e₃.1 * partialZ (fun s => (A' s).1) q) p.1 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).1)
        (g := fun x : ℝ => rotatedCoordinates F origin (x, p.2.1, p.2.2))
        (x := p.1)
        (hu := by simpa [q] using hDiff.fst)
        (hg := hq))
  have hA2 : HasDerivAt
      (fun x : ℝ => (A' (rotatedCoordinates F origin (x, p.2.1, p.2.2))).2.1)
      (F.e₁.1 * partialX (fun s => (A' s).2.1) q +
        F.e₂.1 * partialY (fun s => (A' s).2.1) q +
        F.e₃.1 * partialZ (fun s => (A' s).2.1) q) p.1 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).2.1)
        (g := fun x : ℝ => rotatedCoordinates F origin (x, p.2.1, p.2.2))
        (x := p.1)
        (hu := by simpa [q] using hDiff.snd.fst)
        (hg := hq))
  have hA3 : HasDerivAt
      (fun x : ℝ => (A' (rotatedCoordinates F origin (x, p.2.1, p.2.2))).2.2)
      (F.e₁.1 * partialX (fun s => (A' s).2.2) q +
        F.e₂.1 * partialY (fun s => (A' s).2.2) q +
        F.e₃.1 * partialZ (fun s => (A' s).2.2) q) p.1 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).2.2)
        (g := fun x : ℝ => rotatedCoordinates F origin (x, p.2.1, p.2.2))
        (x := p.1)
        (hu := by simpa [q] using hDiff.snd.snd)
        (hg := hq))
  have hout := (hA1.mul_const F.e₁.1).add
    ((hA2.mul_const F.e₂.1).add (hA3.mul_const F.e₃.1))
  have hd : partialX (fun s => (transformedField F origin A' s).1) p =
      (F.e₁.1 * partialX (fun s => (A' s).1) q +
        F.e₂.1 * partialY (fun s => (A' s).1) q +
        F.e₃.1 * partialZ (fun s => (A' s).1) q) * F.e₁.1 +
      ((F.e₁.1 * partialX (fun s => (A' s).2.1) q +
        F.e₂.1 * partialY (fun s => (A' s).2.1) q +
        F.e₃.1 * partialZ (fun s => (A' s).2.1) q) * F.e₂.1 +
      (F.e₁.1 * partialX (fun s => (A' s).2.2) q +
        F.e₂.1 * partialY (fun s => (A' s).2.2) q +
        F.e₃.1 * partialZ (fun s => (A' s).2.2) q) * F.e₃.1) := by
    simpa [partialX, transformedField, fromComponents, addVec, scaleVec, q]
      using hout.deriv
  rw [hd]
  unfold diagonalXExpansion
  dsimp [q]
  ring

theorem gap9 (F : Frame) (origin p : Vec3) (A' : Vec3 → Vec3)
    (hDiff : DifferentiableFieldAt A' (rotatedCoordinates F origin p)) :
    partialY (fun s => (transformedField F origin A' s).2.1) p =
      diagonalYExpansion F A' (rotatedCoordinates F origin p) := by
  let q := rotatedCoordinates F origin p
  let d : Vec3 := (F.e₁.2.1, F.e₂.2.1, F.e₃.2.1)
  let c : Vec3 := rotatedCoordinates F origin (p.1, 0, p.2.2)
  have hpath :
      (fun y : ℝ => rotatedCoordinates F origin (p.1, y, p.2.2)) =
        (fun y : ℝ => y • d + c) := by
    funext y
    ext <;>
      simp [d, c, rotatedCoordinates, dot, subVec, smul_eq_mul] <;>
      ring
  have hq : HasFDerivAt
      (fun y : ℝ => rotatedCoordinates F origin (p.1, y, p.2.2))
      (ContinuousLinearMap.toSpanSingleton ℝ d) p.2.1 := by
    rw [hpath]
    exact hasFDerivAt_smul_add_vec3 d c p.2.1
  have hA1 : HasDerivAt
      (fun y : ℝ => (A' (rotatedCoordinates F origin (p.1, y, p.2.2))).1)
      (F.e₁.2.1 * partialX (fun s => (A' s).1) q +
        F.e₂.2.1 * partialY (fun s => (A' s).1) q +
        F.e₃.2.1 * partialZ (fun s => (A' s).1) q) p.2.1 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).1)
        (g := fun y : ℝ => rotatedCoordinates F origin (p.1, y, p.2.2))
        (x := p.2.1)
        (hu := by simpa [q] using hDiff.fst)
        (hg := hq))
  have hA2 : HasDerivAt
      (fun y : ℝ => (A' (rotatedCoordinates F origin (p.1, y, p.2.2))).2.1)
      (F.e₁.2.1 * partialX (fun s => (A' s).2.1) q +
        F.e₂.2.1 * partialY (fun s => (A' s).2.1) q +
        F.e₃.2.1 * partialZ (fun s => (A' s).2.1) q) p.2.1 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).2.1)
        (g := fun y : ℝ => rotatedCoordinates F origin (p.1, y, p.2.2))
        (x := p.2.1)
        (hu := by simpa [q] using hDiff.snd.fst)
        (hg := hq))
  have hA3 : HasDerivAt
      (fun y : ℝ => (A' (rotatedCoordinates F origin (p.1, y, p.2.2))).2.2)
      (F.e₁.2.1 * partialX (fun s => (A' s).2.2) q +
        F.e₂.2.1 * partialY (fun s => (A' s).2.2) q +
        F.e₃.2.1 * partialZ (fun s => (A' s).2.2) q) p.2.1 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).2.2)
        (g := fun y : ℝ => rotatedCoordinates F origin (p.1, y, p.2.2))
        (x := p.2.1)
        (hu := by simpa [q] using hDiff.snd.snd)
        (hg := hq))
  have hout := (hA1.mul_const F.e₁.2.1).add
    ((hA2.mul_const F.e₂.2.1).add (hA3.mul_const F.e₃.2.1))
  have hd : partialY (fun s => (transformedField F origin A' s).2.1) p =
      (F.e₁.2.1 * partialX (fun s => (A' s).1) q +
        F.e₂.2.1 * partialY (fun s => (A' s).1) q +
        F.e₃.2.1 * partialZ (fun s => (A' s).1) q) * F.e₁.2.1 +
      ((F.e₁.2.1 * partialX (fun s => (A' s).2.1) q +
        F.e₂.2.1 * partialY (fun s => (A' s).2.1) q +
        F.e₃.2.1 * partialZ (fun s => (A' s).2.1) q) * F.e₂.2.1 +
      (F.e₁.2.1 * partialX (fun s => (A' s).2.2) q +
        F.e₂.2.1 * partialY (fun s => (A' s).2.2) q +
        F.e₃.2.1 * partialZ (fun s => (A' s).2.2) q) * F.e₃.2.1) := by
    simpa [partialY, transformedField, fromComponents, addVec, scaleVec, q]
      using hout.deriv
  rw [hd]
  unfold diagonalYExpansion
  dsimp [q]
  ring

theorem gap10 (F : Frame) (origin p : Vec3) (A' : Vec3 → Vec3)
    (hDiff : DifferentiableFieldAt A' (rotatedCoordinates F origin p)) :
    partialZ (fun s => (transformedField F origin A' s).2.2) p =
      diagonalZExpansion F A' (rotatedCoordinates F origin p) := by
  let q := rotatedCoordinates F origin p
  let d : Vec3 := (F.e₁.2.2, F.e₂.2.2, F.e₃.2.2)
  let c : Vec3 := rotatedCoordinates F origin (p.1, p.2.1, 0)
  have hpath :
      (fun z : ℝ => rotatedCoordinates F origin (p.1, p.2.1, z)) =
        (fun z : ℝ => z • d + c) := by
    funext z
    ext <;>
      simp [d, c, rotatedCoordinates, dot, subVec, smul_eq_mul] <;>
      ring
  have hq : HasFDerivAt
      (fun z : ℝ => rotatedCoordinates F origin (p.1, p.2.1, z))
      (ContinuousLinearMap.toSpanSingleton ℝ d) p.2.2 := by
    rw [hpath]
    exact hasFDerivAt_smul_add_vec3 d c p.2.2
  have hA1 : HasDerivAt
      (fun z : ℝ => (A' (rotatedCoordinates F origin (p.1, p.2.1, z))).1)
      (F.e₁.2.2 * partialX (fun s => (A' s).1) q +
        F.e₂.2.2 * partialY (fun s => (A' s).1) q +
        F.e₃.2.2 * partialZ (fun s => (A' s).1) q) p.2.2 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).1)
        (g := fun z : ℝ => rotatedCoordinates F origin (p.1, p.2.1, z))
        (x := p.2.2)
        (hu := by simpa [q] using hDiff.fst)
        (hg := hq))
  have hA2 : HasDerivAt
      (fun z : ℝ => (A' (rotatedCoordinates F origin (p.1, p.2.1, z))).2.1)
      (F.e₁.2.2 * partialX (fun s => (A' s).2.1) q +
        F.e₂.2.2 * partialY (fun s => (A' s).2.1) q +
        F.e₃.2.2 * partialZ (fun s => (A' s).2.1) q) p.2.2 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).2.1)
        (g := fun z : ℝ => rotatedCoordinates F origin (p.1, p.2.1, z))
        (x := p.2.2)
        (hu := by simpa [q] using hDiff.snd.fst)
        (hg := hq))
  have hA3 : HasDerivAt
      (fun z : ℝ => (A' (rotatedCoordinates F origin (p.1, p.2.1, z))).2.2)
      (F.e₁.2.2 * partialX (fun s => (A' s).2.2) q +
        F.e₂.2.2 * partialY (fun s => (A' s).2.2) q +
        F.e₃.2.2 * partialZ (fun s => (A' s).2.2) q) p.2.2 := by
    simpa [q, d, smul_eq_mul] using
      (hasDerivAt_comp_vec3
        (u := fun s => (A' s).2.2)
        (g := fun z : ℝ => rotatedCoordinates F origin (p.1, p.2.1, z))
        (x := p.2.2)
        (hu := by simpa [q] using hDiff.snd.snd)
        (hg := hq))
  have hout := (hA1.mul_const F.e₁.2.2).add
    ((hA2.mul_const F.e₂.2.2).add (hA3.mul_const F.e₃.2.2))
  have hd : partialZ (fun s => (transformedField F origin A' s).2.2) p =
      (F.e₁.2.2 * partialX (fun s => (A' s).1) q +
        F.e₂.2.2 * partialY (fun s => (A' s).1) q +
        F.e₃.2.2 * partialZ (fun s => (A' s).1) q) * F.e₁.2.2 +
      ((F.e₁.2.2 * partialX (fun s => (A' s).2.1) q +
        F.e₂.2.2 * partialY (fun s => (A' s).2.1) q +
        F.e₃.2.2 * partialZ (fun s => (A' s).2.1) q) * F.e₂.2.2 +
      (F.e₁.2.2 * partialX (fun s => (A' s).2.2) q +
        F.e₂.2.2 * partialY (fun s => (A' s).2.2) q +
        F.e₃.2.2 * partialZ (fun s => (A' s).2.2) q) * F.e₃.2.2) := by
    simpa [partialZ, transformedField, fromComponents, addVec, scaleVec, q]
      using hout.deriv
  rw [hd]
  unfold diagonalZExpansion
  dsimp [q]
  ring

theorem gap11 (F : Frame) (origin p : Vec3) (A' : Vec3 → Vec3)
    (hDiff : DifferentiableFieldAt A' (rotatedCoordinates F origin p)) :
    divergence (transformedField F origin A') p =
      diagonalXExpansion F A' (rotatedCoordinates F origin p) +
        diagonalYExpansion F A' (rotatedCoordinates F origin p) +
          diagonalZExpansion F A' (rotatedCoordinates F origin p) := by
  unfold divergence
  rw [gap8 F origin p A' hDiff, gap9 F origin p A' hDiff,
    gap10 F origin p A' hDiff]

theorem gap12 (F : Frame) (origin p : Vec3) (A' : Vec3 → Vec3)
    (hFrame : IsOrthonormal F)
    (hDiff : DifferentiableFieldAt A' (rotatedCoordinates F origin p)) :
    divergence (transformedField F origin A') p =
      divergence A' (rotatedCoordinates F origin p) := by
  rw [gap11 F origin p A' hDiff]
  rcases hFrame with ⟨h11, h22, h33, h12, h13, h23⟩
  unfold diagonalXExpansion diagonalYExpansion diagonalZExpansion divergence
  unfold dot at h11 h22 h33 h12 h13 h23
  linear_combination
    (partialX (fun s => (A' s).1) (rotatedCoordinates F origin p)) * h11 +
    (partialY (fun s => (A' s).2.1) (rotatedCoordinates F origin p)) * h22 +
    (partialZ (fun s => (A' s).2.2) (rotatedCoordinates F origin p)) * h33 +
    (partialY (fun s => (A' s).1) (rotatedCoordinates F origin p) +
      partialX (fun s => (A' s).2.1) (rotatedCoordinates F origin p)) * h12 +
    (partialZ (fun s => (A' s).1) (rotatedCoordinates F origin p) +
      partialX (fun s => (A' s).2.2) (rotatedCoordinates F origin p)) * h13 +
    (partialZ (fun s => (A' s).2.1) (rotatedCoordinates F origin p) +
      partialY (fun s => (A' s).2.2) (rotatedCoordinates F origin p)) * h23

theorem gap13 (F : Frame) (origin p : Vec3) (A' : Vec3 → Vec3)
    (hFrame : IsOrthonormal F)
    (hDiff : DifferentiableFieldAt A' (rotatedCoordinates F origin p)) :
    divergence (transformedField F origin A') p =
      divergence A' (rotatedCoordinates F origin p) := by
  exact gap12 F origin p A' hFrame hDiff

end

end ProofGap.Exercise4421
