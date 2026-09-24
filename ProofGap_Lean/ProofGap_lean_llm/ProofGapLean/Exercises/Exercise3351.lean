import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

namespace ProofGap.Exercise3351

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (r s : Vec3) : ℝ :=
  r.1 * s.1 + r.2.1 * s.2.1 + r.2.2 * s.2.2

def IsOrthonormal3 (l : Fin 3 → Vec3) : Prop :=
  ∀ i j, dot (l i) (l j) = if i = j then 1 else 0

def partialX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => u s y z) x

def partialY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => u x s z) y

def partialZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => u x y s) z

def partialXX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX u s y z) x

def partialXY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX u x s z) y

def partialXZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialX u x y s) z

def partialYY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialY u x s z) y

def partialYZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialY u x y s) z

def partialZZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialZ u x y s) z

def dirFirst (u : ℝ → ℝ → ℝ → ℝ) (l : Vec3) (x y z : ℝ) : ℝ :=
  deriv (fun t => u (x + t * l.1) (y + t * l.2.1) (z + t * l.2.2)) 0

def dirSecond (u : ℝ → ℝ → ℝ → ℝ) (l : Vec3) (x y z : ℝ) : ℝ :=
  deriv
    (deriv (fun t => u (x + t * l.1) (y + t * l.2.1) (z + t * l.2.2))) 0

def IsC2 (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2)

private def coordinateMatrix (l : Fin 3 → Vec3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => ![(l i).1, (l i).2.1, (l i).2.2] j

private theorem column_orthonormal (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    ∀ j k, (∑ i : Fin 3, ![(l i).1, (l i).2.1, (l i).2.2] j *
      ![(l i).1, (l i).2.1, (l i).2.2] k) = if j = k then 1 else 0 := by
  let M := coordinateMatrix l
  have hdot (i j : Fin 3) :
      (∑ x : Fin 3, ![(l i).1, (l i).2.1, (l i).2.2] x *
        ![(l j).1, (l j).2.1, (l j).2.2] x) = dot (l i) (l j) := by
    simp [Fin.sum_univ_succ, dot, add_assoc]
  have hMM : M * M.transpose = 1 := by
    ext i j
    simp only [M, coordinateMatrix, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.one_apply]
    rw [hdot i j]
    exact hl i j
  have hTM : M.transpose * M = 1 :=
    (Matrix.mul_eq_one_comm).mp hMM
  intro j k
  have h := congrFun (congrFun hTM j) k
  simpa [M, coordinateMatrix, Matrix.mul_apply, Matrix.one_apply] using h

private theorem deriv_affine_line
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Differentiable ℝ f) (p v : E) (t : ℝ) :
    deriv (fun s : ℝ => f (p + s • v)) t = (fderiv ℝ f (p + t • v)) v := by
  have hc : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add p
  exact (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt t hc).deriv

private theorem dirFirst_coordinate_formula
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u) (v : Vec3) (x y z : ℝ) :
    dirFirst u v x y z =
      partialX u x y z * v.1 + partialY u x y z * v.2.1 +
        partialZ u x y z * v.2.2 := by
  let F : Vec3 → ℝ := fun p => u p.1 p.2.1 p.2.2
  let ex : Vec3 := (1, 0, 0)
  let ey : Vec3 := (0, 1, 0)
  let ez : Vec3 := (0, 0, 1)
  have hF : Differentiable ℝ F :=
    (show ContDiff ℝ 2 F from hu).differentiable (by decide)
  have hd : dirFirst u v x y z = (fderiv ℝ F (x, y, z)) v := by
    unfold dirFirst
    simpa [F, smul_eq_mul] using
      deriv_affine_line F hF (x, y, z) v 0
  have hx : partialX u x y z = (fderiv ℝ F (x, y, z)) ex := by
    unfold partialX
    simpa [F, ex, smul_eq_mul] using
      deriv_affine_line F hF (0, y, z) ex x
  have hy : partialY u x y z = (fderiv ℝ F (x, y, z)) ey := by
    unfold partialY
    simpa [F, ey, smul_eq_mul] using
      deriv_affine_line F hF (x, 0, z) ey y
  have hz : partialZ u x y z = (fderiv ℝ F (x, y, z)) ez := by
    unfold partialZ
    simpa [F, ez, smul_eq_mul] using
      deriv_affine_line F hF (x, y, 0) ez z
  have hv : v = v.1 • ex + v.2.1 • ey + v.2.2 • ez := by
    rcases v with ⟨a, b, c⟩
    simp [ex, ey, ez]
  rw [hd, hv]
  simp only [map_add, map_smul]
  rw [← hx, ← hy, ← hz]
  simp [smul_eq_mul]
  ring

private theorem differentiable_fderiv_of_contDiff_two
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fderiv ℝ f) := by
  let g : E → E → F := fun _ x => f x
  have hg : ContDiff ℝ 2 (Function.uncurry g) := by
    change ContDiff ℝ 2 (fun p : E × E => f p.2)
    exact hf.comp contDiff_snd
  have hi : ContDiff ℝ 1 (fun x : E => x) := contDiff_id
  have hd : ContDiff ℝ 1 (fun x : E => fderiv ℝ (g x) x) := by
    exact hg.fderiv hi (by decide)
  have hd' : ContDiff ℝ 1 (fun x : E => fderiv ℝ f x) := by
    simpa [g] using hd
  exact hd'.differentiable (by decide)

private theorem deriv_fderiv_line
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 2 f) (p w v : E) (t : ℝ) :
    deriv (fun s : ℝ => (fderiv ℝ f (p + s • w)) v) t =
      ((fderiv ℝ (fderiv ℝ f) (p + t • w)) w) v := by
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    differentiable_fderiv_of_contDiff_two f hf
  have hc : HasDerivAt (fun s : ℝ => p + s • w) w t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const w).const_add p
  have hcomp : HasDerivAt
      (fun s : ℝ => fderiv ℝ f (p + s • w))
      ((fderiv ℝ (fderiv ℝ f) (p + t • w)) w) t :=
    hDf.differentiableAt.hasFDerivAt.comp_hasDerivAt t hc
  simpa using (hcomp.clm_apply (hasDerivAt_const (x := t) v)).deriv

private theorem second_deriv_affine_line
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 2 f) (p v : E) :
    deriv (deriv (fun t : ℝ => f (p + t • v))) 0 =
      ((fderiv ℝ (fderiv ℝ f) p) v) v := by
  have hfd : Differentiable ℝ f := hf.differentiable (by decide)
  have hfirst :
      deriv (fun t : ℝ => f (p + t • v)) =
        fun t => (fderiv ℝ f (p + t • v)) v := by
    funext t
    exact deriv_affine_line f hfd p v t
  rw [hfirst]
  simpa using deriv_fderiv_line f hf p v v 0

private theorem dirSecond_coordinate_formula
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u) (v : Vec3) (x y z : ℝ) :
    dirSecond u v x y z =
      partialXX u x y z * v.1 ^ 2 +
      partialYY u x y z * v.2.1 ^ 2 +
      partialZZ u x y z * v.2.2 ^ 2 +
      2 * partialXY u x y z * (v.1 * v.2.1) +
      2 * partialYZ u x y z * (v.2.1 * v.2.2) +
      2 * partialXZ u x y z * (v.2.2 * v.1) := by
  let F : Vec3 → ℝ := fun p => u p.1 p.2.1 p.2.2
  let ex : Vec3 := (1, 0, 0)
  let ey : Vec3 := (0, 1, 0)
  let ez : Vec3 := (0, 0, 1)
  let H := fderiv ℝ (fderiv ℝ F) (x, y, z)
  have hF : ContDiff ℝ 2 F := hu
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
  have hsec : dirSecond u v x y z = H v v := by
    unfold dirSecond
    simpa [F, H, smul_eq_mul] using
      second_deriv_affine_line F hF (x, y, z) v
  have hentry (p w q : Vec3) (t : ℝ) :
      deriv (fun s : ℝ => (fderiv ℝ F (p + s • w)) q) t =
        (fderiv ℝ (fderiv ℝ F) (p + t • w)) w q :=
    deriv_fderiv_line F hF p w q t
  have hx (a b c : ℝ) :
      partialX u a b c = (fderiv ℝ F (a, b, c)) ex := by
    unfold partialX
    simpa [F, ex, smul_eq_mul] using
      deriv_affine_line F hFd (0, b, c) ex a
  have hy (a b c : ℝ) :
      partialY u a b c = (fderiv ℝ F (a, b, c)) ey := by
    unfold partialY
    simpa [F, ey, smul_eq_mul] using
      deriv_affine_line F hFd (a, 0, c) ey b
  have hz (a b c : ℝ) :
      partialZ u a b c = (fderiv ℝ F (a, b, c)) ez := by
    unfold partialZ
    simpa [F, ez, smul_eq_mul] using
      deriv_affine_line F hFd (a, b, 0) ez c
  have hxx : partialXX u x y z = H ex ex := by
    unfold partialXX
    rw [show (fun s => partialX u s y z) =
        (fun s => (fderiv ℝ F (s, y, z)) ex) by
      funext s
      exact hx s y z]
    simpa [H, ex, smul_eq_mul] using hentry (0, y, z) ex ex x
  have hxy : partialXY u x y z = H ey ex := by
    unfold partialXY
    rw [show (fun s => partialX u x s z) =
        (fun s => (fderiv ℝ F (x, s, z)) ex) by
      funext s
      exact hx x s z]
    simpa [H, ex, ey, smul_eq_mul] using hentry (x, 0, z) ey ex y
  have hxz : partialXZ u x y z = H ez ex := by
    unfold partialXZ
    rw [show (fun s => partialX u x y s) =
        (fun s => (fderiv ℝ F (x, y, s)) ex) by
      funext s
      exact hx x y s]
    simpa [H, ex, ez, smul_eq_mul] using hentry (x, y, 0) ez ex z
  have hyy : partialYY u x y z = H ey ey := by
    unfold partialYY
    rw [show (fun s => partialY u x s z) =
        (fun s => (fderiv ℝ F (x, s, z)) ey) by
      funext s
      exact hy x s z]
    simpa [H, ey, smul_eq_mul] using hentry (x, 0, z) ey ey y
  have hyz : partialYZ u x y z = H ez ey := by
    unfold partialYZ
    rw [show (fun s => partialY u x y s) =
        (fun s => (fderiv ℝ F (x, y, s)) ey) by
      funext s
      exact hy x y s]
    simpa [H, ey, ez, smul_eq_mul] using hentry (x, y, 0) ez ey z
  have hzz : partialZZ u x y z = H ez ez := by
    unfold partialZZ
    rw [show (fun s => partialZ u x y s) =
        (fun s => (fderiv ℝ F (x, y, s)) ez) by
      funext s
      exact hz x y s]
    simpa [H, ez, smul_eq_mul] using hentry (x, y, 0) ez ez z
  have hsymm : ∀ a b : Vec3, H a b = H b a := by
    intro a b
    simpa [H] using
      ((hF.contDiffAt).isSymmSndFDerivAt (by norm_num [minSmoothness]) a b)
  have hexy : H ex ey = partialXY u x y z := by
    calc
      H ex ey = H ey ex := hsymm ex ey
      _ = partialXY u x y z := hxy.symm
  have hexz : H ex ez = partialXZ u x y z := by
    calc
      H ex ez = H ez ex := hsymm ex ez
      _ = partialXZ u x y z := hxz.symm
  have heyz : H ey ez = partialYZ u x y z := by
    calc
      H ey ez = H ez ey := hsymm ey ez
      _ = partialYZ u x y z := hyz.symm
  have hv : v = v.1 • ex + v.2.1 • ey + v.2.2 • ez := by
    rcases v with ⟨a, b, c⟩
    simp [ex, ey, ez]
  rw [hsec]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  rw [← hxx, hexy, hexz, ← hxy, ← hyy, heyz, ← hxz, ← hyz, ← hzz]
  simp [smul_eq_mul]
  ring

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u)
    (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    ∀ x y z,
      ∑ i : Fin 3, dirFirst u (l i) x y z ^ 2 =
        ∑ i : Fin 3,
          (partialX u x y z * (l i).1 +
            partialY u x y z * (l i).2.1 +
            partialZ u x y z * (l i).2.2) ^ 2 := by
  intro x y z
  apply Finset.sum_congr rfl
  intro i hi
  rw [dirFirst_coordinate_formula u hu (l i) x y z]

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (l : Fin 3 → Vec3) :
    ∀ x y z,
      (∑ i : Fin 3,
          (partialX u x y z * (l i).1 +
            partialY u x y z * (l i).2.1 +
            partialZ u x y z * (l i).2.2) ^ 2) =
        partialX u x y z ^ 2 * (∑ i : Fin 3, (l i).1 ^ 2) +
          partialY u x y z ^ 2 * (∑ i : Fin 3, (l i).2.1 ^ 2) +
          partialZ u x y z ^ 2 * (∑ i : Fin 3, (l i).2.2 ^ 2) +
          2 * partialX u x y z * partialY u x y z *
            (∑ i : Fin 3, (l i).1 * (l i).2.1) +
          2 * partialY u x y z * partialZ u x y z *
            (∑ i : Fin 3, (l i).2.1 * (l i).2.2) +
          2 * partialZ u x y z * partialX u x y z *
            (∑ i : Fin 3, (l i).2.2 * (l i).1) := by
  intro x y z
  calc
    (∑ i : Fin 3,
        (partialX u x y z * (l i).1 +
          partialY u x y z * (l i).2.1 +
          partialZ u x y z * (l i).2.2) ^ 2) =
        ∑ i : Fin 3,
          (partialX u x y z ^ 2 * (l i).1 ^ 2 +
            partialY u x y z ^ 2 * (l i).2.1 ^ 2 +
            partialZ u x y z ^ 2 * (l i).2.2 ^ 2 +
            (2 * partialX u x y z * partialY u x y z) *
              ((l i).1 * (l i).2.1) +
            (2 * partialY u x y z * partialZ u x y z) *
              ((l i).2.1 * (l i).2.2) +
            (2 * partialZ u x y z * partialX u x y z) *
              ((l i).2.2 * (l i).1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem gap3 (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    (∑ i : Fin 3, (l i).1 * (l i).2.1) = 0 := by
  simpa using column_orthonormal l hl (0 : Fin 3) (1 : Fin 3)

theorem gap4 (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    (∑ i : Fin 3, (l i).2.1 * (l i).2.2) = 0 := by
  simpa using column_orthonormal l hl (1 : Fin 3) (2 : Fin 3)

theorem gap5 (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    (∑ i : Fin 3, (l i).2.2 * (l i).1) = 0 := by
  simpa [mul_comm] using column_orthonormal l hl (2 : Fin 3) (0 : Fin 3)

theorem gap6 (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    (∑ i : Fin 3, (l i).1 ^ 2) = 1 := by
  simpa [pow_two] using column_orthonormal l hl (0 : Fin 3) (0 : Fin 3)

theorem gap7 (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    (∑ i : Fin 3, (l i).2.1 ^ 2) = 1 := by
  simpa [pow_two] using column_orthonormal l hl (1 : Fin 3) (1 : Fin 3)

theorem gap8 (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    (∑ i : Fin 3, (l i).2.2 ^ 2) = 1 := by
  simpa [pow_two] using column_orthonormal l hl (2 : Fin 3) (2 : Fin 3)

theorem gap9 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u)
    (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    ∀ x y z,
      ∑ i : Fin 3, dirFirst u (l i) x y z ^ 2 =
        partialX u x y z ^ 2 + partialY u x y z ^ 2 +
          partialZ u x y z ^ 2 := by
  intro x y z
  rw [gap1 u hu l hl x y z, gap2 u l x y z]
  rw [gap3 l hl, gap4 l hl, gap5 l hl, gap6 l hl, gap7 l hl, gap8 l hl]
  ring

theorem gap10 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u)
    (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    ∀ x y z,
      ∑ i : Fin 3, dirSecond u (l i) x y z =
        partialXX u x y z * (∑ i : Fin 3, (l i).1 ^ 2) +
          partialYY u x y z * (∑ i : Fin 3, (l i).2.1 ^ 2) +
          partialZZ u x y z * (∑ i : Fin 3, (l i).2.2 ^ 2) +
          2 * partialXY u x y z * (∑ i : Fin 3, (l i).1 * (l i).2.1) +
          2 * partialYZ u x y z * (∑ i : Fin 3, (l i).2.1 * (l i).2.2) +
          2 * partialXZ u x y z * (∑ i : Fin 3, (l i).2.2 * (l i).1) := by
  intro x y z
  calc
    (∑ i : Fin 3, dirSecond u (l i) x y z) =
        ∑ i : Fin 3,
          (partialXX u x y z * (l i).1 ^ 2 +
            partialYY u x y z * (l i).2.1 ^ 2 +
            partialZZ u x y z * (l i).2.2 ^ 2 +
            2 * partialXY u x y z * ((l i).1 * (l i).2.1) +
            2 * partialYZ u x y z * ((l i).2.1 * (l i).2.2) +
            2 * partialXZ u x y z * ((l i).2.2 * (l i).1)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [dirSecond_coordinate_formula u hu (l i) x y z]
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem gap11 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u)
    (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    ∀ x y z,
      ∑ i : Fin 3, dirSecond u (l i) x y z =
        partialXX u x y z + partialYY u x y z + partialZZ u x y z := by
  intro x y z
  rw [gap10 u hu l hl x y z]
  rw [gap3 l hl, gap4 l hl, gap5 l hl, gap6 l hl, gap7 l hl, gap8 l hl]
  ring

theorem gap12 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u)
    (l : Fin 3 → Vec3) (hl : IsOrthonormal3 l) :
    ∀ x y z,
      (∑ i : Fin 3, dirFirst u (l i) x y z ^ 2 =
        partialX u x y z ^ 2 + partialY u x y z ^ 2 +
          partialZ u x y z ^ 2) ∧
      (∑ i : Fin 3, dirSecond u (l i) x y z =
        partialXX u x y z + partialYY u x y z + partialZZ u x y z) := by
  intro x y z
  exact ⟨gap9 u hu l hl x y z, gap11 u hu l hl x y z⟩

end

end ProofGap.Exercise3351
