import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3350

noncomputable section

abbrev Vec3 := ℝ × ℝ × ℝ

def vec3 (x y z : ℝ) : Vec3 :=
  (x, y, z)

def direction (α β γ : ℝ) : Vec3 :=
  vec3 (Real.cos α) (Real.cos β) (Real.cos γ)

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

def partialYX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialY u s y z) x

def partialYY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialY u x s z) y

def partialYZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialY u x y s) z

def partialZX (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialZ u s y z) x

def partialZY (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialZ u x s z) y

def partialZZ (u : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun s => partialZ u x y s) z

def dirFirst (u : ℝ → ℝ → ℝ → ℝ) (l : Vec3) (x y z : ℝ) : ℝ :=
  deriv (fun t => u (x + t * l.1) (y + t * l.2.1) (z + t * l.2.2)) 0

def dirSecond (u : ℝ → ℝ → ℝ → ℝ) (l : Vec3) (x y z : ℝ) : ℝ :=
  deriv
    (deriv (fun t => u (x + t * l.1) (y + t * l.2.1) (z + t * l.2.2))) 0

def IsC2 (u : ℝ → ℝ → ℝ → ℝ) : Prop :=
  ContDiff ℝ 2 (fun p : ℝ × ℝ × ℝ => u p.1 p.2.1 p.2.2)

private theorem deriv_affine_line
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : Differentiable ℝ f) (p v : E) (t : ℝ) :
    deriv (fun s : ℝ => f (p + s • v)) t =
      (fderiv ℝ f (p + t • v)) v := by
  have hc : HasDerivAt (fun s : ℝ => p + s • v) v t := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id t).smul_const v).const_add p
  exact (hf.differentiableAt.hasFDerivAt.comp_hasDerivAt t hc).deriv

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
  have hd : ContDiff ℝ 1 (fun x : E => fderiv ℝ (g x) x) :=
    hg.fderiv hi (by decide)
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

private theorem dirFirst_coordinate_formula
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u)
    (v : Vec3) (x y z : ℝ) :
    dirFirst u v x y z =
      partialX u x y z * v.1 +
        partialY u x y z * v.2.1 +
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

private theorem dirSecond_raw_formula
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u)
    (v : Vec3) (x y z : ℝ) :
    dirSecond u v x y z =
      (partialXX u x y z * v.1 +
          partialYX u x y z * v.2.1 +
          partialZX u x y z * v.2.2) * v.1 +
        (partialXY u x y z * v.1 +
          partialYY u x y z * v.2.1 +
          partialZY u x y z * v.2.2) * v.2.1 +
        (partialXZ u x y z * v.1 +
          partialYZ u x y z * v.2.1 +
          partialZZ u x y z * v.2.2) * v.2.2 := by
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
        fun s => (fderiv ℝ F (s, y, z)) ex by
      funext s
      exact hx s y z]
    simpa [H, ex, smul_eq_mul] using hentry (0, y, z) ex ex x
  have hyx : partialYX u x y z = H ex ey := by
    unfold partialYX
    rw [show (fun s => partialY u s y z) =
        fun s => (fderiv ℝ F (s, y, z)) ey by
      funext s
      exact hy s y z]
    simpa [H, ex, ey, smul_eq_mul] using hentry (0, y, z) ex ey x
  have hzx : partialZX u x y z = H ex ez := by
    unfold partialZX
    rw [show (fun s => partialZ u s y z) =
        fun s => (fderiv ℝ F (s, y, z)) ez by
      funext s
      exact hz s y z]
    simpa [H, ex, ez, smul_eq_mul] using hentry (0, y, z) ex ez x
  have hxy : partialXY u x y z = H ey ex := by
    unfold partialXY
    rw [show (fun s => partialX u x s z) =
        fun s => (fderiv ℝ F (x, s, z)) ex by
      funext s
      exact hx x s z]
    simpa [H, ex, ey, smul_eq_mul] using hentry (x, 0, z) ey ex y
  have hyy : partialYY u x y z = H ey ey := by
    unfold partialYY
    rw [show (fun s => partialY u x s z) =
        fun s => (fderiv ℝ F (x, s, z)) ey by
      funext s
      exact hy x s z]
    simpa [H, ey, smul_eq_mul] using hentry (x, 0, z) ey ey y
  have hzy : partialZY u x y z = H ey ez := by
    unfold partialZY
    rw [show (fun s => partialZ u x s z) =
        fun s => (fderiv ℝ F (x, s, z)) ez by
      funext s
      exact hz x s z]
    simpa [H, ey, ez, smul_eq_mul] using hentry (x, 0, z) ey ez y
  have hxz : partialXZ u x y z = H ez ex := by
    unfold partialXZ
    rw [show (fun s => partialX u x y s) =
        fun s => (fderiv ℝ F (x, y, s)) ex by
      funext s
      exact hx x y s]
    simpa [H, ex, ez, smul_eq_mul] using hentry (x, y, 0) ez ex z
  have hyz : partialYZ u x y z = H ez ey := by
    unfold partialYZ
    rw [show (fun s => partialY u x y s) =
        fun s => (fderiv ℝ F (x, y, s)) ey by
      funext s
      exact hy x y s]
    simpa [H, ey, ez, smul_eq_mul] using hentry (x, y, 0) ez ey z
  have hzz : partialZZ u x y z = H ez ez := by
    unfold partialZZ
    rw [show (fun s => partialZ u x y s) =
        fun s => (fderiv ℝ F (x, y, s)) ez by
      funext s
      exact hz x y s]
    simpa [H, ez, smul_eq_mul] using hentry (x, y, 0) ez ez z
  have hv : v = v.1 • ex + v.2.1 • ey + v.2.2 • ez := by
    rcases v with ⟨a, b, c⟩
    simp [ex, ey, ez]
  rw [hsec]
  conv_lhs => rw [hv]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply]
  rw [← hxx, ← hyx, ← hzx, ← hxy, ← hyy, ← hzy,
    ← hxz, ← hyz, ← hzz]
  simp [smul_eq_mul]
  ring

private theorem mixed_partials
    (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u) (x y z : ℝ) :
    partialYX u x y z = partialXY u x y z ∧
      partialZX u x y z = partialXZ u x y z ∧
      partialZY u x y z = partialYZ u x y z := by
  let F : Vec3 → ℝ := fun p => u p.1 p.2.1 p.2.2
  let ex : Vec3 := (1, 0, 0)
  let ey : Vec3 := (0, 1, 0)
  let ez : Vec3 := (0, 0, 1)
  let H := fderiv ℝ (fderiv ℝ F) (x, y, z)
  have hF : ContDiff ℝ 2 F := hu
  have hFd : Differentiable ℝ F := hF.differentiable (by decide)
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
  have hyx : partialYX u x y z = H ex ey := by
    unfold partialYX
    rw [show (fun s => partialY u s y z) =
        fun s => (fderiv ℝ F (s, y, z)) ey by
      funext s
      exact hy s y z]
    simpa [H, ex, ey, smul_eq_mul] using hentry (0, y, z) ex ey x
  have hxy : partialXY u x y z = H ey ex := by
    unfold partialXY
    rw [show (fun s => partialX u x s z) =
        fun s => (fderiv ℝ F (x, s, z)) ex by
      funext s
      exact hx x s z]
    simpa [H, ex, ey, smul_eq_mul] using hentry (x, 0, z) ey ex y
  have hzx : partialZX u x y z = H ex ez := by
    unfold partialZX
    rw [show (fun s => partialZ u s y z) =
        fun s => (fderiv ℝ F (s, y, z)) ez by
      funext s
      exact hz s y z]
    simpa [H, ex, ez, smul_eq_mul] using hentry (0, y, z) ex ez x
  have hxz : partialXZ u x y z = H ez ex := by
    unfold partialXZ
    rw [show (fun s => partialX u x y s) =
        fun s => (fderiv ℝ F (x, y, s)) ex by
      funext s
      exact hx x y s]
    simpa [H, ex, ez, smul_eq_mul] using hentry (x, y, 0) ez ex z
  have hzy : partialZY u x y z = H ey ez := by
    unfold partialZY
    rw [show (fun s => partialZ u x s z) =
        fun s => (fderiv ℝ F (x, s, z)) ez by
      funext s
      exact hz x s z]
    simpa [H, ey, ez, smul_eq_mul] using hentry (x, 0, z) ey ez y
  have hyz : partialYZ u x y z = H ez ey := by
    unfold partialYZ
    rw [show (fun s => partialY u x y s) =
        fun s => (fderiv ℝ F (x, y, s)) ey by
      funext s
      exact hy x y s]
    simpa [H, ey, ez, smul_eq_mul] using hentry (x, y, 0) ez ey z
  have hsymm : ∀ a b : Vec3, H a b = H b a := by
    intro a b
    simpa [H] using
      hF.contDiffAt.isSymmSndFDerivAt
        (by norm_num [minSmoothness]) a b
  exact ⟨hyx.trans ((hsymm ex ey).trans hxy.symm),
    hzx.trans ((hsymm ex ez).trans hxz.symm),
    hzy.trans ((hsymm ey ez).trans hyz.symm)⟩

theorem gap1 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u) (α β γ : ℝ) :
    ∀ x y z,
      dirFirst u (direction α β γ) x y z =
        partialX u x y z * Real.cos α +
          partialY u x y z * Real.cos β +
          partialZ u x y z * Real.cos γ := by
  intro x y z
  simpa [direction, vec3] using
    dirFirst_coordinate_formula u hu (direction α β γ) x y z

theorem gap2 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u) (α β γ : ℝ) :
    ∀ x y z,
      dirSecond u (direction α β γ) x y z =
        (partialXX u x y z * Real.cos α +
            partialYX u x y z * Real.cos β +
            partialZX u x y z * Real.cos γ) * Real.cos α +
          (partialXY u x y z * Real.cos α +
            partialYY u x y z * Real.cos β +
            partialZY u x y z * Real.cos γ) * Real.cos β +
          (partialXZ u x y z * Real.cos α +
            partialYZ u x y z * Real.cos β +
            partialZZ u x y z * Real.cos γ) * Real.cos γ := by
  intro x y z
  simpa [direction, vec3] using
    dirSecond_raw_formula u hu (direction α β γ) x y z

theorem gap3 (u : ℝ → ℝ → ℝ → ℝ) (hu : IsC2 u) (α β γ : ℝ) :
    ∀ x y z,
      dirSecond u (direction α β γ) x y z =
        partialXX u x y z * Real.cos α ^ 2 +
          partialYY u x y z * Real.cos β ^ 2 +
          partialZZ u x y z * Real.cos γ ^ 2 +
          2 * partialXY u x y z * Real.cos α * Real.cos β +
          2 * partialYZ u x y z * Real.cos β * Real.cos γ +
          2 * partialXZ u x y z * Real.cos γ * Real.cos α := by
  intro x y z
  rw [gap2 u hu α β γ x y z]
  rcases mixed_partials u hu x y z with ⟨hyx, hzx, hzy⟩
  rw [hyx, hzx, hzy]
  ring

end

end ProofGap.Exercise3350
