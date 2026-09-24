import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Order.Filter.Tendsto
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise4414

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

def divergence (F : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (F q).1) p +
    partialY (fun q => (F q).2.1) p +
      partialZ (fun q => (F q).2.2) p

def laplacian (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  divergence (gradient u) p

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def addField (F G : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  ((F p).1 + (G p).1,
    (F p).2.1 + (G p).2.1,
    (F p).2.2 + (G p).2.2)

def scalarFieldMul (u : Vec3 → ℝ) (F : Vec3 → Vec3) (p : Vec3) : Vec3 :=
  (u p * (F p).1, u p * (F p).2.1, u p * (F p).2.2)

def C2At (u : Vec3 → ℝ) (p : Vec3) : Prop :=
  ContDiffAt ℝ 2 u p

private theorem deriv_mul_comm_of_differentiableAt
    {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y * g y) x =
      f x * deriv g x + g x * deriv f x := by
  simpa [mul_comm, add_comm] using (hf.hasDerivAt.mul hg.hasDerivAt).deriv

private theorem deriv_add_of_differentiableAt
    {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (fun y => f y + g y) x = deriv f x + deriv g x := by
  exact (hf.hasDerivAt.add hg.hasDerivAt).deriv

private theorem deriv_differentiableAt_of_contDiffAt_two
    {f : ℝ → ℝ} {x : ℝ} (h : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (deriv f) x := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x :=
    h.fderiv_right (by norm_num)
  have hdd : DifferentiableAt ℝ (fderiv ℝ f) x :=
    hd.differentiableAt (by norm_num)
  change DifferentiableAt ℝ (fun y => (fderiv ℝ f y) 1) x
  fun_prop

private theorem sliceX_contDiffAt_two (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    ContDiffAt ℝ 2 (fun x => u (x, p.2.1, p.2.2)) p.1 := by
  change ContDiffAt ℝ 2 u p at hu
  have hp : ContDiffAt ℝ 2 (fun x : ℝ => (x, p.2.1, p.2.2)) p.1 := by
    fun_prop
  simpa only [Function.comp_apply] using hu.comp p.1 hp

private theorem sliceY_contDiffAt_two (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    ContDiffAt ℝ 2 (fun y => u (p.1, y, p.2.2)) p.2.1 := by
  change ContDiffAt ℝ 2 u p at hu
  have hp : ContDiffAt ℝ 2 (fun y : ℝ => (p.1, y, p.2.2)) p.2.1 := by
    fun_prop
  simpa only [Function.comp_apply] using hu.comp p.2.1 hp

private theorem sliceZ_contDiffAt_two (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    ContDiffAt ℝ 2 (fun z => u (p.1, p.2.1, z)) p.2.2 := by
  change ContDiffAt ℝ 2 u p at hu
  have hp : ContDiffAt ℝ 2 (fun z : ℝ => (p.1, p.2.1, z)) p.2.2 := by
    fun_prop
  simpa only [Function.comp_apply] using hu.comp p.2.2 hp

private theorem sliceX_differentiableAt (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    DifferentiableAt ℝ (fun x => u (x, p.2.1, p.2.2)) p.1 :=
  (sliceX_contDiffAt_two u p hu).differentiableAt (by decide)

private theorem sliceY_differentiableAt (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    DifferentiableAt ℝ (fun y => u (p.1, y, p.2.2)) p.2.1 :=
  (sliceY_contDiffAt_two u p hu).differentiableAt (by decide)

private theorem sliceZ_differentiableAt (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    DifferentiableAt ℝ (fun z => u (p.1, p.2.1, z)) p.2.2 :=
  (sliceZ_contDiffAt_two u p hu).differentiableAt (by decide)

private theorem partialX_slice_differentiableAt (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    DifferentiableAt ℝ (fun x => partialX u (x, p.2.1, p.2.2)) p.1 := by
  simpa [partialX] using
    deriv_differentiableAt_of_contDiffAt_two (sliceX_contDiffAt_two u p hu)

private theorem partialY_slice_differentiableAt (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    DifferentiableAt ℝ (fun y => partialY u (p.1, y, p.2.2)) p.2.1 := by
  simpa [partialY] using
    deriv_differentiableAt_of_contDiffAt_two (sliceY_contDiffAt_two u p hu)

private theorem partialZ_slice_differentiableAt (u : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) :
    DifferentiableAt ℝ (fun z => partialZ u (p.1, p.2.1, z)) p.2.2 := by
  simpa [partialZ] using
    deriv_differentiableAt_of_contDiffAt_two (sliceZ_contDiffAt_two u p hu)

private theorem divergence_congr_of_eventuallyEq
    {F G : Vec3 → Vec3} {p : Vec3} (h : F =ᶠ[nhds p] G) :
    divergence F p = divergence G p := by
  have htx :
      Filter.Tendsto (fun x : ℝ => (x, p.2.1, p.2.2)) (nhds p.1) (nhds p) := by
    exact
      (show ContDiffAt ℝ 2 (fun x : ℝ => (x, p.2.1, p.2.2)) p.1 by
        fun_prop).continuousAt
  have hty :
      Filter.Tendsto (fun y : ℝ => (p.1, y, p.2.2)) (nhds p.2.1) (nhds p) := by
    exact
      (show ContDiffAt ℝ 2 (fun y : ℝ => (p.1, y, p.2.2)) p.2.1 by
        fun_prop).continuousAt
  have htz :
      Filter.Tendsto (fun z : ℝ => (p.1, p.2.1, z)) (nhds p.2.2) (nhds p) := by
    exact
      (show ContDiffAt ℝ 2 (fun z : ℝ => (p.1, p.2.1, z)) p.2.2 by
        fun_prop).continuousAt
  have hx :
      (fun x => (F (x, p.2.1, p.2.2)).1) =ᶠ[nhds p.1]
        (fun x => (G (x, p.2.1, p.2.2)).1) :=
    (h.comp_tendsto htx).mono fun _ hq => congrArg Prod.fst hq
  have hy :
      (fun y => (F (p.1, y, p.2.2)).2.1) =ᶠ[nhds p.2.1]
        (fun y => (G (p.1, y, p.2.2)).2.1) :=
    (h.comp_tendsto hty).mono fun _ hq =>
      congrArg (fun q => q.2.1) hq
  have hz :
      (fun z => (F (p.1, p.2.1, z)).2.2) =ᶠ[nhds p.2.2]
        (fun z => (G (p.1, p.2.1, z)).2.2) :=
    (h.comp_tendsto htz).mono fun _ hq =>
      congrArg (fun q => q.2.2) hq
  unfold divergence partialX partialY partialZ
  rw [hx.deriv_eq, hy.deriv_eq, hz.deriv_eq]

private theorem divergence_addField_of_differentiableAt
    (F G : Vec3 → Vec3) (p : Vec3)
    (hFx : DifferentiableAt ℝ (fun x => (F (x, p.2.1, p.2.2)).1) p.1)
    (hGx : DifferentiableAt ℝ (fun x => (G (x, p.2.1, p.2.2)).1) p.1)
    (hFy : DifferentiableAt ℝ (fun y => (F (p.1, y, p.2.2)).2.1) p.2.1)
    (hGy : DifferentiableAt ℝ (fun y => (G (p.1, y, p.2.2)).2.1) p.2.1)
    (hFz : DifferentiableAt ℝ (fun z => (F (p.1, p.2.1, z)).2.2) p.2.2)
    (hGz : DifferentiableAt ℝ (fun z => (G (p.1, p.2.1, z)).2.2) p.2.2) :
    divergence (addField F G) p = divergence F p + divergence G p := by
  unfold divergence addField partialX partialY partialZ
  dsimp only
  rw [deriv_add_of_differentiableAt hFx hGx,
    deriv_add_of_differentiableAt hFy hGy,
    deriv_add_of_differentiableAt hFz hGz]
  ring

private theorem divergence_scalar_gradient
    (u v : Vec3 → ℝ) (p : Vec3) (hu : C2At u p) (hv : C2At v p) :
    divergence (scalarFieldMul u (gradient v)) p =
      u p * laplacian v p + dot (gradient u p) (gradient v p) := by
  have hx := deriv_mul_comm_of_differentiableAt
    (sliceX_differentiableAt u p hu)
    (partialX_slice_differentiableAt v p hv)
  have hy := deriv_mul_comm_of_differentiableAt
    (sliceY_differentiableAt u p hu)
    (partialY_slice_differentiableAt v p hv)
  have hz := deriv_mul_comm_of_differentiableAt
    (sliceZ_differentiableAt u p hu)
    (partialZ_slice_differentiableAt v p hv)
  unfold partialX at hx
  unfold partialY at hy
  unfold partialZ at hz
  unfold laplacian
  unfold divergence scalarFieldMul dot gradient partialX partialY partialZ
  dsimp at hx hy hz ⊢
  rw [hx, hy, hz]
  ring_nf

theorem gap1 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) (hv : C2At v p) :
    gradient (fun q => u q * v q) p =
      (u p * (gradient v p).1 + v p * (gradient u p).1,
        u p * (gradient v p).2.1 + v p * (gradient u p).2.1,
        u p * (gradient v p).2.2 + v p * (gradient u p).2.2) := by
  unfold gradient
  apply Prod.ext
  · dsimp only
    unfold partialX
    exact deriv_mul_comm_of_differentiableAt
      (sliceX_differentiableAt u p hu) (sliceX_differentiableAt v p hv)
  · apply Prod.ext
    · dsimp only
      unfold partialY
      exact deriv_mul_comm_of_differentiableAt
        (sliceY_differentiableAt u p hu) (sliceY_differentiableAt v p hv)
    · dsimp only
      unfold partialZ
      exact deriv_mul_comm_of_differentiableAt
        (sliceZ_differentiableAt u p hu) (sliceZ_differentiableAt v p hv)

theorem gap2 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) (hv : C2At v p) :
    laplacian (fun q => u q * v q) p =
      divergence
        (addField (scalarFieldMul u (gradient v))
          (scalarFieldMul v (gradient u))) p := by
  change ContDiffAt ℝ 2 u p at hu
  change ContDiffAt ℝ 2 v p at hv
  have hgrad :
      gradient (fun q => u q * v q) =ᶠ[nhds p]
        addField (scalarFieldMul u (gradient v))
          (scalarFieldMul v (gradient u)) := by
    filter_upwards [hu.eventually (by simp), hv.eventually (by simp)] with q huq hvq
    simpa [addField, scalarFieldMul] using gap1 u v q huq hvq
  unfold laplacian
  exact divergence_congr_of_eventuallyEq hgrad

theorem gap3 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) (hv : C2At v p) :
    divergence
        (addField (scalarFieldMul u (gradient v))
          (scalarFieldMul v (gradient u))) p =
      divergence (scalarFieldMul u (gradient v)) p +
        divergence (scalarFieldMul v (gradient u)) p := by
  apply divergence_addField_of_differentiableAt
  · simpa [scalarFieldMul, gradient] using
      (sliceX_differentiableAt u p hu).mul
        (partialX_slice_differentiableAt v p hv)
  · simpa [scalarFieldMul, gradient] using
      (sliceX_differentiableAt v p hv).mul
        (partialX_slice_differentiableAt u p hu)
  · simpa [scalarFieldMul, gradient] using
      (sliceY_differentiableAt u p hu).mul
        (partialY_slice_differentiableAt v p hv)
  · simpa [scalarFieldMul, gradient] using
      (sliceY_differentiableAt v p hv).mul
        (partialY_slice_differentiableAt u p hu)
  · simpa [scalarFieldMul, gradient] using
      (sliceZ_differentiableAt u p hu).mul
        (partialZ_slice_differentiableAt v p hv)
  · simpa [scalarFieldMul, gradient] using
      (sliceZ_differentiableAt v p hv).mul
        (partialZ_slice_differentiableAt u p hu)

theorem gap4 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) (hv : C2At v p) :
    laplacian (fun q => u q * v q) p =
      divergence (scalarFieldMul u (gradient v)) p +
        divergence (scalarFieldMul v (gradient u)) p := by
  calc
    laplacian (fun q => u q * v q) p =
        divergence
          (addField (scalarFieldMul u (gradient v))
            (scalarFieldMul v (gradient u))) p := gap2 u v p hu hv
    _ = divergence (scalarFieldMul u (gradient v)) p +
          divergence (scalarFieldMul v (gradient u)) p := gap3 u v p hu hv

theorem gap5 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) (hv : C2At v p) :
    divergence (scalarFieldMul u (gradient v)) p +
        divergence (scalarFieldMul v (gradient u)) p =
      u p * laplacian v p + dot (gradient u p) (gradient v p) +
        v p * laplacian u p + dot (gradient u p) (gradient v p) := by
  rw [divergence_scalar_gradient u v p hu hv,
    divergence_scalar_gradient v u p hv hu]
  unfold dot
  ring

theorem gap6 (u v : Vec3 → ℝ) (p : Vec3) :
    u p * laplacian v p + dot (gradient u p) (gradient v p) +
        v p * laplacian u p + dot (gradient u p) (gradient v p) =
      u p * laplacian v p + v p * laplacian u p +
        2 * dot (gradient u p) (gradient v p) := by
  unfold dot
  ring

theorem gap7 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) (hv : C2At v p) :
    divergence (scalarFieldMul u (gradient v)) p +
        divergence (scalarFieldMul v (gradient u)) p =
      u p * laplacian v p + v p * laplacian u p +
        2 * dot (gradient u p) (gradient v p) := by
  calc
    divergence (scalarFieldMul u (gradient v)) p +
        divergence (scalarFieldMul v (gradient u)) p =
      u p * laplacian v p + dot (gradient u p) (gradient v p) +
        v p * laplacian u p + dot (gradient u p) (gradient v p) :=
      gap5 u v p hu hv
    _ = u p * laplacian v p + v p * laplacian u p +
        2 * dot (gradient u p) (gradient v p) := gap6 u v p

theorem gap8 (u v : Vec3 → ℝ) (p : Vec3)
    (hu : C2At u p) (hv : C2At v p) :
    laplacian (fun q => u q * v q) p =
      u p * laplacian v p + v p * laplacian u p +
        2 * dot (gradient u p) (gradient v p) := by
  calc
    laplacian (fun q => u q * v q) p =
        divergence (scalarFieldMul u (gradient v)) p +
          divergence (scalarFieldMul v (gradient u)) p := gap4 u v p hu hv
    _ = u p * laplacian v p + v p * laplacian u p +
        2 * dot (gradient u p) (gradient v p) := gap7 u v p hu hv

end

end ProofGap.Exercise4414
