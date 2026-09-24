import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3494

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialX (partialX f) x y
def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialX f) x y
def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ := partialY (partialY f) x y

private theorem eventually_partialX_eq
    {f g : ℝ → ℝ → ℝ} {x y : ℝ}
    (hfg : ∀ᶠ p : ℝ × ℝ in nhds (x, y), f p.1 p.2 = g p.1 p.2) :
    ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX f p.1 p.2 = partialX g p.1 p.2 := by
  rcases mem_nhds_iff.1 hfg with ⟨s, hs, hsopen, hxy⟩
  filter_upwards [hsopen.mem_nhds hxy] with p hp
  have hlocal : ∀ᶠ q : ℝ × ℝ in nhds p,
      f q.1 q.2 = g q.1 q.2 :=
    Filter.mem_of_superset (hsopen.mem_nhds hp) hs
  have hpull : (fun t : ℝ => f t p.2) =ᶠ[nhds p.1]
      (fun t : ℝ => g t p.2) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hlocal
  unfold partialX
  exact hpull.deriv_eq

private theorem eventually_partialY_eq
    {f g : ℝ → ℝ → ℝ} {x y : ℝ}
    (hfg : ∀ᶠ p : ℝ × ℝ in nhds (x, y), f p.1 p.2 = g p.1 p.2) :
    ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY f p.1 p.2 = partialY g p.1 p.2 := by
  rcases mem_nhds_iff.1 hfg with ⟨s, hs, hsopen, hxy⟩
  filter_upwards [hsopen.mem_nhds hxy] with p hp
  have hlocal : ∀ᶠ q : ℝ × ℝ in nhds p,
      f q.1 q.2 = g q.1 q.2 :=
    Filter.mem_of_superset (hsopen.mem_nhds hp) hs
  have hpull : (fun t : ℝ => f p.1 t) =ᶠ[nhds p.2]
      (fun t : ℝ => g p.1 t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hlocal
  unfold partialY
  exact hpull.deriv_eq

private theorem hasDerivAt_inv_sqrt
    (y : ℝ) (hy : 0 < y) :
    HasDerivAt (fun t : ℝ => 1 / Real.sqrt t)
      (-(1 / (2 * y * Real.sqrt y))) y := by
  have hsqrt : Real.sqrt y ≠ 0 := Real.sqrt_ne_zero'.mpr hy
  have h :=
    (hasDerivAt_const y (1 : ℝ)).div (Real.hasDerivAt_sqrt hy.ne') hsqrt
  convert h using 1 <;>
    field_simp [hsqrt] <;>
    nlinarith [Real.sq_sqrt hy.le]

private theorem hasDerivAt_comp₂
    (F : ℝ → ℝ → ℝ) (g h : ℝ → ℝ) {x dg dh : ℝ}
    (hF : DifferentiableAt ℝ (Function.uncurry F) (g x, h x))
    (hg : HasDerivAt g dg x) (hh : HasDerivAt h dh x) :
    HasDerivAt (fun t => F (g t) (h t))
      (dg * partialX F (g x) (h x) + dh * partialY F (g x) (h x)) x := by
  let D := fderiv ℝ (Function.uncurry F) (g x, h x)
  have hc := hF.hasFDerivAt.comp x
    (hg.hasFDerivAt.prodMk hh.hasFDerivAt)
  have hc' : HasDerivAt (fun t => F (g t) (h t)) (D (dg, dh)) x := by
    simpa [D, Function.comp_def, Function.uncurry] using hc.hasDerivAt
  have hdx0 : HasDerivAt (fun t : ℝ => F t (h x))
      (D (1, 0)) (g x) := by
    have hx := hF.hasFDerivAt.comp (g x)
      ((hasDerivAt_id (g x)).hasFDerivAt.prodMk
        (hasDerivAt_const (g x) (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hx.hasDerivAt
  have hdx : partialX F (g x) (h x) = D (1, 0) := by
    change deriv (fun t : ℝ => F t (h x)) (g x) = D (1, 0)
    exact hdx0.deriv
  have hdy0 : HasDerivAt (fun t : ℝ => F (g x) t)
      (D (0, 1)) (h x) := by
    have hy := hF.hasFDerivAt.comp (h x)
      ((hasDerivAt_const (h x) (g x)).hasFDerivAt.prodMk
        (hasDerivAt_id (h x)).hasFDerivAt)
    simpa [D, Function.comp_def, Function.uncurry] using hy.hasDerivAt
  have hdy : partialY F (g x) (h x) = D (0, 1) := by
    change deriv (fun t : ℝ => F (g x) t) (h x) = D (0, 1)
    exact hdy0.deriv
  have hlin : D (dg, dh) = dg * D (1, 0) + dh * D (0, 1) := by
    calc
      D (dg, dh) = D (dg • (1, 0) + dh • (0, 1)) := by
        congr 1
        ext <;> simp
      _ = dg • D (1, 0) + dh • D (0, 1) := by
        rw [map_add, map_smul, map_smul]
      _ = dg * D (1, 0) + dh * D (0, 1) := by simp
  convert hc' using 1
  simpa [hdx, hdy] using hlin.symm

private theorem mixed_partial_comm
    {f : ℝ → ℝ → ℝ} {x y : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (x, y)) :
    partialX (partialY f) x y = partialXY f x y := by
  let F := Function.uncurry f
  let D := fderiv ℝ (fderiv ℝ F) (x, y)
  let ex : ℝ × ℝ := (1, 0)
  let ey : ℝ × ℝ := (0, 1)
  have hnear : ∀ᶠ q : ℝ × ℝ in nhds (x, y),
      ContDiffAt ℝ 2 F q := by
    simpa [F] using h.eventually (by decide)
  have hnearX := (continuousAt_id.prodMk continuousAt_const).eventually hnear
  have hnearY := (continuousAt_const.prodMk continuousAt_id).eventually hnear
  have hpartialY : (fun t : ℝ => partialY f t y) =ᶠ[nhds x]
      (fun t : ℝ => (fderiv ℝ F (t, y)) ey) := by
    filter_upwards [hnearX] with t ht
    have hs := (ht.differentiableAt (by decide)).hasFDerivAt.comp y
      ((hasDerivAt_const y t).hasFDerivAt.prodMk
        (hasDerivAt_id y).hasFDerivAt)
    unfold partialY
    simpa [F, ey, Function.comp_def, Function.uncurry] using hs.hasDerivAt.deriv
  have hpartialX : (fun t : ℝ => partialX f x t) =ᶠ[nhds y]
      (fun t : ℝ => (fderiv ℝ F (x, t)) ex) := by
    filter_upwards [hnearY] with t ht
    have hs := (ht.differentiableAt (by decide)).hasFDerivAt.comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        (hasDerivAt_const x t).hasFDerivAt)
    unfold partialX
    simpa [F, ex, Function.comp_def, Function.uncurry] using hs.hasDerivAt.deriv
  have hc : ContDiffAt ℝ 1 (fderiv ℝ F) (x, y) := by
    simpa [F] using h.fderiv_right (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ F) (x, y) :=
    hc.differentiableAt (by decide)
  have hFD : HasFDerivAt (fderiv ℝ F) D (x, y) := by
    simpa [D] using hd.hasFDerivAt
  let evY : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ey
  let evX : ((ℝ × ℝ) →L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousLinearMap.apply ℝ ℝ ex
  have hEvalY := evY.hasFDerivAt.comp (x, y) hFD
  have hEvalX := evX.hasFDerivAt.comp (x, y) hFD
  have houtY : HasDerivAt
      (fun t : ℝ => (fderiv ℝ F (t, y)) ey) (D ex ey) x := by
    have hcomp := hEvalY.comp x
      ((hasDerivAt_id x).hasFDerivAt.prodMk
        (hasDerivAt_const x y).hasFDerivAt)
    simpa [evY, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have houtX : HasDerivAt
      (fun t : ℝ => (fderiv ℝ F (x, t)) ex) (D ey ex) y := by
    have hcomp := hEvalX.comp y
      ((hasDerivAt_const y x).hasFDerivAt.prodMk
        (hasDerivAt_id y).hasFDerivAt)
    simpa [evX, ex, ey, Function.comp_def] using hcomp.hasDerivAt
  have hlhs : partialX (partialY f) x y = D ex ey := by
    unfold partialX
    exact hpartialY.deriv_eq.trans houtY.deriv
  have hrhs : partialXY f x y = D ey ex := by
    unfold partialXY partialY
    exact hpartialX.deriv_eq.trans houtX.deriv
  have hsymm : D ex ey = D ey ex := by
    simpa [D, F, ex, ey] using
      h.isSymmSndFDerivAt (by norm_num)
        ((1, 0) : ℝ × ℝ) ((0, 1) : ℝ × ℝ)
  exact hlhs.trans (hsymm.trans hrhs.symm)

theorem gap1 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 - 2 * Real.sqrt p.2) :
    partialX u x y = 1 := by
  have hu : (fun t : ℝ => u t y) =ᶠ[nhds x]
      (fun t : ℝ => t - 2 * Real.sqrt y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hU
  unfold partialX
  exact hu.deriv_eq.trans ((hasDerivAt_id x).sub_const _).deriv

theorem gap2 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 + 2 * Real.sqrt p.2) :
    partialX v x y = 1 := by
  have hv : (fun t : ℝ => v t y) =ᶠ[nhds x]
      (fun t : ℝ => t + 2 * Real.sqrt y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hV
  unfold partialX
  exact hv.deriv_eq.trans ((hasDerivAt_id x).add_const _).deriv

theorem gap3 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 - 2 * Real.sqrt p.2) :
    partialY u x y = -(1 / Real.sqrt y) := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y]
      (fun t : ℝ => x - 2 * Real.sqrt t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have h :=
    (hasDerivAt_const y x).sub ((Real.hasDerivAt_sqrt hy.ne').const_mul 2)
  unfold partialY
  calc
    deriv (fun t : ℝ => u x t) y =
        deriv (fun t : ℝ => x - 2 * Real.sqrt t) y := hu.deriv_eq
    _ = -(1 / Real.sqrt y) := by
      convert h.deriv using 1 <;>
        field_simp [Real.sqrt_ne_zero'.mpr hy] <;> ring

theorem gap4 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 + 2 * Real.sqrt p.2) :
    partialY v x y = 1 / Real.sqrt y := by
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => x + 2 * Real.sqrt t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  have h :=
    (hasDerivAt_const y x).add ((Real.hasDerivAt_sqrt hy.ne').const_mul 2)
  unfold partialY
  calc
    deriv (fun t : ℝ => v x t) y =
        deriv (fun t : ℝ => x + 2 * Real.sqrt t) y := hv.deriv_eq
    _ = 1 / Real.sqrt y := by
      convert h.deriv using 1 <;>
        field_simp [Real.sqrt_ne_zero'.mpr hy] <;> ring

theorem gap5 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 - 2 * Real.sqrt p.2) :
    partialXX u x y = 0 := by
  have hp := (continuousAt_id.prodMk continuousAt_const).eventually
    (eventually_partialX_eq
      (f := u) (g := fun a b : ℝ => a - 2 * Real.sqrt b) hU)
  have hu : (fun t : ℝ => partialX u t y) =ᶠ[nhds x]
      (fun _ : ℝ => 1) := by
    filter_upwards [hp] with t ht
    calc
      partialX u t y =
          partialX (fun a b : ℝ => a - 2 * Real.sqrt b) t y := ht
      _ = 1 := by
        unfold partialX
        exact ((hasDerivAt_id t).sub_const _).deriv
  change deriv (fun t : ℝ => partialX u t y) x = 0
  exact hu.deriv_eq.trans (hasDerivAt_const x (1 : ℝ)).deriv

theorem gap6 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 + 2 * Real.sqrt p.2) :
    partialXX v x y = 0 := by
  have hp := (continuousAt_id.prodMk continuousAt_const).eventually
    (eventually_partialX_eq
      (f := v) (g := fun a b : ℝ => a + 2 * Real.sqrt b) hV)
  have hv : (fun t : ℝ => partialX v t y) =ᶠ[nhds x]
      (fun _ : ℝ => 1) := by
    filter_upwards [hp] with t ht
    calc
      partialX v t y =
          partialX (fun a b : ℝ => a + 2 * Real.sqrt b) t y := ht
      _ = 1 := by
        unfold partialX
        exact ((hasDerivAt_id t).add_const _).deriv
  change deriv (fun t : ℝ => partialX v t y) x = 0
  exact hv.deriv_eq.trans (hasDerivAt_const x (1 : ℝ)).deriv

theorem gap7 (u : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 - 2 * Real.sqrt p.2) :
    partialYY u x y = 1 / (2 * y * Real.sqrt y) := by
  have hp := (continuousAt_const.prodMk continuousAt_id).eventually
    (eventually_partialY_eq
      (f := u) (g := fun a b : ℝ => a - 2 * Real.sqrt b) hU)
  have hpos : ∀ᶠ t : ℝ in nhds y, 0 < t := eventually_gt_nhds hy
  have hu : (fun t : ℝ => partialY u x t) =ᶠ[nhds y]
      (fun t : ℝ => -(1 / Real.sqrt t)) := by
    filter_upwards [hp, hpos] with t ht htpos
    calc
      partialY u x t =
          partialY (fun a b : ℝ => a - 2 * Real.sqrt b) x t := ht
      _ = -(1 / Real.sqrt t) := by
        unfold partialY
        have h :=
          (hasDerivAt_const t x).sub
            ((Real.hasDerivAt_sqrt htpos.ne').const_mul 2)
        convert h.deriv using 1 <;>
          field_simp [Real.sqrt_ne_zero'.mpr htpos] <;> ring
  change deriv (fun t : ℝ => partialY u x t) y =
    1 / (2 * y * Real.sqrt y)
  exact hu.deriv_eq.trans (by
    simpa only [neg_neg] using (hasDerivAt_inv_sqrt y hy).neg.deriv)

theorem gap8 (v : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 + 2 * Real.sqrt p.2) :
    partialYY v x y = -(1 / (2 * y * Real.sqrt y)) := by
  have hp := (continuousAt_const.prodMk continuousAt_id).eventually
    (eventually_partialY_eq
      (f := v) (g := fun a b : ℝ => a + 2 * Real.sqrt b) hV)
  have hpos : ∀ᶠ t : ℝ in nhds y, 0 < t := eventually_gt_nhds hy
  have hv : (fun t : ℝ => partialY v x t) =ᶠ[nhds y]
      (fun t : ℝ => 1 / Real.sqrt t) := by
    filter_upwards [hp, hpos] with t ht htpos
    calc
      partialY v x t =
          partialY (fun a b : ℝ => a + 2 * Real.sqrt b) x t := ht
      _ = 1 / Real.sqrt t := by
        unfold partialY
        have h :=
          (hasDerivAt_const t x).add
            ((Real.hasDerivAt_sqrt htpos.ne').const_mul 2)
        convert h.deriv using 1 <;>
          field_simp [Real.sqrt_ne_zero'.mpr htpos] <;> ring
  change deriv (fun t : ℝ => partialY v x t) y =
    -(1 / (2 * y * Real.sqrt y))
  exact hv.deriv_eq.trans (hasDerivAt_inv_sqrt y hy).deriv

theorem gap9 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hZx : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialX Z p.1 p.2 =
        partialX z (u p.1 p.2) (v p.1 p.2) +
          partialY z (u p.1 p.2) (v p.1 p.2))
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 - 2 * Real.sqrt p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 + 2 * Real.sqrt p.2) :
    partialXX Z x y =
      partialXX z (u x y) (v x y) +
        2 * partialXY z (u x y) (v x y) +
        partialYY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u t y) =ᶠ[nhds x]
      (fun t : ℝ => t - 2 * Real.sqrt y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hU
  have hv : (fun t : ℝ => v t y) =ᶠ[nhds x]
      (fun t : ℝ => t + 2 * Real.sqrt y) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hV
  have hdu : HasDerivAt (fun t : ℝ => u t y) 1 x :=
    ((hasDerivAt_id x).sub_const _).congr_of_eventuallyEq hu
  have hdv : HasDerivAt (fun t : ℝ => v t y) 1 x :=
    ((hasDerivAt_id x).add_const _).congr_of_eventuallyEq hv
  have hmix : partialX (partialY z) (u x y) (v x y) =
      partialXY z (u x y) (v x y) :=
    mixed_partial_comm hC2z
  have hA := hasDerivAt_comp₂ (partialX z)
    (fun t => u t y) (fun t => v t y) hDiffZu hdu hdv
  have hB := hasDerivAt_comp₂ (partialY z)
    (fun t => u t y) (fun t => v t y) hDiffZv hdu hdv
  have hR := hA.add hB
  have hz : (fun t : ℝ => partialX Z t y) =ᶠ[nhds x]
      (fun t : ℝ =>
        partialX z (u t y) (v t y) +
          partialY z (u t y) (v t y)) := by
    simpa using (continuousAt_id.prodMk continuousAt_const).eventually hZx
  change deriv (fun t : ℝ => partialX Z t y) x = _
  calc
    deriv (fun t : ℝ => partialX Z t y) x =
        deriv (fun t : ℝ =>
          partialX z (u t y) (v t y) +
            partialY z (u t y) (v t y)) x := hz.deriv_eq
    _ = _ := by
      convert hR.deriv using 1 <;>
        simp only [partialXX, partialXY, partialYY] at * <;>
        rw [hmix] <;> ring

theorem gap10 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (hZy : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      partialY Z p.1 p.2 =
        -(1 / Real.sqrt p.2) * partialX z (u p.1 p.2) (v p.1 p.2) +
          1 / Real.sqrt p.2 * partialY z (u p.1 p.2) (v p.1 p.2))
    (hDiffZu : DifferentiableAt ℝ (Function.uncurry (partialX z)) (u x y, v x y))
    (hDiffZv : DifferentiableAt ℝ (Function.uncurry (partialY z)) (u x y, v x y))
    (hC2z : ContDiffAt ℝ 2 (Function.uncurry z) (u x y, v x y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 - 2 * Real.sqrt p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 + 2 * Real.sqrt p.2) :
    partialYY Z x y =
      1 / (2 * y * Real.sqrt y) * partialX z (u x y) (v x y) -
        1 / (2 * y * Real.sqrt y) * partialY z (u x y) (v x y) +
        1 / y * partialXX z (u x y) (v x y) -
        2 / y * partialXY z (u x y) (v x y) +
        1 / y * partialYY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y]
      (fun t : ℝ => x - 2 * Real.sqrt t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => x + 2 * Real.sqrt t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  have hdu0 :=
    (hasDerivAt_const y x).sub ((Real.hasDerivAt_sqrt hy.ne').const_mul 2)
  have hdv0 :=
    (hasDerivAt_const y x).add ((Real.hasDerivAt_sqrt hy.ne').const_mul 2)
  have hdu : HasDerivAt (fun t : ℝ => u x t)
      (-(1 / Real.sqrt y)) y := by
    apply HasDerivAt.congr_of_eventuallyEq _ hu
    convert hdu0 using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hy] <;> ring
  have hdv : HasDerivAt (fun t : ℝ => v x t)
      (1 / Real.sqrt y) y := by
    apply HasDerivAt.congr_of_eventuallyEq _ hv
    convert hdv0 using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hy] <;> ring
  have hmix : partialX (partialY z) (u x y) (v x y) =
      partialXY z (u x y) (v x y) :=
    mixed_partial_comm hC2z
  have hA := hasDerivAt_comp₂ (partialX z)
    (fun t => u x t) (fun t => v x t) hDiffZu hdu hdv
  have hB := hasDerivAt_comp₂ (partialY z)
    (fun t => u x t) (fun t => v x t) hDiffZv hdu hdv
  have hc := hasDerivAt_inv_sqrt y hy
  have hnc : HasDerivAt (fun t : ℝ => -(1 / Real.sqrt t))
      (1 / (2 * y * Real.sqrt y)) y := by
    simpa only [neg_neg] using hc.neg
  have hR := hnc.mul hA |>.add (hc.mul hB)
  have hz : (fun t : ℝ => partialY Z x t) =ᶠ[nhds y]
      (fun t : ℝ =>
        -(1 / Real.sqrt t) * partialX z (u x t) (v x t) +
          1 / Real.sqrt t * partialY z (u x t) (v x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hZy
  have hsqrt : Real.sqrt y ≠ 0 := Real.sqrt_ne_zero'.mpr hy
  change deriv (fun t : ℝ => partialY Z x t) y = _
  calc
    deriv (fun t : ℝ => partialY Z x t) y =
        deriv (fun t : ℝ =>
          -(1 / Real.sqrt t) * partialX z (u x t) (v x t) +
            1 / Real.sqrt t * partialY z (u x t) (v x t)) y := hz.deriv_eq
    _ = _ := by
      convert hR.deriv using 1 <;>
        simp only [partialXX, partialXY, partialYY] at * <;>
        rw [hmix] <;>
        field_simp [hy.ne', hsqrt] <;>
        ring_nf <;>
        rw [Real.sq_sqrt hy.le] <;> ring

theorem gap11 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (hCompose : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      Z p.1 p.2 = z (u p.1 p.2) (v p.1 p.2))
    (hDiffz : DifferentiableAt ℝ (Function.uncurry z) (u x y, v x y))
    (hU : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      u p.1 p.2 = p.1 - 2 * Real.sqrt p.2)
    (hV : ∀ᶠ p : ℝ × ℝ in nhds (x, y),
      v p.1 p.2 = p.1 + 2 * Real.sqrt p.2) :
    partialY Z x y =
      -(1 / Real.sqrt y) * partialX z (u x y) (v x y) +
        1 / Real.sqrt y * partialY z (u x y) (v x y) := by
  have hu : (fun t : ℝ => u x t) =ᶠ[nhds y]
      (fun t : ℝ => x - 2 * Real.sqrt t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hU
  have hv : (fun t : ℝ => v x t) =ᶠ[nhds y]
      (fun t : ℝ => x + 2 * Real.sqrt t) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hV
  have hdu0 :=
    (hasDerivAt_const y x).sub ((Real.hasDerivAt_sqrt hy.ne').const_mul 2)
  have hdv0 :=
    (hasDerivAt_const y x).add ((Real.hasDerivAt_sqrt hy.ne').const_mul 2)
  have hdu : HasDerivAt (fun t : ℝ => u x t)
      (-(1 / Real.sqrt y)) y := by
    apply HasDerivAt.congr_of_eventuallyEq _ hu
    convert hdu0 using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hy] <;> ring
  have hdv : HasDerivAt (fun t : ℝ => v x t)
      (1 / Real.sqrt y) y := by
    apply HasDerivAt.congr_of_eventuallyEq _ hv
    convert hdv0 using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hy] <;> ring
  have hR := hasDerivAt_comp₂ z
    (fun t => u x t) (fun t => v x t) hDiffz hdu hdv
  have hz : (fun t : ℝ => Z x t) =ᶠ[nhds y]
      (fun t : ℝ => z (u x t) (v x t)) := by
    simpa using (continuousAt_const.prodMk continuousAt_id).eventually hCompose
  unfold partialY
  exact hz.deriv_eq.trans hR.deriv

theorem gap12 (u v z Z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (hPDE : partialXX Z x y - y * partialYY Z x y = 1 / 2 * partialY Z x y)
    (hZxx : partialXX Z x y =
      partialXX z (u x y) (v x y) + 2 * partialXY z (u x y) (v x y) +
        partialYY z (u x y) (v x y))
    (hZyy : partialYY Z x y =
      1 / (2 * y * Real.sqrt y) * partialX z (u x y) (v x y) -
        1 / (2 * y * Real.sqrt y) * partialY z (u x y) (v x y) +
        1 / y * partialXX z (u x y) (v x y) -
        2 / y * partialXY z (u x y) (v x y) +
        1 / y * partialYY z (u x y) (v x y))
    (hZy : partialY Z x y =
      -(1 / Real.sqrt y) * partialX z (u x y) (v x y) +
        1 / Real.sqrt y * partialY z (u x y) (v x y)) :
    partialXY z (u x y) (v x y) = 0 := by
  rw [hZxx, hZyy, hZy] at hPDE
  have hsqrt : Real.sqrt y ≠ 0 := Real.sqrt_ne_zero'.mpr hy
  field_simp [hy.ne', hsqrt, Real.sq_sqrt hy.le] at hPDE
  have hsqrtpos : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  nlinarith

end

end ProofGap.Exercise3494
