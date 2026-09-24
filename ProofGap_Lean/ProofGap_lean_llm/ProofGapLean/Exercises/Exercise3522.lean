import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise3522

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def coordX (x y : ℝ) : ℝ := x / y

def coordY (x y : ℝ) : ℝ := -1 / y

def pullback (U : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  U (coordX x y) (coordY x y) / Real.sqrt y *
    Real.exp (-x ^ 2 / (4 * y))

def heatExpression (f : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  partialXX f x y = partialY f x y

private theorem hasDerivAt_comp_two
    (U : ℝ → ℝ → ℝ) (a b : ℝ → ℝ) (x da db : ℝ)
    (hU : Differentiable ℝ (Function.uncurry U))
    (ha : HasDerivAt a da x) (hb : HasDerivAt b db x) :
    HasDerivAt (fun t => U (a t) (b t))
      (partialX U (a x) (b x) * da + partialY U (a x) (b x) * db) x := by
  let F' := fderiv ℝ (Function.uncurry U) (a x, b x)
  have hF : HasFDerivAt (Function.uncurry U) F' (a x, b x) :=
    hU.differentiableAt.hasFDerivAt
  have hab := ha.hasFDerivAt.prodMk hb.hasFDerivAt
  have hc := hF.comp x hab
  have hxF : partialX U (a x) (b x) = F' (1, 0) := by
    have hs := hF.comp (a x)
      ((hasDerivAt_id (a x)).hasFDerivAt.prodMk
        (hasDerivAt_const (a x) (b x)).hasFDerivAt)
    simpa [partialX, Function.comp_def] using hs.hasDerivAt.deriv
  have hyF : partialY U (a x) (b x) = F' (0, 1) := by
    have hs := hF.comp (b x)
      ((hasDerivAt_const (b x) (a x)).hasFDerivAt.prodMk
        (hasDerivAt_id (b x)).hasFDerivAt)
    simpa [partialY, Function.comp_def] using hs.hasDerivAt.deriv
  have hlin : F' (da, db) =
      partialX U (a x) (b x) * da + partialY U (a x) (b x) * db := by
    rw [show (da, db) = da • (1, 0) + db • (0, 1) by ext <;> simp,
      map_add, map_smul, map_smul, ← hxF, ← hyF]
    simp [mul_comm]
  have hcd : HasDerivAt (fun t => U (a t) (b t)) (F' (da, db)) x := by
    simpa [Function.comp_def] using hc.hasDerivAt
  rw [hlin] at hcd
  exact hcd

private theorem differential_coord_formula
    (U : ℝ → ℝ → ℝ) (x y dx dy : ℝ) (hy : y ≠ 0) (hUC2 : C2 U) :
    differential (fun a b => U (coordX a b) (coordY a b)) x y dx dy =
      partialX U (coordX x y) (coordY x y) *
          (1 / y * dx - x / y ^ 2 * dy) +
        partialY U (coordX x y) (coordY x y) * (1 / y ^ 2 * dy) := by
  have hx : HasDerivAt (fun t : ℝ => coordX t y) (1 / y) x := by
    unfold coordX
    simpa [id_eq] using (hasDerivAt_id x).div_const y
  have hxy : HasDerivAt (fun t : ℝ => coordX x t) (-x / y ^ 2) y := by
    unfold coordX
    simpa [id_eq] using
      (hasDerivAt_const y x).div (hasDerivAt_id y) hy
  have hqx : HasDerivAt (fun t : ℝ => coordY t y) 0 x := by
    unfold coordY
    exact hasDerivAt_const x _
  have hqy : HasDerivAt (fun t : ℝ => coordY x t) (1 / y ^ 2) y := by
    unfold coordY
    simpa [id_eq] using
      (hasDerivAt_const y (-1 : ℝ)).div (hasDerivAt_id y) hy
  have hcx := hasDerivAt_comp_two U (fun t => coordX t y)
    (fun t => coordY t y) x (1 / y) 0 hUC2.1 hx hqx
  have hcy := hasDerivAt_comp_two U (fun t => coordX x t)
    (fun t => coordY x t) y (-x / y ^ 2) (1 / y ^ 2) hUC2.1 hxy hqy
  unfold differential
  change deriv (fun t => U (coordX t y) (coordY t y)) x * dx +
      deriv (fun t => U (coordX x t) (coordY x t)) y * dy = _
  rw [hcx.deriv, hcy.deriv]
  ring

private theorem partialX_pullback_formula
    (U : ℝ → ℝ → ℝ) (x y : ℝ) (hy : 0 < y)
    (hU : Differentiable ℝ (Function.uncurry U)) :
    partialX (pullback U) x y =
      Real.exp (-x ^ 2 / (4 * y)) / Real.sqrt y *
        (partialX U (coordX x y) (coordY x y) / y -
          x * U (coordX x y) (coordY x y) / (2 * y)) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hx : HasDerivAt (fun t : ℝ => coordX t y) (1 / y) x := by
    unfold coordX
    simpa [id_eq] using (hasDerivAt_id x).div_const y
  have hq : HasDerivAt (fun t : ℝ => coordY t y) 0 x := by
    unfold coordY
    exact hasDerivAt_const x _
  have hA := hasDerivAt_comp_two U (fun t => coordX t y)
    (fun t => coordY t y) x (1 / y) 0 hU hx hq
  have hphi : HasDerivAt (fun t : ℝ => -t ^ 2 / (4 * y)) (-x / (2 * y)) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (4 * y) using 1 <;>
      simp [id_eq] <;> ring
  have hp := (hA.div_const (Real.sqrt y)).mul hphi.exp
  have hd := hp.deriv
  change deriv (fun t => U (coordX t y) (coordY t y) / Real.sqrt y *
      Real.exp (-t ^ 2 / (4 * y))) x = _ at hd
  simp [id_eq] at hd
  change deriv (fun t => U (coordX t y) (coordY t y) / Real.sqrt y *
      Real.exp (-t ^ 2 / (4 * y))) x = _
  rw [hd]
  field_simp [hy0, hsq] <;> ring

private theorem partialY_pullback_formula
    (U : ℝ → ℝ → ℝ) (x y : ℝ) (hy : 0 < y)
    (hU : Differentiable ℝ (Function.uncurry U)) :
    partialY (pullback U) x y =
      Real.exp (-x ^ 2 / (4 * y)) / Real.sqrt y *
        (-x * partialX U (coordX x y) (coordY x y) / y ^ 2 +
          partialY U (coordX x y) (coordY x y) / y ^ 2 +
          x ^ 2 * U (coordX x y) (coordY x y) / (4 * y ^ 2) -
          U (coordX x y) (coordY x y) / (2 * y)) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hp : HasDerivAt (fun t : ℝ => coordX x t) (-x / y ^ 2) y := by
    unfold coordX
    simpa [id_eq] using
      (hasDerivAt_const y x).div (hasDerivAt_id y) hy0
  have hq : HasDerivAt (fun t : ℝ => coordY x t) (1 / y ^ 2) y := by
    unfold coordY
    simpa [id_eq] using
      (hasDerivAt_const y (-1 : ℝ)).div (hasDerivAt_id y) hy0
  have hA := hasDerivAt_comp_two U (fun t => coordX x t)
    (fun t => coordY x t) y (-x / y ^ 2) (1 / y ^ 2) hU hp hq
  have hs := Real.hasDerivAt_sqrt hy0
  have hphi : HasDerivAt (fun t : ℝ => -x ^ 2 / (4 * t))
      (x ^ 2 / (4 * y ^ 2)) y := by
    convert (hasDerivAt_const y (-x ^ 2 / 4)).div (hasDerivAt_id y) hy0 using 1 <;>
      (try funext t) <;>
      simp [id_eq, div_eq_mul_inv] <;>
      ring_nf
  have hpb := (hA.div hs hsq).mul hphi.exp
  have hd := hpb.deriv
  change deriv (fun t => U (coordX x t) (coordY x t) / Real.sqrt t *
      Real.exp (-x ^ 2 / (4 * t))) y = _ at hd
  simp [id_eq] at hd
  change deriv (fun t => U (coordX x t) (coordY x t) / Real.sqrt t *
      Real.exp (-x ^ 2 / (4 * t))) y = _
  rw [hd]
  field_simp [hy0, hsq] <;>
    ring_nf <;>
    simp [Real.sq_sqrt hy.le] <;>
    ring <;>
    simp

private theorem partialXX_pullback_formula
    (U : ℝ → ℝ → ℝ) (x y : ℝ) (hy : 0 < y) (hUC2 : C2 U) :
    partialXX (pullback U) x y =
      Real.exp (-x ^ 2 / (4 * y)) / Real.sqrt y *
        (partialXX U (coordX x y) (coordY x y) / y ^ 2 -
          x * partialX U (coordX x y) (coordY x y) / y ^ 2 +
          x ^ 2 * U (coordX x y) (coordY x y) / (4 * y ^ 2) -
          U (coordX x y) (coordY x y) / (2 * y)) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have hx : HasDerivAt (fun t : ℝ => coordX t y) (1 / y) x := by
    unfold coordX
    simpa [id_eq] using (hasDerivAt_id x).div_const y
  have hq : HasDerivAt (fun t : ℝ => coordY t y) 0 x := by
    unfold coordY
    exact hasDerivAt_const x _
  have hA := hasDerivAt_comp_two U (fun t => coordX t y)
    (fun t => coordY t y) x (1 / y) 0 hUC2.1 hx hq
  have hB := hasDerivAt_comp_two (partialX U) (fun t => coordX t y)
    (fun t => coordY t y) x (1 / y) 0 hUC2.2.1 hx hq
  have hphi : HasDerivAt (fun t : ℝ => -t ^ 2 / (4 * y)) (-x / (2 * y)) x := by
    convert ((hasDerivAt_id x).pow 2).neg.div_const (4 * y) using 1 <;>
      simp [id_eq] <;> ring
  have hinner := (hB.div_const y).sub
    (((hasDerivAt_id x).mul hA).div_const (2 * y))
  have houter := ((hphi.exp).div_const (Real.sqrt y)).mul hinner
  have hxx : partialX (partialX U) (coordX x y) (coordY x y) =
      partialXX U (coordX x y) (coordY x y) := rfl
  change deriv (fun t => partialX (pullback U) t y) x = _
  rw [show (fun t => partialX (pullback U) t y) =
      fun t => Real.exp (-t ^ 2 / (4 * y)) / Real.sqrt y *
        (partialX U (coordX t y) (coordY t y) / y -
          t * U (coordX t y) (coordY t y) / (2 * y)) by
    funext t
    exact partialX_pullback_formula U t y hy hUC2.1]
  have hd := houter.deriv
  change deriv (fun t => Real.exp (-t ^ 2 / (4 * y)) / Real.sqrt y *
      (partialX U (coordX t y) (coordY t y) / y -
        t * U (coordX t y) (coordY t y) / (2 * y))) x = _ at hd
  simp [id_eq] at hd
  rw [hxx] at hd
  rw [hd]
  field_simp [hy0, hsq] <;> ring

theorem gap1 (x y dx dy : ℝ)
    (hy : y ≠ 0) :
    differential coordX x y dx dy =
      1 / y * dx - x / y ^ 2 * dy := by
  have hx : HasDerivAt (fun t : ℝ => coordX t y) (1 / y) x := by
    unfold coordX
    simpa [id_eq] using (hasDerivAt_id x).div_const y
  have hy' : HasDerivAt (fun t : ℝ => coordX x t) (-x / y ^ 2) y := by
    unfold coordX
    simpa [id_eq] using
      (hasDerivAt_const y x).div (hasDerivAt_id y) hy
  unfold differential
  change deriv (fun t : ℝ => coordX t y) x * dx +
      deriv (fun t : ℝ => coordX x t) y * dy = _
  rw [hx.deriv, hy'.deriv]
  ring

theorem gap2 (x y dx dy : ℝ)
    (hy : y ≠ 0) :
    differential coordY x y dx dy =
      1 / y ^ 2 * dy := by
  have hx : HasDerivAt (fun t : ℝ => coordY t y) 0 x := by
    unfold coordY
    exact hasDerivAt_const x _
  have hy' : HasDerivAt (fun t : ℝ => coordY x t) (1 / y ^ 2) y := by
    unfold coordY
    simpa [id_eq] using
      (hasDerivAt_const y (-1 : ℝ)).div (hasDerivAt_id y) hy
  unfold differential
  change deriv (fun t : ℝ => coordY t y) x * dx +
      deriv (fun t : ℝ => coordY x t) y * dy = _
  rw [hx.deriv, hy'.deriv]
  ring

theorem gap3 (u U : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y) (hu : 0 < u x y)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b) :
    Real.log (U (coordX x y) (coordY x y)) =
      Real.log (u x y) + (1 : ℝ) / 2 * Real.log y + x ^ 2 / (4 * y) := by
  have hsq : 0 < Real.sqrt y := Real.sqrt_pos.2 hy
  have he : 0 < Real.exp (-x ^ 2 / (4 * y)) := Real.exp_pos _
  have ht := hTransform x y hy
  have hmul : 0 < U (coordX x y) (coordY x y) / Real.sqrt y *
      Real.exp (-x ^ 2 / (4 * y)) := by
    rw [ht] at hu
    unfold pullback at hu
    exact hu
  have hdiv : 0 < U (coordX x y) (coordY x y) / Real.sqrt y :=
    pos_of_mul_pos_left hmul he.le
  have hU : 0 < U (coordX x y) (coordY x y) := by
    rcases div_pos_iff.mp hdiv with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge hsq.le) hneg.2)
  have hlu :
      Real.log (u x y) =
        Real.log (U (coordX x y) (coordY x y)) -
          Real.log (Real.sqrt y) - x ^ 2 / (4 * y) := by
    rw [ht]
    unfold pullback
    rw [Real.log_mul (div_ne_zero hU.ne' hsq.ne') he.ne',
      Real.log_div hU.ne' hsq.ne', Real.log_exp]
    ring
  rw [Real.log_sqrt hy.le] at hlu
  linarith

theorem gap4 (u U : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hy : 0 < y) (hu : 0 < u x y)
    (huC2 : C2 u) (hUC2 : C2 U)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b) :
    differential (fun a b => U (coordX a b) (coordY a b)) x y dx dy =
      U (coordX x y) (coordY x y) / u x y * differential u x y dx dy +
        U (coordX x y) (coordY x y) / (2 * y) * dy +
        x * U (coordX x y) (coordY x y) / (2 * y) * dx -
        x ^ 2 * U (coordX x y) (coordY x y) / (4 * y ^ 2) * dy := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have he : Real.exp (-x ^ 2 / (4 * y)) ≠ 0 := (Real.exp_pos _).ne'
  have hU : U (coordX x y) (coordY x y) ≠ 0 := by
    intro h
    have ht := hTransform x y hy
    unfold pullback at ht
    rw [h, zero_div, zero_mul] at ht
    exact hu.ne' ht
  have hux : partialX u x y = partialX (pullback U) x y := by
    unfold partialX
    rw [show (fun t => u t y) = fun t => pullback U t y by
      funext t
      exact hTransform t y hy]
  have huy : partialY u x y = partialY (pullback U) x y := by
    unfold partialY
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact hTransform x t ht
  rw [differential_coord_formula U x y dx dy hy0 hUC2]
  unfold differential
  rw [hux, huy, partialX_pullback_formula U x y hy hUC2.1,
    partialY_pullback_formula U x y hy hUC2.1]
  have ht := hTransform x y hy
  rw [ht]
  unfold pullback
  field_simp [hy0, hsq, he, hU] <;> ring

theorem gap5 (u U : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hy : y ≠ 0)
    (hUC2 : C2 U) :
    differential (fun a b => U (coordX a b) (coordY a b)) x y dx dy =
      partialX U (coordX x y) (coordY x y) *
          (1 / y * dx - x / y ^ 2 * dy) +
        partialY U (coordX x y) (coordY x y) * (1 / y ^ 2 * dy) := by
  exact differential_coord_formula U x y dx dy hy hUC2

theorem gap6 (u U : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hy : 0 < y) (hu : 0 < u x y)
    (huC2 : C2 u) (hUC2 : C2 U)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b) :
    differential u x y dx dy =
      (u x y / (y * U (coordX x y) (coordY x y)) *
            partialX U (coordX x y) (coordY x y) -
          x * u x y / (2 * y)) * dx +
        (u x y / (y ^ 2 * U (coordX x y) (coordY x y)) *
            partialY U (coordX x y) (coordY x y) -
          x * u x y / (y ^ 2 * U (coordX x y) (coordY x y)) *
            partialX U (coordX x y) (coordY x y) +
          x ^ 2 * u x y / (4 * y ^ 2) - u x y / (2 * y)) * dy := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hU : U (coordX x y) (coordY x y) ≠ 0 := by
    intro h
    have ht := hTransform x y hy
    unfold pullback at ht
    rw [h, zero_div, zero_mul] at ht
    exact hu.ne' ht
  have h4 := gap4 u U x y dx dy hy hu huC2 hUC2 hTransform
  have h5 := gap5 u U x y dx dy hy0 hUC2
  rw [h5] at h4
  unfold differential at h4 ⊢
  field_simp [hy0, hu.ne', hU] at h4 ⊢
  ring_nf at h4 ⊢
  linarith

theorem gap7 (u U : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y) (hu : 0 < u x y)
    (huC2 : C2 u) (hUC2 : C2 U)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b) :
    partialX u x y =
      u x y / (y * U (coordX x y) (coordY x y)) *
          partialX U (coordX x y) (coordY x y) -
        x * u x y / (2 * y) := by
  have h := gap6 u U x y 1 0 hy hu huC2 hUC2 hTransform
  unfold differential at h
  convert h using 1 <;> ring

theorem gap8 (u U : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y) (hu : 0 < u x y)
    (huC2 : C2 u) (hUC2 : C2 U)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b) :
    partialY u x y =
      u x y / (y ^ 2 * U (coordX x y) (coordY x y)) *
          partialY U (coordX x y) (coordY x y) -
        x * u x y / (y ^ 2 * U (coordX x y) (coordY x y)) *
          partialX U (coordX x y) (coordY x y) +
        x ^ 2 * u x y / (4 * y ^ 2) - u x y / (2 * y) := by
  have h := gap6 u U x y 0 1 hy hu huC2 hUC2 hTransform
  unfold differential at h
  convert h using 1 <;> ring

theorem gap9 (u U : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y) (hu : 0 < u x y)
    (huC2 : C2 u) (hUC2 : C2 U)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b) :
    partialXX u x y =
      u x y / (y ^ 2 * U (coordX x y) (coordY x y)) *
          partialXX U (coordX x y) (coordY x y) -
        x * u x y / (y ^ 2 * U (coordX x y) (coordY x y)) *
          partialX U (coordX x y) (coordY x y) +
        x ^ 2 * u x y / (4 * y ^ 2) - u x y / (2 * y) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have he : Real.exp (-x ^ 2 / (4 * y)) ≠ 0 := (Real.exp_pos _).ne'
  have hU : U (coordX x y) (coordY x y) ≠ 0 := by
    intro h
    have ht := hTransform x y hy
    unfold pullback at ht
    rw [h, zero_div, zero_mul] at ht
    exact hu.ne' ht
  have huxx : partialXX u x y = partialXX (pullback U) x y := by
    unfold partialXX
    rw [show (fun t => partialX u t y) = fun t => partialX (pullback U) t y by
      funext t
      unfold partialX
      rw [show (fun s => u s y) = fun s => pullback U s y by
        funext s
        exact hTransform s y hy]]
  rw [huxx, partialXX_pullback_formula U x y hy hUC2]
  have ht := hTransform x y hy
  rw [ht]
  unfold pullback
  field_simp [hy0, hsq, he, hU] <;> ring

theorem gap10 (u U : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (huC2 : C2 u) (hUC2 : C2 U)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b)
    (hHeat : heatExpression u x y) :
    heatExpression U (coordX x y) (coordY x y) := by
  have hy0 : y ≠ 0 := ne_of_gt hy
  have hsq : Real.sqrt y ≠ 0 := (Real.sqrt_pos.2 hy).ne'
  have he : Real.exp (-x ^ 2 / (4 * y)) ≠ 0 := (Real.exp_pos _).ne'
  have hfactor : Real.exp (-x ^ 2 / (4 * y)) / Real.sqrt y ≠ 0 :=
    div_ne_zero he hsq
  have huxx : partialXX u x y = partialXX (pullback U) x y := by
    unfold partialXX
    rw [show (fun t => partialX u t y) = fun t => partialX (pullback U) t y by
      funext t
      unfold partialX
      rw [show (fun s => u s y) = fun s => pullback U s y by
        funext s
        exact hTransform s y hy]]
  have huy : partialY u x y = partialY (pullback U) x y := by
    unfold partialY
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [Ioi_mem_nhds hy] with t ht
    exact hTransform x t ht
  unfold heatExpression at hHeat ⊢
  rw [huxx, huy, partialXX_pullback_formula U x y hy hUC2,
    partialY_pullback_formula U x y hy hUC2.1] at hHeat
  have hbracket := mul_left_cancel₀ hfactor hHeat
  field_simp [hy0] at hbracket
  ring_nf at hbracket
  linarith

theorem gap11 (u U : ℝ → ℝ → ℝ) (x y : ℝ)
    (hy : 0 < y)
    (huC2 : C2 u) (hUC2 : C2 U)
    (hTransform : ∀ a b, 0 < b → u a b = pullback U a b) :
    heatExpression u x y →
      heatExpression U (coordX x y) (coordY x y) := by
  intro hHeat
  exact gap10 u U x y hy huC2 hUC2 hTransform hHeat

end

end ProofGap.Exercise3522
