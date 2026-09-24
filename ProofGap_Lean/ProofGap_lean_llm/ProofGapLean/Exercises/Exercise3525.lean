import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3525

noncomputable section

def partialX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f t y) x

def partialY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => f x t) y

def partialXX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f t y) x

def partialXY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialX f x t) y

def partialYX (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f t y) x

def partialYY (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  deriv (fun t => partialY f x t) y

def C2 (f : ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ (Function.uncurry f) ∧
    Differentiable ℝ (Function.uncurry (partialX f)) ∧
    Differentiable ℝ (Function.uncurry (partialY f))

def differential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialX f x y * dx + partialY f x y * dy

def secondDifferential (f : ℝ → ℝ → ℝ) (x y dx dy : ℝ) : ℝ :=
  partialXX f x y * dx ^ 2 + 2 * partialXY f x y * dx * dy +
    partialYY f x y * dy ^ 2

def hessianDet (f : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialXX f x y * partialYY f x y - partialXY f x y ^ 2

def coordFirst (x y : ℝ) : ℝ := x

def coordSecond (x y : ℝ) : ℝ := y

def IsLocalInverseX (z X : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  C2 z ∧ C2 X ∧ partialX z x y ≠ 0 ∧
    (∀ᶠ a in nhds x, ∀ᶠ b in nhds y, X b (z a b) = a)

def IsLocalInverseY (z Y : ℝ → ℝ → ℝ) (x y : ℝ) : Prop :=
  C2 z ∧ C2 Y ∧ partialY z x y ≠ 0 ∧
    (∀ᶠ a in nhds x, ∀ᶠ b in nhds y, Y a (z a b) = b)

private theorem eventuallyEq_at_point
    {α β : Type*} [TopologicalSpace α] {f g : α → β} {x : α}
    (h : f =ᶠ[nhds x] g) : f x = g x := by
  exact h.self_of_nhds

private theorem eventually_deriv_eq
    {f g : ℝ → ℝ} {x : ℝ} (h : f =ᶠ[nhds x] g) :
    (fun a => deriv f a) =ᶠ[nhds x] (fun a => deriv g a) := by
  rcases mem_nhds_iff.mp h with ⟨s, hs, hs_open, hxs⟩
  filter_upwards [hs_open.mem_nhds hxs] with a ha
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [hs_open.mem_nhds ha] with b hb
  exact hs hb

private theorem hasDerivAt_partialX
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) : HasDerivAt (fun t => f t y) (partialX f x y) x := by
  have hp := (hasDerivAt_id x).hasFDerivAt.prodMk
    (hasDerivAt_const (x := x) y).hasFDerivAt
  have hc := hf.differentiableAt.hasFDerivAt.comp x hp
  simpa [partialX, Function.comp_def] using hc.differentiableAt.hasDerivAt

private theorem hasDerivAt_partialY
    {f : ℝ → ℝ → ℝ} (hf : Differentiable ℝ (Function.uncurry f))
    (x y : ℝ) : HasDerivAt (fun t => f x t) (partialY f x y) y := by
  have hp := (hasDerivAt_const (x := y) x).hasFDerivAt.prodMk
    (hasDerivAt_id y).hasFDerivAt
  have hc := hf.differentiableAt.hasFDerivAt.comp y hp
  simpa [partialY, Function.comp_def] using hc.differentiableAt.hasDerivAt

private theorem compose_real_hasDerivAt
    {f g : ℝ → ℝ} {x f' g' : ℝ}
    (hf : HasDerivAt f f' (g x)) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => f (g t)) (f' * g') x := by
  simpa [Function.comp_def, mul_comm] using
    ((hf.hasFDerivAt.comp x hg.hasFDerivAt).hasDerivAt)

private theorem hasDerivAt_uncurry
    {f : ℝ → ℝ → ℝ} {u v : ℝ → ℝ} {t du dv : ℝ}
    (hf : Differentiable ℝ (Function.uncurry f))
    (hu : HasDerivAt u du t) (hv : HasDerivAt v dv t) :
    HasDerivAt (fun s => f (u s) (v s))
      (partialX f (u t) (v t) * du + partialY f (u t) (v t) * dv) t := by
  let F : ℝ × ℝ → ℝ := Function.uncurry f
  let L : (ℝ × ℝ) →L[ℝ] ℝ := fderiv ℝ F (u t, v t)
  have hF : HasFDerivAt F L (u t, v t) := hf.differentiableAt.hasFDerivAt
  have hx0 : HasDerivAt (fun s => f (u s) (v s)) (L (du, dv)) t := by
    simpa [F, Function.comp_def] using
      ((hF.comp t (hu.hasFDerivAt.prodMk hv.hasFDerivAt)).hasDerivAt)
  have hx : L (1, 0) = partialX f (u t) (v t) := by
    have hp := (hasDerivAt_id (u t)).hasFDerivAt.prodMk
      (hasDerivAt_const (x := u t) (v t)).hasFDerivAt
    have hc : HasDerivAt (fun s => f s (v t)) (L (1, 0)) (u t) := by
      simpa [F, Function.comp_def] using
        ((hF.comp (u t) hp).hasDerivAt)
    simpa [partialX] using hc.deriv.symm
  have hy : L (0, 1) = partialY f (u t) (v t) := by
    have hp := (hasDerivAt_const (x := v t) (u t)).hasFDerivAt.prodMk
      (hasDerivAt_id (v t)).hasFDerivAt
    have hc : HasDerivAt (fun s => f (u t) s) (L (0, 1)) (v t) := by
      simpa [F, Function.comp_def] using
        ((hF.comp (v t) hp).hasDerivAt)
    simpa [partialY] using hc.deriv.symm
  have hsplit : (du, dv) = du • (1, 0) + dv • (0, 1) := by
    ext <;> simp
  have hcoef : L (du, dv) =
      partialX f (u t) (v t) * du + partialY f (u t) (v t) * dv := by
    rw [hsplit, map_add, map_smul, map_smul, hx, hy]
    simp [smul_eq_mul, mul_comm]
  exact hx0.congr_deriv hcoef

private theorem inverseX_second_x
    (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y) :
    partialXX z x y = -partialX z x y ^ 3 * partialYY X y (z x y) := by
  let hz : C2 z := hInv.1
  let hX : C2 X := hInv.2.1
  have hrel := hInv.2.2.2
  have heq : (fun a => X y (z a y)) =ᶠ[nhds x] (fun a => a) := by
    filter_upwards [hrel] with a ha
    exact ha.self_of_nhds
  have hprod :
      (fun a => partialY X y (z a y) * partialX z a y) =ᶠ[nhds x]
        (fun _ => 1) := by
    filter_upwards [eventually_deriv_eq heq] with a ha
    calc
      partialY X y (z a y) * partialX z a y =
          deriv (fun t => X y (z t y)) a := by
            symm
            simpa [Function.comp_def] using
              ((compose_real_hasDerivAt
                (g := fun t => z t y) (x := a)
                (hasDerivAt_partialY hX.1 y (z a y))
                (hasDerivAt_partialX hz.1 a y)).deriv)
      _ = deriv (fun t : ℝ => t) a := ha
      _ = 1 := (hasDerivAt_id a).deriv
  have hA : partialY X y (z x y) * partialX z x y = 1 :=
    eventuallyEq_at_point hprod
  have hsecond :
      (partialYY X y (z x y) * partialX z x y) * partialX z x y +
        partialY X y (z x y) * partialXX z x y = 0 := by
    calc
      _ = deriv (fun a => partialY X y (z a y) * partialX z a y) x := by
        symm
        simpa [partialXX, partialYY, partialX, partialY,
          Function.comp_def] using
          (((compose_real_hasDerivAt
            (g := fun t => z t y) (x := x)
            (hasDerivAt_partialY hX.2.2 y (z x y))
            (hasDerivAt_partialX hz.1 x y)).mul
            (hasDerivAt_partialX hz.2.1 x y)).deriv)
      _ = deriv (fun _ : ℝ => 1) x :=
        eventuallyEq_at_point (eventually_deriv_eq hprod)
      _ = 0 := (hasDerivAt_const (x := x) 1).deriv
  have hp : partialX z x y ≠ 0 := hInv.2.2.1
  have hAinv : partialY X y (z x y) = 1 / partialX z x y :=
    (eq_div_iff hp).2 hA
  rw [hAinv] at hsecond
  field_simp [hp] at hsecond
  nlinarith

private theorem inverseX_second_partials
    (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y)) :
    partialXY z x y =
        -partialX z x y *
          (partialX z x y * partialXY X y (z x y) +
            partialX z x y * partialY z x y * partialYY X y (z x y)) ∧
      partialYY z x y =
        -partialX z x y *
          (partialXX X y (z x y) +
            2 * partialY z x y * partialXY X y (z x y) +
            partialY z x y ^ 2 * partialYY X y (z x y)) := by
  let hz : C2 z := hInv.1
  let hX : C2 X := hInv.2.1
  have hrel := hInv.2.2.2
  have heqA : (fun a => X y (z a y)) =ᶠ[nhds x] (fun a => a) := by
    filter_upwards [hrel] with a ha
    exact ha.self_of_nhds
  have hAev :
      (fun a => partialY X y (z a y) * partialX z a y) =ᶠ[nhds x]
        (fun _ => 1) := by
    filter_upwards [eventually_deriv_eq heqA] with a ha
    calc
      partialY X y (z a y) * partialX z a y =
          deriv (fun t => X y (z t y)) a := by
            symm
            simpa [Function.comp_def] using
              ((compose_real_hasDerivAt
                (g := fun t => z t y) (x := a)
                (hasDerivAt_partialY hX.1 y (z a y))
                (hasDerivAt_partialX hz.1 a y)).deriv)
      _ = deriv (fun t : ℝ => t) a := ha
      _ = 1 := (hasDerivAt_id a).deriv
  have hA : partialY X y (z x y) * partialX z x y = 1 :=
    eventuallyEq_at_point hAev
  have heqY : (fun b => X b (z x b)) =ᶠ[nhds y] (fun _ => x) :=
    hrel.self_of_nhds
  have hBevA :
      (fun a => partialX X y (z a y) +
          partialY X y (z a y) * partialY z a y) =ᶠ[nhds x]
        (fun _ => 0) := by
    filter_upwards [hrel] with a ha
    have hd := Filter.EventuallyEq.deriv_eq ha
    have hid : HasDerivAt (fun b : ℝ => b) 1 y := hasDerivAt_id y
    calc
      partialX X y (z a y) + partialY X y (z a y) * partialY z a y =
          deriv (fun b => X b (z a b)) y := by
            symm
            simpa using (hasDerivAt_uncurry hX.1 hid
              (hasDerivAt_partialY hz.1 a y)).deriv
      _ = deriv (fun _ : ℝ => a) y := hd
      _ = 0 := (hasDerivAt_const (x := y) a).deriv
  have hBevY :
      (fun b => partialX X b (z x b) +
          partialY X b (z x b) * partialY z x b) =ᶠ[nhds y]
        (fun _ => 0) := by
    filter_upwards [eventually_deriv_eq heqY] with b hb
    have hid : HasDerivAt (fun t : ℝ => t) 1 b := hasDerivAt_id b
    calc
      partialX X b (z x b) + partialY X b (z x b) * partialY z x b =
          deriv (fun t => X t (z x t)) b := by
            symm
            simpa using (hasDerivAt_uncurry hX.1 hid
              (hasDerivAt_partialY hz.1 x b)).deriv
      _ = deriv (fun _ : ℝ => x) b := hb
      _ = 0 := (hasDerivAt_const (x := b) x).deriv
  have hxyEq :
      partialXY X y (z x y) * partialX z x y +
        (partialYY X y (z x y) * partialX z x y) * partialY z x y +
        partialY X y (z x y) * partialXY z x y = 0 := by
    have hleft :=
      compose_real_hasDerivAt
        (g := fun t => z t y) (x := x)
        (hasDerivAt_partialY hX.2.1 y (z x y))
        (hasDerivAt_partialX hz.1 x y)
    have hright :=
      (compose_real_hasDerivAt
        (g := fun t => z t y) (x := x)
        (hasDerivAt_partialY hX.2.2 y (z x y))
        (hasDerivAt_partialX hz.1 x y)).mul
        (hasDerivAt_partialX hz.2.2 x y)
    have hc :
        deriv (fun a => partialX X y (z a y) +
          partialY X y (z a y) * partialY z a y) x =
          partialXY X y (z x y) * partialX z x y +
            ((partialYY X y (z x y) * partialX z x y) *
                partialY z x y +
              partialY X y (z x y) * partialYX z x y) := by
      simpa [partialXX, partialXY, partialYX, partialYY, partialX, partialY,
        Function.comp_def] using (hleft.add hright).deriv
    rw [hMixedZ] at hc
    have hd :
        deriv (fun a => partialX X y (z a y) +
          partialY X y (z a y) * partialY z a y) x = 0 := by
      calc
        _ = deriv (fun _ : ℝ => 0) x :=
          eventuallyEq_at_point (eventually_deriv_eq hBevA)
        _ = 0 := (hasDerivAt_const (x := x) 0).deriv
    nlinarith [hc, hd]
  have hp : partialX z x y ≠ 0 := hInv.2.2.1
  have hAinv : partialY X y (z x y) = 1 / partialX z x y :=
    (eq_div_iff hp).2 hA
  have hxy : partialXY z x y =
      -partialX z x y *
        (partialX z x y * partialXY X y (z x y) +
          partialX z x y * partialY z x y * partialYY X y (z x y)) := by
    rw [hAinv] at hxyEq
    field_simp [hp] at hxyEq
    nlinarith
  have hyyEq :
      partialXX X y (z x y) +
        partialXY X y (z x y) * partialY z x y +
        (partialYX X y (z x y) +
          partialYY X y (z x y) * partialY z x y) * partialY z x y +
        partialY X y (z x y) * partialYY z x y = 0 := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 y := hasDerivAt_id y
    have hfirst := hasDerivAt_uncurry hX.2.1 hid
      (hasDerivAt_partialY hz.1 x y)
    have hsecond :=
      (hasDerivAt_uncurry hX.2.2 hid
        (hasDerivAt_partialY hz.1 x y)).mul
        (hasDerivAt_partialY hz.2.2 x y)
    have hc :
        deriv (fun b => partialX X b (z x b) +
          partialY X b (z x b) * partialY z x b) y =
          (partialXX X y (z x y) +
              partialXY X y (z x y) * partialY z x y) +
            ((partialYX X y (z x y) +
                partialYY X y (z x y) * partialY z x y) *
                partialY z x y +
              partialY X y (z x y) * partialYY z x y) := by
      simpa [partialXX, partialXY, partialYX, partialYY, partialX, partialY,
        Function.comp_def] using (hfirst.add hsecond).deriv
    have hd :
        deriv (fun b => partialX X b (z x b) +
          partialY X b (z x b) * partialY z x b) y = 0 := by
      calc
        _ = deriv (fun _ : ℝ => 0) y :=
          eventuallyEq_at_point (eventually_deriv_eq hBevY)
        _ = 0 := (hasDerivAt_const (x := y) 0).deriv
    nlinarith [hc, hd]
  have hyy : partialYY z x y =
      -partialX z x y *
        (partialXX X y (z x y) +
          2 * partialY z x y * partialXY X y (z x y) +
          partialY z x y ^ 2 * partialYY X y (z x y)) := by
    rw [hMixedX, hAinv] at hyyEq
    field_simp [hp] at hyyEq
    nlinarith
  exact ⟨hxy, hyy⟩

private theorem inverseY_hessian_zero
    (z Y : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseY z Y x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedY : partialYX Y x (z x y) = partialXY Y x (z x y))
    (hPDE : hessianDet z x y = 0) :
    hessianDet Y x (z x y) = 0 := by
  let hz : C2 z := hInv.1
  let hY : C2 Y := hInv.2.1
  have hrel := hInv.2.2.2
  have heqA : (fun a => Y a (z a y)) =ᶠ[nhds x] (fun _ => y) := by
    filter_upwards [hrel] with a ha
    exact ha.self_of_nhds
  have hAev :
      (fun a => partialX Y a (z a y) +
          partialY Y a (z a y) * partialX z a y) =ᶠ[nhds x]
        (fun _ => 0) := by
    filter_upwards [eventually_deriv_eq heqA] with a ha
    have hid : HasDerivAt (fun t : ℝ => t) 1 a := hasDerivAt_id a
    calc
      partialX Y a (z a y) + partialY Y a (z a y) * partialX z a y =
          deriv (fun t => Y t (z t y)) a := by
            symm
            simpa using (hasDerivAt_uncurry hY.1 hid
              (hasDerivAt_partialX hz.1 a y)).deriv
      _ = deriv (fun _ : ℝ => y) a := ha
      _ = 0 := (hasDerivAt_const (x := a) y).deriv
  have heqB : (fun b => Y x (z x b)) =ᶠ[nhds y] (fun b => b) :=
    hrel.self_of_nhds
  have hBevA :
      (fun a => partialY Y a (z a y) * partialY z a y) =ᶠ[nhds x]
        (fun _ => 1) := by
    filter_upwards [hrel] with a ha
    have hd := Filter.EventuallyEq.deriv_eq ha
    calc
      partialY Y a (z a y) * partialY z a y =
          deriv (fun b => Y a (z a b)) y := by
            symm
            simpa [Function.comp_def] using
              ((compose_real_hasDerivAt
                (g := fun t => z a t) (x := y)
                (hasDerivAt_partialY hY.1 a (z a y))
                (hasDerivAt_partialY hz.1 a y)).deriv)
      _ = deriv (fun b : ℝ => b) y := hd
      _ = 1 := (hasDerivAt_id y).deriv
  have hB : partialY Y x (z x y) * partialY z x y = 1 :=
    eventuallyEq_at_point hBevA
  have hBevY :
      (fun b => partialY Y x (z x b) * partialY z x b) =ᶠ[nhds y]
        (fun _ => 1) := by
    filter_upwards [eventually_deriv_eq heqB] with b hb
    calc
      partialY Y x (z x b) * partialY z x b =
          deriv (fun t => Y x (z x t)) b := by
            symm
            simpa [Function.comp_def] using
              ((compose_real_hasDerivAt
                (g := fun t => z x t) (x := b)
                (hasDerivAt_partialY hY.1 x (z x b))
                (hasDerivAt_partialY hz.1 x b)).deriv)
      _ = deriv (fun t : ℝ => t) b := hb
      _ = 1 := (hasDerivAt_id b).deriv
  have hxxEq :
      partialXX Y x (z x y) +
        partialXY Y x (z x y) * partialX z x y +
        (partialYX Y x (z x y) +
          partialYY Y x (z x y) * partialX z x y) * partialX z x y +
        partialY Y x (z x y) * partialXX z x y = 0 := by
    have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
    have hfirst := hasDerivAt_uncurry hY.2.1 hid
      (hasDerivAt_partialX hz.1 x y)
    have hsecond :=
      (hasDerivAt_uncurry hY.2.2 hid
        (hasDerivAt_partialX hz.1 x y)).mul
        (hasDerivAt_partialX hz.2.1 x y)
    have hc :
        deriv (fun a => partialX Y a (z a y) +
          partialY Y a (z a y) * partialX z a y) x =
          (partialXX Y x (z x y) +
              partialXY Y x (z x y) * partialX z x y) +
            ((partialYX Y x (z x y) +
                partialYY Y x (z x y) * partialX z x y) *
                partialX z x y +
              partialY Y x (z x y) * partialXX z x y) := by
      simpa [partialXX, partialXY, partialYX, partialYY, partialX, partialY,
        Function.comp_def] using (hfirst.add hsecond).deriv
    have hd :
        deriv (fun a => partialX Y a (z a y) +
          partialY Y a (z a y) * partialX z a y) x = 0 := by
      calc
        _ = deriv (fun _ : ℝ => 0) x :=
          eventuallyEq_at_point (eventually_deriv_eq hAev)
        _ = 0 := (hasDerivAt_const (x := x) 0).deriv
    nlinarith [hc, hd]
  have hp : partialY z x y ≠ 0 := hInv.2.2.1
  have hBinv : partialY Y x (z x y) = 1 / partialY z x y :=
    (eq_div_iff hp).2 hB
  have hxx : partialXX z x y =
      -partialY z x y *
        (partialXX Y x (z x y) +
          2 * partialX z x y * partialXY Y x (z x y) +
          partialX z x y ^ 2 * partialYY Y x (z x y)) := by
    rw [hMixedY, hBinv] at hxxEq
    field_simp [hp] at hxxEq
    nlinarith
  have hxyEq :
      (partialYX Y x (z x y) +
          partialYY Y x (z x y) * partialX z x y) * partialY z x y +
        partialY Y x (z x y) * partialXY z x y = 0 := by
    have hleft :=
      (hasDerivAt_uncurry hY.2.2 (hasDerivAt_id x)
        (hasDerivAt_partialX hz.1 x y)).mul
        (hasDerivAt_partialX hz.2.2 x y)
    have hc :
        deriv (fun a => partialY Y a (z a y) * partialY z a y) x =
          (partialYX Y x (z x y) +
              partialYY Y x (z x y) * partialX z x y) *
              partialY z x y +
            partialY Y x (z x y) * partialYX z x y := by
      simpa [partialXX, partialXY, partialYX, partialYY, partialX, partialY,
        Function.comp_def] using hleft.deriv
    rw [hMixedZ] at hc
    have hd :
        deriv (fun a => partialY Y a (z a y) * partialY z a y) x = 0 := by
      calc
        _ = deriv (fun _ : ℝ => 1) x :=
          eventuallyEq_at_point (eventually_deriv_eq hBevA)
        _ = 0 := (hasDerivAt_const (x := x) 1).deriv
    nlinarith [hc, hd]
  have hxy : partialXY z x y =
      -partialY z x y *
        (partialY z x y * partialXY Y x (z x y) +
          partialY z x y * partialX z x y * partialYY Y x (z x y)) := by
    rw [hMixedY, hBinv] at hxyEq
    field_simp [hp] at hxyEq
    nlinarith
  have hyyEq :
      (partialYY Y x (z x y) * partialY z x y) * partialY z x y +
        partialY Y x (z x y) * partialYY z x y = 0 := by
    calc
      _ = deriv
          (fun b => partialY Y x (z x b) * partialY z x b) y := by
        symm
        simpa [partialYY, partialY, Function.comp_def] using
          (((compose_real_hasDerivAt
            (g := fun t => z x t) (x := y)
            (hasDerivAt_partialY hY.2.2 x (z x y))
            (hasDerivAt_partialY hz.1 x y)).mul
            (hasDerivAt_partialY hz.2.2 x y)).deriv)
      _ = deriv (fun _ : ℝ => 1) y :=
        eventuallyEq_at_point (eventually_deriv_eq hBevY)
      _ = 0 := (hasDerivAt_const (x := y) 1).deriv
  have hyy : partialYY z x y =
      -partialY z x y ^ 3 * partialYY Y x (z x y) := by
    rw [hBinv] at hyyEq
    field_simp [hp] at hyyEq
    nlinarith
  have htransform : hessianDet z x y =
      partialY z x y ^ 4 * hessianDet Y x (z x y) := by
    rw [hessianDet, hessianDet, hxx, hxy, hyy]
    ring
  have hm : partialY z x y ^ 4 * hessianDet Y x (z x y) = 0 := by
    rw [← htransform]
    exact hPDE
  have hpow : partialY z x y ^ 4 ≠ 0 := pow_ne_zero 4 hp
  exact (mul_eq_zero.mp hm).resolve_left hpow

theorem gap1 (z : ℝ → ℝ → ℝ) :
    ∀ x y dx dy,
      differential z x y dx dy =
        partialX z x y * dx + partialY z x y * dy := by
  intros x y dx dy
  rfl

theorem gap2 :
    ∀ x y dx dy,
      secondDifferential coordFirst x y dx dy = 0 := by
  intros x y dx dy
  simp [secondDifferential, coordFirst, partialXX, partialXY, partialYY,
    partialX, partialY]

theorem gap3 :
    ∀ x y dx dy,
      secondDifferential coordSecond x y dx dy = 0 := by
  intros x y dx dy
  simp [secondDifferential, coordSecond, partialXX, partialXY, partialYY,
    partialX, partialY]

theorem gap4 (X : ℝ → ℝ → ℝ) :
    ∀ y z dy dz,
      secondDifferential X y z dy dz =
        partialXX X y z * dy ^ 2 + 2 * partialXY X y z * dy * dz +
          partialYY X y z * dz ^ 2 := by
  intros y z dy dz
  rfl

theorem gap5 (z X : ℝ → ℝ → ℝ) (x y dx dy : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y)) :
    secondDifferential z x y dx dy =
      -partialX z x y *
        (partialXX X y (z x y) * dy ^ 2 +
          2 * partialXY X y (z x y) * dy *
            (partialX z x y * dx + partialY z x y * dy) +
          partialYY X y (z x y) *
            (partialX z x y * dx + partialY z x y * dy) ^ 2) := by
  have hxx := inverseX_second_x z X x y hInv
  have hs := inverseX_second_partials z X x y hInv hMixedZ hMixedX
  have hxy := hs.1
  have hyy := hs.2
  rw [secondDifferential, hxx, hxy, hyy]
  ring

theorem gap6 (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y) :
    partialXX z x y =
      -partialX z x y ^ 3 * partialYY X y (z x y) := by
  exact inverseX_second_x z X x y hInv

theorem gap7 (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y)) :
    partialXY z x y =
      -partialX z x y *
        (partialX z x y * partialXY X y (z x y) +
          partialX z x y * partialY z x y * partialYY X y (z x y)) := by
  exact (inverseX_second_partials z X x y hInv hMixedZ hMixedX).1

theorem gap8 (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y)) :
    partialYY z x y =
      -partialX z x y *
        (partialXX X y (z x y) +
          2 * partialY z x y * partialXY X y (z x y) +
          partialY z x y ^ 2 * partialYY X y (z x y)) := by
  exact (inverseX_second_partials z X x y hInv hMixedZ hMixedX).2

theorem gap9 (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y)) :
    hessianDet z x y =
      partialX z x y ^ 4 * hessianDet X y (z x y) := by
  have hxx := inverseX_second_x z X x y hInv
  have hs := inverseX_second_partials z X x y hInv hMixedZ hMixedX
  have hxy := hs.1
  have hyy := hs.2
  rw [hessianDet, hessianDet, hxx, hxy, hyy]
  ring

theorem gap10 (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y))
    (hPDE : hessianDet z x y = 0) :
    partialX z x y ^ 4 * hessianDet X y (z x y) = 0 := by
  rw [← gap9 z X x y hInv hMixedZ hMixedX]
  exact hPDE

theorem gap11 (z : ℝ → ℝ → ℝ) (x y : ℝ)
    (hPDE : hessianDet z x y = 0) :
    partialXX z x y * partialYY z x y - partialXY z x y ^ 2 = 0 := by
  simpa [hessianDet] using hPDE

theorem gap12 (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y))
    (hPDE : hessianDet z x y = 0) :
    hessianDet X y (z x y) = 0 := by
  have hm := gap10 z X x y hInv hMixedZ hMixedX hPDE
  have hp : partialX z x y ^ 4 ≠ 0 := pow_ne_zero 4 hInv.2.2.1
  exact (mul_eq_zero.mp hm).resolve_left hp

theorem gap13 (z Y : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseY z Y x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedY : partialYX Y x (z x y) = partialXY Y x (z x y))
    (hPDE : hessianDet z x y = 0) :
    hessianDet Y x (z x y) = 0 := by
  exact inverseY_hessian_zero z Y x y hInv hMixedZ hMixedY hPDE

theorem gap14 (z X : ℝ → ℝ → ℝ) (x y : ℝ)
    (hInv : IsLocalInverseX z X x y)
    (hMixedZ : partialYX z x y = partialXY z x y)
    (hMixedX : partialYX X y (z x y) = partialXY X y (z x y)) :
    hessianDet z x y = 0 → hessianDet X y (z x y) = 0 := by
  intro hPDE
  exact gap12 z X x y hInv hMixedZ hMixedX hPDE

end

end ProofGap.Exercise3525
