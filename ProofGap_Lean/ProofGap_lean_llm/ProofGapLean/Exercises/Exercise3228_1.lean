import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise3228_1

noncomputable section

def powerYZ (y z : ℝ) : ℝ :=
  Real.rpow y z

def u (x y z : ℝ) : ℝ :=
  Real.rpow x (powerYZ y z)

def admissible (x y : ℝ) : Prop :=
  0 < x ∧ 0 < y

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def secondXX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f t y z) x

def secondYY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x t z) y

def secondZZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f x y t) z

def mixedXY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f x t z) y

def mixedYZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x y t) z

def mixedZX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f t y z) x

private theorem Real.hasDerivAt_const_rpow {a t : ℝ} (ha : 0 < a) :
    HasDerivAt (fun s : ℝ => Real.rpow a s)
      (Real.rpow a t * Real.log a) t := by
  have hi : HasDerivAt (fun s : ℝ => Real.log a * s) (Real.log a) t := by
    simpa only [zero_mul, zero_add, mul_one] using
      (hasDerivAt_const t (Real.log a)).mul (hasDerivAt_id t)
  have he : HasDerivAt (fun s : ℝ => Real.exp (Real.log a * s))
      (Real.exp (Real.log a * t) * Real.log a) t :=
    (Real.hasDerivAt_exp (Real.log a * t)).comp t hi
  have hfun : (fun s : ℝ => Real.rpow a s) =
      (fun s : ℝ => Real.exp (Real.log a * s)) := by
    funext s
    exact Real.rpow_def_of_pos ha s
  have ht : Real.rpow a t = Real.exp (Real.log a * t) := by
    exact Real.rpow_def_of_pos ha t
  rw [hfun, ht]
  exact he

theorem gap1 :
    ∀ x y z : ℝ, admissible x y →
      partialX u x y z =
        powerYZ y z * Real.rpow x (powerYZ y z - 1) := by
  intro x y z h
  simpa [partialX, u] using
    (Real.hasDerivAt_rpow_const (p := powerYZ y z)
      (Or.inl (ne_of_gt h.1))).deriv

theorem gap2 :
    ∀ y z x : ℝ, admissible x y →
      powerYZ y z * Real.rpow x (powerYZ y z - 1) =
        u x y z * powerYZ y z / x := by
  intro y z x h
  have hpow (s : ℝ) : Real.rpow x s =
      Real.exp (Real.log x * s) := by
    exact Real.rpow_def_of_pos h.1 s
  have hr : Real.rpow x (powerYZ y z - 1) =
      Real.rpow x (powerYZ y z) / x := by
    simp only [hpow]
    rw [show Real.log x * (powerYZ y z - 1) =
        Real.log x * powerYZ y z - Real.log x by ring]
    rw [Real.exp_sub, Real.exp_log h.1]
  rw [hr]
  simp only [u]
  ring

theorem gap3 :
    ∀ x y z : ℝ, admissible x y →
      partialX u x y z = u x y z * powerYZ y z / x := by
  intro x y z h
  rw [gap1 x y z h]
  exact gap2 y z x h

theorem gap4 :
    ∀ x y z : ℝ, admissible x y →
      partialY u x y z =
        z * Real.rpow y (z - 1) * u x y z * Real.log x := by
  intro x y z h
  have hi : HasDerivAt (fun t : ℝ => Real.rpow t z)
      (z * Real.rpow y (z - 1)) y := by
    exact Real.hasDerivAt_rpow_const (p := z)
      (Or.inl (ne_of_gt h.2))
  have ho : HasDerivAt (fun t : ℝ => Real.rpow x t)
      (Real.rpow x (Real.rpow y z) * Real.log x) (Real.rpow y z) := by
    convert Real.hasDerivAt_const_rpow h.1 using 1 <;> ring
  have hc : HasDerivAt (fun t : ℝ => u x t z)
      (z * Real.rpow y (z - 1) * u x y z * Real.log x) y := by
    convert ho.comp y hi using 1 <;> simp [u, powerYZ] <;> ring
  simpa [partialY] using hc.deriv

theorem gap5 :
    ∀ z y x : ℝ, admissible x y →
      z * Real.rpow y (z - 1) * u x y z * Real.log x =
        z * u x y z * Real.rpow y (z - 1) * Real.log x := by
  intro z y x h
  ring

theorem gap6 :
    ∀ x y z : ℝ, admissible x y →
      partialY u x y z =
        z * u x y z * Real.rpow y (z - 1) * Real.log x := by
  intro x y z h
  rw [gap4 x y z h]
  exact gap5 z y x h

theorem gap7 :
    ∀ x y z : ℝ, admissible x y →
      partialZ u x y z =
        u x y z * powerYZ y z * Real.log x * Real.log y := by
  intro x y z h
  have hi : HasDerivAt (fun t : ℝ => Real.rpow y t)
      (Real.rpow y z * Real.log y) z := by
    convert Real.hasDerivAt_const_rpow h.2 using 1 <;> ring
  have ho : HasDerivAt (fun t : ℝ => Real.rpow x t)
      (Real.rpow x (Real.rpow y z) * Real.log x) (Real.rpow y z) := by
    convert Real.hasDerivAt_const_rpow h.1 using 1 <;> ring
  have hc : HasDerivAt (fun t : ℝ => u x y t)
      (u x y z * powerYZ y z * Real.log x * Real.log y) z := by
    convert ho.comp z hi using 1 <;> simp [u, powerYZ] <;> ring
  simpa [partialZ] using hc.deriv

theorem gap8 :
    ∀ x y z : ℝ, admissible x y →
      Real.rpow x (powerYZ y z) * powerYZ y z *
          Real.log x * Real.log y =
        u x y z * powerYZ y z * Real.log x * Real.log y := by
  intro x y z h
  rfl

theorem gap9 :
    ∀ x y z : ℝ, admissible x y →
      partialZ u x y z =
        u x y z * powerYZ y z * Real.log x * Real.log y := by
  intro x y z h
  exact gap7 x y z h

theorem gap10 :
    ∀ x y z : ℝ, admissible x y →
      secondXX u x y z =
        powerYZ y z *
          (-(u x y z / x ^ 2) + (1 / x) * partialX u x y z) := by
  intro x y z h
  have hx : x ≠ 0 := ne_of_gt h.1
  have hu : HasDerivAt (fun t : ℝ => u t y z) (partialX u x y z) x := by
    rw [gap1 x y z h]
    simpa [u] using
      (Real.hasDerivAt_rpow_const (p := powerYZ y z)
        (Or.inl hx))
  have heq : (fun t : ℝ => partialX u t y z) =ᶠ[nhds x]
      (fun t : ℝ => powerYZ y z * (u t y z / t)) := by
    filter_upwards [Ioi_mem_nhds h.1] with t ht
    rw [gap3 t y z ⟨ht, h.2⟩]
    ring
  have hh : HasDerivAt
      (fun t : ℝ => powerYZ y z * (u t y z / t))
      (powerYZ y z *
        ((partialX u x y z * x - u x y z) / x ^ 2)) x := by
    convert (hasDerivAt_const x (powerYZ y z)).mul
      (hu.div (hasDerivAt_id x) hx) using 1 <;>
      simp only [id_eq] <;> ring
  unfold secondXX
  rw [heq.deriv_eq, hh.deriv]
  field_simp [hx]
  ring

theorem gap11 :
    ∀ y z x : ℝ, admissible x y →
      powerYZ y z *
          (-(u x y z / x ^ 2) + (1 / x) * partialX u x y z) =
        u x y z * powerYZ y z * (powerYZ y z - 1) / x ^ 2 := by
  intro y z x h
  rw [gap3 x y z h]
  field_simp [ne_of_gt h.1]
  ring

theorem gap12 :
    ∀ x y z : ℝ, admissible x y →
      secondXX u x y z =
        u x y z * powerYZ y z * (powerYZ y z - 1) / x ^ 2 := by
  intro x y z h
  rw [gap10 x y z h]
  exact gap11 y z x h

theorem gap13 :
    ∀ x y z : ℝ, admissible x y →
      secondYY u x y z =
        z * Real.log x *
          (Real.rpow y (z - 1) * partialY u x y z +
            (z - 1) * Real.rpow y (z - 2) * u x y z) := by
  intro x y z h
  have hr : HasDerivAt (fun t : ℝ => Real.rpow t (z - 1))
      ((z - 1) * Real.rpow y (z - 2)) y := by
    have hz : (z - 1) - 1 = z - 2 := by ring
    simpa only [hz] using
      (Real.hasDerivAt_rpow_const (p := z - 1)
        (Or.inl (ne_of_gt h.2)))
  have hu : HasDerivAt (fun t : ℝ => u x t z) (partialY u x y z) y := by
    have hi : HasDerivAt (fun t : ℝ => Real.rpow t z)
        (z * Real.rpow y (z - 1)) y := by
      exact Real.hasDerivAt_rpow_const (p := z)
        (Or.inl (ne_of_gt h.2))
    have ho : HasDerivAt (fun t : ℝ => Real.rpow x t)
        (Real.rpow x (Real.rpow y z) * Real.log x) (Real.rpow y z) := by
      convert Real.hasDerivAt_const_rpow h.1 using 1 <;> ring
    rw [gap4 x y z h]
    convert ho.comp y hi using 1 <;> simp [u, powerYZ] <;> ring
  have heq : (fun t : ℝ => partialY u x t z) =ᶠ[nhds y]
      (fun t : ℝ => z * Real.log x *
        (Real.rpow t (z - 1) * u x t z)) := by
    filter_upwards [Ioi_mem_nhds h.2] with t ht
    rw [gap4 x t z ⟨h.1, ht⟩]
    ring
  have hh : HasDerivAt
      (fun t : ℝ => z * Real.log x *
        (Real.rpow t (z - 1) * u x t z))
      (z * Real.log x *
        (Real.rpow y (z - 1) * partialY u x y z +
          (z - 1) * Real.rpow y (z - 2) * u x y z)) y := by
    convert (hasDerivAt_const y (z * Real.log x)).mul (hr.mul hu)
      using 1 <;> ring
  unfold secondYY
  rw [heq.deriv_eq, hh.deriv]

theorem gap14 :
    ∀ z x y : ℝ, admissible x y →
      z * Real.log x *
          (Real.rpow y (z - 1) * partialY u x y z +
            (z - 1) * Real.rpow y (z - 2) * u x y z) =
        u x y z * z * Real.rpow y (z - 2) * Real.log x *
          (z * powerYZ y z * Real.log x + z - 1) := by
  intro z x y h
  have hpow (s : ℝ) : Real.rpow y s =
      Real.exp (Real.log y * s) := by
    exact Real.rpow_def_of_pos h.2 s
  have hr : Real.rpow y (z - 1) * Real.rpow y (z - 1) =
      Real.rpow y (z - 2) * powerYZ y z := by
    simp only [powerYZ, hpow, ← Real.exp_add]
    congr 1
    ring
  rw [gap6 x y z h]
  calc
    z * Real.log x *
        (Real.rpow y (z - 1) *
            (z * u x y z * Real.rpow y (z - 1) * Real.log x) +
          (z - 1) * Real.rpow y (z - 2) * u x y z) =
        u x y z * z * Real.log x *
          (z * Real.log x *
              (Real.rpow y (z - 1) * Real.rpow y (z - 1)) +
            (z - 1) * Real.rpow y (z - 2)) := by ring
    _ = u x y z * z * Real.log x *
          (z * Real.log x *
              (Real.rpow y (z - 2) * powerYZ y z) +
            (z - 1) * Real.rpow y (z - 2)) := by rw [hr]
    _ = u x y z * z * Real.rpow y (z - 2) * Real.log x *
          (z * powerYZ y z * Real.log x + z - 1) := by ring

theorem gap15 :
    ∀ x y z : ℝ, admissible x y →
      secondYY u x y z =
        u x y z * z * Real.rpow y (z - 2) * Real.log x *
          (z * powerYZ y z * Real.log x + z - 1) := by
  intro x y z h
  rw [gap13 x y z h]
  exact gap14 z x y h

theorem gap16 :
    ∀ x y z : ℝ, admissible x y →
      secondZZ u x y z =
        (powerYZ y z * partialZ u x y z +
            u x y z * powerYZ y z * Real.log y) *
          Real.log x * Real.log y := by
  intro x y z h
  have hp : HasDerivAt (fun t : ℝ => powerYZ y t)
      (powerYZ y z * Real.log y) z := by
    convert Real.hasDerivAt_const_rpow h.2 using 1 <;>
      simp [powerYZ] <;> ring
  have hu : HasDerivAt (fun t : ℝ => u x y t) (partialZ u x y z) z := by
    have ho : HasDerivAt (fun t : ℝ => Real.rpow x t)
        (Real.rpow x (powerYZ y z) * Real.log x) (powerYZ y z) := by
      convert Real.hasDerivAt_const_rpow h.1 using 1 <;> ring
    rw [gap7 x y z h]
    convert ho.comp z hp using 1 <;> simp [u, powerYZ] <;> ring
  have heq : (fun t : ℝ => partialZ u x y t) =ᶠ[nhds z]
      (fun t : ℝ =>
        (powerYZ y t * u x y t) * Real.log x * Real.log y) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    change partialZ u x y t =
      (powerYZ y t * u x y t) * Real.log x * Real.log y
    rw [gap7 x y t h]
    ring
  have hh : HasDerivAt
      (fun t : ℝ =>
        (powerYZ y t * u x y t) * Real.log x * Real.log y)
      ((powerYZ y z * partialZ u x y z +
          u x y z * powerYZ y z * Real.log y) *
        Real.log x * Real.log y) z := by
    convert ((hp.mul hu).mul (hasDerivAt_const z (Real.log x))).mul
      (hasDerivAt_const z (Real.log y)) using 1 <;> ring
  unfold secondZZ
  rw [heq.deriv_eq, hh.deriv]

theorem gap17 :
    ∀ y x z : ℝ, admissible x y →
      (powerYZ y z * partialZ u x y z +
            u x y z * powerYZ y z * Real.log y) *
          Real.log x * Real.log y =
        u x y z * powerYZ y z * Real.log x * Real.log y ^ 2 *
          (1 + powerYZ y z * Real.log x) := by
  intro y x z h
  rw [gap7 x y z h]
  ring

theorem gap18 :
    ∀ x y z : ℝ, admissible x y →
      secondZZ u x y z =
        u x y z * powerYZ y z * Real.log x * Real.log y ^ 2 *
          (1 + powerYZ y z * Real.log x) := by
  intro x y z h
  rw [gap16 x y z h]
  exact gap17 y x z h

theorem gap19 :
    ∀ x y z : ℝ, admissible x y →
      mixedXY u x y z =
        (1 / x) *
          (powerYZ y z * partialY u x y z +
            u x y z * z * Real.rpow y (z - 1)) := by
  intro x y z h
  have hp : HasDerivAt (fun t : ℝ => powerYZ t z)
      (z * Real.rpow y (z - 1)) y := by
    simpa [powerYZ] using
      (Real.hasDerivAt_rpow_const (p := z)
        (Or.inl (ne_of_gt h.2)))
  have hu : HasDerivAt (fun t : ℝ => u x t z) (partialY u x y z) y := by
    have ho : HasDerivAt (fun t : ℝ => Real.rpow x t)
        (Real.rpow x (powerYZ y z) * Real.log x) (powerYZ y z) := by
      convert Real.hasDerivAt_const_rpow h.1 using 1 <;> ring
    rw [gap4 x y z h]
    convert ho.comp y hp using 1 <;> simp [u, powerYZ] <;> ring
  have heq : (fun t : ℝ => partialX u x t z) =ᶠ[nhds y]
      (fun t : ℝ => (1 / x) * (powerYZ t z * u x t z)) := by
    filter_upwards [Ioi_mem_nhds h.2] with t ht
    rw [gap3 x t z ⟨h.1, ht⟩]
    ring
  have hh : HasDerivAt
      (fun t : ℝ => (1 / x) * (powerYZ t z * u x t z))
      ((1 / x) *
        (powerYZ y z * partialY u x y z +
          u x y z * z * Real.rpow y (z - 1))) y := by
    convert (hasDerivAt_const y (1 / x)).mul (hp.mul hu)
      using 1 <;> ring
  unfold mixedXY
  rw [heq.deriv_eq, hh.deriv]

theorem gap20 :
    ∀ x y z : ℝ, admissible x y →
      (1 / x) *
          (powerYZ y z * partialY u x y z +
            u x y z * z * Real.rpow y (z - 1)) =
        u x y z * z * Real.rpow y (z - 1) *
          (powerYZ y z * Real.log x + 1) / x := by
  intro x y z h
  rw [gap6 x y z h]
  ring

theorem gap21 :
    ∀ x y z : ℝ, admissible x y →
      mixedXY u x y z =
        u x y z * z * Real.rpow y (z - 1) *
          (powerYZ y z * Real.log x + 1) / x := by
  intro x y z h
  rw [gap19 x y z h]
  exact gap20 x y z h

theorem gap22 :
    ∀ x y z : ℝ, admissible x y →
      mixedYZ u x y z =
        (Real.rpow y (z - 1) * u x y z +
            u x y z * z * Real.rpow y (z - 1) * Real.log y +
            z * Real.rpow y (z - 1) * partialZ u x y z) *
          Real.log x := by
  intro x y z h
  have hs : HasDerivAt (fun t : ℝ => t - 1) 1 z := by
    simpa using (hasDerivAt_id z).sub_const 1
  have hr : HasDerivAt (fun t : ℝ => Real.rpow y (t - 1))
      (Real.rpow y (z - 1) * Real.log y) z := by
    have hr0 : HasDerivAt (fun t : ℝ => Real.rpow y t)
        (Real.rpow y (z - 1) * Real.log y) (z - 1) := by
      convert Real.hasDerivAt_const_rpow h.2 using 1 <;> ring
    simpa only [mul_one] using hr0.comp z hs
  have hu : HasDerivAt (fun t : ℝ => u x y t) (partialZ u x y z) z := by
    have hp : HasDerivAt (fun t : ℝ => powerYZ y t)
        (powerYZ y z * Real.log y) z := by
      convert Real.hasDerivAt_const_rpow h.2 using 1 <;>
        simp [powerYZ] <;> ring
    have ho : HasDerivAt (fun t : ℝ => Real.rpow x t)
        (Real.rpow x (powerYZ y z) * Real.log x) (powerYZ y z) := by
      convert Real.hasDerivAt_const_rpow h.1 using 1 <;> ring
    rw [gap7 x y z h]
    convert ho.comp z hp using 1 <;> simp [u, powerYZ] <;> ring
  have heq : (fun t : ℝ => partialY u x y t) =ᶠ[nhds z]
      (fun t : ℝ =>
        t * Real.rpow y (t - 1) * u x y t * Real.log x) := by
    refine Filter.Eventually.of_forall ?_
    intro t
    change partialY u x y t =
      t * Real.rpow y (t - 1) * u x y t * Real.log x
    rw [gap4 x y t h]
  have hh : HasDerivAt
      (fun t : ℝ =>
        t * Real.rpow y (t - 1) * u x y t * Real.log x)
      ((Real.rpow y (z - 1) * u x y z +
          u x y z * z * Real.rpow y (z - 1) * Real.log y +
          z * Real.rpow y (z - 1) * partialZ u x y z) *
        Real.log x) z := by
    convert (((hasDerivAt_id z).mul hr).mul hu).mul
      (hasDerivAt_const z (Real.log x)) using 1 <;>
      simp only [id_eq, one_mul, mul_one, zero_mul, mul_zero, add_zero,
        zero_add] <;>
      ring_nf <;>
      simp <;>
      ac_rfl
  unfold mixedYZ
  rw [heq.deriv_eq, hh.deriv]

theorem gap23 :
    ∀ y z x : ℝ, admissible x y →
      (Real.rpow y (z - 1) * u x y z +
            u x y z * z * Real.rpow y (z - 1) * Real.log y +
            z * Real.rpow y (z - 1) * partialZ u x y z) *
          Real.log x =
        u x y z * Real.rpow y (z - 1) * Real.log x *
          (1 + z * Real.log y * (1 + powerYZ y z * Real.log x)) := by
  intro y z x h
  rw [gap7 x y z h]
  ring

theorem gap24 :
    ∀ x y z : ℝ, admissible x y →
      mixedYZ u x y z =
        u x y z * Real.rpow y (z - 1) * Real.log x *
          (1 + z * Real.log y * (1 + powerYZ y z * Real.log x)) := by
  intro x y z h
  rw [gap22 x y z h]
  exact gap23 y z x h

theorem gap25 :
    ∀ x y z : ℝ, admissible x y →
      mixedZX u x y z =
        powerYZ y z * Real.log y *
          (partialX u x y z * Real.log x + u x y z / x) := by
  intro x y z h
  have hx : x ≠ 0 := ne_of_gt h.1
  have hu : HasDerivAt (fun t : ℝ => u t y z) (partialX u x y z) x := by
    rw [gap1 x y z h]
    simpa [u] using
      (Real.hasDerivAt_rpow_const (p := powerYZ y z)
        (Or.inl hx))
  have hl : HasDerivAt (fun t : ℝ => Real.log t) (1 / x) x := by
    convert Real.hasDerivAt_log hx using 1 <;> field_simp [hx]
  have heq : (fun t : ℝ => partialZ u t y z) =ᶠ[nhds x]
      (fun t : ℝ =>
        powerYZ y z * Real.log y * (u t y z * Real.log t)) := by
    filter_upwards [Ioi_mem_nhds h.1] with t ht
    rw [gap7 t y z ⟨ht, h.2⟩]
    ring
  have hh : HasDerivAt
      (fun t : ℝ =>
        powerYZ y z * Real.log y * (u t y z * Real.log t))
      (powerYZ y z * Real.log y *
        (partialX u x y z * Real.log x + u x y z / x)) x := by
    convert (hasDerivAt_const x (powerYZ y z * Real.log y)).mul
      (hu.mul hl) using 1 <;> ring
  unfold mixedZX
  rw [heq.deriv_eq, hh.deriv]

theorem gap26 :
    ∀ y x z : ℝ, admissible x y →
      powerYZ y z * Real.log y *
          (partialX u x y z * Real.log x + u x y z / x) =
        u x y z * powerYZ y z * Real.log y *
          (powerYZ y z * Real.log x + 1) / x := by
  intro y x z h
  rw [gap3 x y z h]
  field_simp [ne_of_gt h.1]

theorem gap27 :
    ∀ x y z : ℝ, admissible x y →
      mixedZX u x y z =
        u x y z * powerYZ y z * Real.log y *
          (powerYZ y z * Real.log x + 1) / x := by
  intro x y z h
  rw [gap25 x y z h]
  exact gap26 y x z h

end

end ProofGap.Exercise3228_1
