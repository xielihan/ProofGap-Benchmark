import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3231

noncomputable section

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def eulerLHS (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  x * partialX f x y z + y * partialY f x y z + z * partialZ f x y z

def Differentiable3 (f : ℝ → ℝ → ℝ → ℝ) : Prop :=
  Differentiable ℝ
    (fun p : ℝ × (ℝ × ℝ) => f p.1 p.2.1 p.2.2)

def HomogeneousOfDegree (f : ℝ → ℝ → ℝ → ℝ) (n : ℝ) : Prop :=
  ∀ t : ℝ, 0 < t → ∀ x y z : ℝ,
    f (t * x) (t * y) (t * z) = Real.rpow t n * f x y z

def quadraticU (x y z : ℝ) : ℝ :=
  (x - 2 * y + 3 * z) ^ 2

def radialSq (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2

def radialU (x y z : ℝ) : ℝ :=
  x / Real.sqrt (radialSq x y z)

def radialAdmissible (x y z : ℝ) : Prop :=
  0 < radialSq x y z

def radialThreeHalves (x y z : ℝ) : ℝ :=
  Real.rpow (radialSq x y z) (3 / 2 : ℝ)

def powerU (x y z : ℝ) : ℝ :=
  Real.rpow (x / y) (y / z)

def powerExponential (x y z : ℝ) : ℝ :=
  Real.exp ((y / z) * Real.log (x / y))

def powerAdmissible (x y z : ℝ) : Prop :=
  0 < x ∧ 0 < y ∧ z ≠ 0

private def uncurry₃ (f : ℝ → ℝ → ℝ → ℝ) :
    ℝ × ℝ × ℝ → ℝ :=
  fun p => f p.1 p.2.1 p.2.2

private abbrev partial1 := partialX
private abbrev partial2 := partialY
private abbrev partial3 := partialZ
private abbrev Vec3 := ℝ × ℝ × ℝ

private theorem partials_eq_fderiv
    (f : ℝ → ℝ → ℝ → ℝ)
    (hf : Differentiable ℝ (uncurry₃ f)) (a b c : ℝ) :
    partial1 f a b c =
        fderiv ℝ (uncurry₃ f) (a, b, c) ((1, 0, 0) : Vec3) ∧
      partial2 f a b c =
        fderiv ℝ (uncurry₃ f) (a, b, c) ((0, 1, 0) : Vec3) ∧
      partial3 f a b c =
        fderiv ℝ (uncurry₃ f) (a, b, c) ((0, 0, 1) : Vec3) := by
  have h₁ :=
    (hf (a, b, c)).hasFDerivAt.comp a
      ((hasDerivAt_id a).prodMk
        ((hasDerivAt_const (x := a) (c := b)).prodMk
          (hasDerivAt_const (x := a) (c := c))))
  have h₂ :=
    (hf (a, b, c)).hasFDerivAt.comp b
      ((hasDerivAt_const (x := b) (c := a)).prodMk
        ((hasDerivAt_id b).prodMk
          (hasDerivAt_const (x := b) (c := c))))
  have h₃ :=
    (hf (a, b, c)).hasFDerivAt.comp c
      ((hasDerivAt_const (x := c) (c := a)).prodMk
        ((hasDerivAt_const (x := c) (c := b)).prodMk
          (hasDerivAt_id c)))
  constructor
  · simpa [partial1, uncurry₃, Function.comp_def, partialX] using
      h₁.hasDerivAt.deriv
  constructor
  · simpa [partial2, uncurry₃, Function.comp_def, partialY] using
      h₂.hasDerivAt.deriv
  · simpa [partial3, uncurry₃, Function.comp_def, partialZ] using
      h₃.hasDerivAt.deriv

private theorem hasDerivAt_uncurry₃_chain
    (f : ℝ → ℝ → ℝ → ℝ) (hf : Differentiable ℝ (uncurry₃ f))
    {A B C : ℝ → ℝ} {s dA dB dC : ℝ}
    (hA : HasDerivAt A dA s) (hB : HasDerivAt B dB s)
    (hC : HasDerivAt C dC s) :
    HasDerivAt (fun t => f (A t) (B t) (C t))
      (partial1 f (A s) (B s) (C s) * dA +
        partial2 f (A s) (B s) (C s) * dB +
        partial3 f (A s) (B s) (C s) * dC) s := by
  have hcurve :
      HasDerivAt (fun t => (A t, B t, C t)) ((dA, dB, dC) : Vec3) s :=
    hA.prodMk (hB.prodMk hC)
  have hcomp :=
    (hf (A s, B s, C s)).hasFDerivAt.comp_hasDerivAt s hcurve
  have hp := partials_eq_fderiv f hf (A s) (B s) (C s)
  let L := fderiv ℝ (uncurry₃ f) (A s, B s, C s)
  let e₁ : Vec3 := (1, 0, 0)
  let e₂ : Vec3 := (0, 1, 0)
  let e₃ : Vec3 := (0, 0, 1)
  have hv : ((dA, dB, dC) : Vec3) =
      dA • e₁ + dB • e₂ + dC • e₃ := by
    ext <;> simp [e₁, e₂, e₃]
  convert hcomp using 1
  symm
  change L (dA, dB, dC) = _
  rw [hv, map_add, map_add, map_smul, map_smul, map_smul]
  rw [← hp.1, ← hp.2.1, ← hp.2.2]
  simp [smul_eq_mul]
  ring

theorem gap1 :
    ∀ (f : ℝ → ℝ → ℝ → ℝ) (n : ℝ),
      Differentiable3 f → HomogeneousOfDegree f n →
        ∀ x y z : ℝ, eulerLHS f x y z = n * f x y z := by
  intro f n hf hhom x y z
  have hfd : Differentiable ℝ (uncurry₃ f) := by
    simpa [Differentiable3, uncurry₃] using hf
  have hx : HasDerivAt (fun t : ℝ => t * x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const x
  have hy : HasDerivAt (fun t : ℝ => t * y) y 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const y
  have hz : HasDerivAt (fun t : ℝ => t * z) z 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const z
  have hline :=
    hasDerivAt_uncurry₃_chain f hfd hx hy hz
  have hpos : ∀ᶠ t in nhds (1 : ℝ), 0 < t :=
    IsOpen.mem_nhds isOpen_Ioi
      (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
  have heq :
      (fun t : ℝ => f (t * x) (t * y) (t * z)) =ᶠ[nhds 1]
        fun t => Real.rpow t n * f x y z := by
    filter_upwards [hpos] with t ht
    exact hhom t ht x y z
  have hrpow :
      HasDerivAt (fun t : ℝ => Real.rpow t n) n 1 := by
    convert Real.hasDerivAt_rpow_const (p := n) (Or.inl one_ne_zero)
      using 1 <;> simp
  have hrhs :=
    (hrpow.mul_const (f x y z)).deriv
  have hline' := hline.deriv
  simp only [one_mul, partial1, partial2, partial3] at hline'
  unfold eulerLHS
  calc
    x * partialX f x y z + y * partialY f x y z +
        z * partialZ f x y z =
        deriv (fun t : ℝ => f (t * x) (t * y) (t * z)) 1 := by
      rw [hline']
      ring
    _ = deriv (fun t => Real.rpow t n * f x y z) 1 :=
      heq.deriv_eq
    _ = n * f x y z := hrhs

theorem gap2 :
    ∀ x y z t : ℝ,
      quadraticU (t * x) (t * y) (t * z) =
        t ^ 2 * quadraticU x y z := by
  intro x y z t
  unfold quadraticU
  ring

theorem gap3 :
    ∀ x y z : ℝ,
      partialX quadraticU x y z = 2 * (x - 2 * y + 3 * z) := by
  intro x y z
  unfold partialX quadraticU
  have h :
      HasDerivAt (fun t : ℝ => t - 2 * y + 3 * z) 1 x := by
    convert
      ((hasDerivAt_id x).sub_const (2 * y)).add_const (3 * z)
        using 1 <;> ring
  convert (h.pow 2).deriv using 1 <;> ring

theorem gap4 :
    ∀ x y z : ℝ,
      partialY quadraticU x y z = -4 * (x - 2 * y + 3 * z) := by
  intro x y z
  unfold partialY quadraticU
  have h :
      HasDerivAt (fun t : ℝ => x - 2 * t + 3 * z) (-2) y := by
    convert
      ((hasDerivAt_const y x).sub
        ((hasDerivAt_id y).const_mul 2)).add_const (3 * z) using 1 <;>
      ring
  convert (h.pow 2).deriv using 1 <;> ring

theorem gap5 :
    ∀ x y z : ℝ,
      partialZ quadraticU x y z = 6 * (x - 2 * y + 3 * z) := by
  intro x y z
  unfold partialZ quadraticU
  have h :
      HasDerivAt (fun t : ℝ => x - 2 * y + 3 * t) 3 z := by
    convert
      (hasDerivAt_const z (x - 2 * y)).add
        ((hasDerivAt_id z).const_mul 3) using 1 <;>
      ring
  convert (h.pow 2).deriv using 1 <;> ring

theorem gap6 :
    ∀ x y z : ℝ,
      eulerLHS quadraticU x y z =
        (x - 2 * y + 3 * z) * (2 * x - 4 * y + 6 * z) := by
  intro x y z
  rw [show eulerLHS quadraticU x y z =
      x * partialX quadraticU x y z +
        y * partialY quadraticU x y z +
        z * partialZ quadraticU x y z by rfl]
  rw [gap3, gap4, gap5]
  ring

theorem gap7 :
    ∀ x y z : ℝ,
      (x - 2 * y + 3 * z) * (2 * x - 4 * y + 6 * z) =
        2 * quadraticU x y z := by
  intro x y z
  unfold quadraticU
  ring

theorem gap8 :
    ∀ x y z : ℝ,
      eulerLHS quadraticU x y z = 2 * quadraticU x y z := by
  intro x y z
  rw [gap6, gap7]

theorem gap9 :
    ∀ x y z t : ℝ, radialAdmissible x y z → 0 < t →
      radialU (t * x) (t * y) (t * z) = radialU x y z := by
  intro x y z t hrad ht
  have hs :
      radialSq (t * x) (t * y) (t * z) = t ^ 2 * radialSq x y z := by
    unfold radialSq
    ring
  have ht0 : 0 ≤ t := le_of_lt ht
  unfold radialU
  rw [hs, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0]
  field_simp [ne_of_gt ht]

theorem gap10 :
    ∀ x y z t : ℝ, radialAdmissible x y z → 0 < t →
      radialU x y z = Real.rpow t 0 * radialU x y z := by
  intro x y z t _ _
  simp

theorem gap11 :
    ∀ x y z t : ℝ, radialAdmissible x y z → 0 < t →
      radialU (t * x) (t * y) (t * z) =
        Real.rpow t 0 * radialU x y z := by
  intro x y z t hrad ht
  calc
    radialU (t * x) (t * y) (t * z) = radialU x y z :=
      gap9 x y z t hrad ht
    _ = Real.rpow t 0 * radialU x y z :=
      gap10 x y z t hrad ht

private theorem radialThreeHalves_eq_mul_sqrt
    (x y z : ℝ) (h : radialAdmissible x y z) :
    radialThreeHalves x y z =
      radialSq x y z * Real.sqrt (radialSq x y z) := by
  have hr : 0 < radialSq x y z := h
  unfold radialThreeHalves
  calc
    Real.rpow (radialSq x y z) (3 / 2 : ℝ) =
        Real.exp (Real.log (radialSq x y z) * (3 / 2 : ℝ)) :=
      Real.rpow_def_of_pos hr (3 / 2 : ℝ)
    _ = Real.exp (Real.log (radialSq x y z)) *
        Real.exp (Real.log (radialSq x y z) * (1 / 2 : ℝ)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = radialSq x y z *
        Real.rpow (radialSq x y z) (1 / 2 : ℝ) := by
      rw [Real.exp_log hr]
      congr 1
      exact (Real.rpow_def_of_pos hr (1 / 2 : ℝ)).symm
    _ = radialSq x y z * Real.sqrt (radialSq x y z) := by
      congr 1
      exact (Real.sqrt_eq_rpow (radialSq x y z)).symm

theorem gap12 :
    ∀ x y z : ℝ, radialAdmissible x y z →
      partialX radialU x y z =
        (y ^ 2 + z ^ 2) / radialThreeHalves x y z := by
  intro x y z h
  have hr : 0 < radialSq x y z := h
  have hS :
      HasDerivAt (fun t : ℝ => radialSq t y z) (2 * x) x := by
    have hd := ((hasDerivAt_id x).pow 2).add_const (y ^ 2 + z ^ 2)
    convert hd using 1
    · funext t
      simp only [Pi.pow_apply, id_eq]
      unfold radialSq
      ring
    · simp only [Pi.pow_apply, id_eq]
      ring
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (radialSq t y z))
        (x / Real.sqrt (radialSq x y z)) x := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp x hS using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hr] <;> ring
  have hq :=
    (hasDerivAt_id x).div hs (Real.sqrt_ne_zero'.mpr hr)
  unfold partialX radialU
  change deriv ((id : ℝ → ℝ) /
    fun t => Real.sqrt (radialSq t y z)) x = _
  rw [hq.deriv, radialThreeHalves_eq_mul_sqrt x y z h]
  simp only [id_eq]
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)]
  rw [Real.sq_sqrt (le_of_lt hr)]
  unfold radialSq
  ring

theorem gap13 :
    ∀ x y z : ℝ, radialAdmissible x y z →
      partialY radialU x y z =
        -(x * y / radialThreeHalves x y z) := by
  intro x y z h
  have hr : 0 < radialSq x y z := h
  have hS :
      HasDerivAt (fun t : ℝ => radialSq x t z) (2 * y) y := by
    have hd := (hasDerivAt_const y (x ^ 2)).add
      (((hasDerivAt_id y).pow 2).add_const (z ^ 2))
    convert hd using 1
    · funext t
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
      unfold radialSq
      ring
    · simp only [Pi.pow_apply, id_eq]
      ring
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (radialSq x t z))
        (y / Real.sqrt (radialSq x y z)) y := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp y hS using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hr] <;> ring
  have hq :=
    (hasDerivAt_const y x).div hs (Real.sqrt_ne_zero'.mpr hr)
  unfold partialY radialU
  change deriv ((fun _ : ℝ => x) /
    fun t => Real.sqrt (radialSq x t z)) y = _
  rw [hq.deriv, radialThreeHalves_eq_mul_sqrt x y z h]
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)]
  rw [Real.sq_sqrt (le_of_lt hr)]
  ring

theorem gap14 :
    ∀ x y z : ℝ, radialAdmissible x y z →
      partialZ radialU x y z =
        -(x * z / radialThreeHalves x y z) := by
  intro x y z h
  have hr : 0 < radialSq x y z := h
  have hS :
      HasDerivAt (fun t : ℝ => radialSq x y t) (2 * z) z := by
    have hd := (hasDerivAt_const z (x ^ 2 + y ^ 2)).add
      ((hasDerivAt_id z).pow 2)
    convert hd using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have hs :
      HasDerivAt (fun t : ℝ => Real.sqrt (radialSq x y t))
        (z / Real.sqrt (radialSq x y z)) z := by
    convert (Real.hasDerivAt_sqrt (ne_of_gt hr)).comp z hS using 1 <;>
      field_simp [Real.sqrt_ne_zero'.mpr hr] <;> ring
  have hq :=
    (hasDerivAt_const z x).div hs (Real.sqrt_ne_zero'.mpr hr)
  unfold partialZ radialU
  change deriv ((fun _ : ℝ => x) /
    fun t => Real.sqrt (radialSq x y t)) z = _
  rw [hq.deriv, radialThreeHalves_eq_mul_sqrt x y z h]
  field_simp [Real.sqrt_ne_zero'.mpr hr, ne_of_gt hr,
    Real.sq_sqrt (le_of_lt hr)]
  rw [Real.sq_sqrt (le_of_lt hr)]
  ring

theorem gap15 :
    ∀ x y z : ℝ, radialAdmissible x y z →
      eulerLHS radialU x y z =
        (x * y ^ 2 + x * z ^ 2 - x * y ^ 2 - x * z ^ 2) /
          radialThreeHalves x y z := by
  intro x y z h
  unfold eulerLHS
  rw [gap12 x y z h, gap13 x y z h, gap14 x y z h]
  ring

theorem gap16 :
    ∀ x y z : ℝ, radialAdmissible x y z →
      (x * y ^ 2 + x * z ^ 2 - x * y ^ 2 - x * z ^ 2) /
          radialThreeHalves x y z =
        0 * radialU x y z := by
  intro x y z _
  ring

theorem gap17 :
    ∀ x y z : ℝ, radialAdmissible x y z →
      eulerLHS radialU x y z = 0 * radialU x y z := by
  intro x y z h
  rw [gap15 x y z h, gap16 x y z h]

theorem gap18 :
    ∀ x y z t : ℝ, powerAdmissible x y z → t ≠ 0 →
      powerU (t * x) (t * y) (t * z) = powerU x y z := by
  intro x y z t _ ht
  unfold powerU
  have hb : (t * x) / (t * y) = x / y := by
    field_simp [ht]
  have he : (t * y) / (t * z) = y / z := by
    field_simp [ht]
  rw [hb, he]

theorem gap19 :
    ∀ x y z t : ℝ, powerAdmissible x y z → t ≠ 0 →
      powerU x y z = Real.rpow t 0 * powerU x y z := by
  intro x y z t _ _
  simp

theorem gap20 :
    ∀ x y z t : ℝ, powerAdmissible x y z → t ≠ 0 →
      powerU (t * x) (t * y) (t * z) =
        Real.rpow t 0 * powerU x y z := by
  intro x y z t h ht
  calc
    powerU (t * x) (t * y) (t * z) = powerU x y z :=
      gap18 x y z t h ht
    _ = Real.rpow t 0 * powerU x y z := gap19 x y z t h ht

private theorem rpow_sub_one_of_pos {a p : ℝ} (ha : 0 < a) :
    Real.rpow a (p - 1) = Real.rpow a p / a := by
  change a ^ (p - 1) = a ^ p / a
  rw [Real.rpow_def_of_pos ha, Real.rpow_def_of_pos ha]
  rw [show Real.log a * (p - 1) =
      Real.log a * p - Real.log a by ring]
  rw [Real.exp_sub, Real.exp_log ha]

theorem gap21 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      partialX powerU x y z =
        (1 / y) * (y / z) * Real.rpow (x / y) (y / z - 1) := by
  intro x y z h
  have hy0 : y ≠ 0 := ne_of_gt h.2.1
  have hbase : 0 < x / y := div_pos h.1 h.2.1
  have hb : HasDerivAt (fun t : ℝ => t / y) (1 / y) x := by
    simpa using (hasDerivAt_id x).div_const y
  have ho :=
    Real.hasDerivAt_rpow_const (p := y / z) (Or.inl (ne_of_gt hbase))
  unfold partialX powerU
  change deriv (fun t : ℝ => (t / y) ^ (y / z)) x =
    (1 / y) * (y / z) * (x / y) ^ (y / z - 1)
  convert (ho.comp x hb).deriv using 1 <;> ring

theorem gap22 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      (1 / y) * (y / z) * Real.rpow (x / y) (y / z - 1) =
        y * powerU x y z / (x * z) := by
  intro x y z h
  have hx0 : x ≠ 0 := ne_of_gt h.1
  have hy0 : y ≠ 0 := ne_of_gt h.2.1
  have hz0 : z ≠ 0 := h.2.2
  rw [rpow_sub_one_of_pos (div_pos h.1 h.2.1)]
  unfold powerU
  field_simp [hx0, hy0, hz0] <;> ring

theorem gap23 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      partialX powerU x y z =
        y * powerU x y z / (x * z) := by
  intro x y z h
  rw [gap21 x y z h, gap22 x y z h]

private theorem powerU_eq_powerExponential
    (x y z : ℝ) (hbase : 0 < x / y) :
    powerU x y z = powerExponential x y z := by
  unfold powerU powerExponential
  change (x / y) ^ (y / z) =
    Real.exp ((y / z) * Real.log (x / y))
  rw [Real.rpow_def_of_pos hbase]
  congr 1
  ring

theorem gap24 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      partialY powerU x y z = partialY powerExponential x y z := by
  intro x y z h
  have hy : 0 < y := h.2.1
  have hcont : ContinuousAt (fun t : ℝ => x / t) y :=
    continuousAt_const.div continuousAt_id (ne_of_gt hy)
  have hbase : 0 < x / y := div_pos h.1 hy
  have hev : ∀ᶠ t in nhds y, 0 < x / t :=
    hcont.eventually (isOpen_Ioi.mem_nhds hbase)
  have heq :
      (fun t => powerU x t z) =ᶠ[nhds y]
        fun t => powerExponential x t z := by
    filter_upwards [hev] with t ht
    exact powerU_eq_powerExponential x t z ht
  unfold partialY
  exact heq.deriv_eq

theorem gap25 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      partialY powerExponential x y z =
        powerU x y z *
          ((1 / z) * Real.log (x / y) - (y / z) * (1 / y)) := by
  intro x y z h
  have hy0 : y ≠ 0 := ne_of_gt h.2.1
  have hbase : 0 < x / y := div_pos h.1 h.2.1
  have hq :
      HasDerivAt (fun t : ℝ => x / t) (-x / y ^ 2) y := by
    convert (hasDerivAt_const y x).div (hasDerivAt_id y) hy0
      using 1 <;> simp only [id_eq] <;> field_simp [hy0] <;> ring
  have hlog :
      HasDerivAt (fun t : ℝ => Real.log (x / t)) (-1 / y) y := by
    convert (Real.hasDerivAt_log (ne_of_gt hbase)).comp y hq using 1 <;>
      field_simp [ne_of_gt h.1, hy0] <;> ring
  have hexp :
      HasDerivAt (fun t : ℝ => t / z) (1 / z) y := by
    simpa using (hasDerivAt_id y).div_const z
  have hinner :=
    hexp.mul hlog
  have hout :=
    Real.hasDerivAt_exp ((y / z) * Real.log (x / y))
  unfold partialY powerExponential
  have hd :
      deriv (fun t : ℝ =>
        Real.exp ((t / z) * Real.log (x / t))) y =
        Real.exp ((y / z) * Real.log (x / y)) *
          ((1 / z) * Real.log (x / y) + (y / z) * (-1 / y)) := by
    simpa [Function.comp_def] using (hout.comp y hinner).deriv
  rw [hd]
  rw [show Real.exp ((y / z) * Real.log (x / y)) =
      powerU x y z by
    symm
    exact powerU_eq_powerExponential x y z hbase]
  ring

theorem gap26 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      powerU x y z *
          ((1 / z) * Real.log (x / y) - (y / z) * (1 / y)) =
        (powerU x y z / z) * (Real.log (x / y) - 1) := by
  intro x y z h
  field_simp [ne_of_gt h.2.1, h.2.2] <;> ring

theorem gap27 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      partialY powerU x y z =
        (powerU x y z / z) * (Real.log (x / y) - 1) := by
  intro x y z h
  rw [gap24 x y z h, gap25 x y z h, gap26 x y z h]

theorem gap28 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      partialZ powerU x y z =
        powerU x y z * Real.log (x / y) * (-(y / z ^ 2)) := by
  intro x y z h
  have hz0 : z ≠ 0 := h.2.2
  have hbase : 0 < x / y := div_pos h.1 h.2.1
  have heq :
      (fun t => powerU x y t) =
        fun t => powerExponential x y t := by
    funext t
    exact powerU_eq_powerExponential x y t hbase
  have hquot :
      HasDerivAt (fun t : ℝ => y / t) (-y / z ^ 2) z := by
    convert (hasDerivAt_const z y).div (hasDerivAt_id z) hz0
      using 1 <;> simp only [id_eq] <;> field_simp [hz0] <;> ring
  have hinner :=
    hquot.mul_const (Real.log (x / y))
  have hout :=
    Real.hasDerivAt_exp ((y / z) * Real.log (x / y))
  unfold partialZ
  rw [heq]
  change deriv (fun t : ℝ =>
    Real.exp ((y / t) * Real.log (x / y))) z = _
  have hd :
      deriv (fun t : ℝ =>
        Real.exp ((y / t) * Real.log (x / y))) z =
        Real.exp ((y / z) * Real.log (x / y)) *
          ((-y / z ^ 2) * Real.log (x / y)) := by
    simpa [powerExponential, Function.comp_def] using
      (hout.comp z hinner).deriv
  rw [hd]
  rw [show Real.exp ((y / z) * Real.log (x / y)) =
      powerU x y z by
    symm
    exact powerU_eq_powerExponential x y z hbase]
  ring

theorem gap29 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      powerU x y z * Real.log (x / y) * (-(y / z ^ 2)) =
        -(y * powerU x y z / z ^ 2) * Real.log (x / y) := by
  intro x y z h
  field_simp [h.2.2] <;> ring

theorem gap30 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      partialZ powerU x y z =
        -(y * powerU x y z / z ^ 2) * Real.log (x / y) := by
  intro x y z h
  rw [gap28 x y z h, gap29 x y z h]

theorem gap31 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      eulerLHS powerU x y z =
        x * (y * powerU x y z / (x * z)) +
          y * (powerU x y z / z) * (Real.log (x / y) - 1) -
          z * (y * powerU x y z / z ^ 2) * Real.log (x / y) := by
  intro x y z h
  unfold eulerLHS
  rw [gap23 x y z h, gap27 x y z h, gap30 x y z h]
  ring

theorem gap32 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      x * (y * powerU x y z / (x * z)) +
          y * (powerU x y z / z) * (Real.log (x / y) - 1) -
          z * (y * powerU x y z / z ^ 2) * Real.log (x / y) =
        0 * powerU x y z := by
  intro x y z h
  field_simp [ne_of_gt h.1, h.2.2]
  ring

theorem gap33 :
    ∀ x y z : ℝ, powerAdmissible x y z →
      eulerLHS powerU x y z = 0 * powerU x y z := by
  intro x y z h
  rw [gap31 x y z h, gap32 x y z h]

theorem gap34 :
    ∀ x y z : ℝ,
      eulerLHS quadraticU x y z = 2 * quadraticU x y z ∧
      (radialAdmissible x y z →
        eulerLHS radialU x y z = 0 * radialU x y z) ∧
      (powerAdmissible x y z →
        eulerLHS powerU x y z = 0 * powerU x y z) := by
  intro x y z
  exact ⟨gap8 x y z, gap17 x y z, gap33 x y z⟩

end

end ProofGap.Exercise3231
