import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1166

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def radicand (x : ℝ) : ℝ := 1 - 3 * x
def invCubeRoot (x : ℝ) : ℝ :=
  1 / Real.rpow (radicand x) (1 / 3 : ℝ)
def y (x : ℝ) : ℝ := Real.cos (3 * x) * invCubeRoot x

def rawSecond (x : ℝ) : ℝ :=
  Real.cos (3 * x) * (4 / 3 ^ 2 : ℝ) * (-3) ^ 2 /
      Real.rpow (radicand x) (7 / 3 : ℝ) +
    2 * (-3) * Real.sin (3 * x) * (-1 / 3 : ℝ) * (-3) /
      Real.rpow (radicand x) (4 / 3 : ℝ) +
    (-(3 ^ 2 : ℝ)) * Real.cos (3 * x) /
      Real.rpow (radicand x) (1 / 3 : ℝ)

private def reciprocalModel (a x : ℝ) : ℝ :=
  Real.exp (-a * Real.log (radicand x))

private theorem radicand_hasDerivAt (x : ℝ) :
    HasDerivAt radicand (-3) x := by
  simpa [radicand] using
    (hasDerivAt_const x (1 : ℝ)).sub
      ((hasDerivAt_id x).const_mul (3 : ℝ))

private theorem radicand_eventually_pos (x : ℝ) (hx : 0 < radicand x) :
    ∀ᶠ z in nhds x, 0 < radicand z := by
  exact (radicand_hasDerivAt x).continuousAt
    (isOpen_Ioi.mem_nhds hx)

private theorem reciprocalModel_succ (a x : ℝ)
    (hx : 0 < radicand x) :
    reciprocalModel (a + 1) x = reciprocalModel a x / radicand x := by
  have hr :
      (radicand x)⁻¹ = Real.exp (-Real.log (radicand x)) := by
    rw [Real.exp_neg, Real.exp_log hx]
  unfold reciprocalModel
  rw [div_eq_mul_inv, hr, ← Real.exp_add]
  congr 1
  ring

private theorem invRpow_eq_reciprocalModel (a x : ℝ)
    (hx : 0 < radicand x) :
    1 / Real.rpow (radicand x) a = reciprocalModel a x := by
  have hrpow :
      Real.rpow (radicand x) a =
        Real.exp (Real.log (radicand x) * a) := by
    simpa only using (Real.rpow_def_of_pos hx a)
  unfold reciprocalModel
  calc
    1 / Real.rpow (radicand x) a =
        (Real.exp (Real.log (radicand x) * a))⁻¹ := by
      simpa only [one_div] using congrArg Inv.inv hrpow
    _ = Real.exp (-(Real.log (radicand x) * a)) :=
      (Real.exp_neg (Real.log (radicand x) * a)).symm
    _ = Real.exp (-a * Real.log (radicand x)) := by
      congr 1
      ring

private theorem reciprocalModel_hasDerivAt (a x : ℝ)
    (hx : 0 < radicand x) :
    HasDerivAt (reciprocalModel a)
      (3 * a * reciprocalModel (a + 1) x) x := by
  have hlog :
      HasDerivAt (fun z => Real.log (radicand z))
        ((radicand x)⁻¹ * (-3)) x := by
    simpa [one_div] using
      (Real.hasDerivAt_log (ne_of_gt hx)).comp x
        (radicand_hasDerivAt x)
  have hexp :
      HasDerivAt (reciprocalModel a)
        (Real.exp (-a * Real.log (radicand x)) *
          ((-a) * ((radicand x)⁻¹ * (-3)))) x := by
    change HasDerivAt
      (fun z => Real.exp (-a * Real.log (radicand z)))
      (Real.exp (-a * Real.log (radicand x)) *
        ((-a) * ((radicand x)⁻¹ * (-3)))) x
    exact
      (Real.hasDerivAt_exp (-a * Real.log (radicand x))).comp x
        (hlog.const_mul (-a))
  convert hexp using 1
  rw [reciprocalModel_succ a x hx]
  unfold reciprocalModel
  simp only [div_eq_mul_inv]
  ring

private theorem invCubeRoot_eventuallyEq (x : ℝ)
    (hx : 0 < radicand x) :
    invCubeRoot =ᶠ[nhds x] reciprocalModel (1 / 3 : ℝ) := by
  filter_upwards [radicand_eventually_pos x hx] with z hz
  exact invRpow_eq_reciprocalModel (1 / 3 : ℝ) z hz

private theorem invCubeRoot_hasDerivAt (x : ℝ)
    (hx : 0 < radicand x) :
    HasDerivAt invCubeRoot
      (1 / Real.rpow (radicand x) (4 / 3 : ℝ)) x := by
  have hm := reciprocalModel_hasDerivAt (1 / 3 : ℝ) x hx
  have hm' :
      HasDerivAt (reciprocalModel (1 / 3 : ℝ))
        (1 / Real.rpow (radicand x) (4 / 3 : ℝ)) x := by
    convert hm using 1
    rw [show (1 / 3 : ℝ) + 1 = 4 / 3 by ring,
      ← invRpow_eq_reciprocalModel (4 / 3 : ℝ) x hx]
    ring
  exact hm'.congr_of_eventuallyEq
    (invCubeRoot_eventuallyEq x hx)

private theorem invCubeRoot_hasSecondDerivAt (x : ℝ)
    (hx : 0 < radicand x) :
    HasDerivAt (deriv invCubeRoot)
      (4 / Real.rpow (radicand x) (7 / 3 : ℝ)) x := by
  have heq :
      deriv invCubeRoot =ᶠ[nhds x] reciprocalModel (4 / 3 : ℝ) := by
    filter_upwards [radicand_eventually_pos x hx] with z hz
    calc
      deriv invCubeRoot z =
          1 / Real.rpow (radicand z) (4 / 3 : ℝ) :=
        (invCubeRoot_hasDerivAt z hz).deriv
      _ = reciprocalModel (4 / 3 : ℝ) z :=
        invRpow_eq_reciprocalModel (4 / 3 : ℝ) z hz
  have hm := reciprocalModel_hasDerivAt (4 / 3 : ℝ) x hx
  have hm' :
      HasDerivAt (reciprocalModel (4 / 3 : ℝ))
        (4 / Real.rpow (radicand x) (7 / 3 : ℝ)) x := by
    convert hm using 1
    rw [show (4 / 3 : ℝ) + 1 = 7 / 3 by ring,
      ← invRpow_eq_reciprocalModel (7 / 3 : ℝ) x hx]
    ring
  exact hm'.congr_of_eventuallyEq heq

private theorem cosPart_hasDerivAt (x : ℝ) :
    HasDerivAt (fun z => Real.cos (3 * z))
      (-3 * Real.sin (3 * x)) x := by
  have hlin : HasDerivAt (fun z : ℝ => 3 * z) 3 x := by
    simpa using (hasDerivAt_id x).const_mul (3 : ℝ)
  convert (Real.hasDerivAt_cos (3 * x)).comp x hlin using 1 <;> ring

private theorem cosPart_hasSecondDerivAt (x : ℝ) :
    HasDerivAt (deriv (fun z => Real.cos (3 * z)))
      (-9 * Real.cos (3 * x)) x := by
  have hlin : HasDerivAt (fun z : ℝ => 3 * z) 3 x := by
    simpa using (hasDerivAt_id x).const_mul (3 : ℝ)
  have hsin :
      HasDerivAt (fun z => -3 * Real.sin (3 * z))
        (-9 * Real.cos (3 * x)) x := by
    convert ((Real.hasDerivAt_sin (3 * x)).comp x hlin).const_mul (-3) using 1 <;>
      ring
  have heq :
      deriv (fun z => Real.cos (3 * z)) =ᶠ[nhds x]
        fun z => -3 * Real.sin (3 * z) :=
    Filter.Eventually.of_forall fun z => (cosPart_hasDerivAt z).deriv
  exact hsin.congr_of_eventuallyEq heq

theorem gap1 (x : ℝ) (hx : 0 < radicand x) :
    nthDeriv 2 y x =
      Real.cos (3 * x) * nthDeriv 2 invCubeRoot x +
        2 * deriv (fun z => Real.cos (3 * z)) x *
          deriv invCubeRoot x +
        nthDeriv 2 (fun z => Real.cos (3 * z)) x *
          invCubeRoot x := by
  have hpos : ∀ᶠ z in nhds x, 0 < radicand z :=
    radicand_eventually_pos x hx
  have hy' :
      deriv y =ᶠ[nhds x]
        fun z =>
          deriv (fun t => Real.cos (3 * t)) z * invCubeRoot z +
            Real.cos (3 * z) * deriv invCubeRoot z := by
    filter_upwards [hpos] with z hz
    have hp :=
      ((cosPart_hasDerivAt z).mul (invCubeRoot_hasDerivAt z hz)).deriv
    simpa only [y, (cosPart_hasDerivAt z).deriv,
      (invCubeRoot_hasDerivAt z hz).deriv] using hp
  have hsecond :=
    ((cosPart_hasSecondDerivAt x).mul (invCubeRoot_hasDerivAt x hx)).add
      ((cosPart_hasDerivAt x).mul (invCubeRoot_hasSecondDerivAt x hx))
  have hysecond := hsecond.congr_of_eventuallyEq hy'
  change deriv (deriv y) x = _
  rw [hysecond.deriv]
  simp only [nthDeriv]
  rw [(cosPart_hasDerivAt x).deriv,
    (invCubeRoot_hasDerivAt x hx).deriv,
    (cosPart_hasSecondDerivAt x).deriv,
    (invCubeRoot_hasSecondDerivAt x hx).deriv]
  ring

theorem gap2 (x : ℝ) (hx : 0 < radicand x) :
    nthDeriv 2 y x = rawSecond x := by
  rw [gap1 x hx]
  simp only [nthDeriv]
  rw [(cosPart_hasDerivAt x).deriv,
    (invCubeRoot_hasDerivAt x hx).deriv,
    (cosPart_hasSecondDerivAt x).deriv,
    (invCubeRoot_hasSecondDerivAt x hx).deriv]
  unfold rawSecond
  unfold invCubeRoot
  ring

theorem gap3 (x : ℝ) (hx : 0 < radicand x) :
    nthDeriv 2 y x =
      4 * Real.cos (3 * x) /
          Real.rpow (radicand x) (7 / 3 : ℝ) -
        6 * Real.sin (3 * x) /
          Real.rpow (radicand x) (4 / 3 : ℝ) -
        9 * Real.cos (3 * x) /
          Real.rpow (radicand x) (1 / 3 : ℝ) := by
  rw [gap2 x hx]
  unfold rawSecond
  ring

theorem gap4 (x : ℝ) (hx : 0 < radicand x) :
    nthDeriv 2 y x =
      (4 * Real.cos (3 * x)) /
          Real.rpow (radicand x) (7 / 3 : ℝ) -
        (6 * Real.sin (3 * x)) /
          Real.rpow (radicand x) (4 / 3 : ℝ) -
        (9 * Real.cos (3 * x)) /
          Real.rpow (radicand x) (1 / 3 : ℝ) := by
  simpa using gap3 x hx

end

end ProofGap.Exercise1166
