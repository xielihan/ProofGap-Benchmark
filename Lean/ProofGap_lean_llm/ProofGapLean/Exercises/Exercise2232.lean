import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open scoped Interval

namespace ProofGap.Exercise2232

noncomputable section

def firstIntegrand (t : ℝ) : ℝ := Real.sqrt (1 + t ^ 2)
def firstIntegral (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x ^ 2, firstIntegrand t

def secondIntegrand (t : ℝ) : ℝ := 1 / Real.sqrt (1 + t ^ 4)
def secondIntegral (x : ℝ) : ℝ :=
  ∫ t in x ^ 2..x ^ 3, secondIntegrand t
def secondLowerPart (x : ℝ) : ℝ :=
  ∫ t in x ^ 2..0, secondIntegrand t
def secondUpperPart (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x ^ 3, secondIntegrand t

def thirdIntegrand (t : ℝ) : ℝ := Real.cos (Real.pi * t ^ 2)
def thirdIntegral (x : ℝ) : ℝ :=
  ∫ t in Real.sin x..Real.cos x, thirdIntegrand t
def thirdLowerPart (x : ℝ) : ℝ :=
  ∫ t in Real.sin x..0, thirdIntegrand t
def thirdUpperPart (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Real.cos x, thirdIntegrand t

private theorem firstIntegrand_continuous : Continuous firstIntegrand := by
  unfold firstIntegrand
  exact Real.continuous_sqrt.comp
    (continuous_const.add (continuous_id.pow 2))

private theorem secondIntegrand_continuous : Continuous secondIntegrand := by
  unfold secondIntegrand
  exact continuous_const.div
    (Real.continuous_sqrt.comp
      (continuous_const.add (continuous_id.pow 4)))
    (fun t : ℝ => ne_of_gt (Real.sqrt_pos.2 (by positivity)))

private theorem thirdIntegrand_continuous : Continuous thirdIntegrand := by
  unfold thirdIntegrand
  exact Real.continuous_cos.comp
    (continuous_const.mul (continuous_id.pow 2))

private theorem compose_real_hasDerivAt
    {f g : ℝ → ℝ} {f' g' x : ℝ}
    (hf : HasDerivAt f f' (g x))
    (hg : HasDerivAt g g' x) :
    HasDerivAt (f ∘ g) (f' * g') x := by
  exact hf.comp x hg

theorem gap1 (x : ℝ) :
    deriv firstIntegral x =
      firstIntegrand (x ^ 2) * deriv (fun u : ℝ => u ^ 2) x := by
  have hpow : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
  have hint : IntervalIntegrable firstIntegrand MeasureTheory.volume 0 (x ^ 2) :=
    firstIntegrand_continuous.intervalIntegrable 0 (x ^ 2)
  have houter :
      HasDerivAt
        (fun y : ℝ => ∫ t in (0 : ℝ)..y, firstIntegrand t)
        (firstIntegrand (x ^ 2)) (x ^ 2) :=
    intervalIntegral.integral_hasDerivAt_right hint
      firstIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
      firstIntegrand_continuous.continuousAt
  have hchain :
      HasDerivAt
        ((fun y : ℝ => ∫ t in (0 : ℝ)..y, firstIntegrand t) ∘
          (fun u : ℝ => u ^ 2))
        (firstIntegrand (x ^ 2) * (2 * x)) x :=
    compose_real_hasDerivAt
      (g := fun u : ℝ => u ^ 2) houter hpow
  rw [hpow.deriv]
  simpa only [firstIntegral, Function.comp_apply] using hchain.deriv

theorem gap2 (x : ℝ) :
    firstIntegrand (x ^ 2) * deriv (fun u : ℝ => u ^ 2) x =
      2 * x * Real.sqrt (1 + x ^ 4) := by
  have hpow : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
  rw [hpow.deriv]
  unfold firstIntegrand
  have hp : (x ^ 2) ^ 2 = x ^ 4 := by ring
  rw [hp]
  ring

theorem gap3 (x : ℝ) :
    deriv firstIntegral x = 2 * x * Real.sqrt (1 + x ^ 4) := by
  rw [gap1 x, gap2 x]

theorem gap4 (x : ℝ) :
    deriv secondIntegral x =
      deriv secondLowerPart x + deriv secondUpperPart x := by
  have hsum :
      secondIntegral =
        fun y : ℝ => secondLowerPart y + secondUpperPart y := by
    funext y
    unfold secondIntegral secondLowerPart secondUpperPart
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        (secondIntegrand_continuous.intervalIntegrable (y ^ 2) 0)
        (secondIntegrand_continuous.intervalIntegrable 0 (y ^ 3))).symm
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3) using 1 <;> simp <;> ring
  have hl :
      HasDerivAt secondLowerPart
        ((-secondIntegrand (x ^ 2)) * (2 * x)) x := by
    have hint : IntervalIntegrable secondIntegrand MeasureTheory.volume (x ^ 2) 0 :=
      secondIntegrand_continuous.intervalIntegrable (x ^ 2) 0
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in y..(0 : ℝ), secondIntegrand t)
          (-secondIntegrand (x ^ 2)) (x ^ 2) :=
      intervalIntegral.integral_hasDerivAt_left hint
        secondIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        secondIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in y..(0 : ℝ), secondIntegrand t) ∘
            (fun y : ℝ => y ^ 2))
          ((-secondIntegrand (x ^ 2)) * (2 * x)) x :=
      compose_real_hasDerivAt
        (g := fun y : ℝ => y ^ 2) houter h2
    simpa only [secondLowerPart, Function.comp_apply] using hcomp
  have hu :
      HasDerivAt secondUpperPart
        (secondIntegrand (x ^ 3) * (3 * x ^ 2)) x := by
    have hint : IntervalIntegrable secondIntegrand MeasureTheory.volume 0 (x ^ 3) :=
      secondIntegrand_continuous.intervalIntegrable 0 (x ^ 3)
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in (0 : ℝ)..y, secondIntegrand t)
          (secondIntegrand (x ^ 3)) (x ^ 3) :=
      intervalIntegral.integral_hasDerivAt_right hint
        secondIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        secondIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in (0 : ℝ)..y, secondIntegrand t) ∘
            (fun y : ℝ => y ^ 3))
          (secondIntegrand (x ^ 3) * (3 * x ^ 2)) x :=
      compose_real_hasDerivAt
        (g := fun y : ℝ => y ^ 3) houter h3
    simpa only [secondUpperPart, Function.comp_apply] using hcomp
  rw [hsum, hl.deriv, hu.deriv]
  simpa only [Pi.add_apply] using (hl.add hu).deriv

theorem gap5 (x : ℝ) :
    deriv secondIntegral x =
      deriv (fun u : ℝ => u ^ 3) x * secondIntegrand (x ^ 3) -
        deriv (fun u : ℝ => u ^ 2) x * secondIntegrand (x ^ 2) := by
  have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3) using 1 <;> simp <;> ring
  have hlDeriv :
      HasDerivAt secondLowerPart
        ((-secondIntegrand (x ^ 2)) * (2 * x)) x := by
    have hint : IntervalIntegrable secondIntegrand MeasureTheory.volume (x ^ 2) 0 :=
      secondIntegrand_continuous.intervalIntegrable (x ^ 2) 0
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in y..(0 : ℝ), secondIntegrand t)
          (-secondIntegrand (x ^ 2)) (x ^ 2) :=
      intervalIntegral.integral_hasDerivAt_left hint
        secondIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        secondIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in y..(0 : ℝ), secondIntegrand t) ∘
            (fun u : ℝ => u ^ 2))
          ((-secondIntegrand (x ^ 2)) * (2 * x)) x :=
      compose_real_hasDerivAt
        (g := fun u : ℝ => u ^ 2) houter h2
    simpa only [secondLowerPart, Function.comp_apply] using hcomp
  have huDeriv :
      HasDerivAt secondUpperPart
        (secondIntegrand (x ^ 3) * (3 * x ^ 2)) x := by
    have hint : IntervalIntegrable secondIntegrand MeasureTheory.volume 0 (x ^ 3) :=
      secondIntegrand_continuous.intervalIntegrable 0 (x ^ 3)
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in (0 : ℝ)..y, secondIntegrand t)
          (secondIntegrand (x ^ 3)) (x ^ 3) :=
      intervalIntegral.integral_hasDerivAt_right hint
        secondIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        secondIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in (0 : ℝ)..y, secondIntegrand t) ∘
            (fun u : ℝ => u ^ 3))
          (secondIntegrand (x ^ 3) * (3 * x ^ 2)) x :=
      compose_real_hasDerivAt
        (g := fun u : ℝ => u ^ 3) houter h3
    simpa only [secondUpperPart, Function.comp_apply] using hcomp
  have hl :
      deriv secondLowerPart x =
        -deriv (fun u : ℝ => u ^ 2) x * secondIntegrand (x ^ 2) := by
    rw [hlDeriv.deriv, h2.deriv]
    ring
  have hu :
      deriv secondUpperPart x =
        deriv (fun u : ℝ => u ^ 3) x * secondIntegrand (x ^ 3) := by
    rw [huDeriv.deriv, h3.deriv]
    ring
  rw [gap4 x, hl, hu]
  ring

theorem gap6 (x : ℝ) :
    deriv (fun u : ℝ => u ^ 3) x * secondIntegrand (x ^ 3) -
        deriv (fun u : ℝ => u ^ 2) x * secondIntegrand (x ^ 2) =
      3 * x ^ 2 / Real.sqrt (1 + x ^ 12) -
        2 * x / Real.sqrt (1 + x ^ 8) := by
  have h2 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * x) x := by
    convert ((hasDerivAt_id x).pow 2) using 1 <;> simp <;> ring
  have h3 : HasDerivAt (fun u : ℝ => u ^ 3) (3 * x ^ 2) x := by
    convert ((hasDerivAt_id x).pow 3) using 1 <;> simp <;> ring
  rw [h3.deriv, h2.deriv]
  unfold secondIntegrand
  have hp3 : (x ^ 3) ^ 4 = x ^ 12 := by ring
  have hp2 : (x ^ 2) ^ 4 = x ^ 8 := by ring
  rw [hp3, hp2]
  simp only [div_eq_mul_inv, one_mul]

theorem gap7 (x : ℝ) :
    deriv secondIntegral x =
      3 * x ^ 2 / Real.sqrt (1 + x ^ 12) -
        2 * x / Real.sqrt (1 + x ^ 8) := by
  rw [gap5 x, gap6 x]

theorem gap8 (x : ℝ) :
    deriv thirdIntegral x =
      deriv thirdLowerPart x + deriv thirdUpperPart x := by
  have hsum :
      thirdIntegral =
        fun y : ℝ => thirdLowerPart y + thirdUpperPart y := by
    funext y
    unfold thirdIntegral thirdLowerPart thirdUpperPart
    exact
      (intervalIntegral.integral_add_adjacent_intervals
        (thirdIntegrand_continuous.intervalIntegrable (Real.sin y) 0)
        (thirdIntegrand_continuous.intervalIntegrable 0 (Real.cos y))).symm
  have hl :
      HasDerivAt thirdLowerPart
        ((-thirdIntegrand (Real.sin x)) * Real.cos x) x := by
    have hint : IntervalIntegrable thirdIntegrand MeasureTheory.volume (Real.sin x) 0 :=
      thirdIntegrand_continuous.intervalIntegrable (Real.sin x) 0
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in y..(0 : ℝ), thirdIntegrand t)
          (-thirdIntegrand (Real.sin x)) (Real.sin x) :=
      intervalIntegral.integral_hasDerivAt_left hint
        thirdIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        thirdIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in y..(0 : ℝ), thirdIntegrand t) ∘ Real.sin)
          ((-thirdIntegrand (Real.sin x)) * Real.cos x) x :=
      houter.comp x (Real.hasDerivAt_sin x)
    simpa only [thirdLowerPart, Function.comp_apply] using hcomp
  have hu :
      HasDerivAt thirdUpperPart
        (thirdIntegrand (Real.cos x) * (-Real.sin x)) x := by
    have hint : IntervalIntegrable thirdIntegrand MeasureTheory.volume 0 (Real.cos x) :=
      thirdIntegrand_continuous.intervalIntegrable 0 (Real.cos x)
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in (0 : ℝ)..y, thirdIntegrand t)
          (thirdIntegrand (Real.cos x)) (Real.cos x) :=
      intervalIntegral.integral_hasDerivAt_right hint
        thirdIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        thirdIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in (0 : ℝ)..y, thirdIntegrand t) ∘ Real.cos)
          (thirdIntegrand (Real.cos x) * (-Real.sin x)) x :=
      houter.comp x (Real.hasDerivAt_cos x)
    simpa only [thirdUpperPart, Function.comp_apply] using hcomp
  rw [hsum, hl.deriv, hu.deriv]
  simpa only [Pi.add_apply] using (hl.add hu).deriv

theorem gap9 (x : ℝ) :
    deriv thirdIntegral x =
      -deriv Real.sin x * thirdIntegrand (Real.sin x) +
        deriv Real.cos x * thirdIntegrand (Real.cos x) := by
  have hs := Real.hasDerivAt_sin x
  have hc := Real.hasDerivAt_cos x
  have hlDeriv :
      HasDerivAt thirdLowerPart
        ((-thirdIntegrand (Real.sin x)) * Real.cos x) x := by
    have hint : IntervalIntegrable thirdIntegrand MeasureTheory.volume (Real.sin x) 0 :=
      thirdIntegrand_continuous.intervalIntegrable (Real.sin x) 0
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in y..(0 : ℝ), thirdIntegrand t)
          (-thirdIntegrand (Real.sin x)) (Real.sin x) :=
      intervalIntegral.integral_hasDerivAt_left hint
        thirdIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        thirdIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in y..(0 : ℝ), thirdIntegrand t) ∘ Real.sin)
          ((-thirdIntegrand (Real.sin x)) * Real.cos x) x :=
      houter.comp x hs
    simpa only [thirdLowerPart, Function.comp_apply] using hcomp
  have huDeriv :
      HasDerivAt thirdUpperPart
        (thirdIntegrand (Real.cos x) * (-Real.sin x)) x := by
    have hint : IntervalIntegrable thirdIntegrand MeasureTheory.volume 0 (Real.cos x) :=
      thirdIntegrand_continuous.intervalIntegrable 0 (Real.cos x)
    have houter :
        HasDerivAt
          (fun y : ℝ => ∫ t in (0 : ℝ)..y, thirdIntegrand t)
          (thirdIntegrand (Real.cos x)) (Real.cos x) :=
      intervalIntegral.integral_hasDerivAt_right hint
        thirdIntegrand_continuous.stronglyMeasurable.stronglyMeasurableAtFilter
        thirdIntegrand_continuous.continuousAt
    have hcomp :
        HasDerivAt
          ((fun y : ℝ => ∫ t in (0 : ℝ)..y, thirdIntegrand t) ∘ Real.cos)
          (thirdIntegrand (Real.cos x) * (-Real.sin x)) x :=
      houter.comp x hc
    simpa only [thirdUpperPart, Function.comp_apply] using hcomp
  have hl :
      deriv thirdLowerPart x =
        -deriv Real.sin x * thirdIntegrand (Real.sin x) := by
    rw [hlDeriv.deriv, hs.deriv]
    ring
  have hu :
      deriv thirdUpperPart x =
        deriv Real.cos x * thirdIntegrand (Real.cos x) := by
    rw [huDeriv.deriv, hc.deriv]
    ring
  rw [gap8 x, hl, hu]

theorem gap10 (x : ℝ) :
    -deriv Real.sin x * thirdIntegrand (Real.sin x) +
        deriv Real.cos x * thirdIntegrand (Real.cos x) =
      -Real.cos x * Real.cos (Real.pi * Real.sin x ^ 2) -
        Real.sin x * Real.cos (Real.pi * Real.cos x ^ 2) := by
  rw [(Real.hasDerivAt_sin x).deriv, (Real.hasDerivAt_cos x).deriv]
  unfold thirdIntegrand
  ring

theorem gap11 (x : ℝ) :
    -Real.cos x * Real.cos (Real.pi * Real.sin x ^ 2) -
        Real.sin x * Real.cos (Real.pi * Real.cos x ^ 2) =
      (Real.sin x - Real.cos x) *
        Real.cos (Real.pi * Real.sin x ^ 2) := by
  have harg :
      Real.pi * Real.cos x ^ 2 =
        Real.pi - Real.pi * Real.sin x ^ 2 := by
    calc
      Real.pi * Real.cos x ^ 2 =
          Real.pi * (1 - Real.sin x ^ 2) := by
            rw [← Real.sin_sq_add_cos_sq x]
            ring
      _ = Real.pi - Real.pi * Real.sin x ^ 2 := by ring
  have hcos :
      Real.cos (Real.pi * Real.cos x ^ 2) =
        -Real.cos (Real.pi * Real.sin x ^ 2) := by
    rw [harg, Real.cos_sub, Real.cos_pi, Real.sin_pi]
    ring
  rw [hcos]
  ring

theorem gap12 (x : ℝ) :
    deriv thirdIntegral x =
      (Real.sin x - Real.cos x) *
        Real.cos (Real.pi * Real.sin x ^ 2) := by
  rw [gap9 x, gap10 x, gap11 x]

end

end ProofGap.Exercise2232
