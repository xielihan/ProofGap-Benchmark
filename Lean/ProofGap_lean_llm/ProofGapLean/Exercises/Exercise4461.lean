import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Real.Sqrt

namespace ProofGap.Exercise4461

noncomputable section

open MeasureTheory Filter
open scoped Topology

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (p q : Vec3) : ℝ :=
  p.1 * q.1 + p.2.1 * q.2.1 + p.2.2 * q.2.2

def add (p q : Vec3) : Vec3 :=
  (p.1 + q.1, p.2.1 + q.2.1, p.2.2 + q.2.2)

def neg (p : Vec3) : Vec3 :=
  (-p.1, -p.2.1, -p.2.2)

def sub (p q : Vec3) : Vec3 :=
  add p (neg q)

def scale (a : ℝ) (p : Vec3) : Vec3 :=
  (a * p.1, a * p.2.1, a * p.2.2)

def radius (p : Vec3) : ℝ :=
  Real.sqrt (dot p p)

def kernel (P Q : Vec3) : ℝ :=
  1 / radius (sub P Q)

def kernelGradientP (P Q : Vec3) : Vec3 :=
  scale (-1 / radius (sub P Q) ^ 3) (sub P Q)

def kernelGradientQ (P Q : Vec3) : Vec3 :=
  neg (kernelGradientP P Q)

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def coordinateGradient (u : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (partialX u p, partialY u p, partialZ u p)

def newtonPotential (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3) : ℝ :=
  ∫ Q in V, ρ Q * kernel P Q

def potentialGradient (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3) : Vec3 :=
  coordinateGradient (newtonPotential V ρ) P

def sourceGradientIntegral (V : Set Vec3) (ρ : Vec3 → ℝ)
    (P : Vec3) : Vec3 :=
  ∫ Q in V, scale (ρ Q) (kernelGradientQ P Q)

def densityGradientIntegral (V : Set Vec3) (ρ : Vec3 → ℝ)
    (P : Vec3) : Vec3 :=
  ∫ Q in V, scale (kernel P Q) (coordinateGradient ρ Q)

def productGradientQ (ρ : Vec3 → ℝ) (P Q : Vec3) : Vec3 :=
  add (scale (ρ Q) (kernelGradientQ P Q))
    (scale (kernel P Q) (coordinateGradient ρ Q))

def productGradientIntegral (V : Set Vec3) (ρ : Vec3 → ℝ)
    (P : Vec3) : Vec3 :=
  ∫ Q in V, productGradientQ ρ P Q

def boundaryTerm (μS : Measure Vec3) (S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3) (P : Vec3) : Vec3 :=
  ∫ Q in S, scale (ρ Q * kernel P Q) (normal Q) ∂μS

def HasGradientBoundaryTheorem (μS : Measure Vec3) (V S : Set Vec3)
    (normal : Vec3 → Vec3) : Prop :=
  ∀ g : Vec3 → ℝ, ContDiffOn ℝ 1 g (closure V) →
    (∫ Q in V, coordinateGradient g Q) =
      ∫ Q in S, scale (g Q) (normal Q) ∂μS

def exteriorFormula (μS : Measure Vec3) (V S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3) (P : Vec3) : Vec3 :=
  add (neg (boundaryTerm μS S ρ normal P))
    (densityGradientIntegral V ρ P)

def euclideanBall (P : Vec3) (ε : ℝ) : Set Vec3 :=
  {Q | radius (sub P Q) < ε}

def localSourceIntegral (ρ : Vec3 → ℝ) (P : Vec3) (ε : ℝ) : ℝ :=
  ∫ Q in euclideanBall P ε, ρ Q * kernel P Q

def localAbsoluteIntegral (ρ : Vec3 → ℝ) (P : Vec3) (ε : ℝ) : ℝ :=
  ∫ Q in euclideanBall P ε, |ρ Q| * kernel P Q

def localKernelIntegral (P : Vec3) (ε : ℝ) : ℝ :=
  ∫ Q in euclideanBall P ε, kernel P Q

def LocallyBoundedAt (ρ : Vec3 → ℝ) (P : Vec3) : Prop :=
  ∃ ε M : ℝ, 0 < ε ∧ 0 ≤ M ∧
    ∀ Q ∈ euclideanBall P ε, |ρ Q| ≤ M

def AtMostInverseSingularity (g : Vec3 → ℝ) (P : Vec3) : Prop :=
  ∃ C ε : ℝ, 0 ≤ C ∧ 0 < ε ∧
    ∀ Q : Vec3, 0 < radius (sub P Q) →
      radius (sub P Q) < ε →
        |g Q| ≤ C / radius (sub P Q)

def HasPuncturedGradientBoundaryTheorem (μS : Measure Vec3)
    (V S : Set Vec3) (normal : Vec3 → Vec3) (P : Vec3) : Prop :=
  ∀ g : Vec3 → ℝ,
    ContDiffOn ℝ 1 g (closure V \ {P}) →
    IntegrableOn (coordinateGradient g) V →
    AtMostInverseSingularity g P →
      (∫ Q in V, coordinateGradient g Q) =
        ∫ Q in S, scale (g Q) (normal Q) ∂μS

/-- Differentiation under the Newton-potential integral when the evaluation
point stays outside the compact source. -/
def SatisfiesExteriorPotentialDifferentiation : Prop :=
  ∀ (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3),
    IsCompact V → MeasurableSet V → ContinuousOn ρ V →
      P ∉ closure V →
        potentialGradient V ρ P =
          ∫ Q in V, scale (ρ Q) (kernelGradientP P Q)

/-- Differentiation under the weakly singular Newton-potential integral at an
interior point.  This is stated uniformly over all admissible data instead of
repeating the desired equality as a case-specific hypothesis. -/
def SatisfiesInteriorPotentialDifferentiation : Prop :=
  ∀ (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3),
    IsCompact V → MeasurableSet V → ContDiff ℝ 1 ρ →
      P ∈ interior V →
        potentialGradient V ρ P =
          ∫ Q in V, scale (ρ Q) (kernelGradientP P Q)

/-- The three-dimensional polar-coordinate formula
`∫_{B(P,ε)} |P-Q|⁻¹ dQ = 2π ε²`, together with its integrability assertion. -/
def SatisfiesNewtonKernelBallFormula : Prop :=
  ∀ (P : Vec3) (ε : ℝ), 0 < ε →
    IntegrableOn (kernel P) (euclideanBall P ε) ∧
      localKernelIntegral P ε = 2 * Real.pi * ε ^ 2

def potentialPartialX (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3) : ℝ :=
  partialX (newtonPotential V ρ) P

def potentialPartialY (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3) : ℝ :=
  partialY (newtonPotential V ρ) P

def potentialPartialZ (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3) : ℝ :=
  partialZ (newtonPotential V ρ) P

@[simp] private theorem add_eq_add (p q : Vec3) :
    add p q = p + q := by
  rfl

@[simp] private theorem neg_eq_neg (p : Vec3) :
    neg p = -p := by
  rfl

@[simp] private theorem scale_eq_smul (a : ℝ) (p : Vec3) :
    scale a p = a • p := by
  rfl

private theorem kernelGradientP_neg_kernelGradientQ
    (P Q : Vec3) :
    kernelGradientP P Q = neg (kernelGradientQ P Q) := by
  simp [kernelGradientQ]

private theorem dot_self_pos (p : Vec3) (hp : p ≠ 0) :
    0 < dot p p := by
  rcases p with ⟨x, y, z⟩
  simp only [Prod.fst, Prod.snd, dot] at hp ⊢
  by_contra hn
  have hle : x * x + y * y + z * z ≤ 0 := le_of_not_gt hn
  have hx : x = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hy : y = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  have hz : z = 0 := by
    nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
  apply hp
  simp [hx, hy, hz]

private theorem radius_pos_of_ne_zero (p : Vec3) (hp : p ≠ 0) :
    0 < radius p := by
  unfold radius
  exact Real.sqrt_pos.2 (dot_self_pos p hp)

private theorem hasDerivAt_inverseSqrtSumSq
    (x y z : ℝ) (hpos : 0 < x ^ 2 + y ^ 2 + z ^ 2) :
    HasDerivAt
      (fun t : ℝ => 1 / Real.sqrt (t ^ 2 + y ^ 2 + z ^ 2))
      (-x / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 3) x := by
  have hq :
      HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2 + z ^ 2)
        (2 * x) x := by
    simpa [two_mul] using
      ((((hasDerivAt_id x).pow 2).add_const (y ^ 2)).add_const
        (z ^ 2))
  have hs :
      HasDerivAt
        (fun t : ℝ => Real.sqrt (t ^ 2 + y ^ 2 + z ^ 2))
        (1 / (2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) *
          (2 * x)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_sqrt hpos.ne').comp x hq
  have hsqrt_ne :
      Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hi := hs.inv hsqrt_ne
  have hderiv :
      -(1 / (2 * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2)) *
          (2 * x)) /
          Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 =
        -x / Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) ^ 3 := by
    field_simp [hsqrt_ne]
    <;> ring
  rw [hderiv] at hi
  simpa only [Function.comp_apply, one_div] using hi

private theorem hasDerivAt_inverseRadiusX
    (p : Vec3) (hp : p ≠ 0) :
    HasDerivAt (fun x : ℝ => 1 / radius (x, p.2.1, p.2.2))
      (-p.1 / radius p ^ 3) p.1 := by
  simpa [radius, dot, pow_two] using
    hasDerivAt_inverseSqrtSumSq p.1 p.2.1 p.2.2
      (by simpa [dot, pow_two] using dot_self_pos p hp)

private theorem hasDerivAt_inverseRadiusY
    (p : Vec3) (hp : p ≠ 0) :
    HasDerivAt (fun y : ℝ => 1 / radius (p.1, y, p.2.2))
      (-p.2.1 / radius p ^ 3) p.2.1 := by
  simpa [radius, dot, pow_two, add_comm, add_left_comm, add_assoc] using
    hasDerivAt_inverseSqrtSumSq p.2.1 p.1 p.2.2
      (by
        simpa [dot, pow_two, add_comm, add_left_comm, add_assoc] using
          dot_self_pos p hp)

private theorem hasDerivAt_inverseRadiusZ
    (p : Vec3) (hp : p ≠ 0) :
    HasDerivAt (fun z : ℝ => 1 / radius (p.1, p.2.1, z))
      (-p.2.2 / radius p ^ 3) p.2.2 := by
  simpa [radius, dot, pow_two, add_comm, add_left_comm, add_assoc] using
    hasDerivAt_inverseSqrtSumSq p.2.2 p.1 p.2.1
      (by
        simpa [dot, pow_two, add_comm, add_left_comm, add_assoc] using
          dot_self_pos p hp)

private theorem sub_ne_zero_of_ne (P Q : Vec3) (hPQ : P ≠ Q) :
    sub P Q ≠ 0 := by
  simpa [sub] using sub_ne_zero.mpr hPQ

private theorem hasDerivAt_kernelX
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun x : ℝ => kernel P (x, Q.2.1, Q.2.2))
      ((sub P Q).1 / radius (sub P Q) ^ 3) Q.1 := by
  have hinner :
      HasDerivAt (fun x : ℝ => P.1 - x) (-1) Q.1 := by
    simpa using
      (hasDerivAt_const Q.1 P.1).sub (hasDerivAt_id Q.1)
  have hcomp :=
    (hasDerivAt_inverseRadiusX (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp Q.1 hinner
  convert hcomp using 1 <;>
    simp [Function.comp_def, kernel, sub, add, neg] <;> ring

private theorem hasDerivAt_kernelY
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun y : ℝ => kernel P (Q.1, y, Q.2.2))
      ((sub P Q).2.1 / radius (sub P Q) ^ 3) Q.2.1 := by
  have hinner :
      HasDerivAt (fun y : ℝ => P.2.1 - y) (-1) Q.2.1 := by
    simpa using
      (hasDerivAt_const Q.2.1 P.2.1).sub
        (hasDerivAt_id Q.2.1)
  have hcomp :=
    (hasDerivAt_inverseRadiusY (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp Q.2.1 hinner
  convert hcomp using 1 <;>
    simp [Function.comp_def, kernel, sub, add, neg] <;> ring

private theorem hasDerivAt_kernelZ
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun z : ℝ => kernel P (Q.1, Q.2.1, z))
      ((sub P Q).2.2 / radius (sub P Q) ^ 3) Q.2.2 := by
  have hinner :
      HasDerivAt (fun z : ℝ => P.2.2 - z) (-1) Q.2.2 := by
    simpa using
      (hasDerivAt_const Q.2.2 P.2.2).sub
        (hasDerivAt_id Q.2.2)
  have hcomp :=
    (hasDerivAt_inverseRadiusZ (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp Q.2.2 hinner
  convert hcomp using 1 <;>
    simp [Function.comp_def, kernel, sub, add, neg] <;> ring

private theorem coordinateGradient_kernel
    (P Q : Vec3) (hPQ : P ≠ Q) :
    coordinateGradient (kernel P) Q = kernelGradientQ P Q := by
  unfold coordinateGradient partialX partialY partialZ
  rw [(hasDerivAt_kernelX P Q hPQ).deriv,
    (hasDerivAt_kernelY P Q hPQ).deriv,
    (hasDerivAt_kernelZ P Q hPQ).deriv]
  unfold kernelGradientQ kernelGradientP scale neg
  ext <;> simp <;> ring

private theorem density_slice_x_differentiableAt
    (ρ : Vec3 → ℝ) (hρ : ContDiff ℝ 1 ρ) (Q : Vec3) :
    DifferentiableAt ℝ (fun x => ρ (x, Q.2.1, Q.2.2)) Q.1 := by
  have hcurve :
      DifferentiableAt ℝ (fun x : ℝ => (x, Q.2.1, Q.2.2)) Q.1 :=
    differentiableAt_id.prodMk
      ((differentiableAt_const Q.2.1).prodMk
        (differentiableAt_const Q.2.2))
  exact
    (hρ.differentiable one_ne_zero Q).comp Q.1 hcurve

private theorem density_slice_y_differentiableAt
    (ρ : Vec3 → ℝ) (hρ : ContDiff ℝ 1 ρ) (Q : Vec3) :
    DifferentiableAt ℝ (fun y => ρ (Q.1, y, Q.2.2)) Q.2.1 := by
  have hcurve :
      DifferentiableAt ℝ (fun y : ℝ => (Q.1, y, Q.2.2)) Q.2.1 :=
    (differentiableAt_const Q.1).prodMk
      (differentiableAt_id.prodMk
        (differentiableAt_const Q.2.2))
  exact
    (hρ.differentiable one_ne_zero Q).comp Q.2.1 hcurve

private theorem density_slice_z_differentiableAt
    (ρ : Vec3 → ℝ) (hρ : ContDiff ℝ 1 ρ) (Q : Vec3) :
    DifferentiableAt ℝ (fun z => ρ (Q.1, Q.2.1, z)) Q.2.2 := by
  have hcurve :
      DifferentiableAt ℝ (fun z : ℝ => (Q.1, Q.2.1, z)) Q.2.2 :=
    (differentiableAt_const Q.1).prodMk
      ((differentiableAt_const Q.2.1).prodMk
        differentiableAt_id)
  exact
    (hρ.differentiable one_ne_zero Q).comp Q.2.2 hcurve

private theorem partialX_density_kernel
    (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hPQ : P ≠ Q) :
    partialX (fun X => ρ X * kernel P X) Q =
      ρ Q * (kernelGradientQ P Q).1 +
        kernel P Q * partialX ρ Q := by
  have hmul := deriv_mul
    (density_slice_x_differentiableAt ρ hρ Q)
    (hasDerivAt_kernelX P Q hPQ).differentiableAt
  unfold partialX
  change
    deriv
        ((fun x : ℝ => ρ (x, Q.2.1, Q.2.2)) *
          fun x => kernel P (x, Q.2.1, Q.2.2)) Q.1 =
      _
  rw [hmul, (hasDerivAt_kernelX P Q hPQ).deriv]
  have hk :=
    congrArg Prod.fst (coordinateGradient_kernel P Q hPQ)
  unfold coordinateGradient partialX at hk
  rw [(hasDerivAt_kernelX P Q hPQ).deriv] at hk
  simp only [Prod.fst, Prod.snd] at hk
  rw [hk]
  ring

private theorem partialY_density_kernel
    (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hPQ : P ≠ Q) :
    partialY (fun X => ρ X * kernel P X) Q =
      ρ Q * (kernelGradientQ P Q).2.1 +
        kernel P Q * partialY ρ Q := by
  have hmul := deriv_mul
    (density_slice_y_differentiableAt ρ hρ Q)
    (hasDerivAt_kernelY P Q hPQ).differentiableAt
  unfold partialY
  change
    deriv
        ((fun y : ℝ => ρ (Q.1, y, Q.2.2)) *
          fun y => kernel P (Q.1, y, Q.2.2)) Q.2.1 =
      _
  rw [hmul, (hasDerivAt_kernelY P Q hPQ).deriv]
  have hk :=
    congrArg (fun v : Vec3 => v.2.1)
      (coordinateGradient_kernel P Q hPQ)
  unfold coordinateGradient partialY at hk
  rw [(hasDerivAt_kernelY P Q hPQ).deriv] at hk
  simp only [Prod.fst, Prod.snd] at hk
  rw [hk]
  ring

private theorem partialZ_density_kernel
    (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hPQ : P ≠ Q) :
    partialZ (fun X => ρ X * kernel P X) Q =
      ρ Q * (kernelGradientQ P Q).2.2 +
        kernel P Q * partialZ ρ Q := by
  have hmul := deriv_mul
    (density_slice_z_differentiableAt ρ hρ Q)
    (hasDerivAt_kernelZ P Q hPQ).differentiableAt
  unfold partialZ
  change
    deriv
        ((fun z : ℝ => ρ (Q.1, Q.2.1, z)) *
          fun z => kernel P (Q.1, Q.2.1, z)) Q.2.2 =
      _
  rw [hmul, (hasDerivAt_kernelZ P Q hPQ).deriv]
  have hk :=
    congrArg (fun v : Vec3 => v.2.2)
      (coordinateGradient_kernel P Q hPQ)
  unfold coordinateGradient partialZ at hk
  rw [(hasDerivAt_kernelZ P Q hPQ).deriv] at hk
  simp only [Prod.fst, Prod.snd] at hk
  rw [hk]
  ring

private theorem coordinateGradient_density_kernel
    (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hPQ : P ≠ Q) :
    coordinateGradient (fun X => ρ X * kernel P X) Q =
      productGradientQ ρ P Q := by
  unfold coordinateGradient productGradientQ add scale
  apply Prod.ext
  · exact partialX_density_kernel ρ P Q hρ hPQ
  · apply Prod.ext
    · exact partialY_density_kernel ρ P Q hρ hPQ
    · exact partialZ_density_kernel ρ P Q hρ hPQ

private theorem contDiffAt_kernel
    (P Q : Vec3) (hPQ : P ≠ Q) :
    ContDiffAt ℝ 1 (kernel P) Q := by
  have hsquare :
      ContDiff ℝ 1 (fun X : Vec3 => dot (sub P X) (sub P X)) := by
    unfold dot sub add neg
    fun_prop
  have hsquare_ne :
      dot (sub P Q) (sub P Q) ≠ 0 :=
    (dot_self_pos (sub P Q) (sub_ne_zero_of_ne P Q hPQ)).ne'
  have hsqrt :
      ContDiffAt ℝ 1
        (fun X : Vec3 =>
          Real.sqrt (dot (sub P X) (sub P X))) Q :=
    hsquare.contDiffAt.sqrt hsquare_ne
  have hradius_ne : radius (sub P Q) ≠ 0 :=
    (radius_pos_of_ne_zero
      (sub P Q) (sub_ne_zero_of_ne P Q hPQ)).ne'
  unfold kernel
  change
    ContDiffAt ℝ 1
      (fun X : Vec3 =>
        1 / Real.sqrt (dot (sub P X) (sub P X))) Q
  simpa only [one_div] using hsqrt.inv hradius_ne

private theorem contDiffOn_density_kernel
    (ρ : Vec3 → ℝ) (P : Vec3) (s : Set Vec3)
    (hρ : ContDiff ℝ 1 ρ)
    (hs : ∀ Q ∈ s, P ≠ Q) :
    ContDiffOn ℝ 1 (fun Q => ρ Q * kernel P Q) s := by
  intro Q hQ
  exact hρ.contDiffAt.contDiffWithinAt.mul
    (contDiffAt_kernel P Q (hs Q hQ)).contDiffWithinAt

private theorem radius_nonneg (p : Vec3) :
    0 ≤ radius p := by
  exact Real.sqrt_nonneg _

private theorem kernel_nonneg (P Q : Vec3) :
    0 ≤ kernel P Q := by
  unfold kernel
  exact one_div_nonneg.mpr (radius_nonneg _)

private theorem measurable_kernel (P : Vec3) :
    Measurable (kernel P) := by
  unfold kernel radius dot sub add neg
  fun_prop

private theorem measurableSet_euclideanBall (P : Vec3) (ε : ℝ) :
    MeasurableSet (euclideanBall P ε) := by
  unfold euclideanBall
  have hmeas :
      Measurable (fun Q : Vec3 => radius (sub P Q)) := by
    unfold radius dot sub add neg
    fun_prop
  exact measurableSet_lt hmeas measurable_const

private theorem integrableOn_kernelGradientP
    (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (h :
      IntegrableOn
        (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V) :
    IntegrableOn
      (fun Q => scale (ρ Q) (kernelGradientP P Q)) V := by
  have hneg :
      IntegrableOn
        (fun Q => -(scale (ρ Q) (kernelGradientQ P Q))) V := by
    simpa only [Pi.neg_apply] using h.neg
  apply hneg.congr
  filter_upwards with Q
  rw [kernelGradientP_neg_kernelGradientQ]
  simp only [neg_eq_neg, scale_eq_smul, smul_neg, neg_neg]

private theorem potential_eq_neg_source_of_diff
    (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hgradient :
      potentialGradient V ρ P =
        ∫ Q in V, scale (ρ Q) (kernelGradientP P Q)) :
    potentialGradient V ρ P =
      neg (sourceGradientIntegral V ρ P) := by
  rw [hgradient]
  unfold sourceGradientIntegral
  simp only [neg_eq_neg, ← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with Q
  simp [kernelGradientP_neg_kernelGradientQ]

private theorem neg_source_eq_split
    (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    neg (sourceGradientIntegral V ρ P) =
      add (neg (productGradientIntegral V ρ P))
        (densityGradientIntegral V ρ P) := by
  have hproduct :
      productGradientIntegral V ρ P =
        add (sourceGradientIntegral V ρ P)
          (densityGradientIntegral V ρ P) := by
    unfold productGradientIntegral sourceGradientIntegral
      densityGradientIntegral productGradientQ
    simpa only [add_eq_add] using
      MeasureTheory.integral_add hintegrable.1 hintegrable.2
  rw [hproduct]
  simp only [add_eq_add, neg_eq_neg]
  abel

private theorem product_atMostInverseSingularity
    (ρ : Vec3 → ℝ) (P : Vec3)
    (hloc : LocallyBoundedAt ρ P) :
    AtMostInverseSingularity
      (fun Q => ρ Q * kernel P Q) P := by
  rcases hloc with ⟨ε, M, hε, hM, hbound⟩
  refine ⟨M, ε, hM, hε, ?_⟩
  intro Q hradius hradiusε
  have hQ : Q ∈ euclideanBall P ε := hradiusε
  calc
    |ρ Q * kernel P Q| =
        |ρ Q| * kernel P Q := by
      rw [abs_mul, abs_of_nonneg (kernel_nonneg P Q)]
    _ ≤ M * kernel P Q :=
      mul_le_mul_of_nonneg_right (hbound Q hQ)
        (kernel_nonneg P Q)
    _ = M / radius (sub P Q) := by
      unfold kernel
      ring

private theorem ae_ne_for_volume_restrict
    (V : Set Vec3) (P : Vec3) :
    ∀ᵐ Q : Vec3 ∂(volume.restrict V), Q ≠ P := by
  have hsingleton :
      (volume.restrict V) ({P} : Set Vec3) = 0 := by
    rw [Measure.restrict_apply (MeasurableSet.singleton P)]
    exact
      measure_mono_null Set.inter_subset_left
        (by
          rw [Measure.volume_eq_prod ℝ (ℝ × ℝ)]
          exact MeasureTheory.measure_singleton P)
  exact ae_iff.2 (by simpa using hsingleton)

private theorem integrableOn_product_coordinateGradient
    (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hρ : ContDiff ℝ 1 ρ)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    IntegrableOn
      (coordinateGradient (fun Q => ρ Q * kernel P Q)) V := by
  have hproduct :
      IntegrableOn (productGradientQ ρ P) V := by
    unfold productGradientQ
    simpa only [add_eq_add] using
      hintegrable.1.add hintegrable.2
  apply hproduct.congr
  filter_upwards [ae_ne_for_volume_restrict V P] with Q hQP
  exact (coordinateGradient_density_kernel ρ P Q hρ hQP.symm).symm

private theorem integral_coordinateGradient_eq_product
    (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hρ : ContDiff ℝ 1 ρ) :
    (∫ Q in V,
        coordinateGradient (fun X => ρ X * kernel P X) Q) =
      productGradientIntegral V ρ P := by
  unfold productGradientIntegral
  apply MeasureTheory.integral_congr_ae
  filter_upwards [ae_ne_for_volume_restrict V P] with Q hQP
  exact coordinateGradient_density_kernel ρ P Q hρ hQP.symm

theorem gap1 (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContinuousOn ρ V) (hP : P ∉ closure V)
    (hDifferentiation : SatisfiesExteriorPotentialDifferentiation) :
    potentialGradient V ρ P =
      ∫ Q in V, scale (ρ Q) (kernelGradientP P Q) := by
  exact hDifferentiation V ρ P hV hVm hρ hP

theorem gap2 (P Q : Vec3) (hne : P ≠ Q) :
    kernelGradientP P Q =
      scale (-1 / radius (sub P Q) ^ 3) (sub P Q) := by
  rfl

theorem gap3 (P Q : Vec3) (hne : P ≠ Q) :
    scale (-1 / radius (sub P Q) ^ 3) (sub P Q) =
      neg (kernelGradientQ P Q) := by
  exact kernelGradientP_neg_kernelGradientQ P Q

theorem gap4 (P Q : Vec3) (hne : P ≠ Q) :
    kernelGradientP P Q = neg (kernelGradientQ P Q) := by
  exact kernelGradientP_neg_kernelGradientQ P Q

theorem gap5 (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContinuousOn ρ V) (hP : P ∉ closure V)
    (hDifferentiation : SatisfiesExteriorPotentialDifferentiation) :
    potentialGradient V ρ P = neg (sourceGradientIntegral V ρ P) := by
  rw [hDifferentiation V ρ P hV hVm hρ hP]
  unfold sourceGradientIntegral
  simp only [neg_eq_neg, ← MeasureTheory.integral_neg]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with Q
  simp [kernelGradientP_neg_kernelGradientQ]

theorem gap6 (V : Set Vec3) (ρ : Vec3 → ℝ)
    (P : Vec3) (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContDiff ℝ 1 ρ) (hP : P ∉ closure V)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    neg (sourceGradientIntegral V ρ P) =
      add (neg (productGradientIntegral V ρ P))
        (densityGradientIntegral V ρ P) := by
  have hproduct :
      productGradientIntegral V ρ P =
        add (sourceGradientIntegral V ρ P)
          (densityGradientIntegral V ρ P) := by
    unfold productGradientIntegral sourceGradientIntegral
      densityGradientIntegral productGradientQ
    simpa only [add_eq_add] using
      MeasureTheory.integral_add hintegrable.1 hintegrable.2
  rw [hproduct]
  simp only [add_eq_add, neg_eq_neg]
  abel

theorem gap7 (μS : Measure Vec3) (V S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hS : S = frontier V) (hρ : ContDiff ℝ 1 ρ)
    (hboundary : HasGradientBoundaryTheorem μS V S normal)
    (P : Vec3) (hP : P ∉ closure V) :
    productGradientIntegral V ρ P =
      boundaryTerm μS S ρ normal P := by
  have hsmooth :
      ContDiffOn ℝ 1
        (fun Q => ρ Q * kernel P Q) (closure V) := by
    apply contDiffOn_density_kernel ρ P (closure V) hρ
    intro Q hQ hPQ
    apply hP
    simpa [hPQ] using hQ
  have hpoint :
      (∫ Q in V,
          coordinateGradient (fun X => ρ X * kernel P X) Q) =
        productGradientIntegral V ρ P := by
    unfold productGradientIntegral
    apply MeasureTheory.integral_congr_ae
    filter_upwards [ae_restrict_mem hVm] with Q hQV
    apply coordinateGradient_density_kernel ρ P Q hρ
    intro hPQ
    subst Q
    exact hP (subset_closure hQV)
  unfold HasGradientBoundaryTheorem at hboundary
  calc
    productGradientIntegral V ρ P =
        ∫ Q in V,
          coordinateGradient (fun X => ρ X * kernel P X) Q :=
      hpoint.symm
    _ = ∫ Q in S,
        scale ((fun X => ρ X * kernel P X) Q) (normal Q) ∂μS :=
      hboundary (fun X => ρ X * kernel P X) hsmooth
    _ = boundaryTerm μS S ρ normal P := by
      rfl

theorem gap8 (μS : Measure Vec3) (V S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hS : S = frontier V) (hρ : ContDiff ℝ 1 ρ)
    (hboundary : HasGradientBoundaryTheorem μS V S normal)
    (P : Vec3) (hP : P ∉ closure V)
    (hDifferentiation : SatisfiesExteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialGradient V ρ P =
      exteriorFormula μS V S ρ normal P := by
  have hsource :
      potentialGradient V ρ P =
        neg (sourceGradientIntegral V ρ P) :=
    gap5 V ρ P hV hVm hρ.continuous.continuousOn hP
      hDifferentiation
  have hsplit :
      neg (sourceGradientIntegral V ρ P) =
        add (neg (productGradientIntegral V ρ P))
          (densityGradientIntegral V ρ P) :=
    gap6 V ρ P hV hVm hρ hP hintegrable
  have hboundaryTerm :
      productGradientIntegral V ρ P =
        boundaryTerm μS S ρ normal P :=
    gap7 μS V S ρ normal hV hVm hS hρ hboundary P hP
  unfold exteriorFormula
  rw [hsource, hsplit, hboundaryTerm]

theorem gap9 (ρ : Vec3 → ℝ) (P : Vec3) (ε : ℝ)
    (hρ : Continuous ρ) :
    |localSourceIntegral ρ P ε| ≤ localAbsoluteIntegral ρ P ε := by
  unfold localSourceIntegral localAbsoluteIntegral
  calc
    |∫ Q in euclideanBall P ε, ρ Q * kernel P Q| =
        ‖∫ Q in euclideanBall P ε, ρ Q * kernel P Q‖ := by
      rfl
    _ ≤ ∫ Q in euclideanBall P ε, ‖ρ Q * kernel P Q‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ Q in euclideanBall P ε, |ρ Q| * kernel P Q := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with Q
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (kernel_nonneg P Q)]

theorem gap10 (ρ : Vec3 → ℝ) (P : Vec3) (ε M : ℝ)
    (hρc : Continuous ρ) (hε : 0 < ε) (hM : 0 ≤ M)
    (hρ : ∀ Q ∈ euclideanBall P ε, |ρ Q| ≤ M)
    (hkernelIntegrable :
      IntegrableOn (kernel P) (euclideanBall P ε)) :
    localAbsoluteIntegral ρ P ε ≤ M * localKernelIntegral P ε := by
  unfold localAbsoluteIntegral localKernelIntegral
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono_of_nonneg
  · filter_upwards with Q
    exact mul_nonneg (abs_nonneg _) (kernel_nonneg P Q)
  · exact hkernelIntegrable.const_mul M
  · filter_upwards
      [ae_restrict_mem (measurableSet_euclideanBall P ε)] with Q hQ
    exact mul_le_mul_of_nonneg_right (hρ Q hQ)
      (kernel_nonneg P Q)

theorem gap11 (P : Vec3) (ε M : ℝ) (hε : 0 < ε)
    (hkernelFormula : SatisfiesNewtonKernelBallFormula) :
    M * localKernelIntegral P ε = 2 * M * Real.pi * ε ^ 2 := by
  rw [(hkernelFormula P ε hε).2]
  ring

theorem gap12 (ρ : Vec3 → ℝ) (P : Vec3) (ε M : ℝ)
    (hρc : Continuous ρ) (hε : 0 < ε) (hM : 0 ≤ M)
    (hρ : ∀ Q ∈ euclideanBall P ε, |ρ Q| ≤ M)
    (hkernelFormula : SatisfiesNewtonKernelBallFormula) :
    |localSourceIntegral ρ P ε| ≤ 2 * M * Real.pi * ε ^ 2 := by
  have hkernelIntegrable :
      IntegrableOn (kernel P) (euclideanBall P ε) :=
    (hkernelFormula P ε hε).1
  calc
    |localSourceIntegral ρ P ε| ≤
        localAbsoluteIntegral ρ P ε :=
      gap9 ρ P ε hρc
    _ ≤ M * localKernelIntegral P ε :=
      gap10 ρ P ε M hρc hε hM hρ hkernelIntegrable
    _ = 2 * M * Real.pi * ε ^ 2 :=
      gap11 P ε M hε hkernelFormula

theorem gap13 (M : ℝ) :
    Tendsto (fun ε : ℝ => 2 * M * Real.pi * ε ^ 2)
      (𝓝 0) (𝓝 0) := by
  have hcont :
      Continuous (fun ε : ℝ => 2 * M * Real.pi * ε ^ 2) := by
    fun_prop
  have hzero :
      ContinuousAt (fun ε : ℝ => 2 * M * Real.pi * ε ^ 2) 0 :=
    hcont.continuousAt
  unfold ContinuousAt at hzero
  norm_num at hzero
  exact hzero

theorem gap14 (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContDiff ℝ 1 ρ) (hP : P ∈ interior V)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialPartialX V ρ P =
      ∫ Q in V, ρ Q * (kernelGradientP P Q).1 := by
  have hint :
      IntegrableOn
        (fun Q => scale (ρ Q) (kernelGradientP P Q)) V :=
    integrableOn_kernelGradientP V ρ P hintegrable.1
  change (potentialGradient V ρ P).1 = _
  rw [hDifferentiation V ρ P hV hVm hρ hP,
    fst_integral hint]
  rfl

theorem gap15 (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContDiff ℝ 1 ρ) (hP : P ∈ interior V)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialPartialY V ρ P =
      ∫ Q in V, ρ Q * (kernelGradientP P Q).2.1 := by
  have hint :
      IntegrableOn
        (fun Q => scale (ρ Q) (kernelGradientP P Q)) V :=
    integrableOn_kernelGradientP V ρ P hintegrable.1
  change (potentialGradient V ρ P).2.1 = _
  rw [hDifferentiation V ρ P hV hVm hρ hP,
    snd_integral hint,
    fst_integral hint.snd]
  rfl

theorem gap16 (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContDiff ℝ 1 ρ) (hP : P ∈ interior V)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialPartialZ V ρ P =
      ∫ Q in V, ρ Q * (kernelGradientP P Q).2.2 := by
  have hint :
      IntegrableOn
        (fun Q => scale (ρ Q) (kernelGradientP P Q)) V :=
    integrableOn_kernelGradientP V ρ P hintegrable.1
  change (potentialGradient V ρ P).2.2 = _
  rw [hDifferentiation V ρ P hV hVm hρ hP,
    snd_integral hint,
    snd_integral hint.snd]
  rfl

theorem gap17 (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContDiff ℝ 1 ρ) (hP : P ∈ interior V)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation) :
    potentialGradient V ρ P =
      ∫ Q in V, scale (ρ Q) (kernelGradientP P Q) := by
  exact hDifferentiation V ρ P hV hVm hρ hP

theorem gap18 (V : Set Vec3) (ρ : Vec3 → ℝ) (P : Vec3)
    (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContDiff ℝ 1 ρ) (hP : P ∈ interior V)
    (hloc : LocallyBoundedAt ρ P)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation) :
    potentialGradient V ρ P = neg (sourceGradientIntegral V ρ P) := by
  exact potential_eq_neg_source_of_diff V ρ P
    (hDifferentiation V ρ P hV hVm hρ hP)

theorem gap19 (V : Set Vec3) (ρ : Vec3 → ℝ)
    (P : Vec3) (hV : IsCompact V) (hVm : MeasurableSet V)
    (hρ : ContDiff ℝ 1 ρ) (hP : P ∈ interior V)
    (hloc : LocallyBoundedAt ρ P)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialGradient V ρ P =
      add (neg (productGradientIntegral V ρ P))
        (densityGradientIntegral V ρ P) := by
  rw [potential_eq_neg_source_of_diff V ρ P
    (hDifferentiation V ρ P hV hVm hρ hP)]
  exact neg_source_eq_split V ρ P hintegrable

theorem gap20 (μS : Measure Vec3) (V S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (P : Vec3) (hV : IsCompact V) (hVm : MeasurableSet V)
    (hS : S = frontier V) (hρ : ContDiff ℝ 1 ρ)
    (hP : P ∈ interior V) (hloc : LocallyBoundedAt ρ P)
    (hboundary :
      HasPuncturedGradientBoundaryTheorem μS V S normal P)
    (hproductIntegrable :
      IntegrableOn
        (coordinateGradient (fun Q => ρ Q * kernel P Q)) V) :
    productGradientIntegral V ρ P =
      boundaryTerm μS S ρ normal P := by
  have hsmooth :
      ContDiffOn ℝ 1
        (fun Q => ρ Q * kernel P Q) (closure V \ {P}) := by
    apply
      contDiffOn_density_kernel ρ P (closure V \ {P}) hρ
    intro Q hQ
    have hQP : Q ≠ P := by
      simpa only [Set.mem_singleton_iff] using hQ.2
    exact hQP.symm
  have hsingular :
      AtMostInverseSingularity
        (fun Q => ρ Q * kernel P Q) P :=
    product_atMostInverseSingularity ρ P hloc
  unfold HasPuncturedGradientBoundaryTheorem at hboundary
  calc
    productGradientIntegral V ρ P =
        ∫ Q in V,
          coordinateGradient (fun X => ρ X * kernel P X) Q :=
      (integral_coordinateGradient_eq_product V ρ P hρ).symm
    _ = ∫ Q in S,
        scale ((fun X => ρ X * kernel P X) Q) (normal Q) ∂μS :=
      hboundary (fun X => ρ X * kernel P X)
        hsmooth hproductIntegrable hsingular
    _ = boundaryTerm μS S ρ normal P := by
      rfl

theorem gap21 (μS : Measure Vec3) (V S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (P : Vec3) (hV : IsCompact V) (hVm : MeasurableSet V)
    (hS : S = frontier V) (hρ : ContDiff ℝ 1 ρ)
    (hP : P ∈ interior V) (hloc : LocallyBoundedAt ρ P)
    (hboundary :
      HasPuncturedGradientBoundaryTheorem μS V S normal P)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialGradient V ρ P =
      exteriorFormula μS V S ρ normal P := by
  have hproductIntegrable :
      IntegrableOn
        (coordinateGradient (fun Q => ρ Q * kernel P Q)) V :=
    integrableOn_product_coordinateGradient
      V ρ P hρ hintegrable
  have hsplit :
      potentialGradient V ρ P =
        add (neg (productGradientIntegral V ρ P))
          (densityGradientIntegral V ρ P) :=
    gap19 V ρ P hV hVm hρ hP hloc
      hDifferentiation hintegrable
  have hboundaryTerm :
      productGradientIntegral V ρ P =
        boundaryTerm μS S ρ normal P :=
    gap20 μS V S ρ normal P hV hVm hS hρ hP hloc
      hboundary hproductIntegrable
  unfold exteriorFormula
  rw [hsplit, hboundaryTerm]

theorem gap22 (μS : Measure Vec3) (V S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (P : Vec3) (hV : IsCompact V) (hVm : MeasurableSet V)
    (hS : S = frontier V) (hρ : ContDiff ℝ 1 ρ)
    (hP : P ∈ interior V) (hloc : LocallyBoundedAt ρ P)
    (hboundary :
      HasPuncturedGradientBoundaryTheorem μS V S normal P)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialGradient V ρ P =
      add (neg (boundaryTerm μS S ρ normal P))
        (densityGradientIntegral V ρ P) := by
  simpa only [exteriorFormula] using
    gap21 μS V S ρ normal P hV hVm hS hρ hP hloc
      hboundary hDifferentiation hintegrable

theorem gap23 (μS : Measure Vec3) (V S : Set Vec3)
    (ρ : Vec3 → ℝ) (normal : Vec3 → Vec3)
    (P : Vec3) (hV : IsCompact V) (hVm : MeasurableSet V)
    (hS : S = frontier V) (hρ : ContDiff ℝ 1 ρ)
    (hP : P ∈ interior V) (hloc : LocallyBoundedAt ρ P)
    (hboundary :
      HasPuncturedGradientBoundaryTheorem μS V S normal P)
    (hDifferentiation : SatisfiesInteriorPotentialDifferentiation)
    (hintegrable :
      IntegrableOn
          (fun Q => scale (ρ Q) (kernelGradientQ P Q)) V ∧
        IntegrableOn
          (fun Q =>
            scale (kernel P Q) (coordinateGradient ρ Q)) V) :
    potentialGradient V ρ P =
      exteriorFormula μS V S ρ normal P := by
  exact gap21 μS V S ρ normal P hV hVm hS hρ hP hloc
    hboundary hDifferentiation hintegrable

end

end ProofGap.Exercise4461
