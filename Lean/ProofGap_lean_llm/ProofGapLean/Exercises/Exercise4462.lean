import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise4462

noncomputable section

open MeasureTheory
open Filter Set
open scoped Interval Topology

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

def distance (P Q : Vec3) : ℝ :=
  radius (sub P Q)

def kernel (P Q : Vec3) : ℝ :=
  1 / distance P Q

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

def nearRegion (R₁ : ℝ) : Set Vec3 :=
  {Q | radius Q < R₁}

def farRegion (R₁ : ℝ) : Set Vec3 :=
  {Q | R₁ ≤ radius Q}

def splitRadius (R₀ : ℝ) (P : Vec3) : ℝ :=
  max R₀ (2 * (radius P + 1))

def nearPotential (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in nearRegion R₁, ρ Q * kernel P Q

def farPotential (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in farRegion R₁, ρ Q * kernel P Q

def poissonPotential (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  -(1 / (4 * Real.pi)) *
    (nearPotential ρ R₁ P + farPotential ρ R₁ P)

def HasDecay (ρ : Vec3 → ℝ) (M α R₀ : ℝ) : Prop :=
  ∀ Q : Vec3, R₀ ≤ radius Q →
    |ρ Q| ≤ M / Real.rpow (radius Q) (2 + α)

def tailMajorant (α : ℝ) (Q : Vec3) : ℝ :=
  1 / Real.rpow (radius Q) (3 + α)

def tailAbsolutePotential (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in farRegion R₁, |ρ Q * kernel P Q|

def tailMajorantIntegral (α R₁ : ℝ) : ℝ :=
  ∫ Q in farRegion R₁, tailMajorant α Q

def kernelGradientP (P Q : Vec3) : Vec3 :=
  scale (-1 / distance P Q ^ 3) (sub P Q)

def kernelGradientQ (P Q : Vec3) : Vec3 :=
  neg (kernelGradientP P Q)

def kernelLaplacianP (P Q : Vec3) : ℝ :=
  laplacian (fun X => kernel X Q) P

def kernelLaplacianQ (P Q : Vec3) : ℝ :=
  laplacian (fun X => kernel P X) Q

def farPartialX (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in farRegion R₁, ρ Q * partialX (fun X => kernel X Q) P

def farPartialXX (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in farRegion R₁,
    ρ Q * partialX (fun X => partialX (fun Y => kernel Y Q) X) P

def farPartialYY (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in farRegion R₁,
    ρ Q * partialY (fun X => partialY (fun Y => kernel Y Q) X) P

def farPartialZZ (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in farRegion R₁,
    ρ Q * partialZ (fun X => partialZ (fun Y => kernel Y Q) X) P

def sphere (R₁ : ℝ) : Set Vec3 :=
  {Q | radius Q = R₁}

def sphereNormal (Q : Vec3) : Vec3 :=
  scale (1 / radius Q) Q

def surfaceVector (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3) : Vec3 :=
  ∫ Q in sphere R₁,
    scale (ρ Q * kernel P Q) (sphereNormal Q) ∂μS

def nearDensityVector (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : Vec3 :=
  ∫ Q in nearRegion R₁, scale (kernel P Q) (gradient ρ Q)

def nearGradientFormula (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3) : Vec3 :=
  add (neg (surfaceVector μS ρ R₁ P)) (nearDensityVector ρ R₁ P)

def normalDerivativeQ (P Q : Vec3) : ℝ :=
  dot (sphereNormal Q) (kernelGradientQ P Q)

def surfaceNormalTerm (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in sphere R₁, ρ Q * normalDerivativeQ P Q ∂μS

def densityInteraction (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in nearRegion R₁, dot (gradient ρ Q) (kernelGradientP P Q)

def productDivergenceQ (ρ : Vec3 → ℝ) (P Q : Vec3) : ℝ :=
  ρ Q * kernelLaplacianQ P Q +
    dot (gradient ρ Q) (kernelGradientQ P Q)

def productDivergenceIntegral (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3) : ℝ :=
  ∫ Q in nearRegion R₁, productDivergenceQ ρ P Q

def sphereParam (R θ φ : ℝ) : Vec3 :=
  (R * Real.sin φ * Real.cos θ,
    R * Real.sin φ * Real.sin θ,
    R * Real.cos φ)

def IsSphereAreaMeasure (μS : Measure Vec3) (R : ℝ) : Prop :=
  ∀ g : Vec3 → ℝ, Continuous g →
    (∫ Q in sphere R, g Q ∂μS) =
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ φ in (0 : ℝ)..Real.pi,
          g (sphereParam R θ φ) * R ^ 2 * Real.sin φ

def PoissonAnalyticData (ρ : Vec3 → ℝ)
    (M α R₀ R₁ : ℝ) (P : Vec3) : Prop :=
  0 ≤ M ∧ 0 < α ∧ 0 < R₁ ∧ R₀ ≤ R₁ ∧
    ContDiff ℝ 2 ρ ∧ HasDecay ρ M α R₀ ∧ P ∈ nearRegion R₁

def poissonField (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : Vec3 :=
  gradient (poissonPotential ρ R₁) P
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

private theorem gradient_kernel
    (P Q : Vec3) (hPQ : P ≠ Q) :
    gradient (kernel P) Q = kernelGradientQ P Q := by
  unfold gradient partialX partialY partialZ
  rw [(hasDerivAt_kernelX P Q hPQ).deriv,
    (hasDerivAt_kernelY P Q hPQ).deriv,
    (hasDerivAt_kernelZ P Q hPQ).deriv]
  unfold kernelGradientQ kernelGradientP scale neg distance
  ext <;> simp <;> ring

private theorem hasDerivAt_kernelPX
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun x : ℝ => kernel (x, P.2.1, P.2.2) Q)
      (-(sub P Q).1 / radius (sub P Q) ^ 3) P.1 := by
  have hinner :
      HasDerivAt (fun x : ℝ => x - Q.1) 1 P.1 := by
    exact (hasDerivAt_id P.1).sub_const Q.1
  have hcomp :=
    (hasDerivAt_inverseRadiusX (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp P.1 hinner
  convert hcomp using 1 <;>
    simp [kernel, sub, add, neg] <;> ring

private theorem hasDerivAt_kernelPY
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun y : ℝ => kernel (P.1, y, P.2.2) Q)
      (-(sub P Q).2.1 / radius (sub P Q) ^ 3) P.2.1 := by
  have hinner :
      HasDerivAt (fun y : ℝ => y - Q.2.1) 1 P.2.1 := by
    exact (hasDerivAt_id P.2.1).sub_const Q.2.1
  have hcomp :=
    (hasDerivAt_inverseRadiusY (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp P.2.1 hinner
  convert hcomp using 1 <;>
    simp [kernel, sub, add, neg] <;> ring

private theorem hasDerivAt_kernelPZ
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun z : ℝ => kernel (P.1, P.2.1, z) Q)
      (-(sub P Q).2.2 / radius (sub P Q) ^ 3) P.2.2 := by
  have hinner :
      HasDerivAt (fun z : ℝ => z - Q.2.2) 1 P.2.2 := by
    exact (hasDerivAt_id P.2.2).sub_const Q.2.2
  have hcomp :=
    (hasDerivAt_inverseRadiusZ (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp P.2.2 hinner
  convert hcomp using 1 <;>
    simp [kernel, sub, add, neg] <;> ring

private theorem gradient_kernelP
    (P Q : Vec3) (hPQ : P ≠ Q) :
    gradient (fun X => kernel X Q) P =
      kernelGradientP P Q := by
  unfold gradient partialX partialY partialZ
  rw [(hasDerivAt_kernelPX P Q hPQ).deriv,
    (hasDerivAt_kernelPY P Q hPQ).deriv,
    (hasDerivAt_kernelPZ P Q hPQ).deriv]
  unfold kernelGradientP scale distance
  ext <;> simp <;> ring

private theorem hasDerivAt_explicitSecondX
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun x : ℝ =>
        -(x - Q.1) /
          radius (sub (x, P.2.1, P.2.2) Q) ^ 3)
      (-1 / radius (sub P Q) ^ 3 +
        3 * (sub P Q).1 ^ 2 / radius (sub P Q) ^ 5)
      P.1 := by
  have hinner :
      HasDerivAt (fun x : ℝ => x - Q.1) 1 P.1 :=
    (hasDerivAt_id P.1).sub_const Q.1
  have hinv :=
    (hasDerivAt_inverseRadiusX (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp P.1 hinner
  have hnum : HasDerivAt
      (fun x : ℝ => -(x - Q.1)) (-1) P.1 :=
    hinner.neg
  have hmain := hnum.mul (hinv.pow 3)
  have hrne :
      radius (sub P Q) ≠ 0 :=
    (radius_pos_of_ne_zero (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).ne'
  have hrne' :
      radius
        (P.1 - Q.1, P.2.1 - Q.2.1, P.2.2 - Q.2.2) ≠ 0 := by
    simpa [sub, add, neg] using hrne
  convert hmain using 1
  · funext x
    simp [Function.comp_def, sub, add, neg, div_eq_mul_inv]
    ring <;> simp
  · simp only [Pi.pow_apply, Function.comp_apply,
      Nat.cast_ofNat, Nat.reduceSub, mul_one]
    change
      -1 / radius (sub P Q) ^ 3 +
            3 * (sub P Q).1 ^ 2 / radius (sub P Q) ^ 5 =
        -1 * (1 / radius (sub P Q)) ^ 3 +
          (-(sub P Q).1) *
            (3 * (1 / radius (sub P Q)) ^ 2 *
              (-(sub P Q).1 / radius (sub P Q) ^ 3))
    field_simp [hrne]

private theorem hasDerivAt_explicitSecondY
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun y : ℝ =>
        -(y - Q.2.1) /
          radius (sub (P.1, y, P.2.2) Q) ^ 3)
      (-1 / radius (sub P Q) ^ 3 +
        3 * (sub P Q).2.1 ^ 2 / radius (sub P Q) ^ 5)
      P.2.1 := by
  have hinner :
      HasDerivAt (fun y : ℝ => y - Q.2.1) 1 P.2.1 :=
    (hasDerivAt_id P.2.1).sub_const Q.2.1
  have hinv :=
    (hasDerivAt_inverseRadiusY (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp P.2.1 hinner
  have hnum : HasDerivAt
      (fun y : ℝ => -(y - Q.2.1)) (-1) P.2.1 :=
    hinner.neg
  have hmain := hnum.mul (hinv.pow 3)
  have hrne :
      radius (sub P Q) ≠ 0 :=
    (radius_pos_of_ne_zero (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).ne'
  have hrne' :
      radius
        (P.1 - Q.1, P.2.1 - Q.2.1, P.2.2 - Q.2.2) ≠ 0 := by
    simpa [sub, add, neg] using hrne
  convert hmain using 1
  · funext y
    simp [Function.comp_def, sub, add, neg, div_eq_mul_inv]
    ring <;> simp
  · simp only [Pi.pow_apply, Function.comp_apply,
      Nat.cast_ofNat, Nat.reduceSub, mul_one]
    change
      -1 / radius (sub P Q) ^ 3 +
            3 * (sub P Q).2.1 ^ 2 / radius (sub P Q) ^ 5 =
        -1 * (1 / radius (sub P Q)) ^ 3 +
          (-(sub P Q).2.1) *
            (3 * (1 / radius (sub P Q)) ^ 2 *
              (-(sub P Q).2.1 / radius (sub P Q) ^ 3))
    field_simp [hrne]

private theorem hasDerivAt_explicitSecondZ
    (P Q : Vec3) (hPQ : P ≠ Q) :
    HasDerivAt
      (fun z : ℝ =>
        -(z - Q.2.2) /
          radius (sub (P.1, P.2.1, z) Q) ^ 3)
      (-1 / radius (sub P Q) ^ 3 +
        3 * (sub P Q).2.2 ^ 2 / radius (sub P Q) ^ 5)
      P.2.2 := by
  have hinner :
      HasDerivAt (fun z : ℝ => z - Q.2.2) 1 P.2.2 :=
    (hasDerivAt_id P.2.2).sub_const Q.2.2
  have hinv :=
    (hasDerivAt_inverseRadiusZ (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).comp P.2.2 hinner
  have hnum : HasDerivAt
      (fun z : ℝ => -(z - Q.2.2)) (-1) P.2.2 :=
    hinner.neg
  have hmain := hnum.mul (hinv.pow 3)
  have hrne :
      radius (sub P Q) ≠ 0 :=
    (radius_pos_of_ne_zero (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)).ne'
  have hrne' :
      radius
        (P.1 - Q.1, P.2.1 - Q.2.1, P.2.2 - Q.2.2) ≠ 0 := by
    simpa [sub, add, neg] using hrne
  convert hmain using 1
  · funext z
    simp [Function.comp_def, sub, add, neg, div_eq_mul_inv]
    ring <;> simp
  · simp only [Pi.pow_apply, Function.comp_apply,
      Nat.cast_ofNat, Nat.reduceSub, mul_one]
    change
      -1 / radius (sub P Q) ^ 3 +
            3 * (sub P Q).2.2 ^ 2 / radius (sub P Q) ^ 5 =
        -1 * (1 / radius (sub P Q)) ^ 3 +
          (-(sub P Q).2.2) *
            (3 * (1 / radius (sub P Q)) ^ 2 *
              (-(sub P Q).2.2 / radius (sub P Q) ^ 3))
    field_simp [hrne]

private theorem secondPartialXX_kernelP
    (P Q : Vec3) (hPQ : P ≠ Q) :
    partialX (fun X => partialX (fun Y => kernel Y Q) X) P =
      -1 / radius (sub P Q) ^ 3 +
        3 * (sub P Q).1 ^ 2 / radius (sub P Q) ^ 5 := by
  have hcurve :
      Continuous
        (fun x : ℝ => ((x, P.2.1, P.2.2) : Vec3)) := by
    fun_prop
  have hev :
      ∀ᶠ x in 𝓝 P.1,
        ((x, P.2.1, P.2.2) : Vec3) ≠ Q := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      hcurve.continuousAt
        (isOpen_compl_singleton.mem_nhds hPQ)
  have heq :
      (fun x : ℝ =>
        partialX (fun Y => kernel Y Q)
          (x, P.2.1, P.2.2)) =ᶠ[𝓝 P.1]
      (fun x : ℝ =>
        -(x - Q.1) /
          radius (sub (x, P.2.1, P.2.2) Q) ^ 3) := by
    filter_upwards [hev] with x hx
    unfold partialX
    exact
      (hasDerivAt_kernelPX
        (x, P.2.1, P.2.2) Q hx).deriv
  change
    deriv
      (fun x : ℝ =>
        partialX (fun Y => kernel Y Q)
          (x, P.2.1, P.2.2)) P.1 = _
  rw [heq.deriv_eq,
    (hasDerivAt_explicitSecondX P Q hPQ).deriv]

private theorem secondPartialYY_kernelP
    (P Q : Vec3) (hPQ : P ≠ Q) :
    partialY (fun X => partialY (fun Y => kernel Y Q) X) P =
      -1 / radius (sub P Q) ^ 3 +
        3 * (sub P Q).2.1 ^ 2 / radius (sub P Q) ^ 5 := by
  have hcurve :
      Continuous
        (fun y : ℝ => ((P.1, y, P.2.2) : Vec3)) := by
    fun_prop
  have hev :
      ∀ᶠ y in 𝓝 P.2.1,
        ((P.1, y, P.2.2) : Vec3) ≠ Q := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      hcurve.continuousAt
        (isOpen_compl_singleton.mem_nhds hPQ)
  have heq :
      (fun y : ℝ =>
        partialY (fun Y => kernel Y Q)
          (P.1, y, P.2.2)) =ᶠ[𝓝 P.2.1]
      (fun y : ℝ =>
        -(y - Q.2.1) /
          radius (sub (P.1, y, P.2.2) Q) ^ 3) := by
    filter_upwards [hev] with y hy
    unfold partialY
    exact
      (hasDerivAt_kernelPY
        (P.1, y, P.2.2) Q hy).deriv
  change
    deriv
      (fun y : ℝ =>
        partialY (fun Y => kernel Y Q)
          (P.1, y, P.2.2)) P.2.1 = _
  rw [heq.deriv_eq,
    (hasDerivAt_explicitSecondY P Q hPQ).deriv]

private theorem secondPartialZZ_kernelP
    (P Q : Vec3) (hPQ : P ≠ Q) :
    partialZ (fun X => partialZ (fun Y => kernel Y Q) X) P =
      -1 / radius (sub P Q) ^ 3 +
        3 * (sub P Q).2.2 ^ 2 / radius (sub P Q) ^ 5 := by
  have hcurve :
      Continuous
        (fun z : ℝ => ((P.1, P.2.1, z) : Vec3)) := by
    fun_prop
  have hev :
      ∀ᶠ z in 𝓝 P.2.2,
        ((P.1, P.2.1, z) : Vec3) ≠ Q := by
    simpa only [mem_compl_iff, mem_singleton_iff] using
      hcurve.continuousAt
        (isOpen_compl_singleton.mem_nhds hPQ)
  have heq :
      (fun z : ℝ =>
        partialZ (fun Y => kernel Y Q)
          (P.1, P.2.1, z)) =ᶠ[𝓝 P.2.2]
      (fun z : ℝ =>
        -(z - Q.2.2) /
          radius (sub (P.1, P.2.1, z) Q) ^ 3) := by
    filter_upwards [hev] with z hz
    unfold partialZ
    exact
      (hasDerivAt_kernelPZ
        (P.1, P.2.1, z) Q hz).deriv
  change
    deriv
      (fun z : ℝ =>
        partialZ (fun Y => kernel Y Q)
          (P.1, P.2.1, z)) P.2.2 = _
  rw [heq.deriv_eq,
    (hasDerivAt_explicitSecondZ P Q hPQ).deriv]

private theorem kernelLaplacianP_zero
    (P Q : Vec3) (hPQ : P ≠ Q) :
    kernelLaplacianP P Q = 0 := by
  have hrpos :
      0 < radius (sub P Q) :=
    radius_pos_of_ne_zero (sub P Q)
      (sub_ne_zero_of_ne P Q hPQ)
  have hrsq :
      radius (sub P Q) ^ 2 =
        (sub P Q).1 ^ 2 +
          (sub P Q).2.1 ^ 2 +
          (sub P Q).2.2 ^ 2 := by
    unfold radius dot
    rw [Real.sq_sqrt (by
      nlinarith [sq_nonneg (sub P Q).1,
        sq_nonneg (sub P Q).2.1,
        sq_nonneg (sub P Q).2.2])]
    ring
  unfold kernelLaplacianP laplacian divergence gradient
  rw [secondPartialXX_kernelP P Q hPQ,
    secondPartialYY_kernelP P Q hPQ,
    secondPartialZZ_kernelP P Q hPQ]
  field_simp [hrpos.ne']
  nlinarith

private theorem kernel_comm (P Q : Vec3) :
    kernel P Q = kernel Q P := by
  unfold kernel distance radius dot sub add neg
  congr 2
  ring

private theorem kernelLaplacianQ_eq_kernelLaplacianP
    (P Q : Vec3) :
    kernelLaplacianQ P Q = kernelLaplacianP Q P := by
  have heq :
      (fun X => kernel P X) =
        (fun X => kernel X P) := by
    funext X
    exact kernel_comm P X
  unfold kernelLaplacianQ kernelLaplacianP
  rw [heq]

private theorem kernelLaplacianQ_zero
    (P Q : Vec3) (hPQ : P ≠ Q) :
    kernelLaplacianQ P Q = 0 := by
  rw [kernelLaplacianQ_eq_kernelLaplacianP]
  exact kernelLaplacianP_zero Q P hPQ.symm

private def euclideanOfVec3 (P : Vec3) :
    EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![P.1, P.2.1, P.2.2]

private theorem radius_eq_euclideanNorm (P : Vec3) :
    radius P = ‖euclideanOfVec3 P‖ := by
  rw [EuclideanSpace.norm_eq]
  unfold radius dot euclideanOfVec3
  congr 1
  simp [Fin.sum_univ_succ]
  ring

private theorem euclideanOfVec3_add (P Q : Vec3) :
    euclideanOfVec3 (add P Q) =
      euclideanOfVec3 P + euclideanOfVec3 Q := by
  ext i
  fin_cases i <;> simp [euclideanOfVec3, add]

private theorem radius_add_le (P Q : Vec3) :
    radius (add P Q) ≤ radius P + radius Q := by
  rw [radius_eq_euclideanNorm, radius_eq_euclideanNorm,
    radius_eq_euclideanNorm, euclideanOfVec3_add]
  exact norm_add_le _ _

private theorem radius_nonneg (P : Vec3) : 0 ≤ radius P := by
  rw [radius_eq_euclideanNorm]
  exact norm_nonneg _

private theorem radius_sub_triangle (P Q : Vec3) :
    radius Q ≤ radius P + radius (sub P Q) := by
  have hadd : add P (neg (sub P Q)) = Q := by
    ext <;> simp [add, neg, sub]
  calc
    radius Q = radius (add P (neg (sub P Q))) := by
      rw [hadd]
    radius (add P (neg (sub P Q))) ≤
        radius P + radius (neg (sub P Q)) :=
      radius_add_le _ _
    _ = radius P + radius (sub P Q) := by
      unfold radius neg dot
      congr 2
      ring

private theorem continuous_radius : Continuous radius := by
  unfold radius dot
  fun_prop

private theorem measurable_farRegion (R : ℝ) :
    MeasurableSet (farRegion R) := by
  exact measurableSet_le measurable_const continuous_radius.measurable

private theorem measurable_nearRegion (R : ℝ) :
    MeasurableSet (nearRegion R) := by
  exact measurableSet_lt continuous_radius.measurable measurable_const

private theorem measurable_kernel_left (P : Vec3) :
    Measurable (kernel P) := by
  unfold kernel distance radius dot sub add neg
  fun_prop

private theorem splitRadius_pos (R₀ : ℝ) (P : Vec3) :
    0 < splitRadius R₀ P := by
  have hr := radius_nonneg P
  unfold splitRadius
  exact lt_of_lt_of_le (by nlinarith)
    (le_max_right R₀ (2 * (radius P + 1)))

private theorem far_distance_lower
    (R₀ : ℝ) (P Q : Vec3)
    (hQ : splitRadius R₀ P ≤ radius Q) :
    radius Q / 2 ≤ distance P Q := by
  have hsplit :
      2 * (radius P + 1) ≤ radius Q :=
    le_trans
      (le_max_right R₀ (2 * (radius P + 1))) hQ
  have htri :
      radius Q ≤ radius P + distance P Q := by
    simpa [distance] using radius_sub_triangle P Q
  nlinarith

private theorem tail_pointwise_bound
    (ρ : Vec3 → ℝ) (M α R₀ : ℝ) (P Q : Vec3)
    (hM : 0 ≤ M) (hdecay : HasDecay ρ M α R₀)
    (hQ : splitRadius R₀ P ≤ radius Q) :
    |ρ Q * kernel P Q| ≤ 2 * M * tailMajorant α Q := by
  have hRpos := splitRadius_pos R₀ P
  have hrpos : 0 < radius Q := lt_of_lt_of_le hRpos hQ
  have hdlo : radius Q / 2 ≤ distance P Q :=
    far_distance_lower R₀ P Q hQ
  have hdpos : 0 < distance P Q := by nlinarith
  have hρbound :
      |ρ Q| ≤ M / Real.rpow (radius Q) (2 + α) :=
    hdecay Q
      (le_trans (le_max_left R₀ (2 * (radius P + 1))) hQ)
  have hkbound : |kernel P Q| ≤ 2 / radius Q := by
    have htwo :
        2 / radius Q = 1 / (radius Q / 2) := by
      field_simp [hrpos.ne']
    rw [htwo]
    unfold kernel
    rw [abs_of_pos (one_div_pos.mpr hdpos)]
    exact one_div_le_one_div_of_le (by nlinarith) hdlo
  have hpowpos :
      0 < Real.rpow (radius Q) (2 + α) :=
    Real.rpow_pos_of_pos hrpos _
  calc
    |ρ Q * kernel P Q| =
        |ρ Q| * |kernel P Q| := abs_mul _ _
    _ ≤
        (M / Real.rpow (radius Q) (2 + α)) *
          (2 / radius Q) :=
      mul_le_mul hρbound hkbound (abs_nonneg _)
        (div_nonneg hM hpowpos.le)
    _ = 2 * M * tailMajorant α Q := by
      unfold tailMajorant
      rw [show 3 + α = (2 + α) + 1 by ring]
      have hpowadd :
          Real.rpow (radius Q) ((2 + α) + 1) =
            Real.rpow (radius Q) (2 + α) * radius Q := by
        simpa using Real.rpow_add hrpos (2 + α) 1
      rw [hpowadd]
      field_simp [hpowpos.ne', hrpos.ne']

private theorem tail_integrable
    (ρ : Vec3 → ℝ) (M α R₀ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀)
    (htail :
      IntegrableOn (tailMajorant α)
        (farRegion (splitRadius R₀ P))) :
    IntegrableOn (fun Q => ρ Q * kernel P Q)
      (farRegion (splitRadius R₀ P)) := by
  let S := farRegion (splitRadius R₀ P)
  have hmajor :
      IntegrableOn (fun Q => 2 * M * tailMajorant α Q) S :=
    htail.const_mul (2 * M)
  apply Integrable.mono' hmajor
  · exact
      (hρ.measurable.mul
        (measurable_kernel_left P)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (measurable_farRegion
      (splitRadius R₀ P))] with Q hQ
    simpa [Real.norm_eq_abs] using
      tail_pointwise_bound ρ M α R₀ P Q hM hdecay hQ

theorem gap1 (ρ : Vec3 → ℝ) (M α R₀ : ℝ)
    (hdecay : HasDecay ρ M α R₀) (Q : Vec3)
    (hQ : R₀ ≤ radius Q) :
    |ρ Q| ≤ M / Real.rpow (radius Q) (2 + α) := by
  exact hdecay Q hQ

theorem gap2 (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) :
    poissonPotential ρ R₁ P =
      -(1 / (4 * Real.pi)) *
        (nearPotential ρ R₁ P + farPotential ρ R₁ P) := by
  rfl

theorem gap3 (P : Vec3) :
    radius P =
      Real.sqrt (P.1 ^ 2 + P.2.1 ^ 2 + P.2.2 ^ 2) := by
  unfold radius dot
  congr 1
  ring

theorem gap4 (R₀ : ℝ) (P : Vec3) :
    splitRadius R₀ P = max R₀ (2 * (radius P + 1)) := by
  rfl

theorem gap5 (R₀ : ℝ) (P Q : Vec3)
    (hQ : splitRadius R₀ P ≤ radius Q) :
    radius Q ≤ radius P + 1 + distance P Q := by
  have htri := radius_sub_triangle P Q
  unfold distance
  linarith

theorem gap6 (R₀ : ℝ) (P Q : Vec3)
    (hQ : splitRadius R₀ P ≤ radius Q) :
    radius P + 1 + distance P Q ≤
      radius Q / 2 + distance P Q := by
  have hsplit :
      2 * (radius P + 1) ≤ radius Q :=
    le_trans
      (le_max_right R₀ (2 * (radius P + 1))) hQ
  linarith

theorem gap7 (R₀ : ℝ) (P Q : Vec3)
    (hQ : splitRadius R₀ P ≤ radius Q) :
    radius Q ≤ radius Q / 2 + distance P Q := by
  have hd := far_distance_lower R₀ P Q hQ
  linarith

theorem gap8 (ρ : Vec3 → ℝ) (M α R₀ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀)
    (htailRadial :
      ∀ R : ℝ, 0 < R →
        IntegrableOn (tailMajorant α) (farRegion R) ∧
        tailMajorantIntegral α R =
          4 * Real.pi / (α * Real.rpow R α)) :
    tailAbsolutePotential ρ (splitRadius R₀ P) P ≤
      2 * M * tailMajorantIntegral α (splitRadius R₀ P) := by
  let R := splitRadius R₀ P
  have hR : 0 < R := splitRadius_pos R₀ P
  have htail :
      IntegrableOn (tailMajorant α) (farRegion R) :=
    (htailRadial R hR).1
  have hf :
      IntegrableOn (fun Q => ρ Q * kernel P Q)
        (farRegion R) := by
    exact tail_integrable ρ M α R₀ P hM hρ hdecay htail
  have habs :
      IntegrableOn (fun Q => |ρ Q * kernel P Q|)
        (farRegion R) := by
    simpa [Real.norm_eq_abs] using hf.norm
  have hmajor :
      IntegrableOn (fun Q => 2 * M * tailMajorant α Q)
        (farRegion R) :=
    htail.const_mul (2 * M)
  unfold tailAbsolutePotential tailMajorantIntegral
  change
    (∫ Q in farRegion R, |ρ Q * kernel P Q|) ≤
      2 * M * ∫ Q in farRegion R, tailMajorant α Q
  calc
    (∫ Q in farRegion R, |ρ Q * kernel P Q|) ≤
        ∫ Q in farRegion R, 2 * M * tailMajorant α Q :=
      setIntegral_mono_on habs hmajor
        (measurable_farRegion R)
        (fun Q hQ =>
          tail_pointwise_bound ρ M α R₀ P Q hM hdecay hQ)
    _ = 2 * M * ∫ Q in farRegion R, tailMajorant α Q := by
      rw [MeasureTheory.integral_const_mul]

theorem gap9 (M α R₁ : ℝ) (hM : 0 ≤ M)
    (hα : 0 < α) (hR₁ : 0 < R₁)
    (htailRadial :
      ∀ R : ℝ, 0 < R →
        IntegrableOn (tailMajorant α) (farRegion R) ∧
        tailMajorantIntegral α R =
          4 * Real.pi / (α * Real.rpow R α)) :
    2 * M * tailMajorantIntegral α R₁ =
      8 * M * Real.pi / (α * Real.rpow R₁ α) := by
  rw [(htailRadial R₁ hR₁).2]
  ring

theorem gap10 (α R₁ : ℝ) (hα : 0 < α) (hR₁ : 0 < R₁)
    (htailRadial :
      ∀ R : ℝ, 0 < R →
        IntegrableOn (tailMajorant α) (farRegion R) ∧
        tailMajorantIntegral α R =
          4 * Real.pi / (α * Real.rpow R α)) :
    IntegrableOn (tailMajorant α) (farRegion R₁) := by
  exact (htailRadial R₁ hR₁).1

theorem gap11 (ρ : Vec3 → ℝ) (M α R₀ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀)
    (htailRadial :
      ∀ R : ℝ, 0 < R →
        IntegrableOn (tailMajorant α) (farRegion R) ∧
        tailMajorantIntegral α R =
          4 * Real.pi / (α * Real.rpow R α)) :
    IntegrableOn (fun Q => ρ Q * kernel P Q)
      (farRegion (splitRadius R₀ P)) := by
  exact
    tail_integrable ρ M α R₀ P hM hρ hdecay
      (htailRadial (splitRadius R₀ P)
        (splitRadius_pos R₀ P)).1

theorem gap12 (u : Vec3 → ℝ) (P : Vec3) :
    divergence (gradient u) P = laplacian u P := by
  rfl

theorem gap13 (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) :
    divergence (poissonField ρ R₁) P =
      laplacian (poissonPotential ρ R₁) P := by
  rfl

def FarDifferentiationData
    (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) : Prop :=
  partialX (farPotential ρ R₁) P = farPartialX ρ R₁ P ∧
  partialX (fun X => partialX (farPotential ρ R₁) X) P =
      farPartialXX ρ R₁ P ∧
  partialY (fun X => partialY (farPotential ρ R₁) X) P =
      farPartialYY ρ R₁ P ∧
  partialZ (fun X => partialZ (farPotential ρ R₁) X) P =
      farPartialZZ ρ R₁ P ∧
  laplacian (farPotential ρ R₁) P =
    ∫ Q in farRegion R₁, ρ Q * kernelLaplacianP P Q

/-- Uniform dominated-differentiation theorem for the far field. -/
def SatisfiesFarDifferentiationTheorem : Prop :=
  ∀ (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3),
    0 ≤ M → 0 < α → 0 < R₁ → R₀ ≤ R₁ →
      Continuous ρ → HasDecay ρ M α R₀ → P ∈ nearRegion R₁ →
      FarDifferentiationData ρ R₁ P

/-- Uniform gradient formula for the near Newton potential. -/
def SatisfiesNearPotentialGradientTheorem : Prop :=
  ∀ (μS : Measure Vec3) (ρ : Vec3 → ℝ) (R₁ : ℝ),
    0 < R₁ → IsSphereAreaMeasure μS R₁ → ContDiff ℝ 2 ρ →
      ∀ X ∈ nearRegion R₁,
        gradient (nearPotential ρ R₁) X =
          nearGradientFormula μS ρ R₁ X

/-- Uniform differentiation theorem for the two terms in the near-gradient
formula. -/
def SatisfiesNearGradientDivergenceTheorem : Prop :=
  ∀ (μS : Measure Vec3) (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3),
    0 < R₁ → IsSphereAreaMeasure μS R₁ → ContDiff ℝ 2 ρ →
      P ∈ nearRegion R₁ →
        divergence (fun X => nearGradientFormula μS ρ R₁ X) P =
          surfaceNormalTerm μS ρ R₁ P +
            densityInteraction ρ R₁ P

/-- Uniform punctured Green/fundamental-solution identity. -/
def SatisfiesPuncturedGreenIdentity : Prop :=
  ∀ (μS : Measure Vec3) (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3),
    0 < R₁ → IsSphereAreaMeasure μS R₁ → ContDiff ℝ 2 ρ →
      P ∈ nearRegion R₁ →
        productDivergenceIntegral ρ R₁ P =
          surfaceNormalTerm μS ρ R₁ P +
            4 * Real.pi * ρ P

theorem gap14 (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hR₁ : 0 < R₁)
    (hR₀ : R₀ ≤ R₁) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀) (hP : P ∈ nearRegion R₁)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem) :
    partialX (farPotential ρ R₁) P = farPartialX ρ R₁ P := by
  exact
    (hFarTheorem ρ M α R₀ R₁ P
      hM hα hR₁ hR₀ hρ hdecay hP).1

theorem gap15 (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hR₁ : 0 < R₁)
    (hR₀ : R₀ ≤ R₁) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀) (hP : P ∈ nearRegion R₁)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem) :
    partialX (fun X => partialX (farPotential ρ R₁) X) P =
      farPartialXX ρ R₁ P := by
  exact
    (hFarTheorem ρ M α R₀ R₁ P
      hM hα hR₁ hR₀ hρ hdecay hP).2.1

theorem gap16 (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hR₁ : 0 < R₁)
    (hR₀ : R₀ ≤ R₁) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀) (hP : P ∈ nearRegion R₁)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem) :
    partialY (fun X => partialY (farPotential ρ R₁) X) P =
      farPartialYY ρ R₁ P := by
  exact
    (hFarTheorem ρ M α R₀ R₁ P
      hM hα hR₁ hR₀ hρ hdecay hP).2.2.1

theorem gap17 (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hR₁ : 0 < R₁)
    (hR₀ : R₀ ≤ R₁) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀) (hP : P ∈ nearRegion R₁)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem) :
    partialZ (fun X => partialZ (farPotential ρ R₁) X) P =
      farPartialZZ ρ R₁ P := by
  exact
    (hFarTheorem ρ M α R₀ R₁ P
      hM hα hR₁ hR₀ hρ hdecay hP).2.2.2.1

theorem gap18 (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hR₁ : 0 < R₁)
    (hR₀ : R₀ ≤ R₁) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀) (hP : P ∈ nearRegion R₁)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem) :
    laplacian (farPotential ρ R₁) P =
      ∫ Q in farRegion R₁, ρ Q * kernelLaplacianP P Q := by
  exact
    (hFarTheorem ρ M α R₀ R₁ P
      hM hα hR₁ hR₀ hρ hdecay hP).2.2.2.2

theorem gap19 (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hR₁ : 0 < R₁)
    (hR₀ : R₀ ≤ R₁) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀) (hP : P ∈ nearRegion R₁) :
    (∫ Q in farRegion R₁, ρ Q * kernelLaplacianP P Q) = 0 := by
  change radius P < R₁ at hP
  calc
    (∫ Q in farRegion R₁,
        ρ Q * kernelLaplacianP P Q) =
        ∫ _Q in farRegion R₁, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem
        (measurable_farRegion R₁)] with Q hQ
      change R₁ ≤ radius Q at hQ
      have hne : P ≠ Q := by
        intro heq
        subst Q
        exact (not_lt_of_ge hQ) hP
      rw [kernelLaplacianP_zero P Q hne, mul_zero]
    _ = 0 := by simp

theorem gap20 (ρ : Vec3 → ℝ) (M α R₀ R₁ : ℝ) (P : Vec3)
    (hM : 0 ≤ M) (hα : 0 < α) (hR₁ : 0 < R₁)
    (hR₀ : R₀ ≤ R₁) (hρ : Continuous ρ)
    (hdecay : HasDecay ρ M α R₀) (hP : P ∈ nearRegion R₁)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem) :
    laplacian (farPotential ρ R₁) P = 0 := by
  rw [(hFarTheorem ρ M α R₀ R₁ P
    hM hα hR₁ hR₀ hρ hdecay hP).2.2.2.2]
  exact gap19 ρ M α R₀ R₁ P hM hα hR₁ hR₀ hρ hdecay hP

private theorem divergence_congr_of_eventuallyEq
    (F G : Vec3 → Vec3) (P : Vec3)
    (hFG : F =ᶠ[𝓝 P] G) :
    divergence F P = divergence G P := by
  have hxv :
      (fun x : ℝ => F (x, P.2.1, P.2.2)) =ᶠ[𝓝 P.1]
        (fun x : ℝ => G (x, P.2.1, P.2.2)) :=
    hFG.comp_tendsto
      (show ContinuousAt
          (fun x : ℝ => (x, P.2.1, P.2.2)) P.1 by
        fun_prop)
  have hyv :
      (fun y : ℝ => F (P.1, y, P.2.2)) =ᶠ[𝓝 P.2.1]
        (fun y : ℝ => G (P.1, y, P.2.2)) :=
    hFG.comp_tendsto
      (show ContinuousAt
          (fun y : ℝ => (P.1, y, P.2.2)) P.2.1 by
        fun_prop)
  have hzv :
      (fun z : ℝ => F (P.1, P.2.1, z)) =ᶠ[𝓝 P.2.2]
        (fun z : ℝ => G (P.1, P.2.1, z)) :=
    hFG.comp_tendsto
      (show ContinuousAt
          (fun z : ℝ => (P.1, P.2.1, z)) P.2.2 by
        fun_prop)
  have hx :
      (fun x : ℝ => (F (x, P.2.1, P.2.2)).1) =ᶠ[𝓝 P.1]
        (fun x : ℝ => (G (x, P.2.1, P.2.2)).1) := by
    filter_upwards [hxv] with x h
    rw [h]
  have hy :
      (fun y : ℝ => (F (P.1, y, P.2.2)).2.1) =ᶠ[𝓝 P.2.1]
        (fun y : ℝ => (G (P.1, y, P.2.2)).2.1) := by
    filter_upwards [hyv] with y h
    rw [h]
  have hz :
      (fun z : ℝ => (F (P.1, P.2.1, z)).2.2) =ᶠ[𝓝 P.2.2]
        (fun z : ℝ => (G (P.1, P.2.1, z)).2.2) := by
    filter_upwards [hzv] with z h
    rw [h]
  unfold divergence partialX partialY partialZ
  rw [Filter.EventuallyEq.deriv_eq hx,
    Filter.EventuallyEq.deriv_eq hy,
    Filter.EventuallyEq.deriv_eq hz]

private theorem divergence_scale_kernel
    (c : ℝ) (v : Vec3) (P Q : Vec3) (hne : P ≠ Q) :
    divergence
        (fun X => scale (c * kernel X Q) v) P =
      c * dot v (kernelGradientP P Q) := by
  unfold divergence partialX partialY partialZ scale
  rw [
    (((hasDerivAt_kernelPX P Q hne).const_mul c).mul_const v.1).deriv,
    (((hasDerivAt_kernelPY P Q hne).const_mul c).mul_const v.2.1).deriv,
    (((hasDerivAt_kernelPZ P Q hne).const_mul c).mul_const v.2.2).deriv]
  unfold dot kernelGradientP scale distance
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

theorem gap21 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3)
    (hR₁ : 0 < R₁) (hμ : IsSphereAreaMeasure μS R₁)
    (hρ : ContDiff ℝ 2 ρ) (hP : P ∈ nearRegion R₁)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem) :
    gradient (nearPotential ρ R₁) P =
      nearGradientFormula μS ρ R₁ P := by
  exact hNearGradient μS ρ R₁ hR₁ hμ hρ P hP

theorem gap22 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3)
    (hR₁ : 0 < R₁) (hμ : IsSphereAreaMeasure μS R₁)
    (hρ : ContDiff ℝ 2 ρ) (hP : P ∈ nearRegion R₁)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem) :
    laplacian (nearPotential ρ R₁) P =
      divergence (fun X => nearGradientFormula μS ρ R₁ X) P := by
  have hopen : IsOpen (nearRegion R₁) := by
    unfold nearRegion
    exact isOpen_lt continuous_radius continuous_const
  have heq :
      gradient (nearPotential ρ R₁) =ᶠ[𝓝 P]
        (fun X => nearGradientFormula μS ρ R₁ X) := by
    filter_upwards [hopen.mem_nhds hP] with X hX
    exact hNearGradient μS ρ R₁ hR₁ hμ hρ X hX
  unfold laplacian
  exact divergence_congr_of_eventuallyEq _ _ P heq

theorem gap23 (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hne : P ≠ Q) :
    divergence
        (fun X => scale (ρ Q * kernel X Q) (sphereNormal Q)) P =
      ρ Q * dot (sphereNormal Q) (kernelGradientP P Q) := by
  exact divergence_scale_kernel (ρ Q) (sphereNormal Q) P Q hne

theorem gap24 (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hne : P ≠ Q) :
    ρ Q * dot (sphereNormal Q) (kernelGradientP P Q) =
      -ρ Q * normalDerivativeQ P Q := by
  unfold normalDerivativeQ kernelGradientQ neg dot
  ring

theorem gap25 (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hne : P ≠ Q) :
    divergence
        (fun X => scale (ρ Q * kernel X Q) (sphereNormal Q)) P =
      -ρ Q * normalDerivativeQ P Q := by
  calc
    divergence
        (fun X => scale (ρ Q * kernel X Q) (sphereNormal Q)) P =
        ρ Q * dot (sphereNormal Q) (kernelGradientP P Q) :=
      gap23 ρ P Q hρ hne
    _ = -ρ Q * normalDerivativeQ P Q :=
      gap24 ρ P Q hρ hne

theorem gap26 (ρ : Vec3 → ℝ) (P Q : Vec3)
    (hρ : ContDiff ℝ 1 ρ) (hne : P ≠ Q) :
    divergence (fun X => scale (kernel X Q) (gradient ρ Q)) P =
      dot (gradient ρ Q) (kernelGradientP P Q) := by
  simpa using
    divergence_scale_kernel 1 (gradient ρ Q) P Q hne

theorem gap27 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3)
    (hR₁ : 0 < R₁) (hμ : IsSphereAreaMeasure μS R₁)
    (hρ : ContDiff ℝ 2 ρ) (hP : P ∈ nearRegion R₁)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem) :
    laplacian (nearPotential ρ R₁) P =
      surfaceNormalTerm μS ρ R₁ P +
        densityInteraction ρ R₁ P := by
  calc
    laplacian (nearPotential ρ R₁) P =
        divergence
          (fun X => nearGradientFormula μS ρ R₁ X) P :=
      gap22 μS ρ R₁ P hR₁ hμ hρ hP hNearGradient
    _ = surfaceNormalTerm μS ρ R₁ P +
          densityInteraction ρ R₁ P :=
      hNearDivergence μS ρ R₁ P hR₁ hμ hρ hP

theorem gap28 (ρ : Vec3 → ℝ) (P Q : Vec3) :
    productDivergenceQ ρ P Q =
      ρ Q * kernelLaplacianQ P Q +
        dot (gradient ρ Q) (kernelGradientQ P Q) := by
  rfl

theorem gap29 (P Q : Vec3) (hne : P ≠ Q) :
    kernelLaplacianQ P Q = 0 := by
  exact kernelLaplacianQ_zero P Q hne

private theorem productDivergenceIntegral_eq_neg_density
    (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) :
    productDivergenceIntegral ρ R₁ P =
      -densityInteraction ρ R₁ P := by
  unfold productDivergenceIntegral densityInteraction
  calc
    (∫ Q in nearRegion R₁, productDivergenceQ ρ P Q) =
        ∫ Q in nearRegion R₁,
          -dot (gradient ρ Q) (kernelGradientP P Q) := by
      apply integral_congr_ae
      filter_upwards
        [ae_ne_for_volume_restrict (nearRegion R₁) P]
          with Q hQP
      unfold productDivergenceQ kernelGradientQ neg dot
      rw [kernelLaplacianQ_zero P Q hQP.symm]
      ring
    _ = -(∫ Q in nearRegion R₁,
          dot (gradient ρ Q) (kernelGradientP P Q)) := by
      rw [MeasureTheory.integral_neg]

theorem gap30 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3)
    (hR₁ : 0 < R₁) (hμ : IsSphereAreaMeasure μS R₁)
    (hρ : ContDiff ℝ 2 ρ) (hP : P ∈ nearRegion R₁)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem) :
    laplacian (nearPotential ρ R₁) P =
      surfaceNormalTerm μS ρ R₁ P -
        productDivergenceIntegral ρ R₁ P := by
  have hnear :=
    gap27 μS ρ R₁ P hR₁ hμ hρ hP
      hNearGradient hNearDivergence
  have hproduct :=
    productDivergenceIntegral_eq_neg_density ρ R₁ P
  rw [hnear, hproduct]
  ring

theorem gap31 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3)
    (hR₁ : 0 < R₁) (hμ : IsSphereAreaMeasure μS R₁)
    (hρ : ContDiff ℝ 2 ρ) (hP : P ∈ nearRegion R₁)
    (hGreen : SatisfiesPuncturedGreenIdentity) :
    productDivergenceIntegral ρ R₁ P =
      surfaceNormalTerm μS ρ R₁ P +
        4 * Real.pi * ρ P := by
  exact hGreen μS ρ R₁ P hR₁ hμ hρ hP

theorem gap32 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (R₁ : ℝ) (P : Vec3)
    (hR₁ : 0 < R₁) (hμ : IsSphereAreaMeasure μS R₁)
    (hρ : ContDiff ℝ 2 ρ) (hP : P ∈ nearRegion R₁)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem)
    (hGreen : SatisfiesPuncturedGreenIdentity) :
    laplacian (nearPotential ρ R₁) P =
      -4 * Real.pi * ρ P := by
  have hnear :=
    gap30 μS ρ R₁ P hR₁ hμ hρ hP
      hNearGradient hNearDivergence
  rw [hnear, hGreen μS ρ R₁ P hR₁ hμ hρ hP]
  ring

private def directionalDerivative
    (d : Vec3) (f : Vec3 → ℝ) (P : Vec3) : ℝ :=
  fderiv ℝ f P d

private def eX : Vec3 := (1, 0, 0)

private def eY : Vec3 := (0, 1, 0)

private def eZ : Vec3 := (0, 0, 1)

private theorem hasDerivAt_slice_x_at
    (f : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P) :
    HasDerivAt (fun x => f (x, P.2.1, P.2.2))
      (directionalDerivative eX f P) P.1 := by
  have hcurve :
      HasDerivAt (fun x : ℝ => (x, P.2.1, P.2.2)) eX P.1 := by
    unfold eX
    exact
      (hasDerivAt_id P.1).prodMk
        ((hasDerivAt_const P.1 P.2.1).prodMk
          (hasDerivAt_const P.1 P.2.2))
  simpa [Function.comp_def, directionalDerivative] using
    hf.hasFDerivAt.comp_hasDerivAt P.1 hcurve

private theorem hasDerivAt_slice_y_at
    (f : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P) :
    HasDerivAt (fun y => f (P.1, y, P.2.2))
      (directionalDerivative eY f P) P.2.1 := by
  have hcurve :
      HasDerivAt (fun y : ℝ => (P.1, y, P.2.2)) eY P.2.1 := by
    unfold eY
    exact
      (hasDerivAt_const P.2.1 P.1).prodMk
        ((hasDerivAt_id P.2.1).prodMk
          (hasDerivAt_const P.2.1 P.2.2))
  simpa [Function.comp_def, directionalDerivative] using
    hf.hasFDerivAt.comp_hasDerivAt P.2.1 hcurve

private theorem hasDerivAt_slice_z_at
    (f : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P) :
    HasDerivAt (fun z => f (P.1, P.2.1, z))
      (directionalDerivative eZ f P) P.2.2 := by
  have hcurve :
      HasDerivAt (fun z : ℝ => (P.1, P.2.1, z)) eZ P.2.2 := by
    unfold eZ
    exact
      (hasDerivAt_const P.2.2 P.1).prodMk
        ((hasDerivAt_const P.2.2 P.2.1).prodMk
          (hasDerivAt_id P.2.2))
  simpa [Function.comp_def, directionalDerivative] using
    hf.hasFDerivAt.comp_hasDerivAt P.2.2 hcurve

private theorem partialX_add_at
    (f g : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P)
    (hg : DifferentiableAt ℝ g P) :
    partialX (fun X => f X + g X) P =
      partialX f P + partialX g P := by
  unfold partialX
  exact
    deriv_add
      (hasDerivAt_slice_x_at f P hf).differentiableAt
      (hasDerivAt_slice_x_at g P hg).differentiableAt

private theorem partialY_add_at
    (f g : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P)
    (hg : DifferentiableAt ℝ g P) :
    partialY (fun X => f X + g X) P =
      partialY f P + partialY g P := by
  unfold partialY
  exact
    deriv_add
      (hasDerivAt_slice_y_at f P hf).differentiableAt
      (hasDerivAt_slice_y_at g P hg).differentiableAt

private theorem partialZ_add_at
    (f g : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P)
    (hg : DifferentiableAt ℝ g P) :
    partialZ (fun X => f X + g X) P =
      partialZ f P + partialZ g P := by
  unfold partialZ
  exact
    deriv_add
      (hasDerivAt_slice_z_at f P hf).differentiableAt
      (hasDerivAt_slice_z_at g P hg).differentiableAt

private theorem partialX_const_mul_at
    (c : ℝ) (f : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P) :
    partialX (fun X => c * f X) P = c * partialX f P := by
  unfold partialX
  exact deriv_const_mul c
    (hasDerivAt_slice_x_at f P hf).differentiableAt

private theorem partialY_const_mul_at
    (c : ℝ) (f : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P) :
    partialY (fun X => c * f X) P = c * partialY f P := by
  unfold partialY
  exact deriv_const_mul c
    (hasDerivAt_slice_y_at f P hf).differentiableAt

private theorem partialZ_const_mul_at
    (c : ℝ) (f : Vec3 → ℝ) (P : Vec3)
    (hf : DifferentiableAt ℝ f P) :
    partialZ (fun X => c * f X) P = c * partialZ f P := by
  unfold partialZ
  exact deriv_const_mul c
    (hasDerivAt_slice_z_at f P hf).differentiableAt

private theorem partialX_congr_of_eventuallyEq
    (f g : Vec3 → ℝ) (P : Vec3)
    (hfg : f =ᶠ[𝓝 P] g) :
    partialX f P = partialX g P := by
  unfold partialX
  apply Filter.EventuallyEq.deriv_eq
  exact hfg.comp_tendsto
    (show ContinuousAt
        (fun x : ℝ => (x, P.2.1, P.2.2)) P.1 by
      fun_prop)

private theorem partialY_congr_of_eventuallyEq
    (f g : Vec3 → ℝ) (P : Vec3)
    (hfg : f =ᶠ[𝓝 P] g) :
    partialY f P = partialY g P := by
  unfold partialY
  apply Filter.EventuallyEq.deriv_eq
  exact hfg.comp_tendsto
    (show ContinuousAt
        (fun y : ℝ => (P.1, y, P.2.2)) P.2.1 by
      fun_prop)

private theorem partialZ_congr_of_eventuallyEq
    (f g : Vec3 → ℝ) (P : Vec3)
    (hfg : f =ᶠ[𝓝 P] g) :
    partialZ f P = partialZ g P := by
  unfold partialZ
  apply Filter.EventuallyEq.deriv_eq
  exact hfg.comp_tendsto
    (show ContinuousAt
        (fun z : ℝ => (P.1, P.2.1, z)) P.2.2 by
      fun_prop)

private theorem directionalDerivative_contDiffAt
    (d : Vec3) (f : Vec3 → ℝ) (P : Vec3)
    (hf : ContDiffAt ℝ 2 f P) :
    ContDiffAt ℝ 1 (directionalDerivative d f) P := by
  unfold directionalDerivative
  exact
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply
      contDiffAt_const

private theorem partialX_differentiableAt
    (f : Vec3 → ℝ) (P : Vec3)
    (hf : ContDiffAt ℝ 2 f P) :
    DifferentiableAt ℝ (partialX f) P := by
  have heq :
      partialX f =ᶠ[𝓝 P] directionalDerivative eX f := by
    filter_upwards [hf.eventually (by norm_num)] with Q hQ
    exact (hasDerivAt_slice_x_at f Q
      (hQ.differentiableAt (by decide))).deriv
  exact
    (directionalDerivative_contDiffAt eX f P hf).differentiableAt
      (by norm_num) |>.congr_of_eventuallyEq heq

private theorem partialY_differentiableAt
    (f : Vec3 → ℝ) (P : Vec3)
    (hf : ContDiffAt ℝ 2 f P) :
    DifferentiableAt ℝ (partialY f) P := by
  have heq :
      partialY f =ᶠ[𝓝 P] directionalDerivative eY f := by
    filter_upwards [hf.eventually (by norm_num)] with Q hQ
    exact (hasDerivAt_slice_y_at f Q
      (hQ.differentiableAt (by decide))).deriv
  exact
    (directionalDerivative_contDiffAt eY f P hf).differentiableAt
      (by norm_num) |>.congr_of_eventuallyEq heq

private theorem partialZ_differentiableAt
    (f : Vec3 → ℝ) (P : Vec3)
    (hf : ContDiffAt ℝ 2 f P) :
    DifferentiableAt ℝ (partialZ f) P := by
  have heq :
      partialZ f =ᶠ[𝓝 P] directionalDerivative eZ f := by
    filter_upwards [hf.eventually (by norm_num)] with Q hQ
    exact (hasDerivAt_slice_z_at f Q
      (hQ.differentiableAt (by decide))).deriv
  exact
    (directionalDerivative_contDiffAt eZ f P hf).differentiableAt
      (by norm_num) |>.congr_of_eventuallyEq heq

private theorem secondPartialX_const_add
    (c : ℝ) (f g : Vec3 → ℝ) (P : Vec3)
    (hf : ContDiffAt ℝ 2 f P)
    (hg : ContDiffAt ℝ 2 g P) :
    partialX
        (fun X => partialX (fun Y => c * (f Y + g Y)) X) P =
      c *
        (partialX (fun X => partialX f X) P +
          partialX (fun X => partialX g X) P) := by
  have heq :
      (fun X => partialX (fun Y => c * (f Y + g Y)) X) =ᶠ[𝓝 P]
        (fun X => c * (partialX f X + partialX g X)) := by
    filter_upwards [hf.eventually (by norm_num),
      hg.eventually (by norm_num)] with X hfX hgX
    have hfd : DifferentiableAt ℝ f X :=
      hfX.differentiableAt (by decide)
    have hgd : DifferentiableAt ℝ g X :=
      hgX.differentiableAt (by decide)
    calc
      partialX (fun Y => c * (f Y + g Y)) X =
          c * partialX (fun Y => f Y + g Y) X :=
        partialX_const_mul_at c (fun Y => f Y + g Y) X
          (hfd.add hgd)
      _ = c * (partialX f X + partialX g X) := by
        rw [partialX_add_at f g X hfd hgd]
  have hpf := partialX_differentiableAt f P hf
  have hpg := partialX_differentiableAt g P hg
  calc
    partialX
        (fun X => partialX (fun Y => c * (f Y + g Y)) X) P =
        partialX
          (fun X => c * (partialX f X + partialX g X)) P :=
      partialX_congr_of_eventuallyEq _ _ P heq
    _ = c *
        partialX (fun X => partialX f X + partialX g X) P :=
      partialX_const_mul_at c
        (fun X => partialX f X + partialX g X) P
        (hpf.add hpg)
    _ = c *
        (partialX (fun X => partialX f X) P +
          partialX (fun X => partialX g X) P) := by
      rw [partialX_add_at (partialX f) (partialX g) P hpf hpg]

private theorem secondPartialY_const_add
    (c : ℝ) (f g : Vec3 → ℝ) (P : Vec3)
    (hf : ContDiffAt ℝ 2 f P)
    (hg : ContDiffAt ℝ 2 g P) :
    partialY
        (fun X => partialY (fun Y => c * (f Y + g Y)) X) P =
      c *
        (partialY (fun X => partialY f X) P +
          partialY (fun X => partialY g X) P) := by
  have heq :
      (fun X => partialY (fun Y => c * (f Y + g Y)) X) =ᶠ[𝓝 P]
        (fun X => c * (partialY f X + partialY g X)) := by
    filter_upwards [hf.eventually (by norm_num),
      hg.eventually (by norm_num)] with X hfX hgX
    have hfd : DifferentiableAt ℝ f X :=
      hfX.differentiableAt (by decide)
    have hgd : DifferentiableAt ℝ g X :=
      hgX.differentiableAt (by decide)
    calc
      partialY (fun Y => c * (f Y + g Y)) X =
          c * partialY (fun Y => f Y + g Y) X :=
        partialY_const_mul_at c (fun Y => f Y + g Y) X
          (hfd.add hgd)
      _ = c * (partialY f X + partialY g X) := by
        rw [partialY_add_at f g X hfd hgd]
  have hpf := partialY_differentiableAt f P hf
  have hpg := partialY_differentiableAt g P hg
  calc
    partialY
        (fun X => partialY (fun Y => c * (f Y + g Y)) X) P =
        partialY
          (fun X => c * (partialY f X + partialY g X)) P :=
      partialY_congr_of_eventuallyEq _ _ P heq
    _ = c *
        partialY (fun X => partialY f X + partialY g X) P :=
      partialY_const_mul_at c
        (fun X => partialY f X + partialY g X) P
        (hpf.add hpg)
    _ = c *
        (partialY (fun X => partialY f X) P +
          partialY (fun X => partialY g X) P) := by
      rw [partialY_add_at (partialY f) (partialY g) P hpf hpg]

private theorem secondPartialZ_const_add
    (c : ℝ) (f g : Vec3 → ℝ) (P : Vec3)
    (hf : ContDiffAt ℝ 2 f P)
    (hg : ContDiffAt ℝ 2 g P) :
    partialZ
        (fun X => partialZ (fun Y => c * (f Y + g Y)) X) P =
      c *
        (partialZ (fun X => partialZ f X) P +
          partialZ (fun X => partialZ g X) P) := by
  have heq :
      (fun X => partialZ (fun Y => c * (f Y + g Y)) X) =ᶠ[𝓝 P]
        (fun X => c * (partialZ f X + partialZ g X)) := by
    filter_upwards [hf.eventually (by norm_num),
      hg.eventually (by norm_num)] with X hfX hgX
    have hfd : DifferentiableAt ℝ f X :=
      hfX.differentiableAt (by decide)
    have hgd : DifferentiableAt ℝ g X :=
      hgX.differentiableAt (by decide)
    calc
      partialZ (fun Y => c * (f Y + g Y)) X =
          c * partialZ (fun Y => f Y + g Y) X :=
        partialZ_const_mul_at c (fun Y => f Y + g Y) X
          (hfd.add hgd)
      _ = c * (partialZ f X + partialZ g X) := by
        rw [partialZ_add_at f g X hfd hgd]
  have hpf := partialZ_differentiableAt f P hf
  have hpg := partialZ_differentiableAt g P hg
  calc
    partialZ
        (fun X => partialZ (fun Y => c * (f Y + g Y)) X) P =
        partialZ
          (fun X => c * (partialZ f X + partialZ g X)) P :=
      partialZ_congr_of_eventuallyEq _ _ P heq
    _ = c *
        partialZ (fun X => partialZ f X + partialZ g X) P :=
      partialZ_const_mul_at c
        (fun X => partialZ f X + partialZ g X) P
        (hpf.add hpg)
    _ = c *
        (partialZ (fun X => partialZ f X) P +
          partialZ (fun X => partialZ g X) P) := by
      rw [partialZ_add_at (partialZ f) (partialZ g) P hpf hpg]

theorem gap33 (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3)
    (hnear : ContDiffAt ℝ 2 (nearPotential ρ R₁) P)
    (hfar : ContDiffAt ℝ 2 (farPotential ρ R₁) P) :
    laplacian (poissonPotential ρ R₁) P =
      -(1 / (4 * Real.pi)) *
        (laplacian (nearPotential ρ R₁) P +
          laplacian (farPotential ρ R₁) P) := by
  let c : ℝ := -(1 / (4 * Real.pi))
  let f : Vec3 → ℝ := nearPotential ρ R₁
  let g : Vec3 → ℝ := farPotential ρ R₁
  have hx := secondPartialX_const_add c f g P hnear hfar
  have hy := secondPartialY_const_add c f g P hnear hfar
  have hz := secondPartialZ_const_add c f g P hnear hfar
  unfold poissonPotential laplacian divergence gradient
  change
    partialX (fun X => partialX (fun Y => c * (f Y + g Y)) X) P +
          partialY (fun X => partialY (fun Y => c * (f Y + g Y)) X) P +
        partialZ (fun X => partialZ (fun Y => c * (f Y + g Y)) X) P =
      c *
        ((partialX (fun X => partialX f X) P +
              partialY (fun X => partialY f X) P +
            partialZ (fun X => partialZ f X) P) +
          (partialX (fun X => partialX g X) P +
              partialY (fun X => partialY g X) P +
            partialZ (fun X => partialZ g X) P))
  rw [hx, hy, hz]
  ring

theorem gap34 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (M α R₀ R₁ : ℝ) (P : Vec3)
    (hdata : PoissonAnalyticData ρ M α R₀ R₁ P)
    (hμ : IsSphereAreaMeasure μS R₁)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem)
    (hGreen : SatisfiesPuncturedGreenIdentity) :
    -(1 / (4 * Real.pi)) *
        (laplacian (nearPotential ρ R₁) P +
          laplacian (farPotential ρ R₁) P) = ρ P := by
  rcases hdata with
    ⟨hM, hα, hR₁, hR₀, hρ, hdecay, hP⟩
  have hnearLap :
      laplacian (nearPotential ρ R₁) P =
        -4 * Real.pi * ρ P :=
    gap32 μS ρ R₁ P hR₁ hμ hρ hP
      hNearGradient hNearDivergence hGreen
  have hfarLap :
      laplacian (farPotential ρ R₁) P = 0 :=
    gap20 ρ M α R₀ R₁ P hM hα hR₁ hR₀
      hρ.continuous hdecay hP hFarTheorem
  rw [hnearLap, hfarLap]
  field_simp [Real.pi_ne_zero]
  ring

theorem gap35 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (M α R₀ R₁ : ℝ) (P : Vec3)
    (hdata : PoissonAnalyticData ρ M α R₀ R₁ P)
    (hμ : IsSphereAreaMeasure μS R₁)
    (hnear : ContDiffAt ℝ 2 (nearPotential ρ R₁) P)
    (hfar : ContDiffAt ℝ 2 (farPotential ρ R₁) P)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem)
    (hGreen : SatisfiesPuncturedGreenIdentity) :
    laplacian (poissonPotential ρ R₁) P = ρ P := by
  calc
    laplacian (poissonPotential ρ R₁) P =
        -(1 / (4 * Real.pi)) *
          (laplacian (nearPotential ρ R₁) P +
            laplacian (farPotential ρ R₁) P) :=
      gap33 ρ R₁ P hnear hfar
    _ = ρ P :=
      gap34 μS ρ M α R₀ R₁ P hdata hμ hFarTheorem
        hNearGradient hNearDivergence hGreen

theorem gap36 (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) :
    divergence (poissonField ρ R₁) P =
      divergence (gradient (poissonPotential ρ R₁)) P := by
  rfl

theorem gap37 (ρ : Vec3 → ℝ) (R₁ : ℝ) (P : Vec3) :
    divergence (gradient (poissonPotential ρ R₁)) P =
      laplacian (poissonPotential ρ R₁) P := by
  rfl

theorem gap38 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (M α R₀ R₁ : ℝ) (P : Vec3)
    (hdata : PoissonAnalyticData ρ M α R₀ R₁ P)
    (hμ : IsSphereAreaMeasure μS R₁)
    (hnear : ContDiffAt ℝ 2 (nearPotential ρ R₁) P)
    (hfar : ContDiffAt ℝ 2 (farPotential ρ R₁) P)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem)
    (hGreen : SatisfiesPuncturedGreenIdentity) :
    laplacian (poissonPotential ρ R₁) P = ρ P := by
  exact gap35 μS ρ M α R₀ R₁ P hdata hμ hnear hfar
    hFarTheorem hNearGradient hNearDivergence hGreen

theorem gap39 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (M α R₀ R₁ : ℝ) (P : Vec3)
    (hdata : PoissonAnalyticData ρ M α R₀ R₁ P)
    (hμ : IsSphereAreaMeasure μS R₁)
    (hnear : ContDiffAt ℝ 2 (nearPotential ρ R₁) P)
    (hfar : ContDiffAt ℝ 2 (farPotential ρ R₁) P)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem)
    (hGreen : SatisfiesPuncturedGreenIdentity) :
    divergence (poissonField ρ R₁) P = ρ P := by
  calc
    divergence (poissonField ρ R₁) P =
        laplacian (poissonPotential ρ R₁) P :=
      gap13 ρ R₁ P
    _ = ρ P :=
      gap38 μS ρ M α R₀ R₁ P hdata hμ hnear hfar
        hFarTheorem hNearGradient hNearDivergence hGreen

theorem gap40 (μS : Measure Vec3) (ρ : Vec3 → ℝ)
    (M α R₀ R₁ : ℝ) (P : Vec3)
    (hdata : PoissonAnalyticData ρ M α R₀ R₁ P)
    (hμ : IsSphereAreaMeasure μS R₁)
    (hnear : ContDiffAt ℝ 2 (nearPotential ρ R₁) P)
    (hfar : ContDiffAt ℝ 2 (farPotential ρ R₁) P)
    (hFarTheorem : SatisfiesFarDifferentiationTheorem)
    (hNearGradient : SatisfiesNearPotentialGradientTheorem)
    (hNearDivergence : SatisfiesNearGradientDivergenceTheorem)
    (hGreen : SatisfiesPuncturedGreenIdentity) :
    laplacian (poissonPotential ρ R₁) P = ρ P := by
  exact gap38 μS ρ M α R₀ R₁ P hdata hμ hnear hfar
    hFarTheorem hNearGradient hNearDivergence hGreen

end

end ProofGap.Exercise4462
