import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

namespace ProofGap.Exercise4396

noncomputable section

open Filter MeasureTheory
open scoped Interval Topology

abbrev Vec3 := ℝ × ℝ × ℝ

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def cross (a b : Vec3) : Vec3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
    a.2.2 * b.1 - a.1 * b.2.2,
    a.1 * b.2.1 - a.2.1 * b.1)

def vecNorm (a : Vec3) : ℝ :=
  Real.sqrt (a.1 ^ 2 + a.2.1 ^ 2 + a.2.2 ^ 2)

def distance (q p : Vec3) : ℝ :=
  vecNorm (p.1 - q.1, p.2.1 - q.2.1, p.2.2 - q.2.2)

def reciprocalKernel (q p : Vec3) : ℝ :=
  1 / distance q p

def radialUnit (q p : Vec3) : Vec3 :=
  ((p.1 - q.1) / distance q p,
    (p.2.1 - q.2.1) / distance q p,
    (p.2.2 - q.2.2) / distance q p)

def gradient (f : Vec3 → ℝ) (p : Vec3) : Vec3 :=
  (deriv (fun x => f (x, p.2.1, p.2.2)) p.1,
    deriv (fun y => f (p.1, y, p.2.2)) p.2.1,
    deriv (fun z => f (p.1, p.2.1, z)) p.2.2)

def laplacian (f : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => (gradient f (x, p.2.1, p.2.2)).1) p.1 +
    deriv (fun y => (gradient f (p.1, y, p.2.2)).2.1) p.2.1 +
    deriv (fun z => (gradient f (p.1, p.2.1, z)).2.2) p.2.2

def kernelLaplacian (q p : Vec3) : ℝ :=
  laplacian (reciprocalKernel q) p

def normalDerivative (f : Vec3 → ℝ) (p n : Vec3) : ℝ :=
  dot (gradient f p) n

def kernelNormalDerivative (q p n : Vec3) : ℝ :=
  normalDerivative (reciprocalKernel q) p n

def puncturedOutwardNormal (q p : Vec3) : Vec3 :=
  (-((radialUnit q p).1), -((radialUnit q p).2.1),
    -((radialUnit q p).2.2))

structure ParametricSurface where
  param : ℝ → ℝ → Vec3
  s₀ : ℝ
  s₁ : ℝ
  t₀ : ℝ
  t₁ : ℝ

def surfacePartialS (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  (deriv (fun r => (S.param r t).1) s,
    deriv (fun r => (S.param r t).2.1) s,
    deriv (fun r => (S.param r t).2.2) s)

def surfacePartialT (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  (deriv (fun r => (S.param s r).1) t,
    deriv (fun r => (S.param s r).2.1) t,
    deriv (fun r => (S.param s r).2.2) t)

def surfaceAreaVector (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  cross (surfacePartialS S s t) (surfacePartialT S s t)

def surfaceJacobian (S : ParametricSurface) (s t : ℝ) : ℝ :=
  vecNorm (surfaceAreaVector S s t)

def surfaceUnitNormal (S : ParametricSurface) (s t : ℝ) : Vec3 :=
  let J := surfaceJacobian S s t
  let n := surfaceAreaVector S s t
  (n.1 / J, n.2.1 / J, n.2.2 / J)

def surfaceScalarIntegral (S : ParametricSurface) (g : Vec3 → ℝ) : ℝ :=
  ∫ s in S.s₀..S.s₁,
    ∫ t in S.t₀..S.t₁,
      g (S.param s t) * surfaceJacobian S s t

def sphereParam (q : Vec3) (ρ φ θ : ℝ) : Vec3 :=
  (q.1 + ρ * Real.cos φ * Real.cos θ,
    q.2.1 + ρ * Real.cos φ * Real.sin θ,
    q.2.2 + ρ * Real.sin φ)

def smallSphereIntegral (q : Vec3) (ρ : ℝ) (g : Vec3 → ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      ρ ^ 2 * Real.cos φ * g (sphereParam q ρ φ θ)

def smallSphereMean (q : Vec3) (u : Vec3 → ℝ) (ρ : ℝ) : ℝ :=
  1 / (4 * Real.pi * ρ ^ 2) * smallSphereIntegral q ρ u

def greenPairing (f g : Vec3 → ℝ) (p n : Vec3) : ℝ :=
  g p * normalDerivative f p n - f p * normalDerivative g p n

def outerGreenPairing
    (S : ParametricSurface) (f g : Vec3 → ℝ) : ℝ :=
  ∫ s in S.s₀..S.s₁,
    ∫ t in S.t₀..S.t₁,
      greenPairing f g (S.param s t) (surfaceUnitNormal S s t) *
        surfaceJacobian S s t

def smallGreenPairing
    (q : Vec3) (ρ : ℝ) (f g : Vec3 → ℝ) : ℝ :=
  smallSphereIntegral q ρ
    (fun p => greenPairing f g p (puncturedOutwardNormal q p))

def greenBoundaryIntegrand (u : Vec3 → ℝ) (q p n : Vec3) : ℝ :=
  reciprocalKernel q p * normalDerivative u p n -
    u p * kernelNormalDerivative q p n

def outerGreenIntegral (S : ParametricSurface)
    (u : Vec3 → ℝ) (q : Vec3) : ℝ :=
  outerGreenPairing S u (reciprocalKernel q)

def representationIntegrand (u : Vec3 → ℝ) (q p n : Vec3) : ℝ :=
  u p * dot (radialUnit q p) n / distance q p ^ 2 +
    reciprocalKernel q p * normalDerivative u p n

def outerRepresentationIntegral (S : ParametricSurface)
    (u : Vec3 → ℝ) (q : Vec3) : ℝ :=
  ∫ s in S.s₀..S.s₁,
    ∫ t in S.t₀..S.t₁,
      representationIntegrand u q (S.param s t)
          (surfaceUnitNormal S s t) *
        surfaceJacobian S s t

def closedBall (q : Vec3) (ρ : ℝ) : Set Vec3 :=
  {p | distance q p ≤ ρ}

def puncturedDomain (V : Set Vec3) (q : Vec3) (ρ : ℝ) : Set Vec3 :=
  V \ closedBall q ρ

def IsC2 (u : Vec3 → ℝ) : Prop :=
  ContDiff ℝ 2 u

def SmoothAwayFrom (q : Vec3) (u : Vec3 → ℝ) : Prop :=
  ContDiffOn ℝ 2 u ({q}ᶜ)

def HarmonicOn (u : Vec3 → ℝ) (V : Set Vec3) : Prop :=
  ∀ p ∈ V, laplacian u p = 0

def SurfaceRegular (S : ParametricSurface) : Prop :=
  ∀ s t, surfaceJacobian S s t ≠ 0

def SatisfiesSecondGreenIdentity
    (S : ParametricSurface) (V : Set Vec3) (q : Vec3) : Prop :=
  ∀ (f g : Vec3 → ℝ), SmoothAwayFrom q f → SmoothAwayFrom q g →
    ∀ ρ : ℝ, 0 < ρ → closedBall q ρ ⊆ V →
      outerGreenPairing S f g + smallGreenPairing q ρ f g =
        ∫ p in puncturedDomain V q ρ,
          g p * laplacian f p - f p * laplacian g p

/-- The spherical version of the divergence theorem needed below.

Mathlib's divergence-theorem API currently covers boxes, not the
parametrized Euclidean spheres used in this exercise.  Keeping that missing
background theorem as one universal interface avoids assuming the desired
identity separately at every radius. -/
def SatisfiesBallDivergenceTheorem : Prop :=
  ∀ (u : Vec3 → ℝ) (q : Vec3) (r : ℝ),
    IsC2 u → 0 < r →
      smallSphereIntegral q r
          (fun p => normalDerivative u p (puncturedOutwardNormal q p)) =
        -(∫ p in closedBall q r, laplacian u p)

private def distanceSq (q p : Vec3) : ℝ :=
  (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
    (p.2.2 - q.2.2) ^ 2

private theorem distance_pos_of_ne
    (q p : Vec3) (hpq : p ≠ q) :
    0 < distance q p := by
  have hs : 0 < distanceSq q p := by
    by_contra hn
    have hle : distanceSq q p ≤ 0 := le_of_not_gt hn
    have hx : p.1 = q.1 := by
      unfold distanceSq at hle
      nlinarith [sq_nonneg (p.1 - q.1),
        sq_nonneg (p.2.1 - q.2.1),
        sq_nonneg (p.2.2 - q.2.2)]
    have hy : p.2.1 = q.2.1 := by
      unfold distanceSq at hle
      nlinarith [sq_nonneg (p.1 - q.1),
        sq_nonneg (p.2.1 - q.2.1),
        sq_nonneg (p.2.2 - q.2.2)]
    have hz : p.2.2 = q.2.2 := by
      unfold distanceSq at hle
      nlinarith [sq_nonneg (p.1 - q.1),
        sq_nonneg (p.2.1 - q.2.1),
        sq_nonneg (p.2.2 - q.2.2)]
    apply hpq
    ext <;> assumption
  simpa [distance, vecNorm, distanceSq] using Real.sqrt_pos.2 hs

private theorem distanceSq_pos_of_ne
    (q p : Vec3) (hpq : p ≠ q) :
    0 < distanceSq q p := by
  simpa [distanceSq, distance, vecNorm] using
    (Real.sqrt_pos.1 (distance_pos_of_ne q p hpq))

private theorem distance_sq
    (q p : Vec3) :
    distance q p ^ 2 = distanceSq q p := by
  unfold distance vecNorm distanceSq
  exact Real.sq_sqrt (by positivity)

private theorem reciprocalKernel_smoothAway (q : Vec3) :
    SmoothAwayFrom q (reciprocalKernel q) := by
  have hsq : ContDiff ℝ 2 (distanceSq q) := by
    unfold distanceSq
    fun_prop
  have hsqne :
      ∀ p ∈ ({q}ᶜ : Set Vec3), distanceSq q p ≠ 0 := by
    intro p hp
    exact (distanceSq_pos_of_ne q p
      (Set.mem_compl_singleton_iff.mp hp)).ne'
  have hsqrt :
      ContDiffOn ℝ 2
        (fun p => Real.sqrt (distanceSq q p)) ({q}ᶜ : Set Vec3) :=
    hsq.contDiffOn.sqrt hsqne
  unfold SmoothAwayFrom reciprocalKernel distance vecNorm
  simpa [distanceSq, one_div] using
    (hsqrt.inv fun p hp =>
      (distance_pos_of_ne q p
        (Set.mem_compl_singleton_iff.mp hp)).ne')

private theorem hasDerivAt_invSqrtQuad
    (a B x : ℝ) (hpos : 0 < (x - a) ^ 2 + B) :
    HasDerivAt
      (fun y => 1 / Real.sqrt ((y - a) ^ 2 + B))
      (-(x - a) / Real.sqrt ((x - a) ^ 2 + B) ^ 3) x := by
  have hquad :
      HasDerivAt (fun y => (y - a) ^ 2 + B) (2 * (x - a)) x := by
    simpa [id_eq] using
      (((hasDerivAt_id x).sub_const a).pow 2).add_const B
  have hsqrt := (Real.hasDerivAt_sqrt hpos.ne').comp x hquad
  have hr : Real.sqrt ((x - a) ^ 2 + B) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hinv := hsqrt.inv hr
  simp only [Function.comp_apply] at hinv
  convert hinv using 1
  · funext y
    simp [one_div]
  · field_simp [hr]

private theorem deriv_reciprocalKernel_x
    (q p : Vec3) (hpq : p ≠ q) :
    deriv (fun x => reciprocalKernel q (x, p.2.1, p.2.2)) p.1 =
      -(p.1 - q.1) / distance q p ^ 3 := by
  have hpos := distanceSq_pos_of_ne q p hpq
  have h :=
    hasDerivAt_invSqrtQuad q.1
      ((p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2) p.1
      (by simpa [distanceSq, add_assoc] using hpos)
  simpa [reciprocalKernel, distance, vecNorm, add_assoc] using h.deriv

private theorem deriv_reciprocalKernel_y
    (q p : Vec3) (hpq : p ≠ q) :
    deriv (fun y => reciprocalKernel q (p.1, y, p.2.2)) p.2.1 =
      -(p.2.1 - q.2.1) / distance q p ^ 3 := by
  have hpos := distanceSq_pos_of_ne q p hpq
  have h :=
    hasDerivAt_invSqrtQuad q.2.1
      ((p.1 - q.1) ^ 2 + (p.2.2 - q.2.2) ^ 2) p.2.1
      (by
        simpa [distanceSq, add_comm, add_left_comm, add_assoc] using hpos)
  simpa [reciprocalKernel, distance, vecNorm, add_comm,
    add_left_comm, add_assoc] using h.deriv

private theorem deriv_reciprocalKernel_z
    (q p : Vec3) (hpq : p ≠ q) :
    deriv (fun z => reciprocalKernel q (p.1, p.2.1, z)) p.2.2 =
      -(p.2.2 - q.2.2) / distance q p ^ 3 := by
  have hpos := distanceSq_pos_of_ne q p hpq
  have h :=
    hasDerivAt_invSqrtQuad q.2.2
      ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2) p.2.2
      (by
        simpa [distanceSq, add_comm, add_left_comm, add_assoc] using hpos)
  simpa [reciprocalKernel, distance, vecNorm, add_comm,
    add_left_comm, add_assoc] using h.deriv

private theorem gradient_reciprocalKernel
    (q p : Vec3) (hpq : p ≠ q) :
    gradient (reciprocalKernel q) p =
      (-(p.1 - q.1) / distance q p ^ 3,
        -(p.2.1 - q.2.1) / distance q p ^ 3,
        -(p.2.2 - q.2.2) / distance q p ^ 3) := by
  unfold gradient
  rw [deriv_reciprocalKernel_x q p hpq,
    deriv_reciprocalKernel_y q p hpq,
    deriv_reciprocalKernel_z q p hpq]

private theorem hasDerivAt_invSqrtQuad_second
    (a B x : ℝ) (hpos : 0 < (x - a) ^ 2 + B) :
    HasDerivAt
      (fun y => -(y - a) / Real.sqrt ((y - a) ^ 2 + B) ^ 3)
      (-1 / Real.sqrt ((x - a) ^ 2 + B) ^ 3 +
        3 * (x - a) ^ 2 / Real.sqrt ((x - a) ^ 2 + B) ^ 5) x := by
  have hlin : HasDerivAt (fun y => y - a) 1 x :=
    (hasDerivAt_id x).sub_const a
  have hquad :
      HasDerivAt (fun y => (y - a) ^ 2 + B) (2 * (x - a)) x := by
    simpa [id_eq] using (hlin.pow 2).add_const B
  have hsqrt := (Real.hasDerivAt_sqrt hpos.ne').comp x hquad
  have hr : Real.sqrt ((x - a) ^ 2 + B) ≠ 0 :=
    (Real.sqrt_pos.2 hpos).ne'
  have hquot := hlin.neg.div (hsqrt.pow 3) (pow_ne_zero 3 hr)
  simp only [Function.comp_apply, Pi.pow_apply, Pi.neg_apply] at hquot
  convert hquot using 1
  field_simp [hr] <;> ring

private theorem deriv_gradient_reciprocalKernel_x
    (q p : Vec3) (hpq : p ≠ q) :
    deriv
      (fun x => (gradient (reciprocalKernel q)
        (x, p.2.1, p.2.2)).1) p.1 =
      -1 / distance q p ^ 3 +
        3 * (p.1 - q.1) ^ 2 / distance q p ^ 5 := by
  have hcurve :
      Continuous (fun x : ℝ => ((x, p.2.1, p.2.2) : Vec3)) := by
    fun_prop
  have hevent :
      ∀ᶠ x in nhds p.1,
        ((x, p.2.1, p.2.2) : Vec3) ∈ ({q}ᶜ : Set Vec3) :=
    hcurve.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hpq))
  have heq :
      (fun x => (gradient (reciprocalKernel q)
        (x, p.2.1, p.2.2)).1) =ᶠ[nhds p.1]
      (fun x => -(x - q.1) /
        distance q (x, p.2.1, p.2.2) ^ 3) := by
    filter_upwards [hevent] with x hx
    rw [gradient_reciprocalKernel q (x, p.2.1, p.2.2)
      (Set.mem_compl_singleton_iff.mp hx)]
  calc
    deriv
        (fun x => (gradient (reciprocalKernel q)
          (x, p.2.1, p.2.2)).1) p.1 =
        deriv (fun x => -(x - q.1) /
          distance q (x, p.2.1, p.2.2) ^ 3) p.1 := heq.deriv_eq
    _ = -1 / distance q p ^ 3 +
        3 * (p.1 - q.1) ^ 2 / distance q p ^ 5 := by
      have hpos := distanceSq_pos_of_ne q p hpq
      have h :=
        hasDerivAt_invSqrtQuad_second q.1
          ((p.2.1 - q.2.1) ^ 2 + (p.2.2 - q.2.2) ^ 2) p.1
          (by simpa [distanceSq, add_assoc] using hpos)
      simpa [distance, vecNorm, add_assoc] using h.deriv

private theorem deriv_gradient_reciprocalKernel_y
    (q p : Vec3) (hpq : p ≠ q) :
    deriv
      (fun y => (gradient (reciprocalKernel q)
        (p.1, y, p.2.2)).2.1) p.2.1 =
      -1 / distance q p ^ 3 +
        3 * (p.2.1 - q.2.1) ^ 2 / distance q p ^ 5 := by
  have hcurve :
      Continuous (fun y : ℝ => ((p.1, y, p.2.2) : Vec3)) := by
    fun_prop
  have hevent :
      ∀ᶠ y in nhds p.2.1,
        ((p.1, y, p.2.2) : Vec3) ∈ ({q}ᶜ : Set Vec3) :=
    hcurve.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hpq))
  have heq :
      (fun y => (gradient (reciprocalKernel q)
        (p.1, y, p.2.2)).2.1) =ᶠ[nhds p.2.1]
      (fun y => -(y - q.2.1) /
        distance q (p.1, y, p.2.2) ^ 3) := by
    filter_upwards [hevent] with y hy
    rw [gradient_reciprocalKernel q (p.1, y, p.2.2)
      (Set.mem_compl_singleton_iff.mp hy)]
  calc
    deriv
        (fun y => (gradient (reciprocalKernel q)
          (p.1, y, p.2.2)).2.1) p.2.1 =
        deriv (fun y => -(y - q.2.1) /
          distance q (p.1, y, p.2.2) ^ 3) p.2.1 := heq.deriv_eq
    _ = -1 / distance q p ^ 3 +
        3 * (p.2.1 - q.2.1) ^ 2 / distance q p ^ 5 := by
      have hpos := distanceSq_pos_of_ne q p hpq
      have h :=
        hasDerivAt_invSqrtQuad_second q.2.1
          ((p.1 - q.1) ^ 2 + (p.2.2 - q.2.2) ^ 2) p.2.1
          (by
            simpa [distanceSq, add_comm, add_left_comm, add_assoc] using hpos)
      simpa [distance, vecNorm, add_comm, add_left_comm,
        add_assoc] using h.deriv

private theorem deriv_gradient_reciprocalKernel_z
    (q p : Vec3) (hpq : p ≠ q) :
    deriv
      (fun z => (gradient (reciprocalKernel q)
        (p.1, p.2.1, z)).2.2) p.2.2 =
      -1 / distance q p ^ 3 +
        3 * (p.2.2 - q.2.2) ^ 2 / distance q p ^ 5 := by
  have hcurve :
      Continuous (fun z : ℝ => ((p.1, p.2.1, z) : Vec3)) := by
    fun_prop
  have hevent :
      ∀ᶠ z in nhds p.2.2,
        ((p.1, p.2.1, z) : Vec3) ∈ ({q}ᶜ : Set Vec3) :=
    hcurve.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds
        (Set.mem_compl_singleton_iff.mpr hpq))
  have heq :
      (fun z => (gradient (reciprocalKernel q)
        (p.1, p.2.1, z)).2.2) =ᶠ[nhds p.2.2]
      (fun z => -(z - q.2.2) /
        distance q (p.1, p.2.1, z) ^ 3) := by
    filter_upwards [hevent] with z hz
    rw [gradient_reciprocalKernel q (p.1, p.2.1, z)
      (Set.mem_compl_singleton_iff.mp hz)]
  calc
    deriv
        (fun z => (gradient (reciprocalKernel q)
          (p.1, p.2.1, z)).2.2) p.2.2 =
        deriv (fun z => -(z - q.2.2) /
          distance q (p.1, p.2.1, z) ^ 3) p.2.2 := heq.deriv_eq
    _ = -1 / distance q p ^ 3 +
        3 * (p.2.2 - q.2.2) ^ 2 / distance q p ^ 5 := by
      have hpos := distanceSq_pos_of_ne q p hpq
      have h :=
        hasDerivAt_invSqrtQuad_second q.2.2
          ((p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2) p.2.2
          (by
            simpa [distanceSq, add_comm, add_left_comm, add_assoc] using hpos)
      simpa [distance, vecNorm, add_comm, add_left_comm,
        add_assoc] using h.deriv

private theorem laplacian_reciprocalKernel
    (q p : Vec3) (hpq : p ≠ q) :
    laplacian (reciprocalKernel q) p = 0 := by
  unfold laplacian
  rw [deriv_gradient_reciprocalKernel_x q p hpq,
    deriv_gradient_reciprocalKernel_y q p hpq,
    deriv_gradient_reciprocalKernel_z q p hpq]
  have hr : distance q p ≠ 0 := (distance_pos_of_ne q p hpq).ne'
  have hsqrt_sq := distance_sq q p
  unfold distanceSq at hsqrt_sq
  field_simp [hr]
  nlinarith

private theorem kernelNormalDerivative_formula
    (q p n : Vec3) (hpq : p ≠ q) :
    kernelNormalDerivative q p n =
      -dot (radialUnit q p) n / distance q p ^ 2 := by
  unfold kernelNormalDerivative normalDerivative
  rw [gradient_reciprocalKernel q p hpq]
  unfold dot radialUnit
  have hr : distance q p ≠ 0 := (distance_pos_of_ne q p hpq).ne'
  have hsqrt_sq := distance_sq q p
  unfold distanceSq at hsqrt_sq
  field_simp [hr]
  nlinarith

private theorem deriv_inv_sqrt_sq_zero (a : ℝ) :
    deriv (fun x => 1 / Real.sqrt ((x - a) ^ 2)) a = 0 := by
  apply deriv_zero_of_not_differentiableAt
  intro hdifferentiable
  obtain ⟨δ, hδ, hbound⟩ :=
    (Metric.continuousAt_iff.mp hdifferentiable.continuousAt)
      1 one_pos
  let d : ℝ := min (δ / 2) (1 / 2)
  have hdpos : 0 < d :=
    lt_min (half_pos hδ) (by norm_num)
  have hdδ : d < δ :=
    (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hnear : dist (a + d) a < δ := by
    rw [Real.dist_eq]
    simpa [abs_of_pos hdpos] using hdδ
  have hb := hbound hnear
  have hdist :
      dist
          (1 / Real.sqrt (((a + d) - a) ^ 2))
          (1 / Real.sqrt ((a - a) ^ 2)) =
        1 / d := by
    rw [Real.dist_eq]
    simp [Real.sqrt_sq_eq_abs, abs_of_pos hdpos, one_div]
  rw [hdist] at hb
  have hdhalf : d ≤ 1 / 2 := min_le_right _ _
  have hone : 1 ≤ 1 / d := by
    rw [le_div_iff₀ hdpos]
    linarith
  linarith

private theorem gradient_reciprocalKernel_self (q : Vec3) :
    gradient (reciprocalKernel q) q = (0, 0, 0) := by
  unfold gradient reciprocalKernel distance vecNorm
  apply Prod.ext
  · simpa using deriv_inv_sqrt_sq_zero q.1
  · apply Prod.ext
    · simpa [add_comm, add_left_comm, add_assoc] using
        deriv_inv_sqrt_sq_zero q.2.1
    · simpa [add_comm, add_left_comm, add_assoc] using
        deriv_inv_sqrt_sq_zero q.2.2

private theorem kernelNormalDerivative_formula_all
    (q p n : Vec3) :
    kernelNormalDerivative q p n =
      -dot (radialUnit q p) n / distance q p ^ 2 := by
  by_cases hpq : p = q
  · subst p
    rw [kernelNormalDerivative, normalDerivative,
      gradient_reciprocalKernel_self]
    simp [dot, radialUnit, distance, vecNorm]
  · exact kernelNormalDerivative_formula q p n hpq

private theorem greenPairing_u_kernel_eq_representation
    (u : Vec3 → ℝ) (q p n : Vec3) :
    greenPairing u (reciprocalKernel q) p n =
      representationIntegrand u q p n := by
  unfold greenPairing representationIntegrand
  change
    reciprocalKernel q p * normalDerivative u p n -
        u p * kernelNormalDerivative q p n =
      u p * dot (radialUnit q p) n / distance q p ^ 2 +
        reciprocalKernel q p * normalDerivative u p n
  rw [kernelNormalDerivative_formula_all]
  ring

private theorem outerGreenIntegral_eq_representation
    (S : ParametricSurface) (u : Vec3 → ℝ) (q : Vec3) :
    outerGreenIntegral S u q =
      outerRepresentationIntegral S u q := by
  unfold outerGreenIntegral outerGreenPairing
    outerRepresentationIntegral
  apply intervalIntegral.integral_congr
  intro s _
  apply intervalIntegral.integral_congr
  intro t _
  change
    greenPairing u (reciprocalKernel q) (S.param s t)
          (surfaceUnitNormal S s t) * surfaceJacobian S s t =
      representationIntegrand u q (S.param s t)
          (surfaceUnitNormal S s t) * surfaceJacobian S s t
  rw [greenPairing_u_kernel_eq_representation]

private theorem deriv_slice_x
    {u : Vec3 → ℝ} (hu : Differentiable ℝ u) (p : Vec3) :
    deriv (fun x => u (x, p.2.1, p.2.2)) p.1 =
      fderiv ℝ u p (1, 0, 0) := by
  have hcurve :
      HasDerivAt
        (fun x : ℝ => ((x, p.2.1, p.2.2) : Vec3))
        ((1, 0, 0) : Vec3) p.1 :=
    (hasDerivAt_id p.1).prodMk
      ((hasDerivAt_const p.1 p.2.1).prodMk
        (hasDerivAt_const p.1 p.2.2))
  have hcomp := (hu p).hasFDerivAt.comp_hasDerivAt p.1 hcurve
  simpa [Function.comp_def] using hcomp.deriv

private theorem deriv_slice_y
    {u : Vec3 → ℝ} (hu : Differentiable ℝ u) (p : Vec3) :
    deriv (fun y => u (p.1, y, p.2.2)) p.2.1 =
      fderiv ℝ u p (0, 1, 0) := by
  have hcurve :
      HasDerivAt
        (fun y : ℝ => ((p.1, y, p.2.2) : Vec3))
        ((0, 1, 0) : Vec3) p.2.1 :=
    (hasDerivAt_const p.2.1 p.1).prodMk
      ((hasDerivAt_id p.2.1).prodMk
        (hasDerivAt_const p.2.1 p.2.2))
  have hcomp := (hu p).hasFDerivAt.comp_hasDerivAt p.2.1 hcurve
  simpa [Function.comp_def] using hcomp.deriv

private theorem deriv_slice_z
    {u : Vec3 → ℝ} (hu : Differentiable ℝ u) (p : Vec3) :
    deriv (fun z => u (p.1, p.2.1, z)) p.2.2 =
      fderiv ℝ u p (0, 0, 1) := by
  have hcurve :
      HasDerivAt
        (fun z : ℝ => ((p.1, p.2.1, z) : Vec3))
        ((0, 0, 1) : Vec3) p.2.2 :=
    (hasDerivAt_const p.2.2 p.1).prodMk
      ((hasDerivAt_const p.2.2 p.2.1).prodMk
        (hasDerivAt_id p.2.2))
  have hcomp := (hu p).hasFDerivAt.comp_hasDerivAt p.2.2 hcurve
  simpa [Function.comp_def] using hcomp.deriv

private theorem gradient_eq_fderiv
    {u : Vec3 → ℝ} (hu : Differentiable ℝ u) (p : Vec3) :
    gradient u p =
      (fderiv ℝ u p (1, 0, 0),
        fderiv ℝ u p (0, 1, 0),
        fderiv ℝ u p (0, 0, 1)) := by
  unfold gradient
  rw [deriv_slice_x hu p, deriv_slice_y hu p, deriv_slice_z hu p]

private theorem continuous_gradient
    {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (gradient u) := by
  have hfd : Continuous (fderiv ℝ u) :=
    hu.continuous_fderiv two_ne_zero
  have hx :
      Continuous (fun p => fderiv ℝ u p ((1, 0, 0) : Vec3)) :=
    hfd.clm_apply continuous_const
  have hy :
      Continuous (fun p => fderiv ℝ u p ((0, 1, 0) : Vec3)) :=
    hfd.clm_apply continuous_const
  have hz :
      Continuous (fun p => fderiv ℝ u p ((0, 0, 1) : Vec3)) :=
    hfd.clm_apply continuous_const
  convert hx.prodMk (hy.prodMk hz) using 1
  funext p
  exact gradient_eq_fderiv (hu.differentiable two_ne_zero) p

private theorem contDiff_gradient
    {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u) :
    ContDiff ℝ 1 (gradient u) := by
  have hfd : ContDiff ℝ 1 (fderiv ℝ u) :=
    hu.fderiv_right (by norm_num)
  have hx :
      ContDiff ℝ 1 (fun p => fderiv ℝ u p ((1, 0, 0) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have hy :
      ContDiff ℝ 1 (fun p => fderiv ℝ u p ((0, 1, 0) : Vec3)) :=
    hfd.clm_apply contDiff_const
  have hz :
      ContDiff ℝ 1 (fun p => fderiv ℝ u p ((0, 0, 1) : Vec3)) :=
    hfd.clm_apply contDiff_const
  convert hx.prodMk (hy.prodMk hz) using 1
  funext p
  exact gradient_eq_fderiv (hu.differentiable two_ne_zero) p

private theorem fderiv_apply_eq_dot_gradient
    {u : Vec3 → ℝ} (hu : Differentiable ℝ u)
    (p v : Vec3) :
    fderiv ℝ u p v = dot (gradient u p) v := by
  have hv :
      v =
        v.1 • ((1, 0, 0) : Vec3) +
          v.2.1 • ((0, 1, 0) : Vec3) +
          v.2.2 • ((0, 0, 1) : Vec3) := by
    ext <;> simp
  rw [gradient_eq_fderiv hu p]
  change
    fderiv ℝ u p v =
      fderiv ℝ u p (1, 0, 0) * v.1 +
        fderiv ℝ u p (0, 1, 0) * v.2.1 +
        fderiv ℝ u p (0, 0, 1) * v.2.2
  calc
    fderiv ℝ u p v =
        fderiv ℝ u p
          (v.1 • ((1, 0, 0) : Vec3) +
            v.2.1 • ((0, 1, 0) : Vec3) +
            v.2.2 • ((0, 0, 1) : Vec3)) := by rw [← hv]
    _ = _ := by
      simp only [map_add, map_smul, smul_eq_mul]
      ring

private def sphereUnit (φ θ : ℝ) : Vec3 :=
  (Real.cos φ * Real.cos θ,
    Real.cos φ * Real.sin θ,
    Real.sin φ)

private theorem hasDerivAt_sphereParam_r
    (q : Vec3) (r φ θ : ℝ) :
    HasDerivAt (fun s => sphereParam q s φ θ)
      (sphereUnit φ θ) r := by
  have hx :
      HasDerivAt
        (fun s => q.1 + s * Real.cos φ * Real.cos θ)
        (Real.cos φ * Real.cos θ) r := by
    simpa [id_eq, add_comm, mul_assoc] using
      (((hasDerivAt_id r).mul_const (Real.cos φ)).mul_const (Real.cos θ)
        |>.add_const q.1)
  have hy :
      HasDerivAt
        (fun s => q.2.1 + s * Real.cos φ * Real.sin θ)
        (Real.cos φ * Real.sin θ) r := by
    simpa [id_eq, add_comm, mul_assoc] using
      (((hasDerivAt_id r).mul_const (Real.cos φ)).mul_const (Real.sin θ)
        |>.add_const q.2.1)
  have hz :
      HasDerivAt
        (fun s => q.2.2 + s * Real.sin φ)
        (Real.sin φ) r := by
    simpa [id_eq, add_comm] using
      ((hasDerivAt_id r).mul_const (Real.sin φ) |>.add_const q.2.2)
  simpa [sphereParam, sphereUnit] using hx.prodMk (hy.prodMk hz)

private theorem continuous_laplacian
    {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u) :
    Continuous (laplacian u) := by
  have hg : ContDiff ℝ 1 (gradient u) := contDiff_gradient hu
  let gx : Vec3 → ℝ := fun p => (gradient u p).1
  let gy : Vec3 → ℝ := fun p => (gradient u p).2.1
  let gz : Vec3 → ℝ := fun p => (gradient u p).2.2
  have hgx : ContDiff ℝ 1 gx := hg.fst
  have hgy : ContDiff ℝ 1 gy := hg.snd.fst
  have hgz : ContDiff ℝ 1 gz := hg.snd.snd
  have hx :
      Continuous (fun p => fderiv ℝ gx p ((1, 0, 0) : Vec3)) :=
    (hgx.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hy :
      Continuous (fun p => fderiv ℝ gy p ((0, 1, 0) : Vec3)) :=
    (hgy.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hz :
      Continuous (fun p => fderiv ℝ gz p ((0, 0, 1) : Vec3)) :=
    (hgz.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hsum := (hx.add hy).add hz
  convert hsum using 1
  funext p
  unfold laplacian
  rw [deriv_slice_x (hgx.differentiable one_ne_zero) p,
    deriv_slice_y (hgy.differentiable one_ne_zero) p,
    deriv_slice_z (hgz.differentiable one_ne_zero) p]
  rfl

private theorem measurable_laplacian_reciprocalKernel
    (q : Vec3) :
    Measurable (laplacian (reciprocalKernel q)) := by
  let c := laplacian (reciprocalKernel q) q
  have heq :
      laplacian (reciprocalKernel q) =
        fun p => if p = q then c else 0 := by
    funext p
    split_ifs with hp
    · simpa [c, hp]
    · exact laplacian_reciprocalKernel q p hp
  rw [heq]
  have hmeq : MeasurableSet {p : Vec3 | p = q} := by
    simpa [eq_comm] using measurableSet_singleton q
  exact Measurable.piecewise hmeq measurable_const measurable_const

private theorem measurable_reciprocalKernel
    (q : Vec3) :
    Measurable (reciprocalKernel q) := by
  unfold reciprocalKernel distance vecNorm
  fun_prop

private theorem setIntegral_eq_zero_of_measurable_zero_on
    {s : Set Vec3} {f : Vec3 → ℝ}
    (hf : Measurable f) (hzero : ∀ p ∈ s, f p = 0) :
    (∫ p in s, f p) = 0 := by
  apply integral_eq_zero_of_ae
  change ∀ᵐ p : Vec3 ∂volume.restrict s, f p = 0
  rw [ae_iff]
  have hm : MeasurableSet {p | ¬f p = 0} := by
    simpa only [ne_eq] using (hf (measurableSet_singleton 0)).compl
  rw [Measure.restrict_apply hm]
  have hempty : {p | ¬f p = 0} ∩ s = ∅ := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false]
    intro hp
    exact hp.1 (hzero p hp.2)
  rw [hempty, measure_empty]

private def meanIntegrand
    (u : Vec3 → ℝ) (q : Vec3) (ρ φ θ : ℝ) : ℝ :=
  Real.cos φ * u (sphereParam q ρ φ θ)

private def meanThetaIntegral
    (u : Vec3 → ℝ) (q : Vec3) (ρ φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    meanIntegrand u q ρ φ θ

private def meanAngularIntegral
    (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    meanThetaIntegral u q ρ φ

private theorem continuous_meanThetaIntegral
    {u : Vec3 → ℝ} (q : Vec3) (hu : Continuous u) :
    Continuous
      (fun z : ℝ × ℝ => meanThetaIntegral u q z.1 z.2) := by
  have huncurry :
      Continuous
        (Function.uncurry
          (fun z : ℝ × ℝ => fun θ : ℝ =>
            meanIntegrand u q z.1 z.2 θ)) := by
    have hp :
        Continuous
          (fun a : (ℝ × ℝ) × ℝ =>
            sphereParam q a.1.1 a.1.2 a.2) := by
      unfold sphereParam
      fun_prop
    have hcos :
        Continuous
          (fun a : (ℝ × ℝ) × ℝ => Real.cos a.1.2) := by
      fun_prop
    exact hcos.mul (hu.comp hp)
  have hset :
      Continuous
        (fun z : ℝ × ℝ =>
          ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
            meanIntegrand u q z.1 z.2 θ) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) huncurry
      (isCompact_Icc :
        IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi)))
  unfold meanThetaIntegral
  convert hset using 1
  funext z
  rw [intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← integral_Icc_eq_integral_Ioc]

private theorem continuous_meanAngularIntegral
    {u : Vec3 → ℝ} (q : Vec3) (hu : Continuous u) :
    Continuous (meanAngularIntegral u q) := by
  have htheta := continuous_meanThetaIntegral q hu
  have huncurry :
      Continuous
        (Function.uncurry
          (fun ρ : ℝ => fun φ : ℝ =>
            meanThetaIntegral u q ρ φ)) := by
    simpa [Function.uncurry] using htheta
  have hset :
      Continuous
        (fun ρ : ℝ =>
          ∫ φ in Set.Icc (-Real.pi / 2) (Real.pi / 2),
            meanThetaIntegral u q ρ φ) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) huncurry
      (isCompact_Icc :
        IsCompact (Set.Icc (-Real.pi / 2) (Real.pi / 2)))
  unfold meanAngularIntegral
  change Continuous
    (fun ρ =>
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        meanThetaIntegral u q ρ φ)
  convert hset using 1
  funext ρ
  rw [intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] :
        -Real.pi / 2 ≤ Real.pi / 2),
    ← integral_Icc_eq_integral_Ioc]

private theorem meanAngularIntegral_zero
    (u : Vec3 → ℝ) (q : Vec3) :
    meanAngularIntegral u q 0 = 4 * Real.pi * u q := by
  unfold meanAngularIntegral meanThetaIntegral meanIntegrand
  simp only [sphereParam, zero_mul, add_zero]
  simp_rw [intervalIntegral.integral_const]
  rw [show
      (fun φ : ℝ =>
        (2 * Real.pi - 0) • (Real.cos φ * u q)) =
        fun φ : ℝ => (2 * Real.pi * u q) * Real.cos φ by
      funext φ
      simp only [smul_eq_mul]
      ring]
  rw [intervalIntegral.integral_const_mul, integral_cos]
  rw [Real.sin_pi_div_two]
  have hneg : -Real.pi / 2 = -(Real.pi / 2) := by ring
  rw [hneg, Real.sin_neg, Real.sin_pi_div_two]
  ring

private theorem smallSphereMean_eq_meanAngularIntegral
    (u : Vec3 → ℝ) (q : Vec3) {ρ : ℝ} (hρ : ρ ≠ 0) :
    smallSphereMean q u ρ =
      1 / (4 * Real.pi) * meanAngularIntegral u q ρ := by
  have hinner :
      ∀ φ : ℝ,
        (∫ θ in (0 : ℝ)..2 * Real.pi,
          ρ ^ 2 * Real.cos φ * u (sphereParam q ρ φ θ)) =
        ρ ^ 2 * meanThetaIntegral u q ρ φ := by
    intro φ
    unfold meanThetaIntegral meanIntegrand
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    ring
  unfold smallSphereMean smallSphereIntegral meanAngularIntegral
  simp_rw [hinner]
  rw [intervalIntegral.integral_const_mul]
  field_simp [hρ]

private theorem distance_sphereParam
    (q : Vec3) {ρ : ℝ} (hρ : 0 ≤ ρ) (φ θ : ℝ) :
    distance q (sphereParam q ρ φ θ) = ρ := by
  unfold distance vecNorm sphereParam
  rw [show
      (q.1 + ρ * Real.cos φ * Real.cos θ - q.1) ^ 2 +
          (q.2.1 + ρ * Real.cos φ * Real.sin θ - q.2.1) ^ 2 +
          (q.2.2 + ρ * Real.sin φ - q.2.2) ^ 2 =
        ρ ^ 2 by
      calc
        _ = ρ ^ 2 *
            (Real.cos φ ^ 2 *
                (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
              Real.sin φ ^ 2) := by ring
        _ = ρ ^ 2 := by
          rw [Real.cos_sq_add_sin_sq θ]
          simp only [mul_one]
          rw [Real.cos_sq_add_sin_sq φ]
          ring]
  exact Real.sqrt_sq hρ

private theorem dot_sphereUnit_self (φ θ : ℝ) :
    dot (sphereUnit φ θ) (sphereUnit φ θ) = 1 := by
  unfold dot sphereUnit
  calc
    (Real.cos φ * Real.cos θ) * (Real.cos φ * Real.cos θ) +
        (Real.cos φ * Real.sin θ) * (Real.cos φ * Real.sin θ) +
        Real.sin φ * Real.sin φ =
      Real.cos φ ^ 2 *
          (Real.cos θ ^ 2 + Real.sin θ ^ 2) +
        Real.sin φ ^ 2 := by ring
    _ = 1 := by
      rw [Real.cos_sq_add_sin_sq θ]
      simp only [mul_one]
      exact Real.cos_sq_add_sin_sq φ

private theorem radialUnit_sphereParam
    (q : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (φ θ : ℝ) :
    radialUnit q (sphereParam q ρ φ θ) = sphereUnit φ θ := by
  unfold radialUnit sphereUnit
  rw [distance_sphereParam q hρ.le φ θ]
  simp only [sphereParam]
  apply Prod.ext
  · field_simp [hρ.ne']
    ring
  · apply Prod.ext
    · field_simp [hρ.ne']
      ring
    · field_simp [hρ.ne']
      ring

private theorem puncturedOutwardNormal_sphereParam
    (q : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (φ θ : ℝ) :
    puncturedOutwardNormal q (sphereParam q ρ φ θ) =
      (-(sphereUnit φ θ).1,
        -(sphereUnit φ θ).2.1,
        -(sphereUnit φ θ).2.2) := by
  unfold puncturedOutwardNormal
  rw [radialUnit_sphereParam q hρ φ θ]

private theorem reciprocalKernel_sphereParam
    (q : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (φ θ : ℝ) :
    reciprocalKernel q (sphereParam q ρ φ θ) = 1 / ρ := by
  unfold reciprocalKernel
  rw [distance_sphereParam q hρ.le φ θ]

private theorem normalDerivative_u_punctured_sphere
    (u : Vec3 → ℝ) (q : Vec3)
    {ρ : ℝ} (hρ : 0 < ρ) (φ θ : ℝ) :
    normalDerivative u (sphereParam q ρ φ θ)
        (puncturedOutwardNormal q (sphereParam q ρ φ θ)) =
      -dot (gradient u (sphereParam q ρ φ θ)) (sphereUnit φ θ) := by
  rw [puncturedOutwardNormal_sphereParam q hρ φ θ]
  unfold normalDerivative dot
  ring

private theorem kernelNormalDerivative_punctured_sphere
    (q : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (φ θ : ℝ) :
    kernelNormalDerivative q (sphereParam q ρ φ θ)
        (puncturedOutwardNormal q (sphereParam q ρ φ θ)) =
      1 / ρ ^ 2 := by
  have hpq : sphereParam q ρ φ θ ≠ q := by
    intro hpq
    have hd := distance_sphereParam q hρ.le φ θ
    rw [hpq] at hd
    have hzero : distance q q = 0 := by
      simp [distance, vecNorm]
    linarith
  rw [kernelNormalDerivative_formula q (sphereParam q ρ φ θ)
      (puncturedOutwardNormal q (sphereParam q ρ φ θ)) hpq,
    radialUnit_sphereParam q hρ φ θ,
    puncturedOutwardNormal_sphereParam q hρ φ θ,
    distance_sphereParam q hρ.le φ θ]
  unfold dot
  have hunit := dot_sphereUnit_self φ θ
  unfold dot at hunit
  rw [show
      (sphereUnit φ θ).1 * -(sphereUnit φ θ).1 +
          (sphereUnit φ θ).2.1 * -(sphereUnit φ θ).2.1 +
          (sphereUnit φ θ).2.2 * -(sphereUnit φ θ).2.2 =
        -1 by linarith]
  ring

private def cleanInnerIntegrand
    (u : Vec3 → ℝ) (q : Vec3) (ρ φ θ : ℝ) : ℝ :=
  -Real.cos φ *
    (u (sphereParam q ρ φ θ) +
      ρ * dot (gradient u (sphereParam q ρ φ θ))
        (sphereUnit φ θ))

private def cleanInnerIntegral
    (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      cleanInnerIntegrand u q ρ φ θ

private theorem weighted_greenPairing_sphere
    (u : Vec3 → ℝ) (q : Vec3)
    {ρ : ℝ} (hρ : 0 < ρ) (φ θ : ℝ) :
    ρ ^ 2 * Real.cos φ *
        greenPairing u (reciprocalKernel q)
          (sphereParam q ρ φ θ)
          (puncturedOutwardNormal q (sphereParam q ρ φ θ)) =
      cleanInnerIntegrand u q ρ φ θ := by
  unfold greenPairing cleanInnerIntegrand
  change
    ρ ^ 2 * Real.cos φ *
        (reciprocalKernel q (sphereParam q ρ φ θ) *
            normalDerivative u (sphereParam q ρ φ θ)
              (puncturedOutwardNormal q (sphereParam q ρ φ θ)) -
          u (sphereParam q ρ φ θ) *
            kernelNormalDerivative q (sphereParam q ρ φ θ)
              (puncturedOutwardNormal q (sphereParam q ρ φ θ))) =
      -Real.cos φ *
        (u (sphereParam q ρ φ θ) +
          ρ * dot (gradient u (sphereParam q ρ φ θ))
            (sphereUnit φ θ))
  rw [reciprocalKernel_sphereParam q hρ φ θ,
    normalDerivative_u_punctured_sphere u q hρ φ θ,
    kernelNormalDerivative_punctured_sphere q hρ φ θ]
  field_simp [hρ.ne']
  ring

private theorem smallGreenPairing_eq_clean
    (u : Vec3 → ℝ) (q : Vec3) {ρ : ℝ} (hρ : 0 < ρ) :
    smallGreenPairing q ρ u (reciprocalKernel q) =
      cleanInnerIntegral u q ρ := by
  unfold smallGreenPairing smallSphereIntegral cleanInnerIntegral
  apply intervalIntegral.integral_congr
  intro φ _
  apply intervalIntegral.integral_congr
  intro θ _
  exact weighted_greenPairing_sphere u q hρ φ θ

private def cleanThetaIntegral
    (u : Vec3 → ℝ) (q : Vec3) (ρ φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..2 * Real.pi,
    cleanInnerIntegrand u q ρ φ θ

private theorem continuous_cleanThetaIntegral
    {u : Vec3 → ℝ} (q : Vec3) (hu : ContDiff ℝ 2 u) :
    Continuous
      (fun z : ℝ × ℝ => cleanThetaIntegral u q z.1 z.2) := by
  have hgu : Continuous (gradient u) := continuous_gradient hu
  have huncurry :
      Continuous
        (Function.uncurry
          (fun z : ℝ × ℝ => fun θ : ℝ =>
            cleanInnerIntegrand u q z.1 z.2 θ)) := by
    have hp :
        Continuous
          (fun a : (ℝ × ℝ) × ℝ =>
            sphereParam q a.1.1 a.1.2 a.2) := by
      unfold sphereParam
      fun_prop
    have hsunit :
        Continuous
          (fun a : (ℝ × ℝ) × ℝ =>
            sphereUnit a.1.2 a.2) := by
      unfold sphereUnit
      fun_prop
    have hucomp := hu.continuous.comp hp
    have hgcomp := hgu.comp hp
    have hdot :
        Continuous
          (fun a : (ℝ × ℝ) × ℝ =>
            dot (gradient u (sphereParam q a.1.1 a.1.2 a.2))
              (sphereUnit a.1.2 a.2)) := by
      unfold dot
      exact
        ((hgcomp.fst.mul hsunit.fst).add
          (hgcomp.snd.fst.mul hsunit.snd.fst)).add
            (hgcomp.snd.snd.mul hsunit.snd.snd)
    have hcos :
        Continuous
          (fun a : (ℝ × ℝ) × ℝ => Real.cos a.1.2) := by
      fun_prop
    have hrho :
        Continuous (fun a : (ℝ × ℝ) × ℝ => a.1.1) :=
      continuous_fst.comp continuous_fst
    have hc := hcos.neg.mul (hucomp.add (hrho.mul hdot))
    convert hc using 1
  have hset :
      Continuous
        (fun z : ℝ × ℝ =>
          ∫ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
            cleanInnerIntegrand u q z.1 z.2 θ) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) huncurry
      (isCompact_Icc :
        IsCompact (Set.Icc (0 : ℝ) (2 * Real.pi)))
  unfold cleanThetaIntegral
  convert hset using 1
  funext z
  rw [intervalIntegral.integral_of_le
      (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← integral_Icc_eq_integral_Ioc]

private theorem continuous_cleanInnerIntegral
    {u : Vec3 → ℝ} (q : Vec3) (hu : ContDiff ℝ 2 u) :
    Continuous (cleanInnerIntegral u q) := by
  have htheta := continuous_cleanThetaIntegral q hu
  have huncurry :
      Continuous
        (Function.uncurry
          (fun ρ : ℝ => fun φ : ℝ =>
            cleanThetaIntegral u q ρ φ)) := by
    simpa [Function.uncurry] using htheta
  have hset :
      Continuous
        (fun ρ : ℝ =>
          ∫ φ in Set.Icc (-Real.pi / 2) (Real.pi / 2),
            cleanThetaIntegral u q ρ φ) :=
    continuous_parametric_integral_of_continuous
      (μ := volume) huncurry
      (isCompact_Icc :
        IsCompact (Set.Icc (-Real.pi / 2) (Real.pi / 2)))
  unfold cleanInnerIntegral
  change Continuous
    (fun ρ =>
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        cleanThetaIntegral u q ρ φ)
  convert hset using 1
  funext ρ
  rw [intervalIntegral.integral_of_le
      (by linarith [Real.pi_pos] :
        -Real.pi / 2 ≤ Real.pi / 2),
    ← integral_Icc_eq_integral_Ioc]

private theorem cleanInnerIntegral_zero
    (u : Vec3 → ℝ) (q : Vec3) :
    cleanInnerIntegral u q 0 = -(4 * Real.pi * u q) := by
  unfold cleanInnerIntegral cleanInnerIntegrand
  simp only [zero_mul, sphereParam, add_zero]
  simp_rw [intervalIntegral.integral_const]
  rw [show
      (fun φ : ℝ =>
        (2 * Real.pi - 0) • (-Real.cos φ * u q)) =
        fun φ : ℝ => (-2 * Real.pi * u q) * Real.cos φ by
      funext φ
      simp only [smul_eq_mul]
      ring]
  rw [intervalIntegral.integral_const_mul, integral_cos]
  rw [Real.sin_pi_div_two]
  have hneg : -Real.pi / 2 = -(Real.pi / 2) := by ring
  rw [hneg, Real.sin_neg, Real.sin_pi_div_two]
  ring

private theorem smallSphereIntegral_const_mul
    (q : Vec3) (r c : ℝ) (g : Vec3 → ℝ) :
    smallSphereIntegral q r (fun p => c * g p) =
      c * smallSphereIntegral q r g := by
  unfold smallSphereIntegral
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          r ^ 2 * Real.cos φ * (c * g (sphereParam q r φ θ))) =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        c * ∫ θ in (0 : ℝ)..2 * Real.pi,
          r ^ 2 * Real.cos φ * g (sphereParam q r φ θ) := by
        apply intervalIntegral.integral_congr
        intro φ _
        change
          (∫ θ in (0 : ℝ)..2 * Real.pi,
              r ^ 2 * Real.cos φ * (c * g (sphereParam q r φ θ))) =
            c * ∫ θ in (0 : ℝ)..2 * Real.pi,
              r ^ 2 * Real.cos φ * g (sphereParam q r φ θ)
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro θ _
        ring
    _ = c * ∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          r ^ 2 * Real.cos φ * g (sphereParam q r φ θ) :=
      by rw [intervalIntegral.integral_const_mul]

private theorem intervalIntegral_swap_of_continuous
    (f : ℝ → ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hf : Continuous (Function.uncurry f)) :
    (∫ x in a..b, ∫ y in c..d, f x y) =
      ∫ y in c..d, ∫ x in a..b, f x y := by
  simp only [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  have hiIcc :
      IntegrableOn (Function.uncurry f)
        (Set.Icc a b ×ˢ Set.Icc c d) (volume.prod volume) :=
    hf.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  have hiIoc :
      IntegrableOn (Function.uncurry f)
        (Set.Ioc a b ×ˢ Set.Ioc c d) (volume.prod volume) :=
    hiIcc.mono_set
      (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)
  have hi :
      Integrable (Function.uncurry f)
        ((volume.restrict (Set.Ioc a b)).prod
          (volume.restrict (Set.Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hiIoc
  exact integral_integral_swap hi

private def radialDerivativeIntegrand
    (u : Vec3 → ℝ) (q : Vec3) (r φ θ : ℝ) : ℝ :=
  Real.cos φ *
    dot (gradient u (sphereParam q r φ θ)) (sphereUnit φ θ)

private def radialAngularIntegral
    (u : Vec3 → ℝ) (q : Vec3) (r : ℝ) : ℝ :=
  ∫ φ in -Real.pi / 2..Real.pi / 2,
    ∫ θ in (0 : ℝ)..2 * Real.pi,
      radialDerivativeIntegrand u q r φ θ

private theorem continuous_radialDerivativeIntegrand
    {u : Vec3 → ℝ} (q : Vec3) (hu : ContDiff ℝ 2 u) :
    Continuous
      (fun z : (ℝ × ℝ) × ℝ =>
        radialDerivativeIntegrand u q z.1.1 z.1.2 z.2) := by
  have hp :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ =>
          sphereParam q z.1.1 z.1.2 z.2) := by
    unfold sphereParam
    fun_prop
  have hg := (continuous_gradient hu).comp hp
  have he :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ => sphereUnit z.1.2 z.2) := by
    unfold sphereUnit
    fun_prop
  have hdot :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ =>
          dot (gradient u (sphereParam q z.1.1 z.1.2 z.2))
            (sphereUnit z.1.2 z.2)) := by
    unfold dot
    exact
      ((hg.fst.mul he.fst).add
        (hg.snd.fst.mul he.snd.fst)).add
          (hg.snd.snd.mul he.snd.snd)
  have hcos :
      Continuous
        (fun z : (ℝ × ℝ) × ℝ => Real.cos z.1.2) := by
    fun_prop
  exact hcos.mul hdot

private theorem hasDerivAt_u_sphereParam_r
    {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u)
    (q : Vec3) (r φ θ : ℝ) :
    HasDerivAt (fun s => u (sphereParam q s φ θ))
      (dot (gradient u (sphereParam q r φ θ))
        (sphereUnit φ θ)) r := by
  have h :=
    (hu.differentiable two_ne_zero (sphereParam q r φ θ)).hasFDerivAt
      |>.comp_hasDerivAt r (hasDerivAt_sphereParam_r q r φ θ)
  simpa [Function.comp_def,
    fderiv_apply_eq_dot_gradient (hu.differentiable two_ne_zero)
      (sphereParam q r φ θ) (sphereUnit φ θ)] using h

private theorem radial_ftc
    {u : Vec3 → ℝ} (hu : ContDiff ℝ 2 u)
    (q : Vec3) {ρ : ℝ} (hρ : 0 ≤ ρ) (φ θ : ℝ) :
    (∫ r in (0 : ℝ)..ρ,
        radialDerivativeIntegrand u q r φ θ) =
      Real.cos φ *
        (u (sphereParam q ρ φ θ) - u q) := by
  have hdot :
      Continuous
        (fun r =>
          dot (gradient u (sphereParam q r φ θ))
            (sphereUnit φ θ)) := by
    have hp :
        Continuous (fun r => sphereParam q r φ θ) := by
      unfold sphereParam
      fun_prop
    have hg := (continuous_gradient hu).comp hp
    unfold dot
    exact
      ((hg.fst.mul continuous_const).add
        (hg.snd.fst.mul continuous_const)).add
          (hg.snd.snd.mul continuous_const)
  have hbase :
      (∫ r in (0 : ℝ)..ρ,
          dot (gradient u (sphereParam q r φ θ))
            (sphereUnit φ θ)) =
        u (sphereParam q ρ φ θ) - u q := by
    have h :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt
        (a := (0 : ℝ)) (b := ρ)
        (f := fun r => u (sphereParam q r φ θ))
        (f' := fun r =>
          dot (gradient u (sphereParam q r φ θ))
            (sphereUnit φ θ))
        (fun r _ => hasDerivAt_u_sphereParam_r hu q r φ θ)
        (hdot.intervalIntegrable 0 ρ)
    simpa [sphereParam] using h
  unfold radialDerivativeIntegrand
  rw [intervalIntegral.integral_const_mul, hbase]

private theorem smallSphereFlux_eq_radialAngular
    (u : Vec3 → ℝ) (q : Vec3) {r : ℝ} (hr : 0 < r) :
    smallSphereIntegral q r
        (fun p => normalDerivative u p (puncturedOutwardNormal q p)) =
      -(r ^ 2 * radialAngularIntegral u q r) := by
  unfold smallSphereIntegral radialAngularIntegral
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          r ^ 2 * Real.cos φ *
            normalDerivative u (sphereParam q r φ θ)
              (puncturedOutwardNormal q (sphereParam q r φ θ))) =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        (-r ^ 2) * ∫ θ in (0 : ℝ)..2 * Real.pi,
          radialDerivativeIntegrand u q r φ θ := by
        apply intervalIntegral.integral_congr
        intro φ _
        change
          (∫ θ in (0 : ℝ)..2 * Real.pi,
              r ^ 2 * Real.cos φ *
                normalDerivative u (sphereParam q r φ θ)
                  (puncturedOutwardNormal q (sphereParam q r φ θ))) =
            (-r ^ 2) * ∫ θ in (0 : ℝ)..2 * Real.pi,
              radialDerivativeIntegrand u q r φ θ
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro θ _
        change
          r ^ 2 * Real.cos φ *
              normalDerivative u (sphereParam q r φ θ)
                (puncturedOutwardNormal q (sphereParam q r φ θ)) =
            -r ^ 2 * radialDerivativeIntegrand u q r φ θ
        rw [normalDerivative_u_punctured_sphere u q hr φ θ]
        unfold radialDerivativeIntegrand
        ring
    _ = (-r ^ 2) *
        (∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            radialDerivativeIntegrand u q r φ θ) := by
      rw [intervalIntegral.integral_const_mul]
    _ = -(r ^ 2 *
        (∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            radialDerivativeIntegrand u q r φ θ)) := by ring

private theorem radial_triple_swap
    {u : Vec3 → ℝ} (q : Vec3) (hu : ContDiff ℝ 2 u)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..ρ,
          radialDerivativeIntegrand u q r φ θ) =
      ∫ r in (0 : ℝ)..ρ,
        radialAngularIntegral u q r := by
  have hF := continuous_radialDerivativeIntegrand q hu
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..ρ,
          radialDerivativeIntegrand u q r φ θ) =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ r in (0 : ℝ)..ρ,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            radialDerivativeIntegrand u q r φ θ := by
        apply intervalIntegral.integral_congr
        intro φ _
        apply intervalIntegral_swap_of_continuous
          (fun θ r => radialDerivativeIntegrand u q r φ θ)
          0 (2 * Real.pi) 0 ρ (by positivity) hρ
        have hm :
            Continuous
              (fun z : ℝ × ℝ => ((z.2, φ), z.1)) := by
          fun_prop
        exact hF.comp hm
    _ = ∫ r in (0 : ℝ)..ρ,
        ∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            radialDerivativeIntegrand u q r φ θ := by
      apply intervalIntegral_swap_of_continuous
        (fun φ r =>
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            radialDerivativeIntegrand u q r φ θ)
        (-Real.pi / 2) (Real.pi / 2) 0 ρ
        (by linarith [Real.pi_pos]) hρ
      have hm :
          Continuous
            (fun z : (ℝ × ℝ) × ℝ =>
              ((z.1.2, z.1.1), z.2)) := by
        fun_prop
      have hp :
          Continuous
            (Function.uncurry
              (fun z : ℝ × ℝ => fun θ =>
                radialDerivativeIntegrand u q z.2 z.1 θ)) :=
        hF.comp hm
      exact
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (μ := volume) hp) 0 (2 * Real.pi)
    _ = ∫ r in (0 : ℝ)..ρ,
        radialAngularIntegral u q r := by
      rfl

private theorem radial_triple_eq_mean_sub
    {u : Vec3 → ℝ} (q : Vec3) (hu : ContDiff ℝ 2 u)
    {ρ : ℝ} (hρ : 0 ≤ ρ) :
    (∫ φ in -Real.pi / 2..Real.pi / 2,
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..ρ,
          radialDerivativeIntegrand u q r φ θ) =
      meanAngularIntegral u q ρ - meanAngularIntegral u q 0 := by
  have hmean :
      ∀ r φ : ℝ,
        Continuous (fun θ => meanIntegrand u q r φ θ) := by
    intro r φ
    have hp : Continuous (fun θ => sphereParam q r φ θ) := by
      unfold sphereParam
      fun_prop
    exact continuous_const.mul (hu.continuous.comp hp)
  have htheta :
      Continuous
        (fun z : ℝ × ℝ => meanThetaIntegral u q z.1 z.2) :=
    continuous_meanThetaIntegral q hu.continuous
  have hmρ : Continuous (fun φ : ℝ => (ρ, φ)) :=
    continuous_const.prodMk continuous_id
  have houtρ : Continuous (fun φ => meanThetaIntegral u q ρ φ) :=
    htheta.comp hmρ
  have heq0 :
      (fun φ => meanThetaIntegral u q 0 φ) =
        fun φ => (2 * Real.pi) * (Real.cos φ * u q) := by
    funext φ
    unfold meanThetaIntegral meanIntegrand
    simp [sphereParam, intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hout0 : Continuous (fun φ => meanThetaIntegral u q 0 φ) := by
    rw [heq0]
    fun_prop
  calc
    (∫ φ in -Real.pi / 2..Real.pi / 2,
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ r in (0 : ℝ)..ρ,
          radialDerivativeIntegrand u q r φ θ) =
      ∫ φ in -Real.pi / 2..Real.pi / 2,
        ∫ θ in (0 : ℝ)..2 * Real.pi,
          (meanIntegrand u q ρ φ θ -
            meanIntegrand u q 0 φ θ) := by
        apply intervalIntegral.integral_congr
        intro φ _
        apply intervalIntegral.integral_congr
        intro θ _
        change
          (∫ r in (0 : ℝ)..ρ,
              radialDerivativeIntegrand u q r φ θ) =
            meanIntegrand u q ρ φ θ -
              meanIntegrand u q 0 φ θ
        rw [radial_ftc hu q hρ φ θ]
        unfold meanIntegrand
        simp [sphereParam]
        ring
    _ = ∫ φ in -Real.pi / 2..Real.pi / 2,
        (meanThetaIntegral u q ρ φ -
          meanThetaIntegral u q 0 φ) := by
      apply intervalIntegral.integral_congr
      intro φ _
      change
        (∫ θ in (0 : ℝ)..2 * Real.pi,
            meanIntegrand u q ρ φ θ -
              meanIntegrand u q 0 φ θ) =
          meanThetaIntegral u q ρ φ -
            meanThetaIntegral u q 0 φ
      unfold meanThetaIntegral
      exact intervalIntegral.integral_sub
        ((hmean ρ φ).intervalIntegrable 0 (2 * Real.pi))
        ((hmean 0 φ).intervalIntegrable 0 (2 * Real.pi))
    _ = meanAngularIntegral u q ρ -
        meanAngularIntegral u q 0 := by
      unfold meanAngularIntegral
      exact intervalIntegral.integral_sub
        (houtρ.intervalIntegrable _ _)
        (hout0.intervalIntegrable _ _)

private theorem smallSphereIntegral_div_sq
    (u : Vec3 → ℝ) (q : Vec3) {r : ℝ} (hr : r ≠ 0) :
    smallSphereIntegral q r (fun p => u p / r ^ 2) =
      meanAngularIntegral u q r := by
  unfold smallSphereIntegral meanAngularIntegral
    meanThetaIntegral meanIntegrand
  apply intervalIntegral.integral_congr
  intro φ _
  apply intervalIntegral.integral_congr
  intro θ _
  field_simp [hr]

theorem gap1 (q p : Vec3) (hpq : p ≠ q) :
    kernelLaplacian q p = 0 := by
  exact laplacian_reciprocalKernel q p hpq

theorem gap2 (S : ParametricSurface) (V : Set Vec3)
    (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (hball : closedBall q ρ ⊆ V)
    (hu : IsC2 u) (hharm : HarmonicOn u V)
    (hGreen : SatisfiesSecondGreenIdentity S V q) :
    outerGreenIntegral S u q +
        smallGreenPairing q ρ u (reciprocalKernel q) = 0 := by
  have hku : SmoothAwayFrom q (reciprocalKernel q) :=
    reciprocalKernel_smoothAway q
  have huu : SmoothAwayFrom q u := by
    unfold SmoothAwayFrom
    exact hu.contDiffOn
  have hidentity :=
    hGreen u (reciprocalKernel q) huu hku ρ hρ hball
  have hmeas :
      Measurable
        (fun p =>
          reciprocalKernel q p * laplacian u p -
            u p * laplacian (reciprocalKernel q) p) :=
    ((measurable_reciprocalKernel q).mul
      (continuous_laplacian hu).measurable).sub
      (hu.continuous.measurable.mul
        (measurable_laplacian_reciprocalKernel q))
  have hvolume :
      (∫ p in puncturedDomain V q ρ,
          reciprocalKernel q p * laplacian u p -
            u p * laplacian (reciprocalKernel q) p) = 0 := by
    apply setIntegral_eq_zero_of_measurable_zero_on hmeas
    intro p hp
    have hpq : p ≠ q := by
      intro hpq
      subst p
      apply hp.2
      unfold closedBall
      simp [distance, vecNorm, hρ.le]
    rw [laplacian_reciprocalKernel q p hpq, hharm p hp.1]
    ring
  simpa [outerGreenIntegral, hvolume] using hidentity

theorem gap3 (outerTerm innerTerm : ℝ)
    (hCombined : outerTerm + innerTerm = 0) :
    innerTerm = -outerTerm := by
  linarith

theorem gap4 (q p : Vec3) (ρ : ℝ) (hρ : 0 < ρ)
    (hp : distance q p = ρ) :
    kernelNormalDerivative q p (puncturedOutwardNormal q p) =
      1 / ρ ^ 2 := by
  have hpq : p ≠ q := by
    intro hpq
    subst p
    have hzero : distance q q = 0 := by
      simp [distance, vecNorm]
    linarith
  rw [kernelNormalDerivative_formula q p
    (puncturedOutwardNormal q p) hpq]
  have hsq :
      (p.1 - q.1) ^ 2 + (p.2.1 - q.2.1) ^ 2 +
          (p.2.2 - q.2.2) ^ 2 = ρ ^ 2 := by
    have hd := distance_sq q p
    rw [hp] at hd
    simpa [distanceSq] using hd.symm
  simp only [dot, puncturedOutwardNormal, radialUnit]
  rw [hp]
  field_simp [hρ.ne']
  nlinarith

theorem gap5 (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (hu : IsC2 u)
    (hharm : HarmonicOn u (closedBall q ρ))
    (hdiv : SatisfiesBallDivergenceTheorem) :
    smallSphereIntegral q ρ
        (fun p => 1 / ρ *
          normalDerivative u p (puncturedOutwardNormal q p)) = 0 := by
  have hvolume :
      (∫ p in closedBall q ρ, laplacian u p) = 0 := by
    apply setIntegral_eq_zero_of_measurable_zero_on
      (continuous_laplacian hu).measurable
    exact hharm
  rw [smallSphereIntegral_const_mul]
  rw [hdiv u q ρ hu hρ, hvolume]
  ring

theorem gap6 (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (hu : IsC2 u)
    (hharm : HarmonicOn u (closedBall q ρ))
    (hdiv : SatisfiesBallDivergenceTheorem) :
    smallSphereIntegral q ρ (fun p => u p / ρ ^ 2) =
      4 * Real.pi * u q := by
  have hradial_zero :
      ∀ r : ℝ, 0 < r → r ≤ ρ →
        radialAngularIntegral u q r = 0 := by
    intro r hr hrρ
    have hvolume :
        (∫ p in closedBall q r, laplacian u p) = 0 := by
      apply setIntegral_eq_zero_of_measurable_zero_on
        (continuous_laplacian hu).measurable
      intro p hp
      apply hharm p
      unfold closedBall at hp ⊢
      exact hp.trans hrρ
    have hflux := hdiv u q r hu hr
    rw [hvolume] at hflux
    have hrelation := smallSphereFlux_eq_radialAngular u q hr
    rw [hrelation] at hflux
    have hrsq : 0 < r ^ 2 := sq_pos_of_pos hr
    nlinarith
  have hradial_integral :
      (∫ r in (0 : ℝ)..ρ, radialAngularIntegral u q r) = 0 := by
    calc
      (∫ r in (0 : ℝ)..ρ, radialAngularIntegral u q r) =
          ∫ r in (0 : ℝ)..ρ, (0 : ℝ) := by
        apply intervalIntegral.integral_congr_ae
        refine Filter.Eventually.of_forall ?_
        intro r hrange
        rw [Set.uIoc_of_le hρ.le] at hrange
        exact hradial_zero r hrange.1 hrange.2
      _ = 0 := intervalIntegral.integral_zero
  have hmeanSub :
      meanAngularIntegral u q ρ -
          meanAngularIntegral u q 0 = 0 := by
    calc
      meanAngularIntegral u q ρ -
          meanAngularIntegral u q 0 =
        (∫ φ in -Real.pi / 2..Real.pi / 2,
          ∫ θ in (0 : ℝ)..2 * Real.pi,
            ∫ r in (0 : ℝ)..ρ,
              radialDerivativeIntegrand u q r φ θ) :=
          (radial_triple_eq_mean_sub q hu hρ.le).symm
      _ = ∫ r in (0 : ℝ)..ρ,
          radialAngularIntegral u q r :=
        radial_triple_swap q hu hρ.le
      _ = 0 := hradial_integral
  have hmean :
      meanAngularIntegral u q ρ = 4 * Real.pi * u q := by
    rw [meanAngularIntegral_zero] at hmeanSub
    linarith
  rw [smallSphereIntegral_div_sq u q hρ.ne', hmean]

theorem gap7 (S : ParametricSurface) (V : Set Vec3)
    (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (hball : closedBall q ρ ⊆ V)
    (hu : IsC2 u) (hharm : HarmonicOn u V)
    (hregular : SurfaceRegular S)
    (hGreen : SatisfiesSecondGreenIdentity S V q) :
    u q = 1 / (4 * Real.pi) * outerGreenIntegral S u q := by
  clear hregular
  let R := outerGreenIntegral S u q
  have hpos :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < r :=
    self_mem_nhdsWithin
  have hlt :
      ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r < ρ :=
    Eventually.filter_mono inf_le_left (Iio_mem_nhds hρ)
  have heq :
      cleanInnerIntegral u q =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun _ => -R) := by
    filter_upwards [hpos, hlt] with r hr hrr
    have hsub : closedBall q r ⊆ V := by
      intro p hp
      exact hball (hp.trans hrr.le)
    have hrel :=
      gap2 S V u q r hr hsub hu hharm hGreen
    rw [smallGreenPairing_eq_clean u q hr] at hrel
    dsimp [R]
    linarith
  have htend :
      Tendsto (cleanInnerIntegral u q)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (cleanInnerIntegral u q 0)) :=
    (continuous_cleanInnerIntegral q hu).continuousAt.mono_left
      inf_le_left
  have hconst :
      Tendsto (fun _ : ℝ => -R)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (cleanInnerIntegral u q 0)) :=
    Tendsto.congr' heq htend
  have hlimit : cleanInnerIntegral u q 0 = -R :=
    tendsto_nhds_unique hconst tendsto_const_nhds
  rw [cleanInnerIntegral_zero] at hlimit
  have hR : R = 4 * Real.pi * u q := by
    linarith
  change u q = 1 / (4 * Real.pi) * R
  rw [hR]
  field_simp [Real.pi_ne_zero]

theorem gap8 (u : Vec3 → ℝ) (q : Vec3)
    (hcont : Continuous u) :
    Tendsto (fun ρ => smallSphereMean q u ρ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (u q)) := by
  have hmean :
      Tendsto
        (fun ρ => 1 / (4 * Real.pi) * meanAngularIntegral u q ρ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (u q)) := by
    have hcontMean :
        Tendsto (meanAngularIntegral u q)
          (nhdsWithin 0 (Set.Ioi 0))
          (nhds (meanAngularIntegral u q 0)) :=
      (continuous_meanAngularIntegral q hcont).continuousAt.mono_left
        inf_le_left
    convert (tendsto_const_nhds.mul hcontMean) using 1
    rw [meanAngularIntegral_zero]
    field_simp [Real.pi_ne_zero]
  apply Tendsto.congr' _ hmean
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  exact (smallSphereMean_eq_meanAngularIntegral u q hρ.ne').symm

theorem gap9 (q p n : Vec3) (hpq : p ≠ q) :
    kernelNormalDerivative q p n =
      -dot (radialUnit q p) n / distance q p ^ 2 := by
  exact kernelNormalDerivative_formula q p n hpq

theorem gap10 (S : ParametricSurface) (V : Set Vec3)
    (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (hball : closedBall q ρ ⊆ V)
    (hu : IsC2 u) (hharm : HarmonicOn u V)
    (hregular : SurfaceRegular S)
    (hGreen : SatisfiesSecondGreenIdentity S V q) :
    u q =
      1 / (4 * Real.pi) * outerRepresentationIntegral S u q := by
  rw [← outerGreenIntegral_eq_representation]
  exact gap7 S V u q ρ hρ hball hu hharm hregular hGreen

theorem gap11 (S : ParametricSurface) (V : Set Vec3)
    (u : Vec3 → ℝ) (q : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (hball : closedBall q ρ ⊆ V)
    (hu : IsC2 u) (hharm : HarmonicOn u V)
    (hregular : SurfaceRegular S)
    (hGreen : SatisfiesSecondGreenIdentity S V q) :
    u q =
      1 / (4 * Real.pi) * outerRepresentationIntegral S u q := by
  exact gap10 S V u q ρ hρ hball hu hharm hregular hGreen

end

end ProofGap.Exercise4396
