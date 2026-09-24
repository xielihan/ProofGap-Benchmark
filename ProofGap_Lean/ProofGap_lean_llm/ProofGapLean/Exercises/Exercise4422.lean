import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise4422

noncomputable section

open Filter MeasureTheory

abbrev Vec3 := ℝ × ℝ × ℝ
abbrev SurfaceIntegral := (Vec3 → ℝ) → ℝ

def dot (a b : Vec3) : ℝ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def subVec (a b : Vec3) : Vec3 :=
  (a.1 - b.1, a.2.1 - b.2.1, a.2.2 - b.2.2)

def norm3 (v : Vec3) : ℝ :=
  Real.sqrt (v.1 ^ 2 + v.2.1 ^ 2 + v.2.2 ^ 2)

def normalComponent (a normal : Vec3 → Vec3) (p : Vec3) : ℝ :=
  dot (a p) (normal p)

def partialX (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun x => u (x, p.2.1, p.2.2)) p.1

def partialY (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun y => u (p.1, y, p.2.2)) p.2.1

def partialZ (u : Vec3 → ℝ) (p : Vec3) : ℝ :=
  deriv (fun z => u (p.1, p.2.1, z)) p.2.2

def divergence (a : Vec3 → Vec3) (p : Vec3) : ℝ :=
  partialX (fun q => (a q).1) p +
    partialY (fun q => (a q).2.1) p +
      partialZ (fun q => (a q).2.2) p

def surfaceFlux (I : SurfaceIntegral) (a normal : Vec3 → Vec3) : ℝ :=
  I (normalComponent a normal)

def volumeIntegral (V : Set Vec3) (f : Vec3 → ℝ) : ℝ :=
  ∫ p in V, f p

def volume (V : Set Vec3) : ℝ :=
  ∫ _p in V, (1 : ℝ)

def SatisfiesGauss (V : Set Vec3) (I : SurfaceIntegral)
    (normal : Vec3 → Vec3) : Prop :=
  ∀ a : Vec3 → Vec3, ContDiff ℝ 1 a →
    surfaceFlux I a normal = volumeIntegral V (divergence a)

def SatisfiesIntegralMeanValue (V : Set Vec3) : Prop :=
  ∀ f : Vec3 → ℝ, ContinuousOn f V →
    ∃ M₁ ∈ V, volumeIntegral V f = f M₁ * volume V

def normalizedFlux (V : Set Vec3) (I : SurfaceIntegral)
    (a normal : Vec3 → Vec3) : ℝ :=
  surfaceFlux I a normal / volume V

def ShrinksTo (V : ℕ → Set Vec3) (M : Vec3) : Prop :=
  ∀ ε > 0, ∀ᶠ n in atTop, ∀ p, p ∈ V n → norm3 (subVec p M) < ε

def DivergenceIsFluxLimit (V : ℕ → Set Vec3)
    (I : ℕ → SurfaceIntegral) (normal : ℕ → Vec3 → Vec3)
    (a : Vec3 → Vec3) (M : Vec3) : Prop :=
  Tendsto (fun n => normalizedFlux (V n) (I n) a (normal n))
    atTop (nhds (divergence a M))

private theorem coordinate_abs_lt_of_norm3_lt
    (p M : Vec3) {ε : ℝ}
    (h : norm3 (subVec p M) < ε) :
    |p.1 - M.1| < ε ∧
      |p.2.1 - M.2.1| < ε ∧
        |p.2.2 - M.2.2| < ε := by
  have hsum :
      0 ≤ (p.1 - M.1) ^ 2 + (p.2.1 - M.2.1) ^ 2 +
        (p.2.2 - M.2.2) ^ 2 := by
    positivity
  have hsqrt := Real.sq_sqrt hsum
  have hsqrt_nonneg := Real.sqrt_nonneg
    ((p.1 - M.1) ^ 2 + (p.2.1 - M.2.1) ^ 2 +
      (p.2.2 - M.2.2) ^ 2)
  change Real.sqrt
      ((p.1 - M.1) ^ 2 + (p.2.1 - M.2.1) ^ 2 +
        (p.2.2 - M.2.2) ^ 2) < ε at h
  constructor
  · rw [abs_lt]
    constructor <;>
      nlinarith [sq_nonneg (p.1 - M.1),
        sq_nonneg (p.2.1 - M.2.1), sq_nonneg (p.2.2 - M.2.2),
        sq_nonneg (p.1 - M.1 - ε), sq_nonneg (p.1 - M.1 + ε)]
  constructor
  · rw [abs_lt]
    constructor <;>
      nlinarith [sq_nonneg (p.1 - M.1),
        sq_nonneg (p.2.1 - M.2.1), sq_nonneg (p.2.2 - M.2.2),
        sq_nonneg (p.2.1 - M.2.1 - ε),
        sq_nonneg (p.2.1 - M.2.1 + ε)]
  · rw [abs_lt]
    constructor <;>
      nlinarith [sq_nonneg (p.1 - M.1),
        sq_nonneg (p.2.1 - M.2.1), sq_nonneg (p.2.2 - M.2.2),
        sq_nonneg (p.2.2 - M.2.2 - ε),
        sq_nonneg (p.2.2 - M.2.2 + ε)]

theorem gap1 (a normal : Vec3 → Vec3) :
    ∃ aₙ : Vec3 → ℝ, ∀ p, aₙ p = dot (a p) (normal p) := by
  refine ⟨fun p => dot (a p) (normal p), ?_⟩
  intro p
  rfl

theorem gap2 (a normal : Vec3 → Vec3) (p : Vec3) :
    dot (a p) (normal p) =
      (a p).1 * (normal p).1 +
        (a p).2.1 * (normal p).2.1 +
          (a p).2.2 * (normal p).2.2 := by
  rfl

theorem gap3 (a normal : Vec3 → Vec3) :
    ∃ aₙ : Vec3 → ℝ, ∀ p,
      aₙ p =
        (a p).1 * (normal p).1 +
          (a p).2.1 * (normal p).2.1 +
            (a p).2.2 * (normal p).2.2 := by
  rcases gap1 a normal with ⟨aₙ, haₙ⟩
  refine ⟨aₙ, ?_⟩
  intro p
  rw [haₙ p, gap2 a normal p]

theorem gap4 (I : SurfaceIntegral) (a normal : Vec3 → Vec3) :
    surfaceFlux I a normal = I (fun p => dot (a p) (normal p)) := by
  rfl

theorem gap5 (V : Set Vec3) (I : SurfaceIntegral)
    (a normal : Vec3 → Vec3)
    (hGauss : SatisfiesGauss V I normal)
    (hC1 : ContDiff ℝ 1 a) :
    surfaceFlux I a normal = volumeIntegral V (divergence a) := by
  exact hGauss a hC1

theorem gap6 (V : Set Vec3) (a : Vec3 → Vec3) :
    volumeIntegral V (fun p =>
        partialX (fun q => (a q).1) p +
          partialY (fun q => (a q).2.1) p +
            partialZ (fun q => (a q).2.2) p) =
      volumeIntegral V (divergence a) := by
  rfl

theorem gap7 (V : Set Vec3) (I : SurfaceIntegral)
    (a normal : Vec3 → Vec3)
    (hGauss : SatisfiesGauss V I normal)
    (hC1 : ContDiff ℝ 1 a) :
    surfaceFlux I a normal = volumeIntegral V (divergence a) := by
  exact gap5 V I a normal hGauss hC1

theorem gap8 (V : Set Vec3) (I : SurfaceIntegral)
    (a normal : Vec3 → Vec3) (hGauss : SatisfiesGauss V I normal)
    (hMeanValue : SatisfiesIntegralMeanValue V)
    (hC1 : ContDiff ℝ 1 a)
    (hContinuous : ContinuousOn (divergence a) V) :
    ∃ M₁ ∈ V,
      surfaceFlux I a normal = divergence a M₁ * volume V := by
  rcases hMeanValue (divergence a) hContinuous with ⟨M₁, hM₁, hMean⟩
  refine ⟨M₁, hM₁, ?_⟩
  calc
    surfaceFlux I a normal = volumeIntegral V (divergence a) :=
      gap7 V I a normal hGauss hC1
    _ = divergence a M₁ * volume V := hMean

theorem gap9 (V : Set Vec3) (I : SurfaceIntegral)
    (a normal : Vec3 → Vec3) (hVolume : volume V ≠ 0)
    (hGauss : SatisfiesGauss V I normal)
    (hMeanValue : SatisfiesIntegralMeanValue V)
    (hC1 : ContDiff ℝ 1 a)
    (hContinuous : ContinuousOn (divergence a) V) :
    ∃ M₁ ∈ V,
      divergence a M₁ = normalizedFlux V I a normal := by
  rcases gap8 V I a normal hGauss hMeanValue hC1 hContinuous with
    ⟨M₁, hM₁, hFlux⟩
  refine ⟨M₁, hM₁, ?_⟩
  unfold normalizedFlux
  apply (eq_div_iff hVolume).2
  exact hFlux.symm

theorem gap10 (V : ℕ → Set Vec3) (M : Vec3)
    (points : ℕ → Vec3) (hShrink : ShrinksTo V M)
    (hPoints : ∀ n, points n ∈ V n) :
    Tendsto points atTop (nhds M) := by
  have hx : Tendsto (fun n => (points n).1) atTop (nhds M.1) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    rcases (eventually_atTop.1 (hShrink ε hε)) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hb := coordinate_abs_lt_of_norm3_lt (points n) M
      (hN n hn (points n) (hPoints n))
    simpa only [Real.dist_eq] using hb.1
  have hy : Tendsto (fun n => (points n).2.1) atTop (nhds M.2.1) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    rcases (eventually_atTop.1 (hShrink ε hε)) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hb := coordinate_abs_lt_of_norm3_lt (points n) M
      (hN n hn (points n) (hPoints n))
    simpa only [Real.dist_eq] using hb.2.1
  have hz : Tendsto (fun n => (points n).2.2) atTop (nhds M.2.2) := by
    refine Metric.tendsto_atTop.2 ?_
    intro ε hε
    rcases (eventually_atTop.1 (hShrink ε hε)) with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn
    have hb := coordinate_abs_lt_of_norm3_lt (points n) M
      (hN n hn (points n) (hPoints n))
    simpa only [Real.dist_eq] using hb.2.2
  simpa only [Prod.eta] using hx.prodMk_nhds (hy.prodMk_nhds hz)

theorem gap11 (V : ℕ → Set Vec3) (M : Vec3)
    (hShrink : ShrinksTo V M) (hNonempty : ∀ n, (V n).Nonempty) :
    ∃ M₁ : ℕ → Vec3,
      (∀ n, M₁ n ∈ V n) ∧ Tendsto M₁ atTop (nhds M) := by
  classical
  let M₁ : ℕ → Vec3 := fun n => Classical.choose (hNonempty n)
  have hM₁ : ∀ n, M₁ n ∈ V n := by
    intro n
    exact Classical.choose_spec (hNonempty n)
  refine ⟨M₁, hM₁, ?_⟩
  exact gap10 V M M₁ hShrink hM₁

theorem gap12 (V : ℕ → Set Vec3) (I : ℕ → SurfaceIntegral)
    (normal : ℕ → Vec3 → Vec3) (a : Vec3 → Vec3)
    (M : Vec3)
    (hShrink : ShrinksTo V M) (hNonempty : ∀ n, (V n).Nonempty)
    (hVolume : ∀ n, volume (V n) ≠ 0)
    (hGauss : ∀ n, SatisfiesGauss (V n) (I n) (normal n))
    (hMeanValue : ∀ n, SatisfiesIntegralMeanValue (V n))
    (hC1 : ContDiff ℝ 1 a)
    (hContinuousOn : ∀ n, ContinuousOn (divergence a) (V n))
    (hContinuous : ContinuousAt (divergence a) M) :
    Tendsto (fun n => normalizedFlux (V n) (I n) a (normal n))
      atTop (nhds (divergence a M)) := by
  classical
  have hex : ∀ n, ∃ p ∈ V n,
      divergence a p = normalizedFlux (V n) (I n) a (normal n) := by
    intro n
    exact gap9 (V n) (I n) a (normal n) (hVolume n)
      (hGauss n) (hMeanValue n) hC1 (hContinuousOn n)
  let M₁ : ℕ → Vec3 := fun n => Classical.choose (hex n)
  have hM₁ : ∀ n, M₁ n ∈ V n := by
    intro n
    exact (Classical.choose_spec (hex n)).1
  have hFlux : ∀ n,
      divergence a (M₁ n) = normalizedFlux (V n) (I n) a (normal n) := by
    intro n
    exact (Classical.choose_spec (hex n)).2
  have hPoints : Tendsto M₁ atTop (nhds M) :=
    gap10 V M M₁ hShrink hM₁
  have hDiv : Tendsto (fun n => divergence a (M₁ n))
      atTop (nhds (divergence a M)) :=
    hContinuous.tendsto.comp hPoints
  have hfun :
      (fun n => normalizedFlux (V n) (I n) a (normal n)) =
        (fun n => divergence a (M₁ n)) := by
    funext n
    exact (hFlux n).symm
  rw [hfun]
  exact hDiv

theorem gap13 (V : ℕ → Set Vec3) (I : ℕ → SurfaceIntegral)
    (normal : ℕ → Vec3 → Vec3) (a : Vec3 → Vec3)
    (M : Vec3)
    (hShrink : ShrinksTo V M) (hNonempty : ∀ n, (V n).Nonempty)
    (hVolume : ∀ n, volume (V n) ≠ 0)
    (hGauss : ∀ n, SatisfiesGauss (V n) (I n) (normal n))
    (hMeanValue : ∀ n, SatisfiesIntegralMeanValue (V n))
    (hC1 : ContDiff ℝ 1 a)
    (hContinuousOn : ∀ n, ContinuousOn (divergence a) (V n))
    (hContinuous : ContinuousAt (divergence a) M) :
    DivergenceIsFluxLimit V I normal a M := by
  unfold DivergenceIsFluxLimit
  exact gap12 V I normal a M hShrink hNonempty hVolume hGauss
    hMeanValue hC1 hContinuousOn hContinuous

end

end ProofGap.Exercise4422
