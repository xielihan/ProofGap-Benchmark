import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1074

noncomputable section

def oscillatingCurve (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  f x * Real.sin (a * x)

def contactParameter (a : ℝ) (k : ℤ) : ℝ :=
  ((4 * (k : ℝ) + 1) * Real.pi) / (2 * a)

def contactPoints (a : ℝ) : Set ℝ :=
  {x | ∃ k : ℤ, x = contactParameter a k}

def k₁ (f : ℝ → ℝ) (a : ℝ) (k : ℤ) : ℝ :=
  deriv f (contactParameter a k)

def k₂ (f : ℝ → ℝ) (a : ℝ) (k : ℤ) : ℝ :=
  deriv (oscillatingCurve a f) (contactParameter a k)

private theorem deriv_mul_eq_left_of_hasDerivAt_zero
    (f g : ℝ → ℝ) (x : ℝ) (hg : HasDerivAt g 0 x) (hg1 : g x = 1) :
    deriv (fun y => f y * g y) x = deriv f x := by
  by_cases hf : DifferentiableAt ℝ f x
  · simpa [hg1] using (hf.hasDerivAt.mul hg).deriv
  · have hgx : g x ≠ 0 := by simp [hg1]
    have hfg : ¬DifferentiableAt ℝ (fun y => f y * g y) x := by
      intro h
      have hq : DifferentiableAt ℝ (fun y => (f y * g y) / g y) x :=
        h.div hg.differentiableAt hgx
      have hne : ∀ᶠ y in nhds x, g y ≠ 0 :=
        hg.continuousAt.eventually_ne hgx
      have heq : (fun y => (f y * g y) / g y) =ᶠ[nhds x] f := by
        filter_upwards [hne] with y hy
        field_simp [hy]
      exact hf (hq.congr_of_eventuallyEq heq.symm)
    simp [deriv_zero_of_not_differentiableAt hf,
      deriv_zero_of_not_differentiableAt hfg]

theorem gap1 (a x : ℝ) (f : ℝ → ℝ) (hf : 0 < f x) :
    f x = f x * Real.sin (a * x) ↔ Real.sin (a * x) = 1 := by
  constructor
  · intro h
    nlinarith
  · intro h
    rw [h, mul_one]

theorem gap2 (a x : ℝ) (f : ℝ → ℝ) (ha : a ≠ 0)
    (hf : ∀ t, 0 < f t) :
    x ∈ contactPoints a ↔ f x = f x * Real.sin (a * x) := by
  rw [gap1 a x f (hf x)]
  simp only [contactPoints, Set.mem_setOf_eq, contactParameter]
  rw [Real.sin_eq_one_iff]
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨k, ?_⟩
    field_simp [ha]
    <;> ring
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    apply mul_left_cancel₀ ha
    calc
      a * x = Real.pi / 2 + (k : ℝ) * (2 * Real.pi) := hk.symm
      _ = a * ((4 * (k : ℝ) + 1) * Real.pi / (2 * a)) := by
        field_simp [ha]
        <;> ring

theorem gap3 (a : ℝ) (f : ℝ → ℝ) (k : ℤ) (ha : a ≠ 0) :
    k₁ f a k = deriv f (contactParameter a k) := by
  rfl

theorem gap4 (a : ℝ) (f : ℝ → ℝ) (k : ℤ) (ha : a ≠ 0) :
    k₂ f a k =
      deriv f (contactParameter a k) *
          Real.sin ((4 * (k : ℝ) + 1) * Real.pi / 2) +
        a * Real.cos ((4 * (k : ℝ) + 1) * Real.pi / 2) *
          f (contactParameter a k) := by
  have hmem : contactParameter a k ∈ contactPoints a := ⟨k, rfl⟩
  have hs0 : Real.sin (a * contactParameter a k) = 1 :=
    (gap1 a (contactParameter a k) (fun _ => (1 : ℝ)) zero_lt_one).mp
      ((gap2 a (contactParameter a k) (fun _ => (1 : ℝ)) ha
        (fun _ => zero_lt_one)).mp hmem)
  have hc0 : Real.cos (a * contactParameter a k) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq (a * contactParameter a k),
      sq_nonneg (Real.cos (a * contactParameter a k))]
  have harg :
      a * contactParameter a k =
        (4 * (k : ℝ) + 1) * Real.pi / 2 := by
    unfold contactParameter
    field_simp [ha]
    <;> ring
  have hs :
      Real.sin ((4 * (k : ℝ) + 1) * Real.pi / 2) = 1 := by
    simpa [harg] using hs0
  have hc :
      Real.cos ((4 * (k : ℝ) + 1) * Real.pi / 2) = 0 := by
    simpa [harg] using hc0
  have hg : HasDerivAt (fun t : ℝ => Real.sin (a * t)) 0
      (contactParameter a k) := by
    simpa [hc0] using
      ((Real.hasDerivAt_sin (a * contactParameter a k)).comp
        (contactParameter a k)
        ((hasDerivAt_id (contactParameter a k)).const_mul a))
  unfold k₂ oscillatingCurve
  calc
    deriv (fun x => f x * Real.sin (a * x)) (contactParameter a k) =
        deriv f (contactParameter a k) :=
      deriv_mul_eq_left_of_hasDerivAt_zero f
        (fun t => Real.sin (a * t)) (contactParameter a k) hg hs0
    _ = deriv f (contactParameter a k) *
          Real.sin ((4 * (k : ℝ) + 1) * Real.pi / 2) +
        a * Real.cos ((4 * (k : ℝ) + 1) * Real.pi / 2) *
          f (contactParameter a k) := by
      rw [hs, hc]
      ring

theorem gap5 (a : ℝ) (f : ℝ → ℝ) (k : ℤ) (ha : a ≠ 0) :
    deriv f (contactParameter a k) *
          Real.sin ((4 * (k : ℝ) + 1) * Real.pi / 2) +
        a * Real.cos ((4 * (k : ℝ) + 1) * Real.pi / 2) *
          f (contactParameter a k) =
      deriv f (contactParameter a k) := by
  have hmem : contactParameter a k ∈ contactPoints a := ⟨k, rfl⟩
  have hs0 : Real.sin (a * contactParameter a k) = 1 :=
    (gap1 a (contactParameter a k) (fun _ => (1 : ℝ)) zero_lt_one).mp
      ((gap2 a (contactParameter a k) (fun _ => (1 : ℝ)) ha
        (fun _ => zero_lt_one)).mp hmem)
  have hc0 : Real.cos (a * contactParameter a k) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq (a * contactParameter a k),
      sq_nonneg (Real.cos (a * contactParameter a k))]
  have harg :
      a * contactParameter a k =
        (4 * (k : ℝ) + 1) * Real.pi / 2 := by
    unfold contactParameter
    field_simp [ha]
    <;> ring
  have hs :
      Real.sin ((4 * (k : ℝ) + 1) * Real.pi / 2) = 1 := by
    simpa [harg] using hs0
  have hc :
      Real.cos ((4 * (k : ℝ) + 1) * Real.pi / 2) = 0 := by
    simpa [harg] using hc0
  rw [hs, hc]
  ring

theorem gap6 (a : ℝ) (f : ℝ → ℝ) (k : ℤ) (ha : a ≠ 0) :
    k₂ f a k = deriv f (contactParameter a k) := by
  rw [gap4 a f k ha, gap5 a f k ha]

theorem gap7 (a : ℝ) (f : ℝ → ℝ) (k : ℤ) (ha : a ≠ 0) :
    k₁ f a k = k₂ f a k := by
  rw [gap3 a f k ha, gap6 a f k ha]

theorem gap8 (a : ℝ) (f : ℝ → ℝ) (ha : a ≠ 0) :
    ∀ k : ℤ, k₁ f a k = k₂ f a k := by
  intro k
  exact gap7 a f k ha

end

end ProofGap.Exercise1074
