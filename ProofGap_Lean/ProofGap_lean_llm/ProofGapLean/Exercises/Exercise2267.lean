import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open scoped Interval

namespace ProofGap.Exercise2267

noncomputable section

def Antiderivative (f F : ℝ → ℝ) : Prop :=
  ∀ x, HasDerivAt F (f x) x

def periodIncrement (f : ℝ → ℝ) (T : ℝ) : ℝ :=
  ∫ t in 0..T, f t

def periodicPart (F : ℝ → ℝ) (K T x : ℝ) : ℝ :=
  F x - K / T * x

theorem gap1 (f F : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hF : Antiderivative f F) :
    ∀ x, F (x + T) - F x = ∫ t in x..x + T, f t := by
  intro x
  symm
  exact intervalIntegral.integral_eq_sub_of_hasDeriv_right
    (fun y _ => (hF y).continuousAt.continuousWithinAt)
    (fun y _ => (hF y).hasDerivWithinAt)
    (hf.intervalIntegrable _ _)

theorem gap2 (f : ℝ → ℝ) (T x₀ : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ x, (∫ t in x..x + T, f t) = ∫ t in x₀..x₀ + T, f t := by
  intro x
  exact hper.intervalIntegral_add_eq x x₀

theorem gap3 (f : ℝ → ℝ) (T x₀ : ℝ) :
    ∃ K : ℝ, (∫ t in x₀..x₀ + T, f t) = K := by
  exact ⟨∫ t in x₀..x₀ + T, f t, rfl⟩

theorem gap4 (f : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) :
    ∀ x, (∫ t in x..x + T, f t) = periodIncrement f T := by
  intro x
  simpa only [periodIncrement, zero_add] using
    (gap2 f T 0 hf hper x)

theorem gap5 (f F : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) (hF : Antiderivative f F) :
    ∀ x, F (x + T) - F x = periodIncrement f T := by
  intro x
  calc
    F (x + T) - F x = ∫ t in x..x + T, f t := gap1 f F T hf hF x
    _ = periodIncrement f T := gap4 f T hf hper x

theorem gap6 (f F : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) (hF : Antiderivative f F) :
    let K := periodIncrement f T
    K = 0 → Function.Periodic F T := by
  dsimp only
  intro hK x
  apply sub_eq_zero.mp
  rw [gap5 f F T hf hper hF x, hK]

theorem gap7 (f F : ℝ → ℝ) (T x : ℝ) (hT : T ≠ 0) :
    let K := periodIncrement f T
    periodicPart F K T (x + T) =
      F (x + T) - K / T * (x + T) := by
  rfl

theorem gap8 (f F : ℝ → ℝ) (T x : ℝ) (hT : T ≠ 0) :
    let K := periodIncrement f T
    F (x + T) - K / T * (x + T) =
      F (x + T) - K / T * x - K := by
  dsimp only
  field_simp [hT] <;> ring

theorem gap9 (f F : ℝ → ℝ) (T x : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) (hF : Antiderivative f F) (hT : T ≠ 0) :
    let K := periodIncrement f T
    F (x + T) - K / T * x - K = F x - K / T * x := by
  dsimp only
  have hinc := gap5 f F T hf hper hF x
  linarith

theorem gap10 (f F : ℝ → ℝ) (T x : ℝ) :
    let K := periodIncrement f T
    F x - K / T * x = periodicPart F K T x := by
  rfl

theorem gap11 (f F : ℝ → ℝ) (T x : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) (hF : Antiderivative f F) (hT : T ≠ 0) :
    let K := periodIncrement f T
    periodicPart F K T (x + T) = periodicPart F K T x := by
  dsimp only
  calc
    periodicPart F (periodIncrement f T) T (x + T) =
        F (x + T) - periodIncrement f T / T * (x + T) :=
      gap7 f F T x hT
    _ = F (x + T) - periodIncrement f T / T * x - periodIncrement f T :=
      gap8 f F T x hT
    _ = F x - periodIncrement f T / T * x :=
      gap9 f F T x hf hper hF hT
    _ = periodicPart F (periodIncrement f T) T x :=
      gap10 f F T x

theorem gap12 (f F : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) (hF : Antiderivative f F) (hT : T ≠ 0) :
    let K := periodIncrement f T
    Function.Periodic (periodicPart F K T) T := by
  dsimp only
  intro x
  exact gap11 f F T x hf hper hF hT

theorem gap13 (f F : ℝ → ℝ) (T x : ℝ) :
    let K := periodIncrement f T
    F x = periodicPart F K T x + K / T * x := by
  dsimp only
  unfold periodicPart
  ring

theorem gap14 (f F : ℝ → ℝ) (T : ℝ) (hf : Continuous f)
    (hper : Function.Periodic f T) (hF : Antiderivative f F) (hT : T ≠ 0) :
    ∃ φ : ℝ → ℝ, ∃ K : ℝ,
      Function.Periodic φ T ∧ ∀ x, F x = φ x + K / T * x := by
  refine ⟨periodicPart F (periodIncrement f T) T, periodIncrement f T, ?_, ?_⟩
  · exact gap12 f F T hf hper hF hT
  · intro x
    exact gap13 f F T x

end

end ProofGap.Exercise2267
