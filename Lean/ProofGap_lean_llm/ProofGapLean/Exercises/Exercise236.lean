import ProofGapLean.Prelude.Elementary
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise236

noncomputable section

def base (k T : ℝ) : ℝ := Real.rpow k (1 / T)
def periodicFactor (a : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  Real.rpow a (-x) * f x

/-- Source: `proof_gap/exercise_236/1.txt`. -/
theorem gap1 (k T : ℝ) (hk : 0 < k) (hT : 0 < T) :
    0 < base k T := by
  unfold base
  exact Real.rpow_pos_of_pos hk _

/-- Source: `proof_gap/exercise_236/2.txt`. -/
theorem gap2 (k T : ℝ) (hk : 0 < k) (hT : 0 < T) :
    Real.rpow (base k T) T = k := by
  have hdiv : (1 / T) * T = (1 : ℝ) := by
    simp [hT.ne']
  change Real.rpow (Real.rpow k (1 / T)) T = k
  calc
    Real.rpow (Real.rpow k (1 / T)) T =
        Real.rpow k ((1 / T) * T) :=
      (Real.rpow_mul (le_of_lt hk) (1 / T) T).symm
    _ = Real.rpow k 1 := by rw [hdiv]
    _ = k := Real.rpow_one k

/-- Source: `proof_gap/exercise_236/3.txt`. -/
theorem gap3 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (hscale : ∀ x, f (x + T) = k * f x) : ∀ x,
    f (x + T) = Real.rpow (base k T) T * f x := by
  intro x
  calc
    f (x + T) = k * f x := hscale x
    _ = Real.rpow (base k T) T * f x := by
      rw [gap2 k T hk hT]

/-- Source: `proof_gap/exercise_236/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (k T : ℝ) : ∀ x,
    periodicFactor (base k T) f (x + T) =
      Real.rpow (base k T) (-(x + T)) * f (x + T) := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_236/5.txt`. -/
theorem gap5 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (hscale : ∀ x, f (x + T) = k * f x) : ∀ x,
    Real.rpow (base k T) (-(x + T)) * f (x + T) =
      Real.rpow (base k T) (-x) * Real.rpow (base k T) (-T) *
        Real.rpow (base k T) T * f x := by
  intro x
  have ha : 0 < base k T := gap1 k T hk hT
  have hneg : -(x + T) = -x + -T := by
    ring
  rw [gap3 f k T hk hT hscale x, hneg]
  calc
    Real.rpow (base k T) (-x + -T) *
        (Real.rpow (base k T) T * f x) =
      (Real.rpow (base k T) (-x) * Real.rpow (base k T) (-T)) *
        (Real.rpow (base k T) T * f x) := by
      exact congrArg
        (fun z : ℝ => z * (Real.rpow (base k T) T * f x))
        (Real.rpow_add ha (-x) (-T))
    _ = Real.rpow (base k T) (-x) * Real.rpow (base k T) (-T) *
          Real.rpow (base k T) T * f x := by
      simp only [mul_assoc]

/-- Source: `proof_gap/exercise_236/6.txt`. -/
theorem gap6 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T) : ∀ x,
    Real.rpow (base k T) (-x) * Real.rpow (base k T) (-T) *
        Real.rpow (base k T) T * f x =
      Real.rpow (base k T) (-x) * f x := by
  intro x
  have ha : 0 < base k T := gap1 k T hk hT
  have hcancel :
      Real.rpow (base k T) (-T) * Real.rpow (base k T) T = 1 := by
    calc
      Real.rpow (base k T) (-T) * Real.rpow (base k T) T =
          Real.rpow (base k T) (-T + T) :=
        (Real.rpow_add ha (-T) T).symm
      _ = 1 := by simp
  simpa only [mul_assoc, hcancel, mul_one]

/-- Source: `proof_gap/exercise_236/7.txt`. -/
theorem gap7 (f : ℝ → ℝ) (k T : ℝ) : ∀ x,
    Real.rpow (base k T) (-x) * f x =
      periodicFactor (base k T) f x := by
  intro x
  rfl

/-- Source: `proof_gap/exercise_236/8.txt`. -/
theorem gap8 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (hscale : ∀ x, f (x + T) = k * f x) : ∀ x,
    periodicFactor (base k T) f (x + T) =
      periodicFactor (base k T) f x := by
  intro x
  calc
    periodicFactor (base k T) f (x + T) =
        Real.rpow (base k T) (-(x + T)) * f (x + T) :=
      gap4 f k T x
    _ = Real.rpow (base k T) (-x) * Real.rpow (base k T) (-T) *
          Real.rpow (base k T) T * f x :=
      gap5 f k T hk hT hscale x
    _ = Real.rpow (base k T) (-x) * f x :=
      gap6 f k T hk hT x
    _ = periodicFactor (base k T) f x :=
      gap7 f k T x

/-- Source: `proof_gap/exercise_236/9.txt`. -/
theorem gap9 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (hscale : ∀ x, f (x + T) = k * f x) :
    Function.Periodic (periodicFactor (base k T) f) T := by
  exact gap8 f k T hk hT hscale

/-- Source: `proof_gap/exercise_236/10.txt`. -/
theorem gap10 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T) : ∀ x,
    f x = Real.rpow (base k T) x * periodicFactor (base k T) f x := by
  intro x
  unfold periodicFactor
  have ha : 0 < base k T := gap1 k T hk hT
  have hcancel :
      Real.rpow (base k T) x * Real.rpow (base k T) (-x) = 1 := by
    calc
      Real.rpow (base k T) x * Real.rpow (base k T) (-x) =
          Real.rpow (base k T) (x + -x) :=
        (Real.rpow_add ha x (-x)).symm
      _ = 1 := by simp
  calc
    f x = 1 * f x := by simp
    _ = (Real.rpow (base k T) x * Real.rpow (base k T) (-x)) * f x := by
      rw [hcancel]
    _ = Real.rpow (base k T) x *
          (Real.rpow (base k T) (-x) * f x) :=
      mul_assoc _ _ _

/-- Source: `proof_gap/exercise_236/11.txt`. -/
theorem gap11 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (hscale : ∀ x, f (x + T) = k * f x) :
    Function.Periodic (periodicFactor (base k T) f) T := by
  exact gap9 f k T hk hT hscale

/-- Source: `proof_gap/exercise_236/12.txt`; move witnesses outside the point quantifier. -/
theorem gap12 (f : ℝ → ℝ) (k T : ℝ) (hk : 0 < k) (hT : 0 < T)
    (hscale : ∀ x, f (x + T) = k * f x) :
    ∃ a : ℝ, ∃ phi : ℝ → ℝ,
      0 < a ∧ Function.Periodic phi T ∧
        ∀ x, f x = Real.rpow a x * phi x := by
  refine ⟨base k T, periodicFactor (base k T) f, gap1 k T hk hT, ?_, ?_⟩
  · exact gap11 f k T hk hT hscale
  · exact gap10 f k T hk hT

end

end ProofGap.Exercise236
