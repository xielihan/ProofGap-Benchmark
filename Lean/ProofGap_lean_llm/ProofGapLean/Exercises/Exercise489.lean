import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise489

noncomputable section

def original (a x : ℝ) : ℝ :=
  (Real.cos (a + 2 * x) - 2 * Real.cos (a + x) + Real.cos a) / x ^ 2
def differenceForm (a x : ℝ) : ℝ :=
  (Real.cos (a + 2 * x) - Real.cos (a + x) -
    (Real.cos (a + x) - Real.cos a)) / x ^ 2
def expanded (a x : ℝ) : ℝ :=
  (-2 * Real.sin (a + 3 * x / 2) * Real.sin (x / 2) +
    2 * Real.sin (a + x / 2) * Real.sin (x / 2)) / x ^ 2
def factored (a x : ℝ) : ℝ :=
  -(2 * Real.sin (x / 2) *
    (Real.sin (a + 3 * x / 2) - Real.sin (a + x / 2)) / x ^ 2)
def normalized (a x : ℝ) : ℝ :=
  -(Real.sin (x / 2) / (x / 2)) ^ 2 * Real.cos (a + x)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_489/1.txt`. -/
private theorem cosDifferenceIdentity (u v : ℝ) :
    Real.cos u - Real.cos v =
      -2 * Real.sin ((u + v) / 2) * Real.sin ((u - v) / 2) := by
  have hu : u = (u + v) / 2 + (u - v) / 2 := by
    ring
  have hv : v = (u + v) / 2 - (u - v) / 2 := by
    ring
  calc
    Real.cos u - Real.cos v =
        Real.cos ((u + v) / 2 + (u - v) / 2) -
          Real.cos ((u + v) / 2 - (u - v) / 2) :=
      congrArg₂ (fun p q : ℝ => p - q)
        (congrArg Real.cos hu) (congrArg Real.cos hv)
    _ = -2 * Real.sin ((u + v) / 2) * Real.sin ((u - v) / 2) := by
      rw [Real.cos_add, Real.cos_sub]
      ring

private theorem sinDifferenceIdentity (u v : ℝ) :
    Real.sin u - Real.sin v =
      2 * Real.cos ((u + v) / 2) * Real.sin ((u - v) / 2) := by
  have hu : u = (u + v) / 2 + (u - v) / 2 := by
    ring
  have hv : v = (u + v) / 2 - (u - v) / 2 := by
    ring
  calc
    Real.sin u - Real.sin v =
        Real.sin ((u + v) / 2 + (u - v) / 2) -
          Real.sin ((u + v) / 2 - (u - v) / 2) :=
      congrArg₂ (fun p q : ℝ => p - q)
        (congrArg Real.sin hu) (congrArg Real.sin hv)
    _ = 2 * Real.cos ((u + v) / 2) * Real.sin ((u - v) / 2) := by
      rw [Real.sin_add, Real.sin_sub]
      ring

theorem gap1 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (differenceForm a) L := by
  have h : original a = differenceForm a := by
    funext x
    unfold original differenceForm
    ring
  rw [h]

/-- Source: `proof_gap/exercise_489/2.txt`. -/
theorem gap2 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (expanded a) L := by
  have h : original a = expanded a := by
    funext x
    unfold original expanded
    have hn :
        Real.cos (a + 2 * x) - 2 * Real.cos (a + x) + Real.cos a =
          (Real.cos (a + 2 * x) - Real.cos (a + x)) -
            (Real.cos (a + x) - Real.cos a) := by
      ring
    rw [hn]
    rw [cosDifferenceIdentity (a + 2 * x) (a + x),
      cosDifferenceIdentity (a + x) a]
    have h1 : ((a + 2 * x) + (a + x)) / 2 = a + 3 * x / 2 := by
      ring
    have h2 : ((a + 2 * x) - (a + x)) / 2 = x / 2 := by
      ring
    have h3 : ((a + x) + a) / 2 = a + x / 2 := by
      ring
    have h4 : ((a + x) - a) / 2 = x / 2 := by
      ring
    rw [h1, h2, h3, h4]
    ring
  rw [h]

/-- Source: `proof_gap/exercise_489/3.txt`. -/
theorem gap3 (a L : ℝ) :
    HasLimitAtZero (expanded a) L ↔ HasLimitAtZero (factored a) L := by
  have h : expanded a = factored a := by
    funext x
    unfold expanded factored
    ring
  rw [h]

/-- Source: `proof_gap/exercise_489/4.txt`. -/
theorem gap4 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (factored a) L := by
  exact (gap2 a L).trans (gap3 a L)

/-- Source: `proof_gap/exercise_489/5.txt`. -/
theorem gap5 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (normalized a) L := by
  have h : factored a = normalized a := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [factored, normalized]
    · unfold factored normalized
      rw [sinDifferenceIdentity (a + 3 * x / 2) (a + x / 2)]
      have h1 : ((a + 3 * x / 2) + (a + x / 2)) / 2 = a + x := by
        ring
      have h2 : ((a + 3 * x / 2) - (a + x / 2)) / 2 = x / 2 := by
        ring
      rw [h1, h2]
      field_simp [hx]
  calc
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (factored a) L := gap4 a L
    _ ↔ HasLimitAtZero (normalized a) L := by rw [h]

/-- Source: `proof_gap/exercise_489/6.txt`. -/
theorem gap6 (a : ℝ) : HasLimitAtZero (normalized a) (-Real.cos a) := by
  unfold HasLimitAtZero normalized
  have hhalf :
      Filter.Tendsto (fun x : ℝ => x / 2)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hfull :
          Filter.Tendsto (fun x : ℝ => x / 2) (nhds 0) (nhds 0) := by
        simpa only [id_eq, zero_div] using
          ((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).div_const 2).tendsto
      exact hfull.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
      exact div_ne_zero hx (by norm_num)
  have hsinDeriv : HasDerivAt Real.sin 1 0 := by
    simpa using (Real.hasDerivAt_sin 0)
  have hsincBase :
      Filter.Tendsto (fun x : ℝ => Real.sin x / x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    have hs := hsinDeriv.tendsto_slope
    change Filter.Tendsto
      (fun x : ℝ => (x - 0)⁻¹ • (Real.sin x - Real.sin 0))
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) at hs
    simpa [div_eq_mul_inv, mul_comm] using hs
  have hsinc :
      Filter.Tendsto (fun x : ℝ => Real.sin (x / 2) / (x / 2))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    exact hsincBase.comp hhalf
  have hid :
      Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
    (continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).tendsto
  have hargFull :
      Filter.Tendsto (fun x : ℝ => a + x) (nhds 0) (nhds (a + 0)) := by
    exact tendsto_const_nhds.add hid
  have harg :
      Filter.Tendsto (fun x : ℝ => a + x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds a) := by
    simpa using hargFull.mono_left inf_le_left
  have hcos :
      Filter.Tendsto (fun x : ℝ => Real.cos (a + x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.cos a)) := by
    exact (Real.continuous_cos.tendsto a).comp harg
  simpa using (hsinc.pow 2).neg.mul hcos

/-- Source: `proof_gap/exercise_489/7.txt`. -/
theorem gap7 (a : ℝ) : HasLimitAtZero (original a) (-Real.cos a) := by
  exact (gap5 a (-Real.cos a)).mpr (gap6 a)

end

end ProofGap.Exercise489
