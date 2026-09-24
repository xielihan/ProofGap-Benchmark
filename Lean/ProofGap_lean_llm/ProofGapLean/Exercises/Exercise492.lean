import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise492

noncomputable section

def original (a x : ℝ) : ℝ :=
  (Real.sin (a + x) * Real.sin (a + 2 * x) - Real.sin a ^ 2) / x
def productToSum (a x : ℝ) : ℝ :=
  ((1 / 2 : ℝ) * (Real.cos x - Real.cos (2 * a + 3 * x)) -
    Real.sin a ^ 2) / x
def rearranged (a x : ℝ) : ℝ :=
  (Real.cos x - Real.cos (2 * a + 3 * x) -
    (1 - Real.cos (2 * a))) / (2 * x)
def normalized (a x : ℝ) : ℝ :=
  -(Real.sin (x / 2) ^ 2 / x) +
    (Real.sin (3 * x / 2) / (3 * x / 2)) *
      (3 * Real.sin (2 * a + 3 * x / 2) / 2)
def HasLimitAtZero (f : ℝ → ℝ) (L : ℝ) : Prop :=
  Filter.Tendsto f (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds L)

/-- Source: `proof_gap/exercise_492/1.txt`. -/
private theorem original_product_identity (a : ℝ) :
    original a = productToSum a := by
  funext x
  unfold original productToSum
  apply congrArg (fun y : ℝ => y / x)
  have h :
      2 * Real.sin (a + x) * Real.sin (a + 2 * x) =
        Real.cos x - Real.cos (2 * a + 3 * x) := by
    calc
      2 * Real.sin (a + x) * Real.sin (a + 2 * x) =
          Real.cos ((a + x) - (a + 2 * x)) -
            Real.cos ((a + x) + (a + 2 * x)) :=
        Real.two_mul_sin_mul_sin (a + x) (a + 2 * x)
      _ = Real.cos x - Real.cos (2 * a + 3 * x) := by
        rw [show (a + x) - (a + 2 * x) = -x by ring,
          show (a + x) + (a + 2 * x) = 2 * a + 3 * x by ring,
          Real.cos_neg]
  calc
    Real.sin (a + x) * Real.sin (a + 2 * x) - Real.sin a ^ 2 =
        (1 / 2 : ℝ) *
            (2 * Real.sin (a + x) * Real.sin (a + 2 * x)) -
          Real.sin a ^ 2 := by ring
    _ = (1 / 2 : ℝ) *
          (Real.cos x - Real.cos (2 * a + 3 * x)) - Real.sin a ^ 2 := by
      rw [h]

private theorem product_rearranged_identity (a : ℝ) :
    productToSum a = rearranged a := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [productToSum, rearranged]
  · unfold productToSum rearranged
    rw [Real.cos_two_mul']
    field_simp [hx]
    nlinarith [Real.sin_sq_add_cos_sq a]

private theorem rearranged_normalized_identity (a : ℝ) :
    rearranged a = normalized a := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [rearranged, normalized]
  · have hxcos :
        Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
      calc
        Real.cos x = Real.cos (2 * (x / 2)) := by
          congr 1
          ring
        _ = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 :=
          Real.cos_two_mul' (x / 2)
        _ = 1 - 2 * Real.sin (x / 2) ^ 2 := by
          nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
    have hprod :
        2 * Real.sin (2 * a + 3 * x / 2) * Real.sin (3 * x / 2) =
          Real.cos (2 * a) - Real.cos (2 * a + 3 * x) := by
      calc
        2 * Real.sin (2 * a + 3 * x / 2) * Real.sin (3 * x / 2) =
            Real.cos ((2 * a + 3 * x / 2) - (3 * x / 2)) -
              Real.cos ((2 * a + 3 * x / 2) + (3 * x / 2)) :=
          Real.two_mul_sin_mul_sin
            (2 * a + 3 * x / 2) (3 * x / 2)
        _ = Real.cos (2 * a) - Real.cos (2 * a + 3 * x) := by
          rw [show (2 * a + 3 * x / 2) - (3 * x / 2) = 2 * a by ring,
            show (2 * a + 3 * x / 2) + (3 * x / 2) =
              2 * a + 3 * x by ring]
    have hcos :
        Real.cos (2 * a + 3 * x) =
          Real.cos (2 * a) -
            2 * Real.sin (2 * a + 3 * x / 2) * Real.sin (3 * x / 2) := by
      calc
        Real.cos (2 * a + 3 * x) =
            Real.cos (2 * a) -
              (Real.cos (2 * a) - Real.cos (2 * a + 3 * x)) := by ring
        _ = Real.cos (2 * a) -
              2 * Real.sin (2 * a + 3 * x / 2) * Real.sin (3 * x / 2) := by
          rw [← hprod]
    unfold rearranged normalized
    rw [hxcos, hcos]
    field_simp [hx] <;> ring

private def limitForm (a x : ℝ) : ℝ :=
  -(Real.sin ((1 / 2 : ℝ) * x) / ((1 / 2 : ℝ) * x)) ^ 2 *
      x * (1 / 4 : ℝ) +
    (Real.sin ((3 / 2 : ℝ) * x) / ((3 / 2 : ℝ) * x)) *
      ((3 / 2 : ℝ) * Real.sin (2 * a + (3 / 2 : ℝ) * x))

private theorem normalized_limitForm_identity (a : ℝ) :
    normalized a = limitForm a := by
  funext x
  by_cases hx : x = 0
  · subst x
    simp [normalized, limitForm]
  · unfold normalized limitForm
    field_simp [hx] <;> ring

private theorem tendsto_const_mul_punctured (c : ℝ) (hc : c ≠ 0) :
    Filter.Tendsto (fun x : ℝ => c * x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hid :
        Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
      continuousAt_id
    have h :
        Filter.Tendsto (fun x : ℝ => c * x) (nhds 0) (nhds (c * 0)) :=
      tendsto_const_nhds.mul hid
    simpa using h.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    exact mul_ne_zero hc hx

private theorem tendsto_sinc_punctured :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  simpa [div_eq_mul_inv, mul_comm] using
    (Real.hasDerivAt_sin 0).tendsto_slope_zero

theorem gap1 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (productToSum a) L := by
  rw [original_product_identity]

/-- Source: `proof_gap/exercise_492/2.txt`. -/
theorem gap2 (a L : ℝ) :
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (rearranged a) L := by
  calc
    HasLimitAtZero (original a) L ↔ HasLimitAtZero (productToSum a) L := gap1 a L
    _ ↔ HasLimitAtZero (rearranged a) L := by
      rw [product_rearranged_identity]

/-- Source: `proof_gap/exercise_492/3.txt`. -/
theorem gap3 (a L : ℝ) :
    HasLimitAtZero (rearranged a) L ↔ HasLimitAtZero (normalized a) L := by
  rw [rearranged_normalized_identity]

/-- Source: `proof_gap/exercise_492/4.txt`. -/
theorem gap4 (a : ℝ) :
    HasLimitAtZero (normalized a) ((3 / 2 : ℝ) * Real.sin (2 * a)) := by
  rw [normalized_limitForm_identity]
  unfold HasLimitAtZero limitForm
  have hid :
      Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) :=
    continuousAt_id
  have hx :
      Filter.Tendsto (fun x : ℝ => x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) :=
    hid.mono_left inf_le_left
  have hhalf :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sin ((1 / 2 : ℝ) * x) / ((1 / 2 : ℝ) * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    exact tendsto_sinc_punctured.comp
      (tendsto_const_mul_punctured (1 / 2 : ℝ) (by norm_num))
  have hthree :
      Filter.Tendsto
        (fun x : ℝ =>
          Real.sin ((3 / 2 : ℝ) * x) / ((3 / 2 : ℝ) * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
    exact tendsto_sinc_punctured.comp
      (tendsto_const_mul_punctured (3 / 2 : ℝ) (by norm_num))
  have hscale :
      Filter.Tendsto (fun x : ℝ => (3 / 2 : ℝ) * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using
      (tendsto_const_nhds.mul hx :
        Filter.Tendsto (fun x : ℝ => (3 / 2 : ℝ) * x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
          (nhds ((3 / 2 : ℝ) * 0)))
  have harg :
      Filter.Tendsto (fun x : ℝ => 2 * a + (3 / 2 : ℝ) * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (2 * a)) := by
    simpa using
      (tendsto_const_nhds.add hscale :
        Filter.Tendsto (fun x : ℝ => 2 * a + (3 / 2 : ℝ) * x)
          (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (2 * a + 0)))
  have hsin :
      Filter.Tendsto
        (fun x : ℝ => Real.sin (2 * a + (3 / 2 : ℝ) * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (Real.sin (2 * a))) :=
    (Real.continuous_sin.tendsto (2 * a)).comp harg
  have hfirstCore :
      Filter.Tendsto
        (fun x : ℝ =>
          -(Real.sin ((1 / 2 : ℝ) * x) / ((1 / 2 : ℝ) * x)) ^ 2 * x)
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using (hhalf.pow 2).neg.mul hx
  have hquarter :
      Filter.Tendsto (fun _ : ℝ => (1 / 4 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (1 / 4 : ℝ)) :=
    tendsto_const_nhds
  have hfirst :
      Filter.Tendsto
        (fun x : ℝ =>
          -(Real.sin ((1 / 2 : ℝ) * x) / ((1 / 2 : ℝ) * x)) ^ 2 *
            x * (1 / 4 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 0) := by
    simpa using hfirstCore.mul hquarter
  have hconstant :
      Filter.Tendsto (fun _ : ℝ => (3 / 2 : ℝ))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds (3 / 2 : ℝ)) :=
    tendsto_const_nhds
  have hsinScaled :
      Filter.Tendsto
        (fun x : ℝ =>
          (3 / 2 : ℝ) * Real.sin (2 * a + (3 / 2 : ℝ) * x))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds ((3 / 2 : ℝ) * Real.sin (2 * a))) := by
    exact hconstant.mul hsin
  have hsecond :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.sin ((3 / 2 : ℝ) * x) / ((3 / 2 : ℝ) * x)) *
            ((3 / 2 : ℝ) * Real.sin (2 * a + (3 / 2 : ℝ) * x)))
        (nhdsWithin 0 ({0} : Set ℝ)ᶜ)
        (nhds ((3 / 2 : ℝ) * Real.sin (2 * a))) := by
    simpa using hthree.mul hsinScaled
  simpa only [zero_add] using hfirst.add hsecond

/-- Source: `proof_gap/exercise_492/5.txt`. -/
theorem gap5 (a : ℝ) :
    HasLimitAtZero (original a) ((3 / 2 : ℝ) * Real.sin (2 * a)) := by
  apply (gap2 a ((3 / 2 : ℝ) * Real.sin (2 * a))).mpr
  apply (gap3 a ((3 / 2 : ℝ) * Real.sin (2 * a))).mpr
  exact gap4 a

end

end ProofGap.Exercise492
