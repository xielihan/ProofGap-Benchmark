import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2167

noncomputable section

def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def NormalizedSignFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives (fun x => x ^ 2),
    G 0 = 0 ∧ ∃ C : ℝ, ∀ x, F x = Real.sign x * G x + C}
def signPrimitive (x : ℝ) := Real.sign x * (x ^ 3 / 3)
def primitive (x : ℝ) := x ^ 2 * |x| / 3

private theorem hasDerivAt_cube_div_three (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
  convert ((hasDerivAt_id x).pow 3).div_const 3 using 1 <;>
    simp only [id_eq] <;> ring

private theorem hasDerivAt_primitive_zero :
    HasDerivAt primitive 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hc : ContinuousAt (fun y : ℝ => y * |y| / 3) 0 := by
    simpa only [id_eq] using
      (continuousAt_id.mul continuous_abs.continuousAt).div_const 3
  have ht0 : Tendsto (fun y : ℝ => y * |y| / 3) (nhds 0) (nhds 0) := by
    simpa using hc.tendsto
  have ht : Tendsto (fun y : ℝ => y * |y| / 3)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) :=
    ht0.mono_left inf_le_left
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hy0 : y ≠ 0 := by simpa using hy
  unfold slope primitive
  simp only [vsub_eq_sub, sub_zero, smul_eq_mul]
  field_simp [hy0]
  ring

private theorem hasDerivAt_primitive (x : ℝ) :
    HasDerivAt primitive (x * |x|) x := by
  by_cases hx : x = 0
  · subst x
    simpa using hasDerivAt_primitive_zero
  · unfold primitive
    convert (((hasDerivAt_id x).pow 2).mul (hasDerivAt_abs hx)).div_const 3 using 1 <;>
      simp only [id_eq]
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · simp [hneg, abs_of_neg hneg] <;> ring
    · simp [hpos, abs_of_pos hpos] <;> ring

private theorem signPrimitive_eq_primitive (x : ℝ) :
    signPrimitive x = primitive x := by
  rcases lt_trichotomy x 0 with hneg | hzero | hpos
  · simp [signPrimitive, primitive, Real.sign_of_neg hneg, abs_of_neg hneg] <;> ring
  · subst x
    norm_num [signPrimitive, primitive]
  · simp [signPrimitive, primitive, Real.sign_of_pos hpos, abs_of_pos hpos] <;> ring

private theorem sub_eq_sub_of_same_deriv {F P f : ℝ → ℝ}
    (hF : ∀ x, HasDerivAt F (f x) x)
    (hP : ∀ x, HasDerivAt P (f x) x) :
    ∀ x, F x - F 0 = P x - P 0 := by
  let H : ℝ → ℝ := fun x => F x - P x
  have hH : ∀ x, HasDerivAt H 0 x := by
    intro x
    simpa [H] using (hF x).sub (hP x)
  have hdiff : Differentiable ℝ H := fun x => (hH x).differentiableAt
  have hzero : ∀ x, deriv H x = 0 := fun x => (hH x).deriv
  intro x
  have hc := is_const_of_deriv_eq_zero hdiff hzero x 0
  dsimp [H] at hc
  linarith

private theorem normalized_square_antiderivative {G : ℝ → ℝ}
    (hG : ∀ x, HasDerivAt G (x ^ 2) x) (hG0 : G 0 = 0) :
    G = fun x : ℝ => x ^ 3 / 3 := by
  funext x
  have hd := sub_eq_sub_of_same_deriv hG hasDerivAt_cube_div_three x
  rw [hG0] at hd
  norm_num at hd ⊢
  linarith

theorem gap1 :
    Antiderivatives (fun x => x * |x|) = NormalizedSignFamily := by
  ext F
  simp only [Antiderivatives, NormalizedSignFamily, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨(fun x : ℝ => x ^ 3 / 3), (fun x => hasDerivAt_cube_div_three x), by norm_num, F 0, ?_⟩
    intro x
    have hd := sub_eq_sub_of_same_deriv hF hasDerivAt_primitive x
    have hp0 : primitive 0 = 0 := by norm_num [primitive]
    have hFx : F x = primitive x + F 0 := by
      rw [hp0] at hd
      linarith
    calc
      F x = primitive x + F 0 := hFx
      _ = Real.sign x * (x ^ 3 / 3) + F 0 := by
        rw [← signPrimitive_eq_primitive x]
        rfl
  · rintro ⟨G, hG, hG0, C, hFC⟩
    have hGcube := normalized_square_antiderivative hG hG0
    have hFeq : F = fun x => primitive x + C := by
      funext x
      rw [hFC x, hGcube]
      simpa [signPrimitive] using
        congrArg (fun y : ℝ => y + C) (signPrimitive_eq_primitive x)
    intro x
    rw [hFeq]
    exact (hasDerivAt_primitive x).add_const C
theorem gap2 :
    NormalizedSignFamily = PrimitiveFamily signPrimitive := by
  ext F
  simp only [NormalizedSignFamily, Antiderivatives, PrimitiveFamily, Set.mem_setOf_eq]
  constructor
  · rintro ⟨G, hG, hG0, C, hFC⟩
    have hGcube := normalized_square_antiderivative hG hG0
    refine ⟨C, ?_⟩
    intro x
    rw [hFC x, hGcube]
    rfl
  · rintro ⟨C, hFC⟩
    refine ⟨(fun x : ℝ => x ^ 3 / 3), (fun x => hasDerivAt_cube_div_three x), by norm_num, C, ?_⟩
    intro x
    rw [hFC x]
    rfl
theorem gap3 :
    PrimitiveFamily signPrimitive = PrimitiveFamily primitive := by
  rw [show signPrimitive = primitive by
    funext x
    exact signPrimitive_eq_primitive x]
theorem gap4 :
    Antiderivatives (fun x => x * |x|) = PrimitiveFamily primitive := by
  rw [gap1, gap2, gap3]

end
end ProofGap.Exercise2167
