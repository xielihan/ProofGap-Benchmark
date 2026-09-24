import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2166

noncomputable section

def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def NormalizedSignFamily : Set (ℝ → ℝ) :=
  {F | ∃ G ∈ Antiderivatives (fun x => x),
    G 0 = 0 ∧ ∃ C : ℝ, ∀ x, F x = Real.sign x * G x + C}
def signPrimitive (x : ℝ) := Real.sign x * (1 / 2 * x ^ 2)
def primitive (x : ℝ) := x * |x| / 2

private theorem same_deriv_eq_add_sub_at_zero
    (u v d : ℝ → ℝ)
    (hu : ∀ x, HasDerivAt u (d x) x)
    (hv : ∀ x, HasDerivAt v (d x) x)
    (x : ℝ) :
    u x = v x + (u 0 - v 0) := by
  have hdiff : Differentiable ℝ (fun y => u y - v y) := by
    intro y
    exact (hu y).differentiableAt.sub (hv y).differentiableAt
  have hzero : ∀ y, deriv (fun z => u z - v z) y = 0 := by
    intro y
    simpa using ((hu y).sub (hv y)).deriv
  have hc := is_const_of_deriv_eq_zero hdiff hzero x 0
  linarith

theorem gap1 (x : ℝ) :
    |x| = Real.sign x * x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [abs_of_neg hx, Real.sign_of_neg hx]
    ring
  · subst x
    simp [Real.sign]
  · rw [abs_of_pos hx, Real.sign_of_pos hx]
    ring
theorem gap2 :
    Antiderivatives (fun x => |x|) = NormalizedSignFamily := by
  have hq : ∀ x, HasDerivAt (fun y : ℝ => 1 / 2 * y ^ 2) x x := by
    intro x
    convert (((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)) using 1 <;>
      norm_num <;> ring
  have hprim : ∀ x, HasDerivAt primitive |x| x := by
    intro x
    by_cases hx : x = 0
    · subst x
      rw [hasDerivAt_iff_tendsto_slope]
      simp only [abs_zero]
      have heq :
          slope primitive 0 =ᶠ[nhdsWithin 0 ({0} : Set ℝ)ᶜ]
            (fun y : ℝ => |y| / 2) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        have hy0 : y ≠ 0 := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
        simp only [slope, primitive, abs_zero, mul_zero, zero_div,
          vsub_eq_sub, sub_zero, smul_eq_mul]
        field_simp [hy0] <;> ring
      have hc : ContinuousAt (fun y : ℝ => |y| / 2) 0 :=
        (continuous_abs.div_const (2 : ℝ)).continuousAt
      change Tendsto (fun y : ℝ => |y| / 2) (nhds 0)
        (nhds ((fun y : ℝ => |y| / 2) 0)) at hc
      have ht :
          Tendsto (fun y : ℝ => |y| / 2) (nhds 0) (nhds 0) := by
        simpa only [abs_zero, zero_div] using hc
      exact (ht.mono_left inf_le_left).congr' heq.symm
    · have hm :=
        ((hasDerivAt_id x).mul (hasDerivAt_abs hx)).div_const (2 : ℝ)
      unfold primitive
      convert hm using 1
      rcases lt_or_gt_of_ne hx with hxneg | hxpos
      · have hnotpos : ¬ 0 < x := not_lt_of_ge hxneg.le
        simp [abs_of_neg hxneg, SignType.sign, hxneg, hx, hnotpos] <;> ring
      · have hnotneg : ¬ x < 0 := not_lt_of_ge hxpos.le
        simp [abs_of_pos hxpos, SignType.sign, hxpos, hx, hnotneg] <;> ring
  ext F
  change
    (∀ x, HasDerivAt F |x| x) ↔
      ∃ G, (∀ x, HasDerivAt G x x) ∧ G 0 = 0 ∧
        ∃ C : ℝ, ∀ x, F x = Real.sign x * G x + C
  constructor
  · intro hF
    refine ⟨(fun x : ℝ => 1 / 2 * x ^ 2), hq, by norm_num, F 0, ?_⟩
    intro x
    have hc := same_deriv_eq_add_sub_at_zero F primitive
      (fun y : ℝ => |y|) hF hprim x
    calc
      F x = primitive x + F 0 := by simpa [primitive] using hc
      _ = Real.sign x * (1 / 2 * x ^ 2) + F 0 := by
        rw [primitive, gap1 x]
        ring
  · rintro ⟨G, hG, hG0, C, hF⟩
    have hGq : ∀ x, G x = 1 / 2 * x ^ 2 := by
      intro x
      have hc := same_deriv_eq_add_sub_at_zero G
        (fun y : ℝ => 1 / 2 * y ^ 2) (fun y : ℝ => y) hG hq x
      simpa [hG0] using hc
    have hEq : ∀ y, F y = primitive y + C := by
      intro y
      calc
        F y = Real.sign y * G y + C := hF y
        _ = Real.sign y * (1 / 2 * y ^ 2) + C := by rw [hGq y]
        _ = primitive y + C := by
          rw [primitive, gap1 y]
          ring
    have hfun : F = fun y => primitive y + C := by
      funext y
      exact hEq y
    intro x
    rw [hfun]
    exact (hprim x).add_const C
theorem gap3 :
    NormalizedSignFamily = PrimitiveFamily signPrimitive := by
  have hq : ∀ x, HasDerivAt (fun y : ℝ => 1 / 2 * y ^ 2) x x := by
    intro x
    convert (((hasDerivAt_id x).pow 2).const_mul (1 / 2 : ℝ)) using 1 <;>
      norm_num <;> ring
  ext F
  change
    (∃ G, (∀ x, HasDerivAt G x x) ∧ G 0 = 0 ∧
      ∃ C : ℝ, ∀ x, F x = Real.sign x * G x + C) ↔
    ∃ C : ℝ, ∀ x, F x = signPrimitive x + C
  constructor
  · rintro ⟨G, hG, hG0, C, hF⟩
    have hGq : ∀ x, G x = 1 / 2 * x ^ 2 := by
      intro x
      have hc := same_deriv_eq_add_sub_at_zero G
        (fun y : ℝ => 1 / 2 * y ^ 2) (fun y : ℝ => y) hG hq x
      simpa [hG0] using hc
    refine ⟨C, ?_⟩
    intro x
    calc
      F x = Real.sign x * G x + C := hF x
      _ = Real.sign x * (1 / 2 * x ^ 2) + C := by rw [hGq x]
      _ = signPrimitive x + C := by rfl
  · rintro ⟨C, hF⟩
    refine ⟨(fun x : ℝ => 1 / 2 * x ^ 2), hq, by norm_num, C, ?_⟩
    simpa [signPrimitive] using hF
theorem gap4 :
    PrimitiveFamily signPrimitive = PrimitiveFamily primitive := by
  have hsp : ∀ x, signPrimitive x = primitive x := by
    intro x
    rw [signPrimitive, primitive, gap1 x]
    ring
  ext F
  change
    (∃ C : ℝ, ∀ x, F x = signPrimitive x + C) ↔
      ∃ C : ℝ, ∀ x, F x = primitive x + C
  constructor
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x
    rw [← hsp x]
    exact hF x
  · rintro ⟨C, hF⟩
    refine ⟨C, ?_⟩
    intro x
    rw [hsp x]
    exact hF x
theorem gap5 :
    Antiderivatives (fun x => |x|) = PrimitiveFamily primitive := by
  calc
    Antiderivatives (fun x => |x|) = NormalizedSignFamily := gap2
    _ = PrimitiveFamily signPrimitive := gap3
    _ = PrimitiveFamily primitive := gap4

end
end ProofGap.Exercise2166
