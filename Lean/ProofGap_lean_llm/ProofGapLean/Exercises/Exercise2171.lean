import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2171

open Filter

noncomputable section

def center : Set ℝ := Set.Ioo (-1) 1
def right : Set ℝ := Set.Ioi 1
def left : Set ℝ := Set.Iio (-1)
def integrand (x : ℝ) := max 1 (x ^ 2)
def AntiderivativesOn (s : Set ℝ) (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x ∈ s, HasDerivAt F (f x) x}
def PrimitiveFamilyOn (s : Set ℝ) (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ s, F x = p x + C}
def Antiderivatives (f : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∀ x, HasDerivAt F (f x) x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x, F x = p x + C}
def normalizedPrimitive (x : ℝ) :=
  if |x| ≤ 1 then x
  else x ^ 3 / 3 + 2 / 3 * Real.sign x

private theorem tendsto_ite_same
    (p : ℝ → Prop) [DecidablePred p] {f g : ℝ → ℝ}
    {l : Filter ℝ} {a : ℝ}
    (hf : Tendsto f l (nhds a)) (hg : Tendsto g l (nhds a)) :
    Tendsto (fun x => if p x then f x else g x) l (nhds a) := by
  rw [tendsto_def] at hf hg ⊢
  intro s hs
  filter_upwards [hf s hs, hg s hs] with x hfx hgx
  change (if p x then f x else g x) ∈ s
  by_cases hx : p x
  · simpa [hx] using hfx
  · simpa [hx] using hgx

private theorem cubic_hasDerivAt (x : ℝ) :
    HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
  convert
    ((((hasDerivAt_id x).mul (hasDerivAt_id x)).mul
      (hasDerivAt_id x)).div_const 3)
    using 1
  all_goals
    try funext y
    simp [id] <;> ring

private theorem hasDerivAt_ite_same
    (p : ℝ → Prop) [DecidablePred p] {f g : ℝ → ℝ} {f' x : ℝ}
    (hfg : f x = g x) (hf : HasDerivAt f f' x)
    (hg : HasDerivAt g f' x) :
    HasDerivAt (fun y => if p y then f y else g y) f' x := by
  rw [hasDerivAt_iff_tendsto_slope] at hf hg ⊢
  have heq : slope (fun y => if p y then f y else g y) x =
      fun y => if p y then slope f x y else slope g x y := by
    funext y
    unfold slope
    by_cases hx : p x <;> by_cases hy : p y <;> simp [hx, hy, hfg]
  rw [heq]
  exact tendsto_ite_same p hf hg

private theorem antiderivativesOn_eq_primitiveFamilyOn
    {s : Set ℝ} {f p : ℝ → ℝ} (hsopen : IsOpen s)
    (hsconn : IsPreconnected s) {a : ℝ} (ha : a ∈ s)
    (hp : ∀ x, HasDerivAt p (f x) x) :
    AntiderivativesOn s f = PrimitiveFamilyOn s p := by
  ext F
  simp only [AntiderivativesOn, PrimitiveFamilyOn, Set.mem_setOf_eq]
  constructor
  · intro hF
    refine ⟨F a - p a, ?_⟩
    have hder : ∀ x ∈ s, HasDerivAt (fun y => F y - p y) 0 x := by
      intro x hx
      simpa using (hF x hx).sub (hp x)
    have hdiff : DifferentiableOn ℝ (fun y => F y - p y) s := by
      intro x hx
      exact (hder x hx).differentiableAt.differentiableWithinAt
    have hzero : ∀ x ∈ s, deriv (fun y => F y - p y) x = 0 := by
      intro x hx
      exact (hder x hx).deriv
    intro x hx
    have hxy :=
      hsopen.is_const_of_deriv_eq_zero hsconn hdiff hzero hx ha
    linarith
  · rintro ⟨C, hC⟩ x hx
    have heq : F =ᶠ[nhds x] fun y => p y + C := by
      filter_upwards [hsopen.mem_nhds hx] with y hy
      exact hC y hy
    exact (heq.hasDerivAt_iff).2 ((hp x).add_const C)

private theorem normalizedPrimitive_hasDerivAt (x : ℝ) :
    HasDerivAt normalizedPrimitive (integrand x) x := by
  by_cases hin : |x| < 1
  · rcases (abs_lt.mp hin) with ⟨hxlo, hxhi⟩
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (by linarith) (by linarith)
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have heq : normalizedPrimitive =ᶠ[nhds x] fun y => y := by
      filter_upwards [Ioo_mem_nhds hxlo hxhi] with y hy
      have hay : |y| < 1 := abs_lt.mpr hy
      simp [normalizedPrimitive, le_of_lt hay]
    simpa [integrand, max_eq_left hx2] using
      (heq.hasDerivAt_iff).2 (hasDerivAt_id x)
  · by_cases hout : 1 < |x|
    · by_cases hxnonneg : 0 ≤ x
      · have hx1 : 1 < x := by simpa [abs_of_nonneg hxnonneg] using hout
        have hp : 0 < (x - 1) * (x + 1) :=
          mul_pos (by linarith) (by linarith)
        have hx2 : 1 ≤ x ^ 2 := by nlinarith
        let q : ℝ → ℝ := fun y => y ^ 3 / 3 + 2 / 3
        have heq : normalizedPrimitive =ᶠ[nhds x] q := by
          filter_upwards [Ioi_mem_nhds hx1] with y hy
          have hy0 : 0 < y := lt_trans zero_lt_one hy
          have hay : ¬ |y| ≤ 1 := by
            rw [abs_of_pos hy0]
            exact not_le.mpr hy
          simp [normalizedPrimitive, q, hay, Real.sign_of_pos hy0]
        have hq : HasDerivAt q (x ^ 2) x := by
          simpa [q] using (cubic_hasDerivAt x).add_const (2 / 3)
        simpa [integrand, max_eq_right hx2] using
          (heq.hasDerivAt_iff).2 hq
      · have hxneg : x < 0 := lt_of_not_ge hxnonneg
        have hx1 : x < -1 := by
          rw [abs_of_neg hxneg] at hout
          linarith
        have hp : 0 < (x - 1) * (x + 1) :=
          mul_pos_of_neg_of_neg (by linarith) (by linarith)
        have hx2 : 1 ≤ x ^ 2 := by nlinarith
        let q : ℝ → ℝ := fun y => y ^ 3 / 3 - 2 / 3
        have heq : normalizedPrimitive =ᶠ[nhds x] q := by
          filter_upwards [Iio_mem_nhds hx1] with y hy
          change y < -1 at hy
          have hy0 : y < 0 := lt_trans hy (by norm_num)
          have hay : ¬ |y| ≤ 1 := by
            rw [abs_of_neg hy0]
            exact not_le.mpr (by linarith)
          simp [normalizedPrimitive, q, hay, Real.sign_of_neg hy0]
          ring
        have hq : HasDerivAt q (x ^ 2) x := by
          simpa [q] using (cubic_hasDerivAt x).sub_const (2 / 3)
        simpa [integrand, max_eq_right hx2] using
          (heq.hasDerivAt_iff).2 hq
    · have habs : |x| = 1 := by linarith
      rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with hx | hx
      · subst x
        let q : ℝ → ℝ := fun y => y ^ 3 / 3 + 2 / 3 * Real.sign y
        have heq : q =ᶠ[nhds 1] fun y => y ^ 3 / 3 + 2 / 3 := by
          filter_upwards [Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
          simp [q, Real.sign_of_pos hy]
        have hq : HasDerivAt q 1 1 := by
          apply (heq.hasDerivAt_iff).2
          simpa using (cubic_hasDerivAt 1).add_const (2 / 3)
        have hfg : (1 : ℝ) = q 1 := by
          norm_num [q, Real.sign_of_pos]
        have hd := hasDerivAt_ite_same
          (p := fun y : ℝ => |y| ≤ 1) hfg (hasDerivAt_id 1) hq
        simpa [normalizedPrimitive, q, integrand] using hd
      · subst x
        let q : ℝ → ℝ := fun y => y ^ 3 / 3 + 2 / 3 * Real.sign y
        have heq : q =ᶠ[nhds (-1)] fun y => y ^ 3 / 3 - 2 / 3 := by
          filter_upwards [Iio_mem_nhds (show (-1 : ℝ) < 0 by norm_num)] with y hy
          simp [q, Real.sign_of_neg hy]
          ring
        have hq : HasDerivAt q 1 (-1) := by
          apply (heq.hasDerivAt_iff).2
          simpa using (cubic_hasDerivAt (-1)).sub_const (2 / 3)
        have hfg : (-1 : ℝ) = q (-1) := by
          norm_num [q, Real.sign_of_neg]
        have hd := hasDerivAt_ite_same
          (p := fun y : ℝ => |y| ≤ 1) hfg (hasDerivAt_id (-1)) hq
        simpa [normalizedPrimitive, q, integrand] using hd

theorem gap1 :
    AntiderivativesOn center integrand =
      AntiderivativesOn center (fun _ => 1) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    change -1 < x ∧ x < 1 at hx
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (by linarith [hx.2]) (by linarith [hx.1])
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    simpa [integrand, max_eq_left hx2] using
      h x (by simpa [center] using hx)
  · intro h x hx
    change -1 < x ∧ x < 1 at hx
    have hp : 0 < (1 - x) * (1 + x) :=
      mul_pos (by linarith [hx.2]) (by linarith [hx.1])
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    simpa [integrand, max_eq_left hx2] using
      h x (by simpa [center] using hx)
theorem gap2 :
    AntiderivativesOn center (fun _ => 1) =
      PrimitiveFamilyOn center (fun x => x) := by
  exact antiderivativesOn_eq_primitiveFamilyOn
    (s := center) (f := fun _ => 1) (p := fun x => x) (a := 0)
    (by simpa [center] using
      (isOpen_Ioo : IsOpen (Set.Ioo (-1 : ℝ) 1)))
    (by simpa [center] using
      (isPreconnected_Ioo : IsPreconnected (Set.Ioo (-1 : ℝ) 1)))
    (by norm_num [center])
    (fun x => hasDerivAt_id x)
theorem gap3 :
    AntiderivativesOn center integrand =
      PrimitiveFamilyOn center (fun x => x) := by
  rw [gap1, gap2]
theorem gap4 :
    AntiderivativesOn right integrand =
      AntiderivativesOn right (fun x => x ^ 2) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    change 1 < x at hx
    have hp : 0 < (x - 1) * (x + 1) :=
      mul_pos (by linarith) (by linarith)
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    simpa [integrand, max_eq_right hx2] using
      h x (by simpa [right] using hx)
  · intro h x hx
    change 1 < x at hx
    have hp : 0 < (x - 1) * (x + 1) :=
      mul_pos (by linarith) (by linarith)
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    simpa [integrand, max_eq_right hx2] using
      h x (by simpa [right] using hx)
theorem gap5 :
    AntiderivativesOn right (fun x => x ^ 2) =
      PrimitiveFamilyOn right (fun x => x ^ 3 / 3) := by
  exact antiderivativesOn_eq_primitiveFamilyOn
    (s := right) (f := fun x => x ^ 2) (p := fun x => x ^ 3 / 3) (a := 2)
    (by simpa [right] using
      (isOpen_Ioi : IsOpen (Set.Ioi (1 : ℝ))))
    (by simpa [right] using
      (isPreconnected_Ioi : IsPreconnected (Set.Ioi (1 : ℝ))))
    (by norm_num [right])
    cubic_hasDerivAt
theorem gap6 :
    AntiderivativesOn right integrand =
      PrimitiveFamilyOn right (fun x => x ^ 3 / 3) := by
  rw [gap4, gap5]
theorem gap7 :
    AntiderivativesOn left integrand =
      AntiderivativesOn left (fun x => x ^ 2) := by
  ext F
  simp only [AntiderivativesOn, Set.mem_setOf_eq]
  constructor
  · intro h x hx
    change x < -1 at hx
    have hp : 0 < (x - 1) * (x + 1) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    simpa [integrand, max_eq_right hx2] using
      h x (by simpa [left] using hx)
  · intro h x hx
    change x < -1 at hx
    have hp : 0 < (x - 1) * (x + 1) :=
      mul_pos_of_neg_of_neg (by linarith) (by linarith)
    have hx2 : 1 ≤ x ^ 2 := by nlinarith
    simpa [integrand, max_eq_right hx2] using
      h x (by simpa [left] using hx)
theorem gap8 :
    AntiderivativesOn left (fun x => x ^ 2) =
      PrimitiveFamilyOn left (fun x => x ^ 3 / 3) := by
  exact antiderivativesOn_eq_primitiveFamilyOn
    (s := left) (f := fun x => x ^ 2) (p := fun x => x ^ 3 / 3) (a := -2)
    (by simpa [left] using
      (isOpen_Iio : IsOpen (Set.Iio (-1 : ℝ))))
    (by simpa [left] using
      (isPreconnected_Iio : IsPreconnected (Set.Iio (-1 : ℝ))))
    (by norm_num [left])
    cubic_hasDerivAt
theorem gap9 :
    AntiderivativesOn left integrand =
      PrimitiveFamilyOn left (fun x => x ^ 3 / 3) := by
  rw [gap7, gap8]
theorem gap10 :
    normalizedPrimitive 1 = 1 := by
  norm_num [normalizedPrimitive]
theorem gap11 :
    Tendsto normalizedPrimitive (nhdsWithin 1 (Set.Ioi 1))
      (nhds (normalizedPrimitive 1)) := by
  exact
    (normalizedPrimitive_hasDerivAt 1).continuousAt.tendsto.mono_left
      inf_le_left
theorem gap12 :
    Tendsto normalizedPrimitive (nhdsWithin 1 (Set.Ioi 1)) (nhds 1) := by
  simpa [gap10] using gap11
theorem gap13 :
    ∃ C₁ : ℝ, 1 = 1 + C₁ := by
  refine ⟨0, ?_⟩
  norm_num
theorem gap14 :
    ∃ C₁ C₂ : ℝ, 1 + C₁ = 1 / 3 + C₂ := by
  refine ⟨0, 2 / 3, ?_⟩
  norm_num
theorem gap15 :
    ∃ C₂ : ℝ, 1 = 1 / 3 + C₂ := by
  refine ⟨2 / 3, ?_⟩
  norm_num
theorem gap16 :
    ∃ C₁ : ℝ, C₁ = 0 := by
  exact ⟨0, rfl⟩
theorem gap17 :
    ∃ C₂ : ℝ, C₂ = 2 / 3 := by
  exact ⟨2 / 3, rfl⟩
theorem gap18 :
    Tendsto normalizedPrimitive (nhds (-1))
      (nhds (normalizedPrimitive (-1))) := by
  exact (normalizedPrimitive_hasDerivAt (-1)).continuousAt.tendsto
theorem gap19 :
    ∃ C₃ : ℝ, -1 = -1 / 3 + C₃ := by
  refine ⟨-2 / 3, ?_⟩
  norm_num
theorem gap20 :
    ∃ C₃ : ℝ, C₃ = -2 / 3 := by
  exact ⟨-2 / 3, rfl⟩
theorem gap21 :
    ∀ x, normalizedPrimitive x =
      if |x| ≤ 1 then x
      else x ^ 3 / 3 + 2 / 3 * Real.sign x := by
  intro x
  rfl
theorem gap22 :
    Antiderivatives integrand = PrimitiveFamily normalizedPrimitive := by
  simpa [Antiderivatives, PrimitiveFamily, AntiderivativesOn,
    PrimitiveFamilyOn] using
    (antiderivativesOn_eq_primitiveFamilyOn
      (s := Set.univ) (f := integrand) (p := normalizedPrimitive) (a := 0)
      (isOpen_univ : IsOpen (Set.univ : Set ℝ))
      (isPreconnected_univ : IsPreconnected (Set.univ : Set ℝ))
      (by simp)
      normalizedPrimitive_hasDerivAt)

end
end ProofGap.Exercise2171
