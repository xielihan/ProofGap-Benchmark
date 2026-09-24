import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

namespace ProofGap.Exercise3087

noncomputable section

open Filter
open scoped BigOperators Topology

def SummableFromOne (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 1))

def tangentTransform (alpha : ℕ → ℝ) (n : ℕ) : ℝ :=
  Real.tan (Real.pi / 4 + alpha n)

def transformedTerm (alpha : ℕ → ℝ) (n : ℕ) : ℝ :=
  tangentTransform alpha n - 1

def tangentRemainder (alpha : ℕ → ℝ) (n : ℕ) : ℝ :=
  transformedTerm alpha n - 2 * alpha n

def tangentPartialProduct (alpha : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, (tangentTransform alpha i)

def NonzeroConvergentTangentProduct (alpha : ℕ → ℝ) : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧
    Tendsto (tangentPartialProduct alpha) atTop (𝓝 P)

private theorem abs_tan_lt_one_of_abs_lt_pi_div_four {x : ℝ}
    (hx : |x| < Real.pi / 4) :
    |Real.tan x| < 1 := by
  rcases abs_lt.mp hx with ⟨hxl, hxu⟩
  have hlo : -1 < Real.tan x := by
    have h := Real.tan_lt_tan_of_lt_of_lt_pi_div_two
      (x := -(Real.pi / 4)) (y := x)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hxl
    simpa [Real.tan_neg, Real.tan_pi_div_four] using h
  have hhi : Real.tan x < 1 := by
    have h := Real.tan_lt_tan_of_lt_of_lt_pi_div_two
      (x := x) (y := Real.pi / 4)
      (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]) hxu
    simpa [Real.tan_pi_div_four] using h
  exact abs_lt.mpr ⟨hlo, hhi⟩

private def tangentRemainderFn (x : ℝ) : ℝ :=
  Real.tan (Real.pi / 4 + x) - 1 - 2 * x

private theorem tangentRemainderFn_hasDerivAt :
    HasDerivAt tangentRemainderFn 0 0 := by
  have hcos : Real.cos (Real.pi / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  have hinner :
      HasDerivAt (fun x : ℝ => Real.pi / 4 + x) 1 0 := by
    simpa using
      (hasDerivAt_id (𝕜 := ℝ) 0).const_add (Real.pi / 4)
  have houter :
      HasDerivAt Real.tan (1 / Real.cos (Real.pi / 4) ^ 2)
        ((fun x : ℝ => Real.pi / 4 + x) 0) := by
    simpa using Real.hasDerivAt_tan hcos
  have htan0 := houter.comp 0 hinner
  have htan :
      HasDerivAt (fun x : ℝ => Real.tan (Real.pi / 4 + x)) 2 0 := by
    convert htan0 using 1
    rw [Real.cos_pi_div_four]
    have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by
      rw [Real.sq_sqrt]
      norm_num
    field_simp
    nlinarith
  have hlinear :
      HasDerivAt (fun x : ℝ => 2 * x) 2 0 := by
    convert (hasDerivAt_const (x := 0) (2 : ℝ)).mul
      (hasDerivAt_id (𝕜 := ℝ) 0) using 1 <;> norm_num
  simpa [tangentRemainderFn] using
    (htan.sub (hasDerivAt_const (x := 0) (1 : ℝ))).sub hlinear

/--
Exercise 3087, gap 1; boundedness alone does not imply
series convergence, so include the missing summability premise.
-/
theorem gap1 (alpha : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → |alpha n| < Real.pi / 4)
    (hsum : SummableFromOne alpha) :
    SummableFromOne alpha := by
  exact hsum

/-- Exercise 3087, gap 2. -/
theorem gap2 (alpha : ℕ → ℝ) (hsum : SummableFromOne alpha) :
    Tendsto alpha atTop (𝓝 0) := by
  apply Summable.tendsto_atTop_zero
  exact (summable_nat_add_iff 1).mp hsum

/-- Exercise 3087, gap 3; restrict to the bounded positive indices. -/
theorem gap3 (alpha : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → |alpha n| < Real.pi / 4) :
    ∀ n : ℕ, 1 ≤ n →
      tangentTransform alpha n =
        (1 + Real.tan (alpha n)) / (1 - Real.tan (alpha n)) := by
  intro n hn
  have hcosq : Real.cos (Real.pi / 4) ≠ 0 := by
    rw [Real.cos_pi_div_four]
    positivity
  have ha := (abs_lt.mp (hbound n hn))
  have hcosa : Real.cos (alpha n) ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  unfold tangentTransform
  rw [Real.tan_add'
    ⟨Real.cos_ne_zero_iff.mp hcosq, Real.cos_ne_zero_iff.mp hcosa⟩,
    Real.tan_pi_div_four]
  ring

/-- Exercise 3087, gap 4; replace the ellipsis by an exact tsum. -/
theorem gap4 (alpha : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → |alpha n| < Real.pi / 4) :
    ∀ n : ℕ, 1 ≤ n →
      tangentTransform alpha n =
        1 + 2 * (∑' k : ℕ, (Real.tan (alpha n)) ^ (k + 1)) := by
  intro n hn
  let t := Real.tan (alpha n)
  have ht : |t| < 1 :=
    abs_tan_lt_one_of_abs_lt_pi_div_four (hbound n hn)
  have hsum :
      (∑' k : ℕ, t ^ (k + 1)) = t / (1 - t) := by
    calc
      (∑' k : ℕ, t ^ (k + 1)) =
          ∑' k : ℕ, t * t ^ k := by
        apply tsum_congr
        intro k
        rw [pow_succ']
      _ = t * ∑' k : ℕ, t ^ k := by
        rw [tsum_mul_left]
      _ = t * (1 - t)⁻¹ := by
        rw [tsum_geometric_of_norm_lt_one]
        simpa [Real.norm_eq_abs] using ht
      _ = t / (1 - t) := by rw [div_eq_mul_inv]
  rw [gap3 alpha hbound n hn]
  change (1 + t) / (1 - t) =
    1 + 2 * (∑' k : ℕ, t ^ (k + 1))
  rw [hsum]
  have hne : 1 - t ≠ 0 := by
    exact sub_ne_zero.mpr (ne_of_gt (abs_lt.mp ht).2)
  field_simp [hne]
  ring

/-- Exercise 3087, gap 5; state little-o as a function relation. -/
theorem gap5 (alpha : ℕ → ℝ) (hsum : SummableFromOne alpha) :
    tangentRemainder alpha =o[atTop] alpha := by
  have ha : Tendsto alpha atTop (𝓝 0) := gap2 alpha hsum
  have hlocal :
      tangentRemainderFn =o[𝓝 0] (fun x : ℝ => x) := by
    simpa [tangentRemainderFn] using
      tangentRemainderFn_hasDerivAt.isLittleO
  have hcomp := hlocal.comp_tendsto ha
  apply hcomp.congr
  · intro n
    rfl
  · intro n
    rfl

/--
Exercise 3087, gap 6; little-o alone does not preserve a
conditionally convergent series, so require summability of the remainder.
-/
theorem gap6 (alpha : ℕ → ℝ) (hsum : SummableFromOne alpha)
    (hrem : SummableFromOne (tangentRemainder alpha)) :
    SummableFromOne (transformedTerm alpha) := by
  unfold SummableFromOne at hsum hrem ⊢
  convert hrem.add (hsum.mul_left 2) using 1
  funext k
  unfold tangentRemainder transformedTerm
  ring

/--
Exercise 3087, gap 7; convergence alone does not imply
square summability, so require absolute summability of the transformed term.
-/
theorem gap7 (alpha : ℕ → ℝ)
    (habs : SummableFromOne (fun n => |transformedTerm alpha n|)) :
    SummableFromOne (fun n => (transformedTerm alpha n) ^ 2) := by
  unfold SummableFromOne at habs ⊢
  have htend :
      Tendsto (fun k : ℕ => |transformedTerm alpha (k + 1)|)
        atTop (𝓝 0) :=
    habs.tendsto_atTop_zero
  have hev :
      ∀ᶠ k : ℕ in atTop, |transformedTerm alpha (k + 1)| < 1 :=
    (tendsto_order.mp htend).2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat habs
  filter_upwards [hev] with k hk
  rw [Real.norm_eq_abs, abs_pow]
  have hnonneg : 0 ≤ |transformedTerm alpha (k + 1)| := abs_nonneg _
  nlinarith

/-- Exercise 3087, gap 8; use asymptotic equivalence to recover `alpha²`. -/
theorem gap8 (alpha : ℕ → ℝ) (hsum : SummableFromOne alpha)
    (hsq : SummableFromOne (fun n => (transformedTerm alpha n) ^ 2)) :
    SummableFromOne (fun n => (alpha n) ^ 2) := by
  unfold SummableFromOne at hsum hsq ⊢
  have habs :
      Summable (fun k : ℕ => ‖alpha (k + 1)‖) :=
    hsum.norm
  have htend :
      Tendsto (fun k : ℕ => ‖alpha (k + 1)‖) atTop (𝓝 0) :=
    habs.tendsto_atTop_zero
  have hev : ∀ᶠ k : ℕ in atTop, ‖alpha (k + 1)‖ < 1 :=
    (tendsto_order.mp htend).2 1 (by norm_num)
  apply Summable.of_norm_bounded_eventually_nat habs
  filter_upwards [hev] with k hk
  rw [norm_pow]
  have hnonneg : 0 ≤ ‖alpha (k + 1)‖ := norm_nonneg _
  nlinarith

/--
Exercise 3087, gap 9; a little-o bound is eventual, not
pointwise at every index.
-/
theorem gap9 (alpha r : ℕ → ℝ) (hr : r =o[atTop] alpha)
    (ha : Tendsto alpha atTop (𝓝 0)) :
    ∀ᶠ n in atTop, |alpha n * r n| ≤ |alpha n| := by
  have halower : ∀ᶠ n : ℕ in atTop, -1 < alpha n :=
    (tendsto_order.mp ha).1 (-1) (by norm_num)
  have haupper : ∀ᶠ n : ℕ in atTop, alpha n < 1 :=
    (tendsto_order.mp ha).2 1 (by norm_num)
  filter_upwards [hr.eventuallyLE, halower, haupper] with n hrn hlow hhigh
  simp only [Real.norm_eq_abs] at hrn
  have han : |alpha n| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  rw [abs_mul]
  calc
    |alpha n| * |r n| ≤ |alpha n| * |alpha n| :=
      mul_le_mul_of_nonneg_left hrn (abs_nonneg _)
    _ ≤ |alpha n| * 1 :=
      mul_le_mul_of_nonneg_left han (abs_nonneg _)
    _ = |alpha n| := mul_one _

/--
Exercise 3087, gap 10; the square of a little-o remainder
is controlled only eventually.
-/
theorem gap10 (alpha r : ℕ → ℝ) (hr : r =o[atTop] alpha)
    (ha : Tendsto alpha atTop (𝓝 0)) :
    ∀ᶠ n in atTop, |(r n) ^ 2| ≤ |alpha n| := by
  have halower : ∀ᶠ n : ℕ in atTop, -1 < alpha n :=
    (tendsto_order.mp ha).1 (-1) (by norm_num)
  have haupper : ∀ᶠ n : ℕ in atTop, alpha n < 1 :=
    (tendsto_order.mp ha).2 1 (by norm_num)
  filter_upwards [hr.eventuallyLE, halower, haupper] with n hrn hlow hhigh
  simp only [Real.norm_eq_abs] at hrn
  have han : |alpha n| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hsquare : |r n| ^ 2 ≤ |alpha n| ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hrn)
      (add_nonneg (abs_nonneg (r n)) (abs_nonneg (alpha n)))]
  rw [abs_pow]
  calc
    |r n| ^ 2 ≤ |alpha n| ^ 2 := hsquare
    _ ≤ |alpha n| := by
      nlinarith [abs_nonneg (alpha n)]

private theorem summableFromOne_tangentRemainder
    (alpha : ℕ → ℝ) (hsum : SummableFromOne alpha) :
    SummableFromOne (tangentRemainder alpha) := by
  have hr := gap5 alpha hsum
  have halpha : Summable alpha :=
    (summable_nat_add_iff 1).mp hsum
  have hrem : Summable (tangentRemainder alpha) :=
    summable_of_isBigO_nat halpha hr.isBigO
  exact (summable_nat_add_iff 1).mpr hrem

private theorem tangentTransform_pos (alpha : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → |alpha n| < Real.pi / 4)
    (n : ℕ) (hn : 1 ≤ n) :
    0 < tangentTransform alpha n := by
  rcases abs_lt.mp (hbound n hn) with ⟨hlower, hupper⟩
  unfold tangentTransform
  apply Real.tan_pos_of_pos_of_lt_pi_div_two
  · linarith [Real.pi_pos]
  · linarith [Real.pi_pos]

private theorem prod_range_shift_eq_tangentPartialProduct
    (alpha : ℕ → ℝ) (n : ℕ) :
    (∏ k ∈ Finset.range n, tangentTransform alpha (k + 1)) =
      tangentPartialProduct alpha n := by
  induction n with
  | zero =>
      simp [tangentPartialProduct]
  | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      unfold tangentPartialProduct
      rw [Finset.prod_Icc_succ_top (by omega)]

private theorem nonzeroConvergentTangentProduct_of_summable
    (alpha : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → |alpha n| < Real.pi / 4)
    (hsum : SummableFromOne alpha) :
    NonzeroConvergentTangentProduct alpha := by
  have hrem : SummableFromOne (tangentRemainder alpha) :=
    summableFromOne_tangentRemainder alpha hsum
  have htrans : SummableFromOne (transformedTerm alpha) :=
    gap6 alpha hsum hrem
  let u : ℕ → ℝ := fun k => transformedTerm alpha (k + 1)
  have hu : Summable u := by
    exact htrans
  have hunorm : Summable (fun k : ℕ => ‖u k‖) :=
    hu.norm
  have hmulti : Multipliable (fun k : ℕ => 1 + u k) :=
    multipliable_one_add_of_summable hunorm
  let P : ℝ := ∏' k : ℕ, (1 + u k)
  refine ⟨P, ?_, ?_⟩
  · dsimp [P]
    apply tprod_one_add_ne_zero_of_summable
    · intro k
      have hpos := tangentTransform_pos alpha hbound (k + 1) (by omega)
      simpa [u, transformedTerm] using ne_of_gt hpos
    · exact hunorm
  · have ht := hmulti.tendsto_prod_tprod_nat
    have hfun :
        (fun n : ℕ => ∏ k ∈ Finset.range n, (1 + u k)) =
          tangentPartialProduct alpha := by
      funext n
      calc
        (∏ k ∈ Finset.range n, (1 + u k)) =
            ∏ k ∈ Finset.range n, tangentTransform alpha (k + 1) := by
          apply Finset.prod_congr rfl
          intro k hk
          simp only [u, transformedTerm]
          ring
        _ = tangentPartialProduct alpha n :=
          prod_range_shift_eq_tangentPartialProduct alpha n
    dsimp [P]
    rw [← hfun]
    exact ht

/--
Exercise 3087, gap 11; apply convergence to the cutoff
sequence and retain the square-summability established in the source chain.
-/
theorem gap11 (alpha : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → |alpha n| < Real.pi / 4)
    (hsum : SummableFromOne alpha)
    (hsq : SummableFromOne (fun n => (alpha n) ^ 2)) :
    NonzeroConvergentTangentProduct alpha := by
  exact nonzeroConvergentTangentProduct_of_summable alpha hbound hsum

/--
Exercise 3087, gap 12; absolute summability is a direct
sufficient condition for the tangent partial products.
-/
theorem gap12 (alpha : ℕ → ℝ)
    (hbound : ∀ n : ℕ, 1 ≤ n → |alpha n| < Real.pi / 4)
    (habs : SummableFromOne (fun n => |alpha n|)) :
    NonzeroConvergentTangentProduct alpha := by
  have hsum : SummableFromOne alpha := by
    unfold SummableFromOne at habs ⊢
    apply Summable.of_norm
    simpa only [Real.norm_eq_abs] using habs
  exact nonzeroConvergentTangentProduct_of_summable alpha hbound hsum

end

end ProofGap.Exercise3087
