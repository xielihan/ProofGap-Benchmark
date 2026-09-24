import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise2799_2

noncomputable section

open scoped BigOperators
open scoped Topology

def term (n : ℕ) (x : ℝ) : ℝ :=
  |x| / ((n : ℝ) ^ 2 + x ^ 2)

def phiTerm (n : ℕ) (x : ℝ) : ℝ :=
  1 / ((n : ℝ) ^ 2 + x ^ 2)

def phiDerivativeTerm (n : ℕ) (x : ℝ) : ℝ :=
  -2 * x / (((n : ℝ) ^ 2 + x ^ 2) ^ 2)

def f (x : ℝ) : ℝ :=
  ∑' n : ℕ, term (n + 1) x

def phi (x : ℝ) : ℝ :=
  ∑' n : ℕ, phiTerm (n + 1) x

def seriesDomain : Set ℝ :=
  {x | Summable (fun n : ℕ => term (n + 1) x)}

def SeriesUniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s,
    |(∑ k ∈ Finset.range (n + 1), u k x) - g x| < ε

private theorem inv_square_shift_summable :
    Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 2)) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).2 h

private theorem seriesUniformlyConvergesOn_of_hasSumUniformlyOn
    (u : ℕ → ℝ → ℝ) (s : Set ℝ)
    (h : HasSumUniformlyOn u (fun x => ∑' n : ℕ, u n x) s) :
    SeriesUniformlyConvergesOn u s (fun x => ∑' n : ℕ, u n x) := by
  have hu := h.tendstoUniformlyOn_finsetRange
  rw [Metric.tendstoUniformlyOn_iff] at hu
  intro ε hε
  rcases Filter.eventually_atTop.1 (hu ε hε) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn x hx
  have hdist := hN (n + 1) (by omega) x hx
  simpa [Real.dist_eq, abs_sub_comm] using hdist

theorem gap1 :
    Summable (fun n : ℕ => term (n + 1) 0) := by
  simpa [term] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))

theorem gap2 (x : ℝ) (n : ℕ) (hx : x ≠ 0) (hn : 1 ≤ n) :
    (term n x) / (1 / (n : ℝ) ^ 2) =
      ((n : ℝ) ^ 2 / ((n : ℝ) ^ 2 + x ^ 2)) * |x| := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden : (n : ℝ) ^ 2 + x ^ 2 ≠ 0 := by positivity
  unfold term
  field_simp [hnpos.ne', hden]
  <;> ring

theorem gap3 (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (((n : ℝ) + 1) ^ 2 /
          (((n : ℝ) + 1) ^ 2 + x ^ 2)) * |x|)
      atTop (𝓝 |x|) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    have hnat : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
      Filter.tendsto_add_atTop_nat 1
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hnat
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (tendsto_inv_atTop_zero :
      Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0)).comp hcast
  have hsmall : Tendsto
      (fun n : ℕ => x ^ 2 * (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hinv.pow 2)
  have hden : Tendsto
      (fun n : ℕ => 1 + x ^ 2 * (((n : ℝ) + 1)⁻¹) ^ 2) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.add hsmall
  have hlim := (hden.inv₀ (by norm_num : (1 : ℝ) ≠ 0)).mul_const |x|
  have hlim' : Tendsto
      (fun n : ℕ => (1 + x ^ 2 * (((n : ℝ) + 1)⁻¹) ^ 2)⁻¹ * |x|)
      atTop (𝓝 |x|) := by
    simpa using hlim
  apply (Filter.tendsto_congr' ?_).2 hlim'
  filter_upwards with n
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]
  <;> ring

theorem gap4 (x : ℝ) :
    Tendsto
      (fun n : ℕ =>
        (term (n + 1) x) / (1 / (((n : ℝ) + 1) ^ 2)))
      atTop (𝓝 |x|) := by
  by_cases hx : x = 0
  · subst x
    simpa [term] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · apply (Filter.tendsto_congr' (Filter.Eventually.of_forall fun n => ?_)).2 (gap3 x)
    simpa [Nat.cast_add, Nat.cast_one] using gap2 x (n + 1) hx (by omega)

theorem gap5 (x : ℝ) :
    Summable (fun n : ℕ => term (n + 1) x) := by
  apply Summable.of_norm_bounded (inv_square_shift_summable.mul_left |x|)
  intro n
  have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hdenpos : 0 < (((n + 1 : ℕ) : ℝ) ^ 2 + x ^ 2) := by positivity
  rw [Real.norm_eq_abs]
  unfold term
  rw [abs_of_nonneg (div_nonneg (abs_nonneg _) hdenpos.le)]
  have hle :
      |x| / ((((n + 1 : ℕ) : ℝ) ^ 2) + x ^ 2) ≤
        |x| / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    apply div_le_div_of_nonneg_left (abs_nonneg x) (sq_pos_of_pos hnpos)
    exact le_add_of_nonneg_right (sq_nonneg x)
  simpa [div_eq_mul_inv, mul_assoc] using hle

theorem gap6 :
    seriesDomain = Set.univ := by
  ext x
  simp [seriesDomain, gap5 x]

theorem gap7 (x : ℝ) :
    Summable (fun n : ℕ => phiTerm (n + 1) x) := by
  apply Summable.of_norm_bounded inv_square_shift_summable
  intro n
  have hnpos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hdenpos : 0 < (((n + 1 : ℕ) : ℝ) ^ 2 + x ^ 2) := by positivity
  rw [Real.norm_eq_abs]
  unfold phiTerm
  rw [abs_of_nonneg (by positivity : 0 ≤ 1 / (((n + 1 : ℕ) : ℝ) ^ 2 + x ^ 2))]
  exact div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hnpos)
    (le_add_of_nonneg_right (sq_nonneg x))

theorem gap8 (x : ℝ) :
    f x = |x| * phi x := by
  unfold f phi
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold term phiTerm
  ring

theorem gap9 (x₀ : ℝ) :
    ∃ l : ℝ, 0 < l := by
  exact ⟨1, by norm_num⟩

theorem gap10 (x₀ : ℝ) :
    ∃ l : ℝ, -l < x₀ := by
  refine ⟨|x₀| + 1, ?_⟩
  linarith [neg_abs_le x₀]

theorem gap11 (x₀ : ℝ) :
    ∃ l : ℝ, x₀ < l := by
  refine ⟨|x₀| + 1, ?_⟩
  linarith [le_abs_self x₀]

theorem gap12 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) :
    HasDerivAt (phiTerm n) (phiDerivativeTerm n x) x ∧
      |deriv (phiTerm n) x| =
        |-2 * x / (((n : ℝ) ^ 2 + x ^ 2) ^ 2)| := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have hden : (n : ℝ) ^ 2 + x ^ 2 ≠ 0 := by positivity
  have hderiv : HasDerivAt (phiTerm n) (phiDerivativeTerm n x) x := by
    have hdenDeriv : HasDerivAt
        (fun y : ℝ => (n : ℝ) ^ 2 + y ^ 2) (2 * x) x := by
      convert (hasDerivAt_const x ((n : ℝ) ^ 2)).add
        ((hasDerivAt_id x).pow 2) using 1 <;> simp only [id_eq] <;> ring
    have hquot := (hasDerivAt_const x (1 : ℝ)).div hdenDeriv hden
    unfold phiTerm phiDerivativeTerm
    convert hquot using 1
    <;> ring
  refine ⟨hderiv, ?_⟩
  rw [hderiv.deriv]
  rfl

theorem gap13 (l x : ℝ) (n : ℕ) (hl : 0 ≤ l)
    (hx : x ∈ Set.Icc (-l) l) (hn : 1 ≤ n) :
    |-2 * x / (((n : ℝ) ^ 2 + x ^ 2) ^ 2)| ≤
      2 * l / (n : ℝ) ^ 4 := by
  have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  have habsx : |x| ≤ l := abs_le.2 ⟨by linarith [hx.1], hx.2⟩
  have hnum : 2 * |x| ≤ 2 * l := by linarith
  have hden : (n : ℝ) ^ 4 ≤ ((n : ℝ) ^ 2 + x ^ 2) ^ 2 := by
    have hnx : 0 ≤ (n : ℝ) ^ 2 * x ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    have hx4 : 0 ≤ x ^ 2 * x ^ 2 := mul_self_nonneg _
    nlinarith
  have habs2 : |(2 : ℝ)| = 2 := abs_of_pos (by norm_num)
  rw [abs_div, abs_mul, abs_neg, habs2,
    abs_of_nonneg (sq_nonneg ((n : ℝ) ^ 2 + x ^ 2))]
  apply div_le_div₀ (mul_nonneg (by norm_num) hl) hnum (by positivity) hden

theorem gap14 (l x : ℝ) (n : ℕ) (hl : 0 ≤ l)
    (hx : x ∈ Set.Icc (-l) l) (hn : 1 ≤ n) :
    |deriv (phiTerm n) x| ≤ 2 * l / (n : ℝ) ^ 4 := by
  rw [(gap12 n x hn).2]
  exact gap13 l x n hl hx hn

theorem gap15 (l : ℝ) :
    Summable (fun n : ℕ => 2 * l / (((n : ℝ) + 1) ^ 4)) := by
  have hbase : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ) ^ 4)) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 4) :=
      Real.summable_one_div_nat_pow.mpr (by norm_num)
    exact (summable_nat_add_iff 1).2 h
  simpa [Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_assoc] using
    hbase.mul_left (2 * l)

theorem gap16 (l : ℝ) (hl : 0 ≤ l) :
    SeriesUniformlyConvergesOn
      (fun n x => phiDerivativeTerm (n + 1) x)
      (Set.Icc (-l) l)
      (fun x => ∑' n : ℕ, phiDerivativeTerm (n + 1) x) := by
  apply seriesUniformlyConvergesOn_of_hasSumUniformlyOn
  apply HasSumUniformlyOn.of_norm_le_summable (gap15 l)
  intro n x hx
  rw [Real.norm_eq_abs]
  unfold phiDerivativeTerm
  simpa [Nat.cast_add, Nat.cast_one] using
    gap13 l x (n + 1) hl hx (by omega)

theorem gap17 (x₀ : ℝ) :
    DifferentiableAt ℝ phi x₀ := by
  let l : ℝ := |x₀| + 1
  have hl : 0 ≤ l := by dsimp [l]; positivity
  have hx₀ : x₀ ∈ Set.Ioo (-l) l := by
    constructor <;> dsimp [l] <;> linarith [neg_abs_le x₀, le_abs_self x₀]
  have hzero : (0 : ℝ) ∈ Set.Ioo (-l) l := by
    have hlpos : 0 < l := by dsimp [l]; positivity
    exact ⟨by linarith, hlpos⟩
  have hderiv : ∀ n y, y ∈ Set.Ioo (-l) l →
      HasDerivAt (phiTerm (n + 1)) (phiDerivativeTerm (n + 1) y) y := by
    intro n y hy
    exact (gap12 (n + 1) y (by omega)).1
  have hbound : ∀ n y, y ∈ Set.Ioo (-l) l →
      ‖phiDerivativeTerm (n + 1) y‖ ≤
        2 * l / (((n : ℝ) + 1) ^ 4) := by
    intro n y hy
    rw [Real.norm_eq_abs]
    unfold phiDerivativeTerm
    simpa [Nat.cast_add, Nat.cast_one] using
      gap13 l y (n + 1) hl ⟨hy.1.le, hy.2.le⟩ (by omega)
  have hd := hasDerivAt_tsum_of_isPreconnected (gap15 l) isOpen_Ioo
    isPreconnected_Ioo hderiv hbound hzero (gap7 0) hx₀
  simpa [phi] using hd.differentiableAt

theorem gap18 (x : ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun y : ℝ => |y|) x := by
  exact differentiableAt_abs hx

theorem gap19 :
    ¬DifferentiableAt ℝ (fun y : ℝ => |y|) 0 := by
  exact not_differentiableAt_abs_zero

theorem gap20 (x : ℝ) :
    0 < phi x := by
  unfold phi
  exact (gap7 x).tsum_pos
    (fun n => by unfold phiTerm; positivity) 0 (by unfold phiTerm; positivity)

theorem gap21 (x : ℝ) (hx : x ≠ 0) :
    DifferentiableAt ℝ f x := by
  have hfeq : f = fun y : ℝ => |y| * phi y := by
    funext y
    exact gap8 y
  rw [hfeq]
  exact (gap18 x hx).mul (gap17 x)

theorem gap22 :
    ¬DifferentiableAt ℝ f 0 := by
  intro hf
  have hquot := hf.div (gap17 0) (ne_of_gt (gap20 0))
  have hquotEq : f / phi = fun x : ℝ => |x| := by
    funext x
    change f x / phi x = |x|
    rw [gap8 x]
    exact mul_div_cancel_right₀ |x| (ne_of_gt (gap20 x))
  rw [hquotEq] at hquot
  exact gap19 hquot

theorem gap23 :
    {x : ℝ | DifferentiableAt ℝ f x} = {x : ℝ | x ≠ 0} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hdiff hx
    subst x
    exact gap22 hdiff
  · exact gap21 x

end

end ProofGap.Exercise2799_2
