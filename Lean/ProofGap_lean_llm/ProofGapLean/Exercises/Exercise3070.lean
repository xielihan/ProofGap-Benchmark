import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3070

noncomputable section

open Filter
open scoped BigOperators Topology

def base (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 2 - 1) / ((n : ℝ) ^ 2 + 1)

def rewrittenBase (n : ℕ) : ℝ :=
  1 - 2 / ((n : ℝ) ^ 2 + 1)

def term (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (base n) p

def rewrittenTerm (p : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (rewrittenBase n) p

def partialProduct (p : ℝ) (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 2 n, term p i

def NonzeroConvergentProduct (p : ℝ) : Prop :=
  ∃ P : ℝ, P ≠ 0 ∧ Tendsto (partialProduct p) atTop (𝓝 P)

def sumFromTwo (f : ℕ → ℝ) : ℝ :=
  ∑' k : ℕ, f (k + 2)

def SummableFromTwo (f : ℕ → ℝ) : Prop :=
  Summable (fun k : ℕ => f (k + 2))

/--
Exercise 3070, gap 1; distinguish the exponent `p` from
the source's overloaded sequence name.
-/
private theorem base_eq_rewrittenBase (n : ℕ) : base n = rewrittenBase n := by
  unfold base rewrittenBase
  have hden : (n : ℝ) ^ 2 + 1 ≠ 0 := by positivity
  field_simp [hden]
  ring

private theorem rewrittenBase_pos_of_two_le (n : ℕ) (hn : 2 ≤ n) :
    0 < rewrittenBase n := by
  rw [← base_eq_rewrittenBase]
  unfold base
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hnum : 0 < (n : ℝ) ^ 2 - 1 := by nlinarith
  have hden : 0 < (n : ℝ) ^ 2 + 1 := by nlinarith
  positivity

private theorem summable_log_rewrittenBase :
    SummableFromTwo (fun n => Real.log (rewrittenBase n)) := by
  unfold SummableFromTwo
  have hp : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := by
    simpa [one_div, Real.rpow_natCast] using
      (Real.summable_nat_rpow_inv (p := (2 : ℝ)) (by norm_num))
  have hpShift : Summable (fun k : ℕ => (1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2) := by
    exact hp.comp_injective (fun a b h => by omega)
  have hmajor : Summable (fun k : ℕ => 4 * ((1 : ℝ) / ((k + 2 : ℕ) : ℝ) ^ 2)) :=
    hpShift.mul_left 4
  refine Summable.of_norm_bounded hmajor ?_
  intro k
  let n : ℕ := k + 2
  let t : ℝ := (n : ℝ) ^ 2
  have hn : 2 ≤ n := by omega
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have ht : (4 : ℝ) ≤ t := by
    dsimp [t]
    nlinarith
  have ht0 : 0 < t := by nlinarith
  have htm1 : 0 < t - 1 := by nlinarith
  have hx : rewrittenBase n = (t - 1) / (t + 1) := by
    rw [← base_eq_rewrittenBase]
    rfl
  have hxpos : 0 < rewrittenBase n := rewrittenBase_pos_of_two_le n hn
  have hxle : rewrittenBase n ≤ 1 := by
    unfold rewrittenBase
    have hd : 0 < (n : ℝ) ^ 2 + 1 := by positivity
    have hquot : 0 ≤ 2 / ((n : ℝ) ^ 2 + 1) := by positivity
    linarith
  have hlognonpos : Real.log (rewrittenBase n) ≤ 0 :=
    Real.log_nonpos hxpos.le hxle
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hxpos)
  rw [Real.log_inv] at hlog
  have hinv : (rewrittenBase n)⁻¹ - 1 = 2 / (t - 1) := by
    rw [hx]
    field_simp
    ring
  rw [hinv] at hlog
  have hfrac : 2 / (t - 1) ≤ 4 / t := by
    apply (div_le_div_iff₀ htm1 ht0).2
    nlinarith
  have habs : |Real.log (rewrittenBase n)| ≤ 4 / t := by
    rw [abs_of_nonpos hlognonpos]
    exact hlog.trans hfrac
  dsimp [n, t] at habs ⊢
  simpa [Real.norm_eq_abs, div_eq_mul_inv] using habs

private theorem prod_Icc_two_eq_range_shift (f : ℕ → ℝ) (n : ℕ) :
    (∏ i ∈ Finset.Icc 2 n, f i) = ∏ k ∈ Finset.range (n - 1), f (k + 2) := by
  have hset : Finset.Icc 2 n = (Finset.range (n - 1)).image (fun k => k + 2) := by
    ext i
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hi
      refine ⟨i - 2, ?_, ?_⟩
      · omega
      · omega
    · rintro ⟨k, hk, rfl⟩
      omega
  rw [hset]
  exact Finset.prod_image (fun a _ b _ hab => Nat.add_right_cancel hab)

private theorem nonzeroConvergentProduct_all (p : ℝ) :
    NonzeroConvergentProduct p := by
  let f : ℕ → ℝ := fun k => p * Real.log (rewrittenBase (k + 2))
  have hslog := summable_log_rewrittenBase
  unfold SummableFromTwo at hslog
  have hsf : Summable f := by
    dsimp [f]
    exact hslog.mul_left p
  let P : ℝ := Real.exp (∑' k : ℕ, f k)
  have hrangeSets : Tendsto (fun m : ℕ => Finset.range m) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro s
    filter_upwards [eventually_ge_atTop (s.sup id + 1)] with m hm
    show s ⊆ Finset.range m
    intro x hx
    simp only [Finset.mem_range]
    have hxle : x ≤ s.sup id := Finset.le_sup (f := id) hx
    omega
  have hsumRange :
      Tendsto (fun m : ℕ => ∑ k ∈ Finset.range m, f k) atTop
        (𝓝 (∑' k : ℕ, f k)) :=
    hsf.hasSum.comp hrangeSets
  have hprod_exp (s : Finset ℕ) :
      (∏ k ∈ s, Real.exp (f k)) = Real.exp (∑ k ∈ s, f k) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih => simp [ha, ih, Real.exp_add]
  have hrange :
      Tendsto (fun m : ℕ => ∏ k ∈ Finset.range m, Real.exp (f k)) atTop (𝓝 P) := by
    have hexp : Tendsto Real.exp (𝓝 (∑' k : ℕ, f k)) (𝓝 P) := by
      exact Real.continuous_exp.continuousAt
    convert hexp.comp hsumRange using 1
    funext m
    exact hprod_exp (Finset.range m)
  have hsub : Tendsto (fun n : ℕ => n - 1) atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro b
    filter_upwards [eventually_ge_atTop (b + 1)] with n hn
    omega
  refine ⟨P, Real.exp_ne_zero _, ?_⟩
  refine (tendsto_congr' ?_).2 (hrange.comp hsub)
  filter_upwards [eventually_ge_atTop 2] with n hn
  unfold partialProduct
  rw [prod_Icc_two_eq_range_shift]
  apply Finset.prod_congr rfl
  intro k hk
  have hk2 : 2 ≤ k + 2 := by omega
  have hpos := rewrittenBase_pos_of_two_le (k + 2) hk2
  have hbase := base_eq_rewrittenBase (k + 2)
  unfold term
  rw [hbase]
  calc
    Real.rpow (rewrittenBase (k + 2)) p =
        (rewrittenBase (k + 2)) ^ p := rfl
    _ = Real.exp (Real.log (rewrittenBase (k + 2)) * p) :=
      Real.rpow_def_of_pos hpos p
    _ = Real.exp (f k) := by simp [f, mul_comm]

theorem gap1 (p : ℝ) (u : ℕ → ℝ) (hu : ∀ n, u n = term p n)
    (hconv : NonzeroConvergentProduct p) :
    ∀ n : ℕ, 2 ≤ n → u n = rewrittenTerm p n := by
  intro n hn
  rw [hu n]
  unfold term rewrittenTerm
  rw [base_eq_rewrittenBase]

/-- Exercise 3070, gap 2; use exact sums and real powers. -/
theorem gap2 (p : ℝ) (hconv : NonzeroConvergentProduct p) :
    sumFromTwo (fun n => Real.log (rewrittenTerm p n)) =
      p * sumFromTwo (fun n => Real.log (rewrittenBase n)) := by
  unfold sumFromTwo
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  unfold rewrittenTerm
  have hk : 2 ≤ k + 2 := by omega
  have hpos := rewrittenBase_pos_of_two_le (k + 2) hk
  exact Real.log_rpow hpos p

/-- Exercise 3070, gap 3. -/
theorem gap3 (p : ℝ) (hconv : NonzeroConvergentProduct p) :
    SummableFromTwo (fun n => Real.log (rewrittenTerm p n)) := by
  have hs := summable_log_rewrittenBase
  unfold SummableFromTwo at hs ⊢
  have hsp : Summable (fun k : ℕ => p * Real.log (rewrittenBase (k + 2))) :=
    hs.mul_left p
  refine hsp.congr ?_
  intro k
  unfold rewrittenTerm
  have hk : 2 ≤ k + 2 := by omega
  have hpos := rewrittenBase_pos_of_two_le (k + 2) hk
  exact (Real.log_rpow hpos p).symm

/-- Exercise 3070, gap 4. -/
theorem gap4 (p : ℝ) :
    NonzeroConvergentProduct p → NonzeroConvergentProduct p := by
  intro h
  exact h

/-- Exercise 3070, gap 5; `RealSet` is the whole real type. -/
theorem gap5 (p : ℝ) :
    p ∈ (Set.univ : Set ℝ) ↔ NonzeroConvergentProduct p := by
  simp only [Set.mem_univ, true_iff]
  exact nonzeroConvergentProduct_all p

end

end ProofGap.Exercise3070
