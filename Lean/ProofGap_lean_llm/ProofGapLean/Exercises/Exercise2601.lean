import ProofGapLean.Prelude.Analysis
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter

open scoped BigOperators

namespace ProofGap.Exercise2601

noncomputable section

def denominatorProduct (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 + Real.sqrt (k + 1))

def term (n : ℕ) : ℝ :=
  Real.sqrt (Nat.factorial n : ℝ) / denominatorProduct n

def explicitRatio (n : ℕ) : ℝ :=
  (2 + Real.sqrt (n + 1)) / Real.sqrt (n + 1)

def raabeQuantity (n : ℕ) : ℝ :=
  (n : ℝ) * (term n / term (n + 1) - 1)

def explicitQuantity (n : ℕ) : ℝ :=
  2 * (n : ℝ) / Real.sqrt (n + 1)

private theorem summable_of_raabe_diverges
    (u : ℕ → ℝ) (hu : ∀ n, 0 < u n)
    (h : Tendsto (fun n : ℕ => (n : ℝ) * (u n / u (n + 1) - 1)) atTop atTop) :
    Summable u := by
  have hevent : ∀ᶠ n : ℕ in atTop,
      (3 : ℝ) ≤ (n : ℝ) * (u n / u (n + 1) - 1) :=
    Filter.tendsto_atTop.1 h 3
  rcases Filter.eventually_atTop.1 hevent with ⟨N₀, hN₀⟩
  let N : ℕ := max N₀ 1
  have hNpos : 1 ≤ N := by
    exact le_max_right _ _
  have hlarge : ∀ n, N ≤ n →
      (3 : ℝ) ≤ (n : ℝ) * (u n / u (n + 1) - 1) := by
    intro n hn
    exact hN₀ n (le_trans (le_max_left _ _) hn)
  have hstep : ∀ n, N ≤ n →
      (((n + 2 : ℕ) : ℝ) ^ 2) * u (n + 1) ≤
        (((n + 1 : ℕ) : ℝ) ^ 2) * u n := by
    intro n hn
    have hn1 : 1 ≤ n := le_trans hNpos hn
    have hx : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn1)
    have hb : 0 < u (n + 1) := hu (n + 1)
    have hr := hlarge n hn
    have hratio : ((n : ℝ) + 3) * u (n + 1) ≤ (n : ℝ) * u n := by
      have hd : (n : ℝ) + 3 ≤ ((n : ℝ) * u n) / u (n + 1) := by
        calc
          (n : ℝ) + 3 ≤ (n : ℝ) * (u n / u (n + 1)) := by
            nlinarith [hr]
          _ = ((n : ℝ) * u n) / u (n + 1) := by ring
      exact (le_div_iff₀ hb).mp hd
    have hthree : 0 < (n : ℝ) + 3 := by positivity
    have htwo : 0 < (n : ℝ) + 2 := by positivity
    have hcoef :
        (n : ℝ) / ((n : ℝ) + 3) ≤
          (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ 2 := by
      apply (div_le_iff₀ hthree).2
      field_simp [ne_of_gt htwo]
      ring_nf
      nlinarith [sq_nonneg (n : ℝ)]
    have hnext :
        u (n + 1) ≤
          (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ 2 * u n := by
      calc
        u (n + 1) ≤ ((n : ℝ) * u n) / ((n : ℝ) + 3) :=
          (le_div_iff₀ hthree).2 (by
            simpa [mul_comm] using hratio)
        _ = ((n : ℝ) / ((n : ℝ) + 3)) * u n := by ring
        _ ≤ (((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ 2 * u n :=
          mul_le_mul_of_nonneg_right hcoef (le_of_lt (hu n))
    norm_num [Nat.cast_add] at ⊢
    calc
      ((n : ℝ) + 2) ^ 2 * u (n + 1) ≤
          ((n : ℝ) + 2) ^ 2 *
            ((((n : ℝ) + 1) / ((n : ℝ) + 2)) ^ 2 * u n) :=
        mul_le_mul_of_nonneg_left hnext (sq_nonneg _)
      _ = ((n : ℝ) + 1) ^ 2 * u n := by
        field_simp [ne_of_gt htwo]
  have hweighted : ∀ n, N ≤ n →
      (((n + 1 : ℕ) : ℝ) ^ 2) * u n ≤
        (((N + 1 : ℕ) : ℝ) ^ 2) * u N := by
    intro n hn
    exact Nat.le_induction (m := N) le_rfl
      (fun k hk ih => (hstep k hk).trans ih) n hn
  let C : ℝ := (((N + 1 : ℕ) : ℝ) ^ 2) * u N
  have htailBound : ∀ m : ℕ,
      u (N + m) ≤ C / (((m + 1 : ℕ) : ℝ) ^ 2) := by
    intro m
    have hw := hweighted (N + m) (by omega)
    have hmn : m + 1 ≤ (N + m) + 1 := by omega
    have hmn' : ((m + 1 : ℕ) : ℝ) ≤ (((N + m) + 1 : ℕ) : ℝ) := by
      exact_mod_cast hmn
    have hsq : (((m + 1 : ℕ) : ℝ) ^ 2) ≤
        ((((N + m) + 1 : ℕ) : ℝ) ^ 2) := by
      nlinarith [sq_nonneg (((N + m) + 1 : ℕ) : ℝ),
        sq_nonneg ((m + 1 : ℕ) : ℝ)]
    have hmul : (((m + 1 : ℕ) : ℝ) ^ 2) * u (N + m) ≤ C := by
      calc
        (((m + 1 : ℕ) : ℝ) ^ 2) * u (N + m) ≤
            ((((N + m) + 1 : ℕ) : ℝ) ^ 2) * u (N + m) :=
          mul_le_mul_of_nonneg_right hsq (le_of_lt (hu (N + m)))
        _ ≤ C := by simpa [C] using hw
    have hdenom_pos :
        (0 : ℝ) < (((m + 1 : ℕ) : ℝ) ^ 2) := by
      positivity
    exact (le_div_iff₀ hdenom_pos).2 (by
      simpa [mul_comm] using hmul)
  have hden_tendsto :
      Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    have hb : ∀ᶠ n : ℕ in atTop, b ≤ (n : ℝ) :=
      Filter.tendsto_atTop.1 tendsto_natCast_atTop_atTop b
    filter_upwards [hb] with n hn
    linarith
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hden_tendsto
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlimit :
      Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 1)⁻¹) atTop (nhds 1) := by
    simpa using hone.sub hinv
  let f : ℕ → ℝ := fun m =>
    1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)
  have hf_nonneg : ∀ m : ℕ, 0 ≤ f m := by
    intro m
    have hx1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hx2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hform : f m =
        1 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
      dsimp [f]
      field_simp [ne_of_gt hx1, ne_of_gt hx2]
      <;> ring
    rw [hform]
    positivity
  have hpartial : ∀ n : ℕ,
      (Finset.range n).sum f = 1 - ((n : ℝ) + 1)⁻¹ := by
    intro n
    induction n with
    | zero => norm_num [f]
    | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
  have hupper : ∀ s : Finset ℕ, s.sum f ≤ 1 := by
    intro s
    let K : ℕ := s.sum (fun m => m) + 1
    have hsub : s ⊆ Finset.range K := by
      intro m hm
      rw [Finset.mem_range]
      have hmle : m ≤ s.sum (fun i => i) := by
        exact Finset.single_le_sum (fun i _ => Nat.zero_le i) hm
      simpa [K] using Nat.lt_succ_of_le hmle
    calc
      s.sum f ≤ (Finset.range K).sum f :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun i _ _ => hf_nonneg i)
      _ = 1 - ((K : ℝ) + 1)⁻¹ := hpartial K
      _ ≤ 1 := by
        have hinv_nonneg : 0 ≤ (((K : ℝ) + 1)⁻¹) := by positivity
        linarith
  have htel : HasSum f 1 := by
    change Tendsto (fun s : Finset ℕ => s.sum f) atTop (nhds 1)
    refine tendsto_order.2 ⟨?_, ?_⟩
    · intro a ha
      have haevent : ∀ᶠ n : ℕ in atTop,
          a < 1 - ((n : ℝ) + 1)⁻¹ :=
        (tendsto_order.1 hlimit).1 a ha
      rcases Filter.eventually_atTop.1 haevent with ⟨n, hn⟩
      refine Filter.eventually_atTop.2 ⟨Finset.range n, ?_⟩
      intro s hs
      have hsumle : (Finset.range n).sum f ≤ s.sum f :=
        Finset.sum_le_sum_of_subset_of_nonneg hs
          (fun i _ _ => hf_nonneg i)
      calc
        a < 1 - ((n : ℝ) + 1)⁻¹ := hn n le_rfl
        _ = (Finset.range n).sum f := (hpartial n).symm
        _ ≤ s.sum f := hsumle
    · intro b hb
      exact Filter.Eventually.of_forall (fun s =>
        lt_of_le_of_lt (hupper s) hb)
  have htelSummable : Summable
      (fun m : ℕ =>
        1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) := by
    simpa [f] using htel.summable
  have hp : Summable (fun m : ℕ => (((m : ℝ) + 1) ^ 2)⁻¹) := by
    have htel2 : Summable (fun m : ℕ =>
        2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2))) :=
      htelSummable.mul_left 2
    refine Summable.of_norm_bounded htel2 ?_
    intro m
    have hx0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    have hx1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hx2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hpinv : 0 < (((m : ℝ) + 1) ^ 2)⁻¹ :=
      inv_pos.2 (pow_pos hx1 2)
    rw [Real.norm_eq_abs, abs_of_pos hpinv]
    calc
      (((m : ℝ) + 1) ^ 2)⁻¹ =
          1 / (((m : ℝ) + 1) ^ 2) := by
        simp [div_eq_mul_inv]
      _ ≤ 2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
        apply (div_le_div_iff₀ (pow_pos hx1 2) (mul_pos hx1 hx2)).2
        nlinarith [sq_nonneg (m : ℝ)]
      _ = 2 * (1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2)) := by
        field_simp [ne_of_gt hx1, ne_of_gt hx2]
        <;> ring
  have hg : Summable (fun m : ℕ =>
      C / (((m + 1 : ℕ) : ℝ) ^ 2)) := by
    simpa [div_eq_mul_inv, Nat.cast_add] using (hp.mul_left C)
  have htail : Summable (fun m : ℕ => u (N + m)) := by
    refine Summable.of_norm_bounded hg ?_
    intro m
    rw [Real.norm_eq_abs, abs_of_pos (hu (N + m))]
    exact htailBound m
  have heq : (fun m : ℕ => u (m + N)) = (fun m : ℕ => u (N + m)) := by
    funext m
    rw [Nat.add_comm]
  have htail' : Summable (fun m : ℕ => u (m + N)) :=
    heq.symm ▸ htail
  exact (summable_nat_add_iff N).mp htail'

theorem gap1
    (a : ℕ → ℝ) (ha : ∀ n, a n = term n) :
    ∀ n, a n / a (n + 1) = explicitRatio n := by
  intro n
  rw [ha n, ha (n + 1)]
  have hden : denominatorProduct n ≠ 0 := by
    apply ne_of_gt
    unfold denominatorProduct
    positivity
  have hfac : Real.sqrt (Nat.factorial n : ℝ) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hsqrt : Real.sqrt (n + 1) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  have hsum : 2 + Real.sqrt (n + 1) ≠ 0 := by
    positivity
  have hprod : denominatorProduct (n + 1) =
      denominatorProduct n * (2 + Real.sqrt (n + 1)) := by
    simp [denominatorProduct, Finset.prod_range_succ]
  have hfactorial : Real.sqrt (Nat.factorial (n + 1) : ℝ) =
      Real.sqrt (Nat.factorial n : ℝ) * Real.sqrt (n + 1) := by
    rw [Nat.factorial_succ]
    push_cast
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ n + 1)]
    ring
  dsimp [term, explicitRatio]
  rw [hprod, hfactorial]
  field_simp [hden, hfac, hsqrt, hsum]
  <;> ring

theorem gap2
    (a : ℕ → ℝ) (ha : ∀ n, a n = term n)
    (hratio : ∀ n, a n / a (n + 1) = explicitRatio n) :
    ∀ n : ℕ, (n : ℝ) * (a n / a (n + 1) - 1) =
      (n : ℝ) * (explicitRatio n - 1) := by
  intro n
  rw [hratio n]

theorem gap3 :
    ∀ n : ℕ, (n : ℝ) * (explicitRatio n - 1) =
      explicitQuantity n := by
  intro n
  have hsqrt : Real.sqrt (n + 1) ≠ 0 := by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    positivity
  unfold explicitRatio explicitQuantity
  field_simp [hsqrt]
  ring

theorem gap4 :
    Tendsto explicitQuantity atTop atTop := by
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbound : ∀ n : ℕ, 1 ≤ n →
      Real.sqrt (n : ℝ) ≤ explicitQuantity n := by
    intro n hn
    have hx : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hx0 : (0 : ℝ) ≤ (n : ℝ) := le_trans (by norm_num) hx
    have hxp : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hprod :
        (Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + 1)) ^ 2 =
          (n : ℝ) * ((n : ℝ) + 1) := by
      rw [mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt (le_of_lt hxp)]
    have hsq :
        (Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + 1)) ^ 2 ≤
          (2 * (n : ℝ)) ^ 2 := by
      nlinarith [hprod, sq_nonneg (n : ℝ)]
    have hmul :
        Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + 1) ≤
          2 * (n : ℝ) := by
      have hz : 0 ≤ Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) + 1) := by
        positivity
      have ht : 0 ≤ 2 * (n : ℝ) := by positivity
      nlinarith
    unfold explicitQuantity
    norm_num [Nat.cast_add] at ⊢
    exact (le_div_iff₀ (Real.sqrt_pos.2 hxp)).2 hmul
  refine Filter.tendsto_atTop.2 ?_
  intro b
  have hsqrtb : ∀ᶠ n : ℕ in atTop, b ≤ Real.sqrt (n : ℝ) :=
    Filter.tendsto_atTop.1 hsqrt b
  have hone : ∀ᶠ n : ℕ in atTop, 1 ≤ n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩
  filter_upwards [hsqrtb, hone] with n hbn hn
  exact hbn.trans (hbound n hn)

theorem gap5
    (hidentity : ∀ n, raabeQuantity n = explicitQuantity n)
    (hdiverge : Tendsto explicitQuantity atTop atTop) :
    Tendsto raabeQuantity atTop atTop := by
  have heq : raabeQuantity = explicitQuantity := funext hidentity
  rw [heq]
  exact hdiverge

theorem gap6
    (hraabe : Tendsto raabeQuantity atTop atTop) :
    Summable term := by
  have hpositive : ∀ n, 0 < term n := by
    intro n
    unfold term denominatorProduct
    positivity
  exact summable_of_raabe_diverges term hpositive hraabe

theorem gap7
    (hsum : Summable term) :
    Summable term := by
  exact hsum

end

end ProofGap.Exercise2601
