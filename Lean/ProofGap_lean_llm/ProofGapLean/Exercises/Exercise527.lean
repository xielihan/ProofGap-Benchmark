import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise527

noncomputable section

def seq (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (((n : ℝ) + x) / ((n : ℝ) - 1)) n
def rewritten (x : ℝ) (n : ℕ) : ℝ :=
  Real.rpow (1 + 1 / (((n : ℝ) - 1) / (x + 1)))
    ((((n : ℝ) - 1) / (x + 1)) * (x + 1) + 1)

/-- Source: `proof_gap/exercise_527/1.txt`; require the nonzero substitution divisor `x+1`. -/
private theorem tendsto_of_eventually_eq {α β : Type*}
    {f g : α → β} {l : Filter α} {la : Filter β}
    (hfg : f =ᶠ[l] g) (hg : Filter.Tendsto g l la) :
    Filter.Tendsto f l la := by
  rw [Filter.tendsto_def] at hg ⊢
  intro s hs
  filter_upwards [hg s hs, hfg] with y hy heq
  change g y ∈ s at hy
  change f y ∈ s
  rw [heq]
  exact hy

private theorem tendsto_nat_of_add_one {α : Type*} {f : ℕ → α}
    {l : Filter α}
    (h : Filter.Tendsto (fun n : ℕ => f (n + 1)) Filter.atTop l) :
    Filter.Tendsto f Filter.atTop l := by
  rw [Filter.tendsto_def] at h ⊢
  intro s hs
  have hs' : ∀ᶠ n : ℕ in Filter.atTop, f (n + 1) ∈ s := h s hs
  rcases Filter.eventually_atTop.1 hs' with ⟨a, ha⟩
  apply Filter.eventually_atTop.2
  refine ⟨a + 1, ?_⟩
  intro b hb
  have hpred : a ≤ b - 1 := by omega
  have hsucc : b - 1 + 1 = b := by omega
  simpa only [hsucc] using ha (b - 1) hpred

private theorem seq_tendsto_exp_of_ne (x : ℝ) (hx : x ≠ -1) :
    Filter.Tendsto (seq x) Filter.atTop
      (nhds (Real.exp (x + 1))) := by
  let c : ℝ := x + 1
  have hc : c ≠ 0 := by
    dsimp [c]
    intro h
    apply hx
    linarith
  have hdivR :
      Filter.Tendsto (fun t : ℝ => c / t) Filter.atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero :
          Filter.Tendsto (fun t : ℝ => t⁻¹) Filter.atTop (nhds 0)))
  have hdiv :
      Filter.Tendsto (fun n : ℕ => c / (n : ℝ)) Filter.atTop (nhds 0) :=
    hdivR.comp
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop)
  have hbase :
      Filter.Tendsto (fun n : ℕ => 1 + c / (n : ℝ))
        Filter.atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hdiv
  have hge : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ n :=
    Filter.eventually_atTop.2 ⟨1, fun _ hn => hn⟩
  have hne :
      ∀ᶠ n : ℕ in Filter.atTop,
        c / (n : ℝ) ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards [hge] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 hnpos)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (div_ne_zero hc hn0)
  have hwithin :
      Filter.Tendsto (fun n : ℕ => c / (n : ℝ)) Filter.atTop
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨hdiv, hne⟩
  have hslope0 :
      Filter.Tendsto (fun h : ℝ => Real.log (1 + h) / h)
        (nhdsWithin 0 ({0}ᶜ : Set ℝ)) (nhds 1) := by
    simpa [div_eq_mul_inv, add_comm, mul_comm] using
      (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto_slope_zero
  have hslope :
      Filter.Tendsto
        (fun n : ℕ => Real.log (1 + c / (n : ℝ)) / (c / (n : ℝ)))
        Filter.atTop (nhds 1) :=
    hslope0.comp hwithin
  have hfactor_eq :
      (fun n : ℕ => c / (n : ℝ) * ((n : ℝ) + 1)) =ᶠ[Filter.atTop]
        (fun n : ℕ => c + c / (n : ℝ)) := by
    filter_upwards [hge] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 hnpos)
    field_simp [hn0]
  have hsum :
      Filter.Tendsto (fun n : ℕ => c + c / (n : ℝ))
        Filter.atTop (nhds c) := by
    simpa using tendsto_const_nhds.add hdiv
  have hfactor :
      Filter.Tendsto (fun n : ℕ => c / (n : ℝ) * ((n : ℝ) + 1))
        Filter.atTop (nhds c) :=
    tendsto_of_eventually_eq hfactor_eq hsum
  have hlog_eq :
      (fun n : ℕ =>
        (Real.log (1 + c / (n : ℝ)) / (c / (n : ℝ))) *
          (c / (n : ℝ) * ((n : ℝ) + 1))) =ᶠ[Filter.atTop]
        (fun n : ℕ => Real.log (1 + c / (n : ℝ)) * ((n : ℝ) + 1)) := by
    filter_upwards [hge] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 hnpos)
    have hq : c / (n : ℝ) ≠ 0 := div_ne_zero hc hn0
    field_simp [hq, hn0]
  have hlog :
      Filter.Tendsto
        (fun n : ℕ => Real.log (1 + c / (n : ℝ)) * ((n : ℝ) + 1))
        Filter.atTop (nhds c) := by
    apply tendsto_of_eventually_eq hlog_eq.symm
    simpa using hslope.mul hfactor
  have hexp :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.exp (Real.log (1 + c / (n : ℝ)) * ((n : ℝ) + 1)))
        Filter.atTop (nhds (Real.exp c)) :=
    Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hpos :
      ∀ᶠ n : ℕ in Filter.atTop, 0 < 1 + c / (n : ℝ) :=
    (tendsto_order.1 hbase).1 0 (by norm_num)
  have hrpow_eq :
      (fun n : ℕ => Real.rpow (1 + c / (n : ℝ)) ((n : ℝ) + 1))
        =ᶠ[Filter.atTop]
      (fun n : ℕ =>
        Real.exp (Real.log (1 + c / (n : ℝ)) * ((n : ℝ) + 1))) := by
    filter_upwards [hpos] with n hb
    exact Real.rpow_def_of_pos hb ((n : ℝ) + 1)
  have hrpow :
      Filter.Tendsto
        (fun n : ℕ => Real.rpow (1 + c / (n : ℝ)) ((n : ℝ) + 1))
        Filter.atTop (nhds (Real.exp c)) :=
    tendsto_of_eventually_eq hrpow_eq hexp
  have hseq_eq :
      (fun n : ℕ => seq x (n + 1)) =ᶠ[Filter.atTop]
        (fun n : ℕ => Real.rpow (1 + c / (n : ℝ)) ((n : ℝ) + 1)) := by
    filter_upwards [hge] with n hn
    have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.2 hnpos)
    have hb :
        (((n + 1 : ℕ) : ℝ) + x) / (((n + 1 : ℕ) : ℝ) - 1) =
          1 + c / (n : ℝ) := by
      dsimp [c]
      simp only [Nat.cast_add, Nat.cast_one]
      field_simp [hn0]
      ring
    unfold seq
    rw [hb]
    simp only [Nat.cast_add, Nat.cast_one]
  have hshift :
      Filter.Tendsto (fun n : ℕ => seq x (n + 1)) Filter.atTop
        (nhds (Real.exp c)) :=
    tendsto_of_eventually_eq hseq_eq hrpow
  simpa [c] using tendsto_nat_of_add_one hshift

theorem gap1 (x : ℝ) (hx : x ≠ -1) (L : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (rewritten x) Filter.atTop (nhds L) := by
  have hx1 : x + 1 ≠ 0 := by
    intro h
    apply hx
    linarith
  have heq : seq x =ᶠ[Filter.atTop] rewritten x := by
    apply Filter.eventually_atTop.2
    refine ⟨2, ?_⟩
    intro n hn
    have hnR : (2 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    have hn1 : (n : ℝ) - 1 ≠ 0 := by
      linarith
    unfold seq rewritten
    congr 1
    · field_simp [hn1, hx1]
      ring
    · field_simp [hx1]
      ring
  constructor
  · intro hs
    exact tendsto_of_eventually_eq heq.symm hs
  · intro hr
    exact tendsto_of_eventually_eq heq hr

/-- Source: `proof_gap/exercise_527/2.txt`; require `x+1≠0` in the displayed substitution. -/
theorem gap2 (x : ℝ) (hx : x ≠ -1) :
    Filter.Tendsto (rewritten x) Filter.atTop (nhds (Real.exp (x + 1))) := by
  exact (gap1 x hx (Real.exp (x + 1))).mp
    (seq_tendsto_exp_of_ne x hx)

/-- Source: `proof_gap/exercise_527/3.txt`; the final limit remains valid for every real `x`. -/
theorem gap3 (x : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop (nhds (Real.exp (x + 1))) := by
  by_cases hx : x = -1
  · subst x
    have heq : seq (-1) =ᶠ[Filter.atTop] (fun _ : ℕ => (1 : ℝ)) := by
      apply Filter.eventually_atTop.2
      refine ⟨2, ?_⟩
      intro n hn
      have hnR : (2 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hn
      have hn1 : (n : ℝ) - 1 ≠ 0 := by
        linarith
      have hb :
          ((n : ℝ) + (-1)) / ((n : ℝ) - 1) = 1 := by
        have hnum : (n : ℝ) + (-1) = (n : ℝ) - 1 := by ring
        rw [hnum, div_self hn1]
      unfold seq
      rw [hb]
      simp
    have ht :
        Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1) :=
      tendsto_const_nhds
    simpa using tendsto_of_eventually_eq heq ht
  · exact seq_tendsto_exp_of_ne x hx

end

end ProofGap.Exercise527
