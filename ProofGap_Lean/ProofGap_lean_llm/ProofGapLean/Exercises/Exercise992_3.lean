import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic

namespace ProofGap.Exercise992_3

open Filter

noncomputable section

def f (n : ℕ) (x : ℝ) : ℝ :=
  if x = 0 then 0 else x ^ n * Real.sin (1 / x)

def derivativeFormula (n : ℕ) (x : ℝ) : ℝ :=
  (n : ℝ) * x ^ (n - 1) * Real.sin (1 / x) -
    x ^ (n - 2) * Real.cos (1 / x)

private theorem privateAbsSinLeOne (x : ℝ) : |Real.sin x| ≤ 1 := by
  exact (abs_le).2 ⟨Real.neg_one_le_sin x, Real.sin_le_one x⟩

private theorem privateAbsCosLeOne (x : ℝ) : |Real.cos x| ≤ 1 := by
  exact (abs_le).2 ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩

private theorem privateHasDerivAtFNeZero (n : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (f n)
      ((n : ℝ) * x ^ (n - 1) * Real.sin x⁻¹ +
        x ^ n * (Real.cos x⁻¹ * (-(x ^ 2)⁻¹))) x := by
  have hsin : HasDerivAt (fun y : ℝ => Real.sin y⁻¹)
      (Real.cos x⁻¹ * (-(x ^ 2)⁻¹)) x := by
    exact (Real.hasDerivAt_sin x⁻¹).comp x (hasDerivAt_inv hx)
  have hprod : HasDerivAt
      (fun y : ℝ => y ^ n * Real.sin y⁻¹)
      ((n : ℝ) * x ^ (n - 1) * Real.sin x⁻¹ +
        x ^ n * (Real.cos x⁻¹ * (-(x ^ 2)⁻¹))) x := by
    convert (hasDerivAt_pow n x).mul hsin using 1
  have heq : f n =ᶠ[nhds x] (fun y : ℝ => y ^ n * Real.sin y⁻¹) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds
      (by simpa : x ∈ ({0}ᶜ : Set ℝ))] with y hy
    have hy0 : y ≠ 0 := by simpa using hy
    simp [f, hy0, one_div]
  exact hprod.congr_of_eventuallyEq heq

private theorem privateDerivFZeroOfOneLt (n : ℕ) (hn : 1 < n) :
    deriv (f n) 0 = 0 := by
  have hp : Tendsto (fun x : ℝ => |x ^ (n - 1)|) (nhds 0) (nhds 0) := by
    simpa [show n - 1 ≠ 0 by omega] using
      (((continuousAt_id : ContinuousAt (fun x : ℝ => x) 0).pow
        (n - 1)).abs.tendsto)
  have hpWithin : Tendsto (fun x : ℝ => |x ^ (n - 1)|)
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) :=
    hp.mono_left
      (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds 0 from inf_le_left)
  have hs : Tendsto
      (fun x : ℝ => x ^ (n - 1) * Real.sin x⁻¹)
      (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hb : ∀ᶠ x : ℝ in nhdsWithin 0 {0}ᶜ,
        dist |x ^ (n - 1)| 0 < ε :=
      (Metric.tendsto_nhds.mp hpWithin) ε hε
    filter_upwards [hb] with x hx
    rw [Real.dist_eq, sub_zero]
    calc
      |x ^ (n - 1) * Real.sin x⁻¹|
          ≤ |x ^ (n - 1)| := by
            rw [abs_mul]
            simpa using mul_le_mul_of_nonneg_left
              (privateAbsSinLeOne x⁻¹) (abs_nonneg (x ^ (n - 1)))
      _ < ε := by simpa [Real.dist_eq] using hx
  have hd : HasDerivAt (f n) 0 0 := by
    rw [hasDerivAt_iff_tendsto_slope_zero]
    apply hs.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hnexp : n = (n - 1) + 1 := by omega
    have hpow : x ^ n = x ^ (n - 1) * x := by
      conv_lhs => rw [hnexp, pow_succ]
    have hfx : f n x = x ^ n * Real.sin x⁻¹ := by
      simp [f, hx0, one_div]
    have hf0 : f n 0 = 0 := by simp [f]
    simp only [zero_add, smul_eq_mul]
    rw [hfx, hf0, sub_zero, hpow]
    field_simp [hx0]
  exact hd.deriv

private def privateRecipTwoPi (k : ℕ) : ℝ :=
  1 / (2 * Real.pi * ((k + 1 : ℕ) : ℝ))

private theorem privateTrigTwoPiNat (k : ℕ) :
    Real.sin (2 * Real.pi * (k : ℝ)) = 0 ∧
      Real.cos (2 * Real.pi * (k : ℝ)) = 1 := by
  induction k with
  | zero => simp
  | succ k ih =>
      have heq : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) =
          2 * Real.pi * (k : ℝ) + 2 * Real.pi := by
        norm_num
        ring
      constructor
      · rw [heq, Real.sin_add]
        simp [ih.1, ih.2]
      · rw [heq, Real.cos_add]
        simp [ih.1, ih.2]

private theorem privateDerivRecipTwoPi (n k : ℕ) :
    deriv (f n) (privateRecipTwoPi k) =
      -(privateRecipTwoPi k) ^ n *
        (2 * Real.pi * ((k + 1 : ℕ) : ℝ)) ^ 2 := by
  let d : ℝ := 2 * Real.pi * ((k + 1 : ℕ) : ℝ)
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hx : privateRecipTwoPi k ≠ 0 := by
    unfold privateRecipTwoPi
    exact one_div_ne_zero hd.ne'
  have hrec : (privateRecipTwoPi k)⁻¹ = d := by
    unfold privateRecipTwoPi
    dsimp [d] at hd ⊢
    field_simp [hd.ne']
  have hsquare : ((privateRecipTwoPi k) ^ 2)⁻¹ = d ^ 2 := by
    calc
      ((privateRecipTwoPi k) ^ 2)⁻¹ =
          ((privateRecipTwoPi k)⁻¹) ^ 2 := by
            exact (inv_pow (privateRecipTwoPi k) 2).symm
      _ = d ^ 2 := by rw [hrec]
  have ht := privateTrigTwoPiNat (k + 1)
  calc
    deriv (f n) (privateRecipTwoPi k) =
        (n : ℝ) * (privateRecipTwoPi k) ^ (n - 1) *
            Real.sin (privateRecipTwoPi k)⁻¹ +
          (privateRecipTwoPi k) ^ n *
            (Real.cos (privateRecipTwoPi k)⁻¹ *
              (-((privateRecipTwoPi k) ^ 2)⁻¹)) :=
      (privateHasDerivAtFNeZero n (privateRecipTwoPi k) hx).deriv
    _ = -(privateRecipTwoPi k) ^ n * d ^ 2 := by
      rw [hrec, ht.1, ht.2, hsquare]
      ring
    _ = -(privateRecipTwoPi k) ^ n *
        (2 * Real.pi * ((k + 1 : ℕ) : ℝ)) ^ 2 := by rfl

private theorem privateDerivRecipTwoPiZero (k : ℕ) :
    deriv (f 0) (privateRecipTwoPi k) =
      -(2 * Real.pi * ((k + 1 : ℕ) : ℝ)) ^ 2 := by
  simpa using privateDerivRecipTwoPi 0 k

private theorem privateDerivRecipTwoPiOne (k : ℕ) :
    deriv (f 1) (privateRecipTwoPi k) =
      -(2 * Real.pi * ((k + 1 : ℕ) : ℝ)) := by
  rw [privateDerivRecipTwoPi]
  unfold privateRecipTwoPi
  have hd : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hd]

private theorem privateDerivRecipTwoPiTwo (k : ℕ) :
    deriv (f 2) (privateRecipTwoPi k) = -1 := by
  rw [privateDerivRecipTwoPi]
  unfold privateRecipTwoPi
  have hd : 2 * Real.pi * ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hd]

private theorem privateTendstoRecipTwoPi :
    Tendsto privateRecipTwoPi atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hp : 0 < 2 * Real.pi :=
    mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos
  obtain ⟨K, hK⟩ := exists_nat_gt (1 / (2 * Real.pi * ε))
  refine ⟨K, ?_⟩
  intro k hk
  have hkcast : (K : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk1 : (K : ℝ) < ((k + 1 : ℕ) : ℝ) := by
    norm_num only [Nat.cast_add, Nat.cast_one]
    linarith
  have hlarge : 1 / (2 * Real.pi * ε) < ((k + 1 : ℕ) : ℝ) :=
    hK.trans hk1
  have hpe : 0 < 2 * Real.pi * ε := mul_pos hp hε
  have hone : 1 < ((k + 1 : ℕ) : ℝ) * (2 * Real.pi * ε) :=
    (div_lt_iff₀ hpe).mp hlarge
  have hd : 0 < 2 * Real.pi * ((k + 1 : ℕ) : ℝ) := by positivity
  rw [Real.dist_eq, sub_zero]
  unfold privateRecipTwoPi
  rw [abs_of_pos (one_div_pos.mpr hd)]
  apply (div_lt_iff₀ hd).2
  simpa [mul_comm, mul_left_comm, mul_assoc] using hone

theorem gap1 (n : ℕ) (hn : 2 < n) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (f n) (derivativeFormula n x) x := by
  have hnexp : n = (n - 2) + 2 := by omega
  have hxpow : x ^ n = x ^ (n - 2) * x ^ 2 := by
    conv_lhs => rw [hnexp, pow_add]
  have hpow :
      x ^ n * (Real.cos x⁻¹ * (-(x ^ 2)⁻¹)) =
        -(x ^ (n - 2) * Real.cos x⁻¹) := by
    rw [hxpow]
    field_simp [hx]
  have hcoef :
      derivativeFormula n x =
        (n : ℝ) * x ^ (n - 1) * Real.sin x⁻¹ +
          x ^ n * (Real.cos x⁻¹ * (-(x ^ 2)⁻¹)) := by
    unfold derivativeFormula
    simp only [one_div]
    rw [hpow]
    ring
  rw [hcoef]
  exact privateHasDerivAtFNeZero n x hx

theorem gap2 (n : ℕ) (hn : 2 < n) :
    Tendsto (fun x => deriv (f n) x) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  have hB : Tendsto
      (fun x : ℝ => |(n : ℝ) * x ^ (n - 1)| + |x ^ (n - 2)|)
      (nhds 0) (nhds 0) := by
    have hcont : ContinuousAt
        (fun x : ℝ => |(n : ℝ) * x ^ (n - 1)| + |x ^ (n - 2)|) 0 :=
      ((continuousAt_const.mul (continuousAt_id.pow (n - 1))).abs).add
        ((continuousAt_id.pow (n - 2)).abs)
    simpa [show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega] using
      hcont.tendsto
  have hBWithin : Tendsto
      (fun x : ℝ => |(n : ℝ) * x ^ (n - 1)| + |x ^ (n - 2)|)
      (nhdsWithin (0 : ℝ) {0}ᶜ) (nhds 0) :=
    hB.mono_left
      (show nhdsWithin (0 : ℝ) {0}ᶜ ≤ nhds 0 from inf_le_left)
  have hformula : ∀ᶠ x : ℝ in nhdsWithin 0 {0}ᶜ,
      deriv (f n) x = derivativeFormula n x := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    exact (gap1 n hn x hx0).deriv
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hbound : ∀ᶠ x : ℝ in nhdsWithin 0 {0}ᶜ,
      dist (|(n : ℝ) * x ^ (n - 1)| + |x ^ (n - 2)|) 0 < ε :=
    (Metric.tendsto_nhds.mp hBWithin) ε hε
  filter_upwards [hformula, hbound] with x hfx hbx
  rw [hfx, Real.dist_eq, sub_zero]
  have hnon :
      0 ≤ |(n : ℝ) * x ^ (n - 1)| + |x ^ (n - 2)| :=
    add_nonneg (abs_nonneg _) (abs_nonneg _)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnon] at hbx
  unfold derivativeFormula
  calc
    |(n : ℝ) * x ^ (n - 1) * Real.sin (1 / x) -
        x ^ (n - 2) * Real.cos (1 / x)|
        ≤ |(n : ℝ) * x ^ (n - 1) * Real.sin (1 / x)| +
          |x ^ (n - 2) * Real.cos (1 / x)| := abs_sub _ _
    _ ≤ |(n : ℝ) * x ^ (n - 1)| + |x ^ (n - 2)| := by
      apply add_le_add
      · rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left
          (privateAbsSinLeOne (1 / x))
          (abs_nonneg ((n : ℝ) * x ^ (n - 1)))
      · rw [abs_mul]
        simpa using mul_le_mul_of_nonneg_left
          (privateAbsCosLeOne (1 / x))
          (abs_nonneg (x ^ (n - 2)))
    _ < ε := hbx

theorem gap3 (n : ℕ) (hn : 2 < n) :
    deriv (f n) 0 = 0 := by
  exact privateDerivFZeroOfOneLt n (by omega)

theorem gap4 (n : ℕ) (hn : 2 < n) :
    Tendsto (fun x => deriv (f n) x) (nhds 0) (nhds (deriv (f n) 0)) := by
  rw [gap3 n hn]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hwithin := (Metric.tendsto_nhds.mp (gap2 n hn)) ε hε
  rcases mem_nhdsWithin_iff_exists_mem_nhds_inter.mp hwithin with
    ⟨s, hs, hsub⟩
  filter_upwards [hs] with x hx
  by_cases hx0 : x = 0
  · subst x
    simpa [gap3 n hn] using hε
  · exact hsub ⟨hx, by simpa using hx0⟩

theorem gap5 (n : ℕ) (hn : 2 < n) :
    ContinuousAt (fun x => deriv (f n) x) 0 := by
  exact gap4 n hn

theorem gap6 (n : ℕ) :
    2 < n ↔ ContinuousAt (fun x => deriv (f n) x) 0 := by
  constructor
  · intro hn
    exact gap5 n hn
  · intro hc
    by_contra hn
    have hnCases : n = 0 ∨ n = 1 ∨ n = 2 := by omega
    rcases hnCases with rfl | rfl | rfl
    · let D : ℝ := deriv (f 0) 0
      have hseq : Tendsto
          (fun k : ℕ => deriv (f 0) (privateRecipTwoPi k))
          atTop (nhds D) := by
        simpa [D] using hc.tendsto.comp privateTendstoRecipTwoPi
      have hev : ∀ᶠ k : ℕ in atTop,
          D - 1 < deriv (f 0) (privateRecipTwoPi k) :=
        hseq.eventually
          (Ioi_mem_nhds (sub_lt_self D (show (0 : ℝ) < 1 by norm_num)))
      rcases eventually_atTop.1 hev with ⟨K, hK⟩
      have hp : 0 < 2 * Real.pi :=
        mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos
      obtain ⟨m, hm⟩ := exists_nat_gt
        ((K : ℝ) + (|D| + 1) / (2 * Real.pi))
      have hq0 : 0 ≤ (|D| + 1) / (2 * Real.pi) :=
        div_nonneg (show (0 : ℝ) ≤ |D| + 1 by positivity) hp.le
      have hKcast : (K : ℝ) < (m : ℝ) := by
        calc
          (K : ℝ) ≤ (K : ℝ) + (|D| + 1) / (2 * Real.pi) :=
            le_add_of_nonneg_right hq0
          _ < (m : ℝ) := hm
      have hKm : K ≤ m := by exact_mod_cast hKcast.le
      have hq : (|D| + 1) / (2 * Real.pi) < (m : ℝ) := by
        calc
          (|D| + 1) / (2 * Real.pi) ≤
              (K : ℝ) + (|D| + 1) / (2 * Real.pi) :=
            le_add_of_nonneg_left (Nat.cast_nonneg K)
          _ < (m : ℝ) := hm
      have hlarge0 : |D| + 1 < 2 * Real.pi * (m : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (div_lt_iff₀ hp).mp hq
      have hlarge : |D| + 1 <
          2 * Real.pi * ((m + 1 : ℕ) : ℝ) := by
        calc
          |D| + 1 < 2 * Real.pi * (m : ℝ) := hlarge0
          _ < 2 * Real.pi * ((m + 1 : ℕ) : ℝ) := by
            norm_num only [Nat.cast_add, Nat.cast_one]
            nlinarith
      have hv := hK m hKm
      rw [privateDerivRecipTwoPiZero] at hv
      have hdpos : 0 < 2 * Real.pi * ((m + 1 : ℕ) : ℝ) := by
        positivity
      have hone : 1 < 2 * Real.pi * ((m + 1 : ℕ) : ℝ) := by
        nlinarith [abs_nonneg D]
      have hdsq :
          2 * Real.pi * ((m + 1 : ℕ) : ℝ) <
            (2 * Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 2 := by
        nlinarith [mul_pos hdpos (sub_pos.mpr hone)]
      have hsq : |D| + 1 <
          (2 * Real.pi * ((m + 1 : ℕ) : ℝ)) ^ 2 :=
        hlarge.trans hdsq
      nlinarith [neg_abs_le D]
    · let D : ℝ := deriv (f 1) 0
      have hseq : Tendsto
          (fun k : ℕ => deriv (f 1) (privateRecipTwoPi k))
          atTop (nhds D) := by
        simpa [D] using hc.tendsto.comp privateTendstoRecipTwoPi
      have hev : ∀ᶠ k : ℕ in atTop,
          D - 1 < deriv (f 1) (privateRecipTwoPi k) :=
        hseq.eventually
          (Ioi_mem_nhds (sub_lt_self D (show (0 : ℝ) < 1 by norm_num)))
      rcases eventually_atTop.1 hev with ⟨K, hK⟩
      have hp : 0 < 2 * Real.pi :=
        mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos
      obtain ⟨m, hm⟩ := exists_nat_gt
        ((K : ℝ) + (|D| + 1) / (2 * Real.pi))
      have hq0 : 0 ≤ (|D| + 1) / (2 * Real.pi) :=
        div_nonneg (show (0 : ℝ) ≤ |D| + 1 by positivity) hp.le
      have hKcast : (K : ℝ) < (m : ℝ) := by
        calc
          (K : ℝ) ≤ (K : ℝ) + (|D| + 1) / (2 * Real.pi) :=
            le_add_of_nonneg_right hq0
          _ < (m : ℝ) := hm
      have hKm : K ≤ m := by exact_mod_cast hKcast.le
      have hq : (|D| + 1) / (2 * Real.pi) < (m : ℝ) := by
        calc
          (|D| + 1) / (2 * Real.pi) ≤
              (K : ℝ) + (|D| + 1) / (2 * Real.pi) :=
            le_add_of_nonneg_left (Nat.cast_nonneg K)
          _ < (m : ℝ) := hm
      have hlarge0 : |D| + 1 < 2 * Real.pi * (m : ℝ) := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using
          (div_lt_iff₀ hp).mp hq
      have hlarge : |D| + 1 <
          2 * Real.pi * ((m + 1 : ℕ) : ℝ) := by
        calc
          |D| + 1 < 2 * Real.pi * (m : ℝ) := hlarge0
          _ < 2 * Real.pi * ((m + 1 : ℕ) : ℝ) := by
            norm_num only [Nat.cast_add, Nat.cast_one]
            nlinarith
      have hv := hK m hKm
      rw [privateDerivRecipTwoPiOne] at hv
      nlinarith [neg_abs_le D]
    · have hzero : deriv (f 2) 0 = 0 :=
        privateDerivFZeroOfOneLt 2 (by omega)
      have hseq : Tendsto
          (fun k : ℕ => deriv (f 2) (privateRecipTwoPi k))
          atTop (nhds 0) := by
        simpa [hzero] using hc.tendsto.comp privateTendstoRecipTwoPi
      have hev : ∀ᶠ k : ℕ in atTop,
          (-1 : ℝ) / 2 < deriv (f 2) (privateRecipTwoPi k) :=
        hseq.eventually
          (Ioi_mem_nhds (show (-1 : ℝ) / 2 < 0 by norm_num))
      rcases eventually_atTop.1 hev with ⟨K, hK⟩
      have hv := hK K le_rfl
      rw [privateDerivRecipTwoPiTwo] at hv
      norm_num at hv

end

end ProofGap.Exercise992_3
