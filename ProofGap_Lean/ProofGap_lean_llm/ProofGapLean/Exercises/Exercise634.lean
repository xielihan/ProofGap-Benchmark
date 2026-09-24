import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise634

noncomputable section

def exponentialIncrement (a x : ℝ) : ℝ :=
  (Real.rpow a x - 1) / x / Real.log a
def exponentSum (a : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k => (k : ℝ) / (n : ℝ) ^ 2 * Real.log a)
def incrementSum (a : ℝ) (n : ℕ) : ℝ :=
  (Finset.Icc 1 n).sum (fun k =>
    Real.rpow a ((k : ℝ) / (n : ℝ) ^ 2) - 1)

/-- Exercise 634, gap 1; add `a≠1`, needed by division by `log a`. -/
private theorem exp_remainder_bound {x : ℝ} (hx : |x| ≤ (1 / 2 : ℝ)) :
    0 ≤ Real.exp x - 1 - x ∧
      Real.exp x - 1 - x ≤ 2 * x ^ 2 := by
  have hlow : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  have hneg : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  have hmul :=
    mul_le_mul_of_nonneg_left hneg (Real.exp_pos x).le
  have hprod : Real.exp x * (1 - x) ≤ 1 := by
    calc
      Real.exp x * (1 - x) = Real.exp x * (-x + 1) := by ring
      _ ≤ Real.exp x * Real.exp (-x) := hmul
      _ = 1 := by rw [← Real.exp_add]; norm_num
  have hderiv : Real.exp x - 1 ≤ x * Real.exp x := by
    nlinarith [hprod]
  constructor
  · nlinarith [hlow]
  · have hxupper : x ≤ (1 / 2 : ℝ) := le_trans (le_abs_self x) hx
    have hrem :
        Real.exp x - 1 - x ≤ x * (Real.exp x - 1) := by
      nlinarith [hderiv]
    by_cases hnonneg : 0 ≤ x
    · have hexple : Real.exp x ≤ 2 := by
        nlinarith [hprod, Real.exp_pos x]
      have hstep :
          x * (Real.exp x - 1) ≤ x * (x * Real.exp x) :=
        mul_le_mul_of_nonneg_left hderiv hnonneg
      have hsqexp : x ^ 2 * Real.exp x ≤ 2 * x ^ 2 := by
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_left hexple (sq_nonneg x))
      nlinarith [hrem, hstep, hsqexp]
    · have hxnonpos : x ≤ 0 := le_of_not_ge hnonneg
      have hxlow : x ≤ Real.exp x - 1 := by nlinarith [hlow]
      have hp := mul_nonneg
        (sub_nonneg.mpr hxlow) (neg_nonneg.mpr hxnonpos)
      nlinarith [hrem, hp]

theorem gap1 (a : ℝ) (ha : 0 < a) (ha1 : a ≠ 1) :
    Filter.Tendsto (exponentialIncrement a)
      (nhdsWithin 0 ({0} : Set ℝ)ᶜ) (nhds 1) := by
  have hlog : Real.log a ≠ 0 := by
    intro h
    apply ha1
    calc
      a = Real.exp (Real.log a) := (Real.exp_log ha).symm
      _ = 1 := by simp [h]
  have hdlog :
      HasDerivAt (fun x : ℝ => Real.log a * x) (Real.log a) 0 := by
    simpa using (hasDerivAt_id 0).const_mul (Real.log a)
  have hd :
      HasDerivAt (fun x : ℝ => Real.exp (Real.log a * x))
        (Real.log a) 0 := by
    simpa using
      (Real.hasDerivAt_exp (Real.log a * 0)).comp 0 hdlog
  have hslope := hd.tendsto_slope
  rw [show slope (fun x : ℝ => Real.exp (Real.log a * x)) 0 =
      fun x : ℝ => (Real.exp (Real.log a * x) - 1) / x by
    funext x
    change (x - 0)⁻¹ *
        (Real.exp (Real.log a * x) - Real.exp (Real.log a * 0)) =
      (Real.exp (Real.log a * x) - 1) / x
    simp [div_eq_mul_inv, mul_comm]] at hslope
  have hfun :
      exponentialIncrement a =
        fun x : ℝ =>
          (Real.exp (Real.log a * x) - 1) / x / Real.log a := by
    funext x
    unfold exponentialIncrement
    have hrpow :
        Real.rpow a x = Real.exp (Real.log a * x) := by
      exact Real.rpow_def_of_pos ha x
    rw [hrpow]
  rw [hfun]
  simpa [hlog] using hslope.div_const (Real.log a)

/-- Exercise 634, gap 2. -/
theorem gap2 (a : ℝ) (k : ℕ) :
    Filter.Tendsto (fun n : ℕ =>
      (k : ℝ) / (n : ℝ) ^ 2 * Real.log a)
      Filter.atTop (nhds 0) := by
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (hinv.pow 2).const_mul ((k : ℝ) * Real.log a)
  simpa [div_eq_mul_inv, inv_pow, mul_assoc, mul_left_comm, mul_comm] using h

/-- Exercise 634, gap 3. -/
theorem gap3 (a : ℝ) :
    Filter.Tendsto (exponentSum a) Filter.atTop
      (nhds ((1 / 2 : ℝ) * Real.log a)) := by
  have hsum : ∀ n : ℕ,
      (∑ k ∈ Finset.Icc 1 n, (k : ℝ)) =
        (n : ℝ) * ((n : ℝ) + 1) / 2 := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
        have hfin :
            Finset.Icc 1 (Nat.succ n) =
              insert (Nat.succ n) (Finset.Icc 1 n) := by
          ext k
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        rw [hfin]
        simp [ih]
        ring
  have hexponent : ∀ n : ℕ,
      exponentSum a n =
        ((n : ℝ) * ((n : ℝ) + 1) / 2) / (n : ℝ) ^ 2 *
          Real.log a := by
    intro n
    unfold exponentSum
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hsum]
    ring
  have hinv :
      Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hlim :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 / 2 : ℝ) * (1 + (n : ℝ)⁻¹) * Real.log a)
        Filter.atTop (nhds ((1 / 2 : ℝ) * Real.log a)) := by
    convert
      (((tendsto_const_nhds.add hinv).const_mul (1 / 2 : ℝ)).mul_const
        (Real.log a)) using 1 <;> ring
  refine hlim.congr' (Filter.eventually_atTop.2 ?_)
  refine ⟨1, ?_⟩
  intro n hn
  rw [hexponent]
  have hnNat : n ≠ 0 :=
    Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast hnNat
  field_simp [hn0]

/-- Exercise 634, gap 4. -/
theorem gap4 (a : ℝ) (ha : 0 < a) :
    Filter.Tendsto (incrementSum a) Filter.atTop
      (nhds ((1 / 2 : ℝ) * Real.log a)) := by
  by_cases ha1 : a = 1
  · subst a
    have hz : incrementSum (1 : ℝ) = fun _ : ℕ => 0 := by
      funext n
      simp [incrementSum]
    rw [hz]
    simpa using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
  · have hinv :
        Filter.Tendsto (fun n : ℕ => ((n : ℝ)⁻¹)) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    have hmajorant :
        Filter.Tendsto
          (fun n : ℕ => 2 * (Real.log a) ^ 2 / (n : ℝ))
          Filter.atTop (nhds 0) := by
      have h := hinv.const_mul (2 * (Real.log a) ^ 2)
      convert h using 1 <;> ring
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (2 * |Real.log a|)
    have hbounds : ∀ᶠ n : ℕ in Filter.atTop,
        0 ≤ incrementSum a n - exponentSum a n ∧
          incrementSum a n - exponentSum a n ≤
            2 * (Real.log a) ^ 2 / (n : ℝ) := by
      refine Filter.eventually_atTop.2 ⟨max 1 N, ?_⟩
      intro n hn
      have hn1 : 1 ≤ n := le_trans (Nat.le_max_left 1 N) hn
      have hnN : N ≤ n := le_trans (Nat.le_max_right 1 N) hn
      have hnNat : n ≠ 0 :=
        Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hnpos : (0 : ℝ) < (n : ℝ) := by
        exact_mod_cast (show 0 < n from lt_of_lt_of_le Nat.zero_lt_one hn1)
      have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
      have hnNreal : (N : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast hnN
      have hratio : |Real.log a| / (n : ℝ) ≤ (1 / 2 : ℝ) := by
        apply (div_le_iff₀ hnpos).2
        nlinarith
      have hterm : ∀ k ∈ Finset.Icc 1 n,
          0 ≤ Real.exp
                (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) - 1 -
                Real.log a * ((k : ℝ) / (n : ℝ) ^ 2) ∧
            Real.exp
                (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) - 1 -
                Real.log a * ((k : ℝ) / (n : ℝ) ^ 2) ≤
              2 * (Real.log a) ^ 2 / (n : ℝ) ^ 2 := by
        intro k hk
        have hk_le : k ≤ n := (Finset.mem_Icc.mp hk).2
        have hkreal : (k : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast hk_le
        have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
        have hn20 : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg (n : ℝ)
        have habsk : |(k : ℝ)| = (k : ℝ) := abs_of_nonneg hk0
        have habsn2 : |(n : ℝ) ^ 2| = (n : ℝ) ^ 2 := abs_of_nonneg hn20
        have habs :
            |Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)| ≤
              |Real.log a| / (n : ℝ) := by
          calc
            |Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)| =
                |Real.log a| * (k : ℝ) / (n : ℝ) ^ 2 := by
                  rw [abs_mul, abs_div, habsk, habsn2]
                  ring
            _ ≤ |Real.log a| * (n : ℝ) / (n : ℝ) ^ 2 := by
                  simp only [div_eq_mul_inv]
                  exact mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left hkreal (abs_nonneg _))
                    (inv_nonneg.mpr hn20)
            _ = |Real.log a| / (n : ℝ) := by
                  field_simp [hn0]
        have hremainder := exp_remainder_bound (le_trans habs hratio)
        refine ⟨hremainder.1, le_trans hremainder.2 ?_⟩
        have hqnonneg : 0 ≤ |Real.log a| / (n : ℝ) :=
          div_nonneg (abs_nonneg _) hnpos.le
        have hp := mul_nonneg
          (sub_nonneg.mpr habs)
          (add_nonneg hqnonneg
            (abs_nonneg (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2))))
        have hsq :
            (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) ^ 2 ≤
              (|Real.log a| / (n : ℝ)) ^ 2 := by
          nlinarith [sq_abs (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2))]
        have hqeq :
            (|Real.log a| / (n : ℝ)) ^ 2 =
              (Real.log a) ^ 2 / (n : ℝ) ^ 2 := by
          rw [div_pow, sq_abs]
        rw [hqeq] at hsq
        calc
          2 * (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) ^ 2 ≤
              2 * ((Real.log a) ^ 2 / (n : ℝ) ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by norm_num)
          _ = 2 * (Real.log a) ^ 2 / (n : ℝ) ^ 2 := by ring
      have hdiff :
          incrementSum a n - exponentSum a n =
            ∑ k ∈ Finset.Icc 1 n,
              (Real.exp
                  (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) - 1 -
                Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) := by
        rw [incrementSum, exponentSum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk
        have hpow :
            Real.rpow a ((k : ℝ) / (n : ℝ) ^ 2) =
              Real.exp
                (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) := by
          exact Real.rpow_def_of_pos ha ((k : ℝ) / (n : ℝ) ^ 2)
        rw [hpow]
        ring
      have hcard : (Finset.Icc 1 n).card = n := by
        rw [Nat.card_Icc]
        omega
      rw [hdiff]
      constructor
      · exact Finset.sum_nonneg fun k hk => (hterm k hk).1
      · calc
          (∑ k ∈ Finset.Icc 1 n,
              (Real.exp
                  (Real.log a * ((k : ℝ) / (n : ℝ) ^ 2)) - 1 -
                Real.log a * ((k : ℝ) / (n : ℝ) ^ 2))) ≤
              ∑ _k ∈ Finset.Icc 1 n,
                (2 * (Real.log a) ^ 2 / (n : ℝ) ^ 2) := by
                  exact Finset.sum_le_sum fun k hk => (hterm k hk).2
          _ = (n : ℝ) *
                (2 * (Real.log a) ^ 2 / (n : ℝ) ^ 2) := by
                  simp [hcard]
          _ = 2 * (Real.log a) ^ 2 / (n : ℝ) := by
                  field_simp [hn0]
    have herror :
        Filter.Tendsto
          (fun n : ℕ => incrementSum a n - exponentSum a n)
          Filter.atTop (nhds 0) := by
      exact Filter.Tendsto.squeeze'
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop (nhds 0))
        hmajorant
        (hbounds.mono fun n h => h.1)
        (hbounds.mono fun n h => h.2)
    simpa using herror.add (gap3 a)

end

end ProofGap.Exercise634
