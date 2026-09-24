import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise587

noncomputable section

def seq (x : ℝ) (n : ℕ) : ℝ :=
  n * Real.arctan (1 / (n * (x ^ 2 + 1) + x)) *
    Real.tan (Real.pi / 4 + x / (2 * n)) ^ n
def normalized (x : ℝ) (n : ℕ) : ℝ :=
  (Real.arctan (1 / (n * (x ^ 2 + 1) + x)) /
    (1 / (n * (x ^ 2 + 1) + x))) *
  (n / (n * (x ^ 2 + 1) + x)) *
  Real.tan (Real.pi / 4 + x / (2 * n)) ^ n

/-- Exercise 587, gap 1. -/
private theorem eventually_seq_eq_normalized (x : ℝ) :
    (fun n : ℕ => seq x n) =ᶠ[Filter.atTop]
      (fun n : ℕ => normalized x n) := by
  let A : ℝ := x ^ 2 + 1
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [sq_nonneg x]
  have hnat :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hbase :
      Filter.Tendsto (fun n : ℕ => A + x * (n : ℝ)⁻¹)
        Filter.atTop (nhds A) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hn_ne : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast (Nat.ne_of_gt hn)
  have hbase_ne : ∀ᶠ n : ℕ in Filter.atTop, A + x * (n : ℝ)⁻¹ ≠ 0 :=
    hbase.eventually_ne (ne_of_gt hApos)
  filter_upwards [hn_ne, hbase_ne] with n hn hb
  have hd : (n : ℝ) * (x ^ 2 + 1) + x ≠ 0 := by
    have hid :
        (n : ℝ) * (x ^ 2 + 1) + x =
          (n : ℝ) * (A + x * (n : ℝ)⁻¹) := by
      dsimp [A]
      field_simp [hn]
    rw [hid]
    exact mul_ne_zero hn hb
  unfold seq normalized
  field_simp [hd, hn]

theorem gap1 (x L : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop (nhds L) ↔
      Filter.Tendsto (normalized x) Filter.atTop (nhds L) := by
  constructor
  · intro h
    exact h.congr' (eventually_seq_eq_normalized x)
  · intro h
    exact h.congr' (eventually_seq_eq_normalized x).symm

/-- Exercise 587, gap 2. -/
theorem gap2 (x : ℝ) :
    Filter.Tendsto (normalized x) Filter.atTop
      (nhds (Real.exp x / (1 + x ^ 2))) := by
  let A : ℝ := x ^ 2 + 1
  have hApos : 0 < A := by
    dsimp [A]
    nlinarith [sq_nonneg x]
  have hAne : A ≠ 0 := ne_of_gt hApos
  have hnat :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hinv :
      Filter.Tendsto (fun n : ℕ => (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnat
  have hbase :
      Filter.Tendsto (fun n : ℕ => A + x * (n : ℝ)⁻¹)
        Filter.atTop (nhds A) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hbaseInv :
      Filter.Tendsto (fun n : ℕ => (A + x * (n : ℝ)⁻¹)⁻¹)
        Filter.atTop (nhds A⁻¹) :=
    hbase.inv₀ hAne
  have hn_ne : ∀ᶠ n : ℕ in Filter.atTop, (n : ℝ) ≠ 0 := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact_mod_cast (Nat.ne_of_gt hn)
  have hbase_ne : ∀ᶠ n : ℕ in Filter.atTop, A + x * (n : ℝ)⁻¹ ≠ 0 :=
    hbase.eventually_ne hAne
  have hB :
      Filter.Tendsto
        (fun n : ℕ => (n : ℝ) / ((n : ℝ) * (x ^ 2 + 1) + x))
        Filter.atTop (nhds (1 / A)) := by
    have h := hbaseInv
    have heq :
        (fun n : ℕ => (A + x * (n : ℝ)⁻¹)⁻¹) =ᶠ[Filter.atTop]
          (fun n : ℕ => (n : ℝ) / ((n : ℝ) * (x ^ 2 + 1) + x)) := by
      filter_upwards [hn_ne] with n hn
      dsimp [A]
      field_simp [hn]
      <;> ring
    simpa [one_div] using h.congr' heq
  have hu :
      Filter.Tendsto
        (fun n : ℕ => 1 / ((n : ℝ) * (x ^ 2 + 1) + x))
        Filter.atTop (nhds 0) := by
    have h := hinv.mul hbaseInv
    have heq :
        (fun n : ℕ => (n : ℝ)⁻¹ * (A + x * (n : ℝ)⁻¹)⁻¹) =ᶠ[Filter.atTop]
          (fun n : ℕ => 1 / ((n : ℝ) * (x ^ 2 + 1) + x)) := by
      filter_upwards [hn_ne] with n hn
      dsimp [A]
      field_simp [hn]
      <;> ring
    simpa using h.congr' heq
  have hu_ne :
      ∀ᶠ n : ℕ in Filter.atTop,
        1 / ((n : ℝ) * (x ^ 2 + 1) + x) ≠ 0 := by
    filter_upwards [hn_ne, hbase_ne] with n hn hb
    have hd : (n : ℝ) * (x ^ 2 + 1) + x ≠ 0 := by
      have hid :
          (n : ℝ) * (x ^ 2 + 1) + x =
            (n : ℝ) * (A + x * (n : ℝ)⁻¹) := by
        dsimp [A]
        field_simp [hn]
        <;> ring
      rw [hid]
      exact mul_ne_zero hn hb
    exact one_div_ne_zero hd
  have hu0 :
      Filter.Tendsto
        (fun n : ℕ => 1 / ((n : ℝ) * (x ^ 2 + 1) + x))
        Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨hu, ?_⟩
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu_ne
  have harctanDeriv : HasDerivAt Real.arctan 1 0 := by
    simpa using Real.hasDerivAt_arctan 0
  have hArctanRaw :
      Filter.Tendsto
        (fun n : ℕ =>
          (1 / ((n : ℝ) * (x ^ 2 + 1) + x))⁻¹ *
            Real.arctan (1 / ((n : ℝ) * (x ^ 2 + 1) + x)))
        Filter.atTop (nhds 1) := by
    have h := harctanDeriv.tendsto_slope_zero.comp hu0
    simpa only [Function.comp_apply, zero_add, Real.arctan_zero, sub_zero] using h
  have hArctan :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.arctan (1 / ((n : ℝ) * (x ^ 2 + 1) + x)) /
            (1 / ((n : ℝ) * (x ^ 2 + 1) + x)))
        Filter.atTop (nhds 1) := by
    refine hArctanRaw.congr' (Filter.Eventually.of_forall ?_)
    intro n
    let u : ℝ := 1 / ((n : ℝ) * (x ^ 2 + 1) + x)
    change u⁻¹ * Real.arctan u = Real.arctan u / u
    simpa only [div_eq_mul_inv] using (mul_comm u⁻¹ (Real.arctan u))
  have ht :
      Filter.Tendsto (fun n : ℕ => x / (2 * (n : ℝ)))
        Filter.atTop (nhds 0) := by
    have hxconst :
        Filter.Tendsto (fun _ : ℕ => (x / 2 : ℝ))
          Filter.atTop (nhds (x / 2)) :=
      tendsto_const_nhds
    have h := hxconst.mul hinv
    simpa [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm, mul_assoc] using h
  have hC :
      Filter.Tendsto
        (fun n : ℕ =>
          Real.tan (Real.pi / 4 + x / (2 * (n : ℝ))) ^ n)
        Filter.atTop (nhds (Real.exp x)) := by
    by_cases hx : x = 0
    · subst x
      simpa [Real.tan_pi_div_four] using
        (tendsto_const_nhds :
          Filter.Tendsto (fun _ : ℕ => (1 : ℝ)) Filter.atTop (nhds 1))
    · have ht_ne :
          ∀ᶠ n : ℕ in Filter.atTop, x / (2 * (n : ℝ)) ≠ 0 := by
        filter_upwards [hn_ne] with n hn
        exact div_ne_zero hx (mul_ne_zero (by norm_num) hn)
      have ht0 :
          Filter.Tendsto (fun n : ℕ => x / (2 * (n : ℝ)))
            Filter.atTop (nhdsWithin 0 {0}ᶜ) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨ht, ?_⟩
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ht_ne
      have hcos : Real.cos (Real.pi / 4) ≠ 0 := by
        rw [Real.cos_pi_div_four]
        positivity
      have htanDeriv : HasDerivAt Real.tan 2 (Real.pi / 4) := by
        convert Real.hasDerivAt_tan hcos using 1
        rw [Real.cos_pi_div_four, div_pow]
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      have hlog : HasDerivAt Real.log 1 (1 : ℝ) := by
        simpa using Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)
      have hlogAtTan :
          HasDerivAt Real.log 1 (Real.tan (Real.pi / 4)) := by
        simpa only [Real.tan_pi_div_four] using hlog
      have hlogDeriv :
          HasDerivAt (fun y : ℝ => Real.log (Real.tan y)) 2
            (Real.pi / 4) := by
        have hcomp := hlogAtTan.comp (Real.pi / 4) htanDeriv
        simpa only [one_mul] using hcomp
      have hqRaw :
          Filter.Tendsto
            (fun n : ℕ =>
              (x / (2 * (n : ℝ)))⁻¹ *
                (Real.log
                    (Real.tan
                      (Real.pi / 4 + x / (2 * (n : ℝ)))) -
                  Real.log (Real.tan (Real.pi / 4))))
            Filter.atTop (nhds 2) := by
        have h := hlogDeriv.tendsto_slope_zero.comp ht0
        simpa only [Function.comp_apply] using h
      have hq :
          Filter.Tendsto
            (fun n : ℕ =>
              Real.log
                  (Real.tan
                    (Real.pi / 4 + x / (2 * (n : ℝ)))) /
                (x / (2 * (n : ℝ))))
            Filter.atTop (nhds 2) := by
        refine hqRaw.congr' (Filter.Eventually.of_forall ?_)
        intro n
        let t : ℝ := x / (2 * (n : ℝ))
        change
          t⁻¹ *
              (Real.log (Real.tan (Real.pi / 4 + t)) -
                Real.log (Real.tan (Real.pi / 4))) =
            Real.log (Real.tan (Real.pi / 4 + t)) / t
        rw [Real.tan_pi_div_four, Real.log_one, sub_zero]
        simpa only [div_eq_mul_inv] using
          (mul_comm t⁻¹ (Real.log (Real.tan (Real.pi / 4 + t))))
      have hscaled :
          Filter.Tendsto
            (fun n : ℕ =>
              (x / 2) *
                (Real.log
                    (Real.tan
                      (Real.pi / 4 + x / (2 * (n : ℝ)))) /
                  (x / (2 * (n : ℝ)))))
            Filter.atTop (nhds x) := by
        convert tendsto_const_nhds.mul hq using 1 <;> ring
      have hlogn :
          Filter.Tendsto
            (fun n : ℕ =>
              (n : ℝ) *
                Real.log
                  (Real.tan
                    (Real.pi / 4 + x / (2 * (n : ℝ)))))
            Filter.atTop (nhds x) := by
        apply hscaled.congr'
        filter_upwards [hn_ne] with n hn
        field_simp [hx, hn]
        <;> ring
      have hangle :
          Filter.Tendsto
            (fun n : ℕ => Real.pi / 4 + x / (2 * (n : ℝ)))
            Filter.atTop (nhds (Real.pi / 4)) := by
        simpa using tendsto_const_nhds.add ht
      have htan :
          Filter.Tendsto
            (fun n : ℕ =>
              Real.tan (Real.pi / 4 + x / (2 * (n : ℝ))))
            Filter.atTop (nhds 1) := by
        simpa [Real.tan_pi_div_four] using
          htanDeriv.continuousAt.tendsto.comp hangle
      have hpos :
          ∀ᶠ n : ℕ in Filter.atTop,
            0 < Real.tan (Real.pi / 4 + x / (2 * (n : ℝ))) :=
        htan.eventually (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
      have hexpAt :
          Filter.Tendsto Real.exp (nhds x) (nhds (Real.exp x)) :=
        Real.continuous_exp.continuousAt
      have hexp :
          Filter.Tendsto
            (fun n : ℕ =>
              Real.exp
                ((n : ℝ) *
                  Real.log
                    (Real.tan
                      (Real.pi / 4 + x / (2 * (n : ℝ))))))
            Filter.atTop (nhds (Real.exp x)) :=
        hexpAt.comp hlogn
      apply hexp.congr'
      filter_upwards [hpos] with n hp
      calc
        Real.exp
            ((n : ℝ) *
              Real.log
                (Real.tan
                  (Real.pi / 4 + x / (2 * (n : ℝ))))) =
            (Real.exp
              (Real.log
                (Real.tan
                  (Real.pi / 4 + x / (2 * (n : ℝ)))))) ^ n := by
              rw [Real.exp_nat_mul]
        _ = Real.tan (Real.pi / 4 + x / (2 * (n : ℝ))) ^ n := by
              rw [Real.exp_log hp]
  have hprod :
      Filter.Tendsto
        (fun n : ℕ =>
          (Real.arctan (1 / ((n : ℝ) * (x ^ 2 + 1) + x)) /
              (1 / ((n : ℝ) * (x ^ 2 + 1) + x))) *
            ((n : ℝ) / ((n : ℝ) * (x ^ 2 + 1) + x)) *
            Real.tan (Real.pi / 4 + x / (2 * (n : ℝ))) ^ n)
        Filter.atTop (nhds ((1 : ℝ) * (1 / A) * Real.exp x)) :=
    (hArctan.mul hB).mul hC
  have hlimit :
      (1 : ℝ) * (1 / A) * Real.exp x = Real.exp x / (1 + x ^ 2) := by
    dsimp [A]
    rw [show 1 + x ^ 2 = x ^ 2 + 1 by ring]
    simp only [one_mul, div_eq_mul_inv]
    ring
  rw [← hlimit]
  simpa only [normalized] using hprod

/-- Exercise 587, gap 3. -/
theorem gap3 (x : ℝ) :
    Filter.Tendsto (seq x) Filter.atTop
      (nhds (Real.exp x / (1 + x ^ 2))) := by
  exact (gap1 x (Real.exp x / (1 + x ^ 2))).mpr (gap2 x)

end

end ProofGap.Exercise587
