import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.PSeries

namespace ProofGap.Exercise2631

noncomputable section

open Filter

def term (n : ℕ) : ℝ :=
  Real.exp (-3 * Real.sqrt n)

def comparison (n : ℕ) : ℝ :=
  1 / Real.rpow n (4 / 3 : ℝ)

theorem gap1 (A : ℝ) :
    ∃ T : ℝ, ∀ t ≥ T, A * t ^ 4 ≤ Real.exp t := by
  have hlarge : ∀ᶠ t : ℝ in atTop, A ≤ Real.exp t / t ^ 4 :=
    Real.tendsto_exp_div_pow_atTop 4 (eventually_ge_atTop A)
  have hpos : ∀ᶠ t : ℝ in atTop, 0 < t := eventually_gt_atTop 0
  obtain ⟨T, hT⟩ := eventually_atTop.1 (hlarge.and hpos)
  refine ⟨T, fun t ht => ?_⟩
  have h := hT t ht
  rw [le_div_iff₀ (pow_pos h.2 4)] at h
  exact h.1

theorem gap2 (A : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n ≥ N, A * Real.rpow n (4 / 3 : ℝ) ≤ Real.exp (3 * Real.sqrt n) := by
  by_cases hA : 0 < A
  · obtain ⟨T, hT⟩ := gap1 A
    have hsqrtTop : Tendsto (fun n : ℕ => 3 * Real.sqrt (n : ℝ)) atTop atTop := by
      exact (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_mul_atTop
        (by norm_num)
    have hEventuallyT : ∀ᶠ n : ℕ in atTop, T ≤ 3 * Real.sqrt (n : ℝ) :=
      hsqrtTop (eventually_ge_atTop T)
    have hEventually : ∀ᶠ n : ℕ in atTop,
        1 ≤ n ∧ T ≤ 3 * Real.sqrt (n : ℝ) :=
      (eventually_ge_atTop 1).and hEventuallyT
    obtain ⟨N, hN⟩ := eventually_atTop.1 hEventually
    refine ⟨N, (hN N le_rfl).1, fun n hn => ?_⟩
    have hnData := hN n hn
    have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnData.1
    have hrpow : Real.rpow (n : ℝ) (4 / 3 : ℝ) ≤ (n : ℝ) ^ 2 := by
      calc
        Real.rpow (n : ℝ) (4 / 3 : ℝ) ≤ Real.rpow (n : ℝ) (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hnOne (by norm_num)
        _ = (n : ℝ) ^ 2 := Real.rpow_two _
    have hsqrtSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hpower : (n : ℝ) ^ 2 ≤ (3 * Real.sqrt (n : ℝ)) ^ 4 := by
      calc
        (n : ℝ) ^ 2 ≤ 81 * (n : ℝ) ^ 2 := by
          nlinarith [sq_nonneg (n : ℝ)]
        _ = (3 * Real.sqrt (n : ℝ)) ^ 4 := by
          rw [show (3 * Real.sqrt (n : ℝ)) ^ 4 =
              81 * (Real.sqrt (n : ℝ) ^ 2) ^ 2 by ring, hsqrtSq]
    exact (mul_le_mul_of_nonneg_left (hrpow.trans hpower) hA.le).trans
      (hT _ hnData.2)
  · have hAnonpos : A ≤ 0 := le_of_not_gt hA
    refine ⟨1, le_rfl, fun n hn => ?_⟩
    have hleft : A * Real.rpow n (4 / 3 : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hAnonpos
        (Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)) _)
    exact hleft.trans (Real.exp_pos _).le

theorem gap3 (A : ℝ) (hA : 0 < A) (N n : ℕ)
    (hN : 1 ≤ N) (hn : N ≤ n)
    (hbound : A * Real.rpow n (4 / 3 : ℝ) ≤ Real.exp (3 * Real.sqrt n)) :
    0 < term n ∧ term n ≤ (1 / A) * comparison n := by
  have hnOne : 1 ≤ n := hN.trans hn
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hrpowpos : 0 < Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hdenpos : 0 < A * Real.rpow (n : ℝ) (4 / 3 : ℝ) :=
    mul_pos hA hrpowpos
  constructor
  · unfold term
    positivity
  · unfold term comparison
    rw [show -3 * Real.sqrt (n : ℝ) = -(3 * Real.sqrt (n : ℝ)) by ring,
      Real.exp_neg]
    have hinv : 1 / Real.exp (3 * Real.sqrt (n : ℝ)) ≤
        1 / (A * Real.rpow (n : ℝ) (4 / 3 : ℝ)) :=
      one_div_le_one_div_of_le hdenpos hbound
    calc
      (Real.exp (3 * Real.sqrt (n : ℝ)))⁻¹ =
          1 / Real.exp (3 * Real.sqrt (n : ℝ)) := by simp
      _ ≤ 1 / (A * Real.rpow (n : ℝ) (4 / 3 : ℝ)) := hinv
      _ = (1 / A) * (1 / Real.rpow (n : ℝ) (4 / 3 : ℝ)) := by
        field_simp [hA.ne', hrpowpos.ne']

theorem gap4 :
    Summable (fun n : ℕ => comparison (n + 1)) := by
  have hall : Summable comparison := by
    unfold comparison
    exact Real.summable_one_div_nat_rpow.mpr (by norm_num)
  exact (summable_nat_add_iff 1).mpr hall

theorem gap5 :
    Summable (fun n : ℕ => term (n + 1)) := by
  obtain ⟨N, hN, hbound⟩ := gap2 1
  have hcomparisonAll : Summable comparison :=
    (summable_nat_add_iff 1).mp gap4
  have hcomparisonTail : Summable (fun k : ℕ => comparison (N + k)) :=
    by simpa [Nat.add_comm] using (summable_nat_add_iff N).mpr hcomparisonAll
  have htermTail : Summable (fun k : ℕ => term (N + k)) := by
    refine hcomparisonTail.of_nonneg_of_le ?_ ?_
    · intro k
      exact (gap3 1 one_pos N (N + k) hN (by omega)
        (hbound (N + k) (by omega))).1.le
    · intro k
      simpa using (gap3 1 one_pos N (N + k) hN (by omega)
        (hbound (N + k) (by omega))).2
  have hall : Summable term := by
    apply (summable_nat_add_iff N).mp
    simpa [Nat.add_comm] using htermTail
  exact (summable_nat_add_iff 1).mpr hall

theorem gap6 :
    Summable (fun n : ℕ => term (n + 1)) := by
  exact gap5

end

end ProofGap.Exercise2631
