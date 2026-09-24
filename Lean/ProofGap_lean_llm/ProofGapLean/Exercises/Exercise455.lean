import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise455

noncomputable section

def root (m : ℤ) (x : ℝ) : ℝ := Real.rpow x (1 / (m : ℝ))
def quotient (m n : ℤ) (x : ℝ) : ℝ :=
  (root m x - 1) / (root n x - 1)
def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 455, gap 1; replace geometric ellipses by the resulting identity near `x=1`. -/
private theorem inv_mul_div_inv_mul_of_ne
    (a b c : ℝ) (hc : c ≠ 0) :
    (c⁻¹ * a) / (c⁻¹ * b) = a / b := by
  by_cases hb : b = 0
  · simp [hb]
  · field_simp [hc, hb]

private theorem hasLimitAt_quotient_of_ne_zero
    (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    HasLimitAt (quotient m n) 1 ((n : ℝ) / m) := by
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast hm
  have hnR : (n : ℝ) ≠ 0 := by
    exact_mod_cast hn
  have hdm :
      HasDerivAt (fun x : ℝ => Real.rpow x (1 / (m : ℝ)))
        (1 / (m : ℝ)) 1 := by
    simpa only [Real.one_rpow, mul_one] using
      (Real.hasDerivAt_rpow_const (Or.inl one_ne_zero) :
        HasDerivAt (fun x : ℝ => Real.rpow x (1 / (m : ℝ)))
          ((1 / (m : ℝ)) *
            Real.rpow 1 ((1 / (m : ℝ)) - 1)) 1)
  have hdn :
      HasDerivAt (fun x : ℝ => Real.rpow x (1 / (n : ℝ)))
        (1 / (n : ℝ)) 1 := by
    simpa only [Real.one_rpow, mul_one] using
      (Real.hasDerivAt_rpow_const (Or.inl one_ne_zero) :
        HasDerivAt (fun x : ℝ => Real.rpow x (1 / (n : ℝ)))
          ((1 / (n : ℝ)) *
            Real.rpow 1 ((1 / (n : ℝ)) - 1)) 1)
  have hone_m : Real.rpow 1 (1 / (m : ℝ)) = 1 := by
    exact Real.one_rpow _
  have hone_n : Real.rpow 1 (1 / (n : ℝ)) = 1 := by
    exact Real.one_rpow _
  have htm :
      Filter.Tendsto
        (fun x : ℝ =>
          (x - 1)⁻¹ * (Real.rpow x (1 / (m : ℝ)) - 1))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (1 / (m : ℝ))) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hdm
    change Filter.Tendsto
      (fun x : ℝ =>
        (x - 1)⁻¹ •
          (Real.rpow x (1 / (m : ℝ)) -
            Real.rpow 1 (1 / (m : ℝ))))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (1 / (m : ℝ))) at h
    rw [hone_m] at h
    simpa only [smul_eq_mul] using h
  have htn :
      Filter.Tendsto
        (fun x : ℝ =>
          (x - 1)⁻¹ * (Real.rpow x (1 / (n : ℝ)) - 1))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (1 / (n : ℝ))) := by
    have h := hasDerivAt_iff_tendsto_slope.mp hdn
    change Filter.Tendsto
      (fun x : ℝ =>
        (x - 1)⁻¹ •
          (Real.rpow x (1 / (n : ℝ)) -
            Real.rpow 1 (1 / (n : ℝ))))
      (nhdsWithin 1 ({1} : Set ℝ)ᶜ) (nhds (1 / (n : ℝ))) at h
    rw [hone_n] at h
    simpa only [smul_eq_mul] using h
  have hnexp : (1 / (n : ℝ)) ≠ 0 :=
    div_ne_zero one_ne_zero hnR
  have hlim := htm.div htn hnexp
  have hraw :
      Filter.Tendsto
        (fun x : ℝ =>
          (Real.rpow x (1 / (m : ℝ)) - 1) /
            (Real.rpow x (1 / (n : ℝ)) - 1))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds ((1 / (m : ℝ)) / (1 / (n : ℝ)))) := by
    apply hlim.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : x ≠ (1 : ℝ) := by
      simpa using hx
    have hxsub : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    exact inv_mul_div_inv_mul_of_ne
      (Real.rpow x (1 / (m : ℝ)) - 1)
      (Real.rpow x (1 / (n : ℝ)) - 1) (x - 1) hxsub
  unfold HasLimitAt quotient root
  convert hraw using 1
  field_simp [hmR, hnR]

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    HasLimitAt (quotient m n) 1 ((n : ℝ) / m) := by
  simpa using
    hasLimitAt_quotient_of_ne_zero (m : ℤ) (n : ℤ) (by omega) (by omega)

/-- Exercise 455, gap 2. -/
theorem gap2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    HasLimitAt (quotient m n) 1 ((n : ℝ) / m) := by
  exact gap1 m n hm hn

/-- Exercise 455, gap 3. -/
theorem gap3 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n') : ∀ x, 0 < x →
    quotient (-(m' : ℤ)) (-(n' : ℤ)) x =
      ((1 - root m' x) / (1 - root n' x)) * (root n' x / root m' x) := by
  intro x hx
  have hxm : root (m' : ℤ) x ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hxn : root (n' : ℤ) x ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hx _)
  have hrm : root (-(m' : ℤ)) x = (root (m' : ℤ) x)⁻¹ := by
    simp [root, Real.rpow_neg (le_of_lt hx)]
  have hrn : root (-(n' : ℤ)) x = (root (n' : ℤ) x)⁻¹ := by
    simp [root, Real.rpow_neg (le_of_lt hx)]
  unfold quotient
  rw [hrm, hrn]
  by_cases hxm1 : root (m' : ℤ) x = 1
  · simp [hxm1]
  by_cases hxn1 : root (n' : ℤ) x = 1
  · simp [hxn1]
  field_simp [hxm, hxn, hxm1, hxn1]

/-- Exercise 455, gap 4. -/
theorem gap4 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n') :
    HasLimitAt (quotient (-(m' : ℤ)) (-(n' : ℤ))) 1 ((n' : ℝ) / m') := by
  simpa using
    hasLimitAt_quotient_of_ne_zero (-(m' : ℤ)) (-(n' : ℤ))
      (by omega) (by omega)

/-- Exercise 455, gap 5. -/
theorem gap5 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n') :
    (n' : ℝ) / m' = ((-(n' : ℤ) : ℤ) : ℝ) / (-(m' : ℤ) : ℤ) := by
  norm_num

/-- Exercise 455, gap 6. -/
theorem gap6 (m' n' : ℕ) (hm : 0 < m') (hn : 0 < n') :
    HasLimitAt (quotient (-(m' : ℤ)) (-(n' : ℤ))) 1
      (((-(n' : ℤ) : ℤ) : ℝ) / (-(m' : ℤ) : ℤ)) := by
  rw [← gap5 m' n' hm hn]
  exact gap4 m' n' hm hn

/-- Exercise 455, gap 7. -/
theorem gap7 (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    HasLimitAt (quotient m n) 1 ((n : ℝ) / m) := by
  exact hasLimitAt_quotient_of_ne_zero m n hm hn

/-- Exercise 455, gap 8. -/
theorem gap8 (m n : ℤ) (hm : m ≠ 0) (hn : n ≠ 0) :
    HasLimitAt (quotient m n) 1 ((n : ℝ) / m) := by
  exact gap7 m n hm hn

end

end ProofGap.Exercise455
