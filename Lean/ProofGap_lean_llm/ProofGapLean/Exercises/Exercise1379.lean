import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1379

noncomputable section

open Topology Filter

def f (m : ℕ) (a x : ℝ) : ℝ :=
  Real.rpow (a ^ m + x) (1 / (m : ℝ))

def firstFormula (m : ℕ) (a x : ℝ) : ℝ :=
  (1 / (m : ℝ)) *
    Real.rpow (a ^ m + x) ((1 - (m : ℝ)) / (m : ℝ))

def secondFormula (m : ℕ) (a x : ℝ) : ℝ :=
  ((1 - (m : ℝ)) / (m : ℝ) ^ 2) *
    Real.rpow (a ^ m + x) ((1 - 2 * (m : ℝ)) / (m : ℝ))

def taylorPolynomial (m : ℕ) (a x : ℝ) : ℝ :=
  a + x / ((m : ℝ) * Real.rpow a ((m : ℝ) - 1)) +
    ((1 - (m : ℝ)) * x ^ 2) /
      (2 * (m : ℝ) ^ 2 * Real.rpow a (2 * (m : ℝ) - 1))

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private theorem m_ne_zero (m : ℕ) (hm : 1 ≤ m) : (m : ℝ) ≠ 0 := by
  exact_mod_cast (Nat.ne_zero_of_lt hm)

private theorem pow_rpow_eq (m : ℕ) (a z : ℝ) (ha : 0 < a) :
    Real.rpow (a ^ m) z = Real.rpow a ((m : ℝ) * z) := by
  exact (Real.rpow_natCast_mul ha.le m z).symm

private theorem deriv_f_formula (m : ℕ) (a x : ℝ) (hm : 1 ≤ m)
    (hx : 0 < a ^ m + x) :
    deriv (f m a) x = firstFormula m a x := by
  have hi : HasDerivAt (fun y : ℝ => a ^ m + y) 1 x := by
    simpa only [Pi.add_apply, zero_add] using
      HasDerivAt.add (hasDerivAt_const x (a ^ m)) (hasDerivAt_id x)
  have hd := (hi.rpow_const (p := 1 / (m : ℝ))
    (Or.inl (ne_of_gt hx))).deriv
  have he : 1 / (m : ℝ) - 1 =
      (1 - (m : ℝ)) / (m : ℝ) := by
    calc
      1 / (m : ℝ) - 1 =
          1 / (m : ℝ) - (m : ℝ) / (m : ℝ) := by
            rw [div_self (m_ne_zero m hm)]
      _ = (1 - (m : ℝ)) / (m : ℝ) := by
        rw [sub_div]
  unfold f firstFormula
  rw [show deriv (fun y : ℝ =>
    Real.rpow (a ^ m + y) (1 / (m : ℝ))) x =
      1 * (1 / (m : ℝ)) *
        Real.rpow (a ^ m + x) (1 / (m : ℝ) - 1) by simpa using hd]
  simp only [one_mul]
  rw [he]

private theorem eventually_positive (m : ℕ) (a x : ℝ)
    (hx : 0 < a ^ m + x) :
    ∀ᶠ y in nhds x, 0 < a ^ m + y := by
  have hc : ContinuousAt (fun y : ℝ => a ^ m + y) x := by fun_prop
  exact hc.eventually (isOpen_Ioi.mem_nhds hx)

private theorem deriv_first_formula (m : ℕ) (a x : ℝ) (hm : 1 ≤ m)
    (hx : 0 < a ^ m + x) :
    HasDerivAt (firstFormula m a) (secondFormula m a x) x := by
  have hi : HasDerivAt (fun y : ℝ => a ^ m + y) 1 x := by
    simpa only [Pi.add_apply, zero_add] using
      HasDerivAt.add (hasDerivAt_const x (a ^ m)) (hasDerivAt_id x)
  have hp := hi.rpow_const
    (p := (1 - (m : ℝ)) / (m : ℝ)) (Or.inl (ne_of_gt hx))
  have hc : HasDerivAt (fun _ : ℝ => (1 / (m : ℝ))) 0 x :=
    hasDerivAt_const x (1 / (m : ℝ))
  have hmul := HasDerivAt.mul hc hp
  unfold firstFormula
  refine hmul.congr_deriv ?_
  unfold secondFormula
  simp only [zero_mul, zero_add, one_mul]
  change
    (1 / (m : ℝ)) *
        (((1 - (m : ℝ)) / (m : ℝ)) *
          (a ^ m + x) ^ (((1 - (m : ℝ)) / (m : ℝ)) - 1)) =
      ((1 - (m : ℝ)) / (m : ℝ) ^ 2) *
        (a ^ m + x) ^ ((1 - 2 * (m : ℝ)) / (m : ℝ))
  have he :
      (1 - (m : ℝ)) / (m : ℝ) - 1 =
        (1 - 2 * (m : ℝ)) / (m : ℝ) := by
    field_simp [m_ne_zero m hm]
    ring
  rw [he]
  ring

private theorem second_deriv_formula (m : ℕ) (a x : ℝ) (hm : 1 ≤ m)
    (hx : 0 < a ^ m + x) :
    deriv (deriv (f m a)) x = secondFormula m a x := by
  have heq : deriv (f m a) =ᶠ[nhds x] firstFormula m a := by
    filter_upwards [eventually_positive m a x hx] with y hy
    exact deriv_f_formula m a y hm hy
  exact ((deriv_first_formula m a x hm hx).congr_of_eventuallyEq heq).deriv

theorem gap1 (m : ℕ) (a x : ℝ) (hm : 1 ≤ m)
    (hx : 0 < a ^ m + x) :
    iterDeriv 1 (f m a) x = firstFormula m a x := by
  exact deriv_f_formula m a x hm hx

theorem gap2 (m : ℕ) (a x : ℝ) (hm : 1 ≤ m)
    (hx : 0 < a ^ m + x) :
    iterDeriv 2 (f m a) x = secondFormula m a x := by
  exact second_deriv_formula m a x hm hx

theorem gap3 (m : ℕ) (a : ℝ) (hm : 1 ≤ m) (ha : 0 < a) :
    f m a 0 = a := by
  unfold f
  simp only [add_zero, one_div]
  exact Real.pow_rpow_inv_natCast ha.le (Nat.ne_zero_of_lt hm)

theorem gap4 (m : ℕ) (a : ℝ) (hm : 1 ≤ m) (ha : 0 < a) :
    iterDeriv 1 (f m a) 0 =
      (1 / (m : ℝ)) * Real.rpow a (1 - (m : ℝ)) := by
  change deriv (f m a) 0 =
    (1 / (m : ℝ)) * Real.rpow a (1 - (m : ℝ))
  rw [deriv_f_formula m a 0 hm (by positivity)]
  unfold firstFormula
  simp only [add_zero]
  rw [pow_rpow_eq m a _ ha]
  congr 2
  field_simp [m_ne_zero m hm]

theorem gap5 (m : ℕ) (a : ℝ) (hm : 1 ≤ m) (ha : 0 < a) :
    iterDeriv 2 (f m a) 0 =
      ((1 - (m : ℝ)) / (m : ℝ) ^ 2) *
        Real.rpow a (1 - 2 * (m : ℝ)) := by
  change deriv (deriv (f m a)) 0 =
    ((1 - (m : ℝ)) / (m : ℝ) ^ 2) *
      Real.rpow a (1 - 2 * (m : ℝ))
  rw [second_deriv_formula m a 0 hm (by positivity)]
  unfold secondFormula
  simp only [add_zero]
  rw [pow_rpow_eq m a _ ha]
  congr 2
  field_simp [m_ne_zero m hm]

theorem gap6 (m : ℕ) (a : ℝ) (hm : 1 ≤ m) (ha : 0 < a) :
    AgreesToOrderAt (f m a) (taylorPolynomial m a) 0 2 := by
  let s : Set ℝ := Set.Ioi (-(a ^ m))
  have h0s : (0 : ℝ) ∈ s := by
    simp only [s, Set.mem_Ioi]
    exact neg_lt_zero.mpr (pow_pos ha m)
  have hcont : ContDiffOn ℝ 2 (f m a) s := by
    have hbase : ContDiffOn ℝ 2 (fun x : ℝ => a ^ m + x) s :=
      contDiffOn_const.add contDiffOn_id
    unfold f
    apply hbase.rpow_const_of_ne
    intro x hx
    have hxpos : 0 < a ^ m + x := by
      simp only [s, Set.mem_Ioi] at hx
      linarith
    exact hxpos.ne'
  have hiter0 : iteratedDerivWithin 0 (f m a) s 0 = a := by
    simp only [iteratedDerivWithin_zero]
    exact gap3 m a hm ha
  have hiter1 : iteratedDerivWithin 1 (f m a) s 0 =
      (1 / (m : ℝ)) * Real.rpow a (1 - (m : ℝ)) := by
    calc
      iteratedDerivWithin 1 (f m a) s 0 = (deriv^[1]) (f m a) 0 :=
        iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi h0s
      _ = (1 / (m : ℝ)) * Real.rpow a (1 - (m : ℝ)) :=
        gap4 m a hm ha
  have hiter2 : iteratedDerivWithin 2 (f m a) s 0 =
      ((1 - (m : ℝ)) / (m : ℝ) ^ 2) *
        Real.rpow a (1 - 2 * (m : ℝ)) := by
    calc
      iteratedDerivWithin 2 (f m a) s 0 = (deriv^[2]) (f m a) 0 :=
        iteratedDerivWithin_of_isOpen_eq_iterate isOpen_Ioi h0s
      _ = ((1 - (m : ℝ)) / (m : ℝ) ^ 2) *
          Real.rpow a (1 - 2 * (m : ℝ)) := gap5 m a hm ha
  have hrpow1 : a ^ (1 - (m : ℝ)) =
      (a ^ ((m : ℝ) - 1))⁻¹ := by
    rw [show 1 - (m : ℝ) = -((m : ℝ) - 1) by ring]
    exact Real.rpow_neg ha.le _
  have hrpow2 : a ^ (1 - 2 * (m : ℝ)) =
      (a ^ (2 * (m : ℝ) - 1))⁻¹ := by
    rw [show 1 - 2 * (m : ℝ) = -(2 * (m : ℝ) - 1) by ring]
    exact Real.rpow_neg ha.le _
  have htaylor (x : ℝ) :
      taylorWithinEval (f m a) 2 s 0 x = taylorPolynomial m a x := by
    rw [taylor_within_apply]
    norm_num [Finset.sum_range_succ, hiter0, hiter1, hiter2]
    unfold taylorPolynomial
    simp only [Real.rpow_eq_pow]
    rw [hrpow1, hrpow2]
    field_simp [m_ne_zero m hm, (Real.rpow_pos_of_pos ha _).ne']
  have hfilter : 𝓝[s] (0 : ℝ) = nhds 0 := by
    rw [← nhdsWithin_univ]
    apply nhdsWithin_eq_iff_eventuallyEq.mpr
    filter_upwards [Ioi_mem_nhds h0s] with x hx
    apply propext
    constructor
    · intro
      exact Set.mem_univ x
    · intro
      exact hx
  have ht := taylor_isLittleO (f := f m a) (n := 2) (s := s)
    (convex_Ioi _) h0s hcont
  rw [hfilter] at ht
  unfold AgreesToOrderAt
  exact ht.congr_left fun x => by rw [htaylor x]

end

end ProofGap.Exercise1379
