import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise2132
noncomputable section

def domain : Set ℝ := Set.Ioo 0 1
def t (x : ℝ) := Real.sqrt (1 - x * Real.sqrt x)
def integrand (x : ℝ) := Real.sqrt (x / (1 - x * Real.sqrt x))
def pullbackCoefficient (x : ℝ) :=
  -(4 / 3 : ℝ) * t x * Real.rpow (1 - t x ^ 2) (-(1 / 3 : ℝ))
def primitive (x : ℝ) := -(4 / 3 : ℝ) * t x

def Family (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ domain, HasDerivAt F (f x) x}
def ScaledIdentityFamily :=
  {F : ℝ → ℝ | ∃ A ∈ Family (fun x => deriv t x),
    ∀ x ∈ domain, F x = -(4 / 3 : ℝ) * A x}
def Translates (p : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem transformFacts (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt t (deriv t x) x ∧
      integrand x = -(4 / 3 : ℝ) * deriv t x ∧
      x = Real.rpow (1 - t x ^ 2) (2 / 3 : ℝ) ∧
      1 = pullbackCoefficient x * deriv t x := by
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs_nonneg : 0 ≤ Real.sqrt x := hs0.le
  have hs_sq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hs_lt_one : Real.sqrt x < 1 := by
    nlinarith [hs_sq]
  have hprod : x * Real.sqrt x < 1 := by
    calc
      x * Real.sqrt x < 1 * Real.sqrt x :=
        mul_lt_mul_of_pos_right hx1 hs0
      _ = Real.sqrt x := one_mul _
      _ < 1 := hs_lt_one
  have hu : 0 < 1 - x * Real.sqrt x := sub_pos.2 hprod
  have ht0 : 0 < t x := by
    dsimp [t]
    exact Real.sqrt_pos.2 hu
  have ht_sq : t x ^ 2 = 1 - x * Real.sqrt x := by
    dsimp [t]
    exact Real.sq_sqrt hu.le
  have hbase : 1 - t x ^ 2 = x * Real.sqrt x := by
    rw [ht_sq]
    ring
  have hxs_as_rpow :
      x * Real.sqrt x = Real.rpow (Real.sqrt x) (3 : ℝ) := by
    calc
      x * Real.sqrt x = Real.sqrt x ^ 2 * Real.sqrt x := by
        rw [hs_sq]
      _ = Real.sqrt x ^ 3 := by ring
      _ = Real.rpow (Real.sqrt x) (3 : ℝ) := by
        norm_num [Real.rpow_natCast]
  have hpow :
      Real.rpow (x * Real.sqrt x) (2 / 3 : ℝ) = x := by
    calc
      Real.rpow (x * Real.sqrt x) (2 / 3 : ℝ) =
          Real.rpow (Real.rpow (Real.sqrt x) (3 : ℝ)) (2 / 3 : ℝ) := by
            rw [hxs_as_rpow]
      _ = Real.rpow (Real.sqrt x) ((3 : ℝ) * (2 / 3 : ℝ)) := by
            exact
              (Real.rpow_mul hs_nonneg (3 : ℝ) (2 / 3 : ℝ)).symm
      _ = Real.sqrt x ^ 2 := by
            norm_num [Real.rpow_natCast]
      _ = x := hs_sq
  have hneg :
      Real.rpow (x * Real.sqrt x) (-(1 / 3 : ℝ)) =
        (Real.sqrt x)⁻¹ := by
    calc
      Real.rpow (x * Real.sqrt x) (-(1 / 3 : ℝ)) =
          Real.rpow (Real.rpow (Real.sqrt x) (3 : ℝ))
            (-(1 / 3 : ℝ)) := by
              rw [hxs_as_rpow]
      _ = Real.rpow (Real.sqrt x)
            ((3 : ℝ) * (-(1 / 3 : ℝ))) := by
              exact
                (Real.rpow_mul hs_nonneg (3 : ℝ)
                  (-(1 / 3 : ℝ))).symm
      _ = (Real.sqrt x)⁻¹ := by
              norm_num [Real.rpow_neg_one]
  have hs_deriv := Real.hasDerivAt_sqrt hx0.ne'
  have hxdiv :
      x * (1 / (2 * Real.sqrt x)) = Real.sqrt x / 2 := by
    field_simp [hs0.ne']
    nlinarith [hs_sq]
  have hu_raw :
      HasDerivAt (fun y : ℝ => 1 - y * Real.sqrt y)
        (-(Real.sqrt x + x * (1 / (2 * Real.sqrt x)))) x := by
    simpa [id] using
      (hasDerivAt_const x (1 : ℝ)).sub
        ((hasDerivAt_id x).mul hs_deriv)
  have hu_coeff :
      -(Real.sqrt x + x * (1 / (2 * Real.sqrt x))) =
        -(3 / 2 : ℝ) * Real.sqrt x := by
    rw [hxdiv]
    ring
  have hu_deriv :
      HasDerivAt (fun y : ℝ => 1 - y * Real.sqrt y)
        (-(3 / 2 : ℝ) * Real.sqrt x) x := by
    rw [← hu_coeff]
    exact hu_raw
  have ht_formula :
      HasDerivAt t (-(3 / 4 : ℝ) * (Real.sqrt x / t x)) x := by
    have hraw := (Real.hasDerivAt_sqrt hu.ne').comp x hu_deriv
    convert hraw using 1
    dsimp [t]
    field_simp [hs0.ne', ht0.ne']
    ring
  have ht_deriv :
      deriv t x = -(3 / 4 : ℝ) * (Real.sqrt x / t x) :=
    ht_formula.deriv
  have hint : integrand x = Real.sqrt x / t x := by
    simp only [integrand, t]
    rw [Real.sqrt_div hx0.le]
  have hrel : integrand x = -(4 / 3 : ℝ) * deriv t x := by
    rw [hint, ht_deriv]
    ring
  refine ⟨?_, hrel, ?_, ?_⟩
  · simpa only [ht_deriv] using ht_formula
  · rw [hbase, hpow]
  · dsimp [pullbackCoefficient]
    rw [hbase]
    change 1 =
      (-(4 / 3 : ℝ) * t x *
        Real.rpow (x * Real.sqrt x) (-(1 / 3 : ℝ))) * deriv t x
    rw [hneg, ht_deriv]
    field_simp [hs0.ne', ht0.ne']

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    x = Real.rpow (1 - t x ^ 2) (2 / 3 : ℝ) := by
  exact (transformFacts x hx).2.2.1
theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    1 = pullbackCoefficient x * deriv t x := by
  exact (transformFacts x hx).2.2.2
theorem gap3 : Family integrand = ScaledIdentityFamily := by
  ext F
  constructor
  · intro hF
    refine ⟨(fun y => -(3 / 4 : ℝ) * F y), ?_, ?_⟩
    · intro x hx
      have hrel := (transformFacts x hx).2.1
      convert (hF x hx).const_mul (-(3 / 4 : ℝ)) using 1
      rw [hrel]
      ring
    · intro x hx
      ring
  · rintro ⟨A, hA, hFA⟩
    intro x hx
    have hd := (hA x hx).const_mul (-(4 / 3 : ℝ))
    have hrel := (transformFacts x hx).2.1
    have hd' :
        HasDerivAt (fun y => -(4 / 3 : ℝ) * A y) (integrand x) x := by
      simpa only [hrel] using hd
    have hopen : IsOpen domain := by
      exact isOpen_Ioo
    have hevent :
        ∀ᶠ y in nhds x, F y = -(4 / 3 : ℝ) * A y :=
      Filter.mem_of_superset (hopen.mem_nhds hx) (by
        intro y hy
        exact hFA y hy)
    exact hd'.congr_of_eventuallyEq hevent
theorem gap4 : ScaledIdentityFamily = Translates primitive := by
  ext F
  constructor
  · rintro ⟨A, hA, hFA⟩
    let D : ℝ → ℝ := fun z => A z - t z
    have hDder : ∀ z ∈ domain, HasDerivAt D 0 z := by
      intro z hz
      dsimp [D]
      simpa using (hA z hz).sub (transformFacts z hz).1
    have hdiff : DifferentiableOn ℝ D domain := by
      intro z hz
      exact (hDder z hz).differentiableAt.differentiableWithinAt
    have hzero : ∀ z ∈ domain, deriv D z = 0 := by
      intro z hz
      exact (hDder z hz).deriv
    have hopen : IsOpen domain := by
      exact isOpen_Ioo
    have hpre : IsPreconnected domain := by
      exact isPreconnected_Ioo
    have hq : (1 / 2 : ℝ) ∈ domain := by
      change (0 : ℝ) < 1 / 2 ∧ (1 / 2 : ℝ) < 1
      norm_num
    refine ⟨-(4 / 3 : ℝ) * (A (1 / 2) - t (1 / 2)), ?_⟩
    intro x hx
    have hconst : D x = D (1 / 2) :=
      hopen.is_const_of_deriv_eq_zero hpre hdiff hzero hx hq
    have hAx : A x = t x + (A (1 / 2) - t (1 / 2)) := by
      dsimp [D] at hconst
      linarith
    rw [hFA x hx, hAx]
    dsimp [primitive]
    ring
  · rintro ⟨C, hF⟩
    refine ⟨(fun z => t z - (3 / 4 : ℝ) * C), ?_, ?_⟩
    · intro x hx
      simpa using
        ((transformFacts x hx).1.sub_const ((3 / 4 : ℝ) * C))
    · intro x hx
      rw [hF x hx]
      dsimp [primitive]
      ring
theorem gap5 :
    Translates primitive =
      Translates (fun x => -(4 / 3 : ℝ) * Real.sqrt (1 - x * Real.sqrt x)) := by
  rfl
theorem gap6 : Family integrand = Translates primitive := by
  rw [gap3, gap4]

end
end ProofGap.Exercise2132
