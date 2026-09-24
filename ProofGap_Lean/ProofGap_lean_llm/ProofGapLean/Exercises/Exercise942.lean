import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise942

noncomputable section

def cubeRoot (x : ℝ) : ℝ :=
  Real.sign x * Real.rpow |x| (1 / 3 : ℝ)

def arccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x

def y942 (x : ℝ) : ℝ := x ^ 6 / (1 + x ^ 12) - arccot (x ^ 6)

def y943 (x : ℝ) : ℝ :=
  Real.log ((1 - cubeRoot x) /
    Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2))) +
  Real.sqrt 3 *
    Real.arctan ((1 + 2 * cubeRoot x) / Real.sqrt 3)

def expanded942 (x : ℝ) : ℝ :=
  (6 * x ^ 5 * (1 + x ^ 12) - 12 * x ^ 17) /
      (1 + x ^ 12) ^ 2 +
    6 * x ^ 5 / (1 + x ^ 12)

def final942 (x : ℝ) : ℝ := 12 * x ^ 5 / (1 + x ^ 12) ^ 2

def expanded943 (x : ℝ) : ℝ :=
  -(1 / (3 * cubeRoot (x ^ 2) * (1 - cubeRoot x))) -
    1 / (2 * (1 + cubeRoot x + cubeRoot (x ^ 2))) *
      (1 / (3 * cubeRoot (x ^ 2)) + 2 / (3 * cubeRoot x)) +
    Real.sqrt 3 *
      (1 / (1 + ((1 + 2 * cubeRoot x) / Real.sqrt 3) ^ 2)) *
      (2 / (3 * Real.sqrt 3 * cubeRoot (x ^ 2)))

def final943 (x : ℝ) : ℝ := -(1 / ((1 - x) * cubeRoot x))

private theorem cubeRoot_facts (x : ℝ) (hx : x ≠ 0) :
    cubeRoot x ^ 3 = x ∧
      cubeRoot (x ^ 2) = cubeRoot x ^ 2 ∧
        HasDerivAt cubeRoot (1 / (3 * cubeRoot (x ^ 2))) x := by
  have hpow (a : ℝ) (ha : 0 < a) :
      Real.rpow a (1 / 3 : ℝ) ^ 3 = a := by
    rw [← Real.rpow_natCast]
    calc
      Real.rpow (Real.rpow a (1 / 3 : ℝ)) (3 : ℝ) =
          Real.rpow a ((1 / 3 : ℝ) * 3) := by
        symm
        exact Real.rpow_mul (le_of_lt ha) _ _
      _ = a := by norm_num
  have hcubed (z : ℝ) (hz0 : z ≠ 0) : cubeRoot z ^ 3 = z := by
    rcases lt_or_gt_of_ne hz0 with hz | hz
    · have hp := hpow (-z) (neg_pos.mpr hz)
      have hcz :
          cubeRoot z = -Real.rpow (-z) (1 / 3 : ℝ) := by
        unfold cubeRoot
        rw [abs_of_neg hz]
        have hs : Real.sign z = -1 := by
          simp [Real.sign, hz]
        rw [hs]
        ring
      rw [hcz]
      calc
        (-Real.rpow (-z) (1 / 3 : ℝ)) ^ 3 =
            -(Real.rpow (-z) (1 / 3 : ℝ) ^ 3) := by ring
        _ = z := by rw [hp]; ring
    · have hp := hpow z hz
      have hcz : cubeRoot z = Real.rpow z (1 / 3 : ℝ) := by
        unfold cubeRoot
        rw [abs_of_pos hz]
        have hn : ¬z < 0 := not_lt_of_ge hz.le
        have hs : Real.sign z = 1 := by
          simp [Real.sign, hz, hn]
        rw [hs]
        ring
      rw [hcz]
      exact hp
  have hcube := hcubed x hx
  have ht0 : cubeRoot x ≠ 0 := by
    intro h
    apply hx
    rw [← hcube, h]
    norm_num
  have hx20 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  have hcube2 := hcubed (x ^ 2) hx20
  have hcuberhs : (cubeRoot x ^ 2) ^ 3 = x ^ 2 := by
    calc
      (cubeRoot x ^ 2) ^ 3 = (cubeRoot x ^ 3) ^ 2 := by ring
      _ = x ^ 2 := by rw [hcube]
  have hb0 : cubeRoot x ^ 2 ≠ 0 := pow_ne_zero 2 ht0
  have hfac :
      (cubeRoot (x ^ 2) - cubeRoot x ^ 2) *
          (cubeRoot (x ^ 2) ^ 2 +
            cubeRoot (x ^ 2) * cubeRoot x ^ 2 +
            (cubeRoot x ^ 2) ^ 2) = 0 := by
    calc
      (cubeRoot (x ^ 2) - cubeRoot x ^ 2) *
          (cubeRoot (x ^ 2) ^ 2 +
            cubeRoot (x ^ 2) * cubeRoot x ^ 2 +
            (cubeRoot x ^ 2) ^ 2) =
          cubeRoot (x ^ 2) ^ 3 - (cubeRoot x ^ 2) ^ 3 := by ring
      _ = 0 := by rw [hcube2, hcuberhs]; ring
  have hquadpos :
      0 < cubeRoot (x ^ 2) ^ 2 +
        cubeRoot (x ^ 2) * cubeRoot x ^ 2 +
        (cubeRoot x ^ 2) ^ 2 := by
    have hb2 : 0 < (cubeRoot x ^ 2) ^ 2 := sq_pos_of_ne_zero hb0
    nlinarith [sq_nonneg (cubeRoot (x ^ 2) + cubeRoot x ^ 2 / 2)]
  have hsquare : cubeRoot (x ^ 2) = cubeRoot x ^ 2 := by
    apply sub_eq_zero.mp
    exact (mul_eq_zero.mp hfac).resolve_right (ne_of_gt hquadpos)
  have hcoeff (a : ℝ) (ha : 0 < a) :
      (1 / 3 : ℝ) * Real.rpow a ((1 / 3 : ℝ) - 1) =
        1 / (3 * Real.rpow a (1 / 3 : ℝ) ^ 2) := by
    have hr0 : Real.rpow a (1 / 3 : ℝ) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos ha _)
    have hsub :
        Real.rpow a ((1 / 3 : ℝ) - 1) =
          Real.rpow a (1 / 3 : ℝ) / Real.rpow a 1 := by
      exact Real.rpow_sub ha _ _
    have hone : Real.rpow a 1 = a := by
      simpa using Real.rpow_one a
    rw [hsub, hone]
    field_simp [ha.ne', hr0]
    nlinarith [hpow a ha]
  refine ⟨hcube, hsquare, ?_⟩
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · have ha : 0 < -x := neg_pos.mpr hneg
    have hr :
        HasDerivAt
          (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * Real.rpow (-x) ((1 / 3 : ℝ) - 1)) (-x) := by
      convert Real.hasDerivAt_rpow_const (Or.inl ha.ne') using 1 <;> ring
    have hinner : HasDerivAt (fun z : ℝ => -z) (-1) x := by
      convert (hasDerivAt_id x).neg using 1 <;> ring
    have hcomp :
        HasDerivAt
          (fun z : ℝ => Real.rpow (-z) (1 / 3 : ℝ))
          (((1 / 3 : ℝ) * Real.rpow (-x) ((1 / 3 : ℝ) - 1)) * (-1)) x := by
      simpa only [Function.comp_apply] using hr.comp x hinner
    have hraw :
        HasDerivAt
          (fun z : ℝ => -Real.rpow (-z) (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * Real.rpow (-x) ((1 / 3 : ℝ) - 1)) x := by
      convert hcomp.neg using 1 <;> ring
    have heq :
        (fun z : ℝ => -Real.rpow (-z) (1 / 3 : ℝ)) =ᶠ[nhds x]
          cubeRoot := by
      filter_upwards [Iio_mem_nhds hneg] with z hz
      change z < 0 at hz
      have hcz : cubeRoot z = -Real.rpow (-z) (1 / 3 : ℝ) := by
        unfold cubeRoot
        rw [abs_of_neg hz]
        have hs : Real.sign z = -1 := by
          simp [Real.sign, hz]
        rw [hs]
        ring
      exact hcz.symm
    have hder :
        HasDerivAt cubeRoot
          ((1 / 3 : ℝ) * Real.rpow (-x) ((1 / 3 : ℝ) - 1)) x := by
      exact hraw.congr_of_eventuallyEq heq.symm
    have hcx : cubeRoot x = -Real.rpow (-x) (1 / 3 : ℝ) := by
      unfold cubeRoot
      rw [abs_of_neg hneg]
      have hs : Real.sign x = -1 := by
        simp [Real.sign, hneg]
      rw [hs]
      ring
    have hcrsq :
        cubeRoot (x ^ 2) = Real.rpow (-x) (1 / 3 : ℝ) ^ 2 := by
      rw [hsquare, hcx]
      ring
    rw [hcoeff (-x) ha, ← hcrsq] at hder
    exact hder
  · have hr :
        HasDerivAt
          (fun z : ℝ => Real.rpow z (1 / 3 : ℝ))
          ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x := by
      convert Real.hasDerivAt_rpow_const (Or.inl hpos.ne') using 1 <;> ring
    have heq :
        (fun z : ℝ => Real.rpow z (1 / 3 : ℝ)) =ᶠ[nhds x]
          cubeRoot := by
      filter_upwards [Ioi_mem_nhds hpos] with z hz
      change 0 < z at hz
      have hcz : cubeRoot z = Real.rpow z (1 / 3 : ℝ) := by
        unfold cubeRoot
        rw [abs_of_pos hz]
        have hn : ¬z < 0 := not_lt_of_ge hz.le
        have hs : Real.sign z = 1 := by
          simp [Real.sign, hz, hn]
        rw [hs]
        ring
      exact hcz.symm
    have hder :
        HasDerivAt cubeRoot
          ((1 / 3 : ℝ) * Real.rpow x ((1 / 3 : ℝ) - 1)) x := by
      exact hr.congr_of_eventuallyEq heq.symm
    have hcx : cubeRoot x = Real.rpow x (1 / 3 : ℝ) := by
      unfold cubeRoot
      rw [abs_of_pos hpos]
      have hn : ¬x < 0 := not_lt_of_ge hpos.le
      have hs : Real.sign x = 1 := by
        simp [Real.sign, hpos, hn]
      rw [hs]
      ring
    have hcrsq :
        cubeRoot (x ^ 2) = Real.rpow x (1 / 3 : ℝ) ^ 2 := by
      rw [hsquare, hcx]
    rw [hcoeff x hpos, ← hcrsq] at hder
    exact hder

theorem gap1 (x : ℝ) : HasDerivAt y942 (expanded942 x) x := by
  unfold y942 expanded942 arccot
  have hden : 1 + x ^ 12 ≠ 0 := by positivity
  have hp6 : HasDerivAt (fun z : ℝ => z ^ 6) (6 * x ^ 5) x := by
    convert (hasDerivAt_id x).pow 6 using 1 <;> norm_num <;> ring
  have hp12 : HasDerivAt (fun z : ℝ => z ^ 12) (12 * x ^ 11) x := by
    convert (hasDerivAt_id x).pow 12 using 1 <;> norm_num <;> ring
  have hdenDeriv :
      HasDerivAt (fun z : ℝ => 1 + z ^ 12) (12 * x ^ 11) x := by
    convert (hasDerivAt_const x 1).add hp12 using 1 <;> ring
  have hquotRaw := hp6.div hdenDeriv hden
  have hquot :
      HasDerivAt (fun z : ℝ => z ^ 6 / (1 + z ^ 12))
        ((6 * x ^ 5 * (1 + x ^ 12) - 12 * x ^ 17) /
          (1 + x ^ 12) ^ 2) x := by
    convert hquotRaw using 1 <;> ring
  have harctanRaw :
      HasDerivAt (fun z : ℝ => Real.arctan (z ^ 6))
        ((1 / (1 + (x ^ 6) ^ 2)) * (6 * x ^ 5)) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_arctan (x ^ 6)).comp x hp6
  have harctan :
      HasDerivAt (fun z : ℝ => Real.arctan (z ^ 6))
        (6 * x ^ 5 / (1 + x ^ 12)) x := by
    convert harctanRaw using 1 <;> ring
  have harccot :
      HasDerivAt (fun z : ℝ => Real.pi / 2 - Real.arctan (z ^ 6))
        (-(6 * x ^ 5 / (1 + x ^ 12))) x := by
    convert (hasDerivAt_const x (Real.pi / 2)).sub harctan using 1 <;> ring
  convert hquot.sub harccot using 1 <;> ring

theorem gap2 (x : ℝ) : expanded942 x = final942 x := by
  unfold expanded942 final942
  have hden : 1 + x ^ 12 ≠ 0 := by positivity
  field_simp [hden] <;> ring

theorem gap3 (x : ℝ) : HasDerivAt y942 (final942 x) x := by
  rw [← gap2 x]
  exact gap1 x

theorem gap4 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x < 1) :
    HasDerivAt y943 (expanded943 x) x := by
  obtain ⟨hcube, hsquare, ht⟩ := cubeRoot_facts x hx0
  have ht0 : cubeRoot x ≠ 0 := by
    intro h
    apply hx0
    calc
      x = cubeRoot x ^ 3 := hcube.symm
      _ = 0 := by rw [h]; norm_num
  have hv0 : cubeRoot (x ^ 2) ≠ 0 := by
    rw [hsquare]
    exact pow_ne_zero 2 ht0
  have hsquare_all (z : ℝ) : cubeRoot (z ^ 2) = cubeRoot z ^ 2 := by
    by_cases hz : z = 0
    · subst z
      norm_num [cubeRoot]
    · exact (cubeRoot_facts z hz).2.1
  have htpow :
      HasDerivAt (fun z : ℝ => cubeRoot z ^ 2)
        (2 * cubeRoot x * (1 / (3 * cubeRoot (x ^ 2)))) x := by
    convert ht.pow 2 using 1 <;> norm_num <;> ring
  have hfun :
      (fun z : ℝ => cubeRoot (z ^ 2)) =
        (fun z : ℝ => cubeRoot z ^ 2) := by
    funext z
    exact hsquare_all z
  have hvraw :
      HasDerivAt (fun z : ℝ => cubeRoot (z ^ 2))
        (2 * cubeRoot x * (1 / (3 * cubeRoot (x ^ 2)))) x := by
    rw [hfun]
    exact htpow
  have hv :
      HasDerivAt (fun z : ℝ => cubeRoot (z ^ 2))
        (2 / (3 * cubeRoot x)) x := by
    convert hvraw using 1
    rw [hsquare]
    field_simp [ht0]
  have hq : 0 < 1 + cubeRoot x + cubeRoot (x ^ 2) := by
    rw [hsquare]
    nlinarith [sq_nonneg (cubeRoot x + (1 / 2 : ℝ))]
  have hq0 : 1 + cubeRoot x + cubeRoot (x ^ 2) ≠ 0 := ne_of_gt hq
  have hu_lt : cubeRoot x < 1 := by
    by_contra h
    have hu_ge : 1 ≤ cubeRoot x := le_of_not_gt h
    have hfactor :
        0 ≤ (cubeRoot x - 1) *
          (cubeRoot x ^ 2 + cubeRoot x + 1) := by
      apply mul_nonneg (sub_nonneg.mpr hu_ge)
      nlinarith [sq_nonneg (cubeRoot x + (1 / 2 : ℝ))]
    nlinarith [hcube, hfactor]
  have hnum0 : 1 - cubeRoot x ≠ 0 := ne_of_gt (sub_pos.mpr hu_lt)
  have hsqrt0 :
      Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hq)
  have hsqrt_sq :
      Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2)) ^ 2 =
        1 + cubeRoot x + cubeRoot (x ^ 2) :=
    Real.sq_sqrt (le_of_lt hq)
  have hsqrt_mul :
      Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2)) *
          Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2)) =
        1 + cubeRoot x + cubeRoot (x ^ 2) :=
    Real.mul_self_sqrt (le_of_lt hq)
  have hs :
      HasDerivAt
        (fun z : ℝ => 1 + cubeRoot z + cubeRoot (z ^ 2))
        (1 / (3 * cubeRoot (x ^ 2)) + 2 / (3 * cubeRoot x)) x := by
    convert ((hasDerivAt_const x 1).add ht).add hv using 1 <;> ring
  have hsqrtBase :
      HasDerivAt Real.sqrt
        (1 / (2 * Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2))))
        (1 + cubeRoot x + cubeRoot (x ^ 2)) := by
    convert Real.hasDerivAt_sqrt hq0 using 1 <;> ring
  have hsqrtRaw := hsqrtBase.comp x hs
  have hsqrt :
      HasDerivAt
        (fun z : ℝ => Real.sqrt (1 + cubeRoot z + cubeRoot (z ^ 2)))
        ((1 / (2 * Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2)))) *
          (1 / (3 * cubeRoot (x ^ 2)) + 2 / (3 * cubeRoot x))) x := by
    simpa only [Function.comp_apply] using hsqrtRaw
  have hquot := ((hasDerivAt_const x 1).sub ht).div hsqrt hsqrt0
  have harg0 :
      (1 - cubeRoot x) /
          Real.sqrt (1 + cubeRoot x + cubeRoot (x ^ 2)) ≠ 0 :=
    div_ne_zero hnum0 hsqrt0
  have hlog := (Real.hasDerivAt_log harg0).comp x hquot
  have hlog' :
      HasDerivAt
        (fun z : ℝ =>
          Real.log ((1 - cubeRoot z) /
            Real.sqrt (1 + cubeRoot z + cubeRoot (z ^ 2))))
        (-(1 / (3 * cubeRoot (x ^ 2) * (1 - cubeRoot x))) -
          1 / (2 * (1 + cubeRoot x + cubeRoot (x ^ 2))) *
            (1 / (3 * cubeRoot (x ^ 2)) + 2 / (3 * cubeRoot x))) x := by
    convert hlog using 1
    field_simp [hnum0, hsqrt0, hq0, ht0, hv0]
    simp only [Pi.sub_apply]
    rw [hsqrt_sq, hsquare]
    ring
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  have hlinear :
      HasDerivAt (fun z : ℝ => 1 + 2 * cubeRoot z)
        (2 / (3 * cubeRoot (x ^ 2))) x := by
    convert (hasDerivAt_const x 1).add (ht.const_mul 2) using 1 <;> ring
  have hatanArgRaw :=
    hlinear.div (hasDerivAt_const x (Real.sqrt 3)) hsqrt3
  have hatanArg :
      HasDerivAt
        (fun z : ℝ => (1 + 2 * cubeRoot z) / Real.sqrt 3)
        (2 / (3 * Real.sqrt 3 * cubeRoot (x ^ 2))) x := by
    convert hatanArgRaw using 1
    field_simp [hsqrt3, hv0]
    ring
  have hatan :
      HasDerivAt
        (fun z : ℝ => Real.arctan ((1 + 2 * cubeRoot z) / Real.sqrt 3))
        ((1 / (1 + ((1 + 2 * cubeRoot x) / Real.sqrt 3) ^ 2)) *
          (2 / (3 * Real.sqrt 3 * cubeRoot (x ^ 2)))) x := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_arctan
        ((1 + 2 * cubeRoot x) / Real.sqrt 3)).comp x hatanArg
  have htotal := hlog'.add (hatan.const_mul (Real.sqrt 3))
  simpa only [y943, expanded943, mul_assoc] using htotal

theorem gap5 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x < 1) :
    expanded943 x = final943 x := by
  obtain ⟨hcube, hsquare, _⟩ := cubeRoot_facts x hx0
  have ht0 : cubeRoot x ≠ 0 := by
    intro h
    apply hx0
    calc
      x = cubeRoot x ^ 3 := hcube.symm
      _ = 0 := by rw [h]; norm_num
  have hv0 : cubeRoot (x ^ 2) ≠ 0 := by
    rw [hsquare]
    exact pow_ne_zero 2 ht0
  have hq : 0 < 1 + cubeRoot x + cubeRoot (x ^ 2) := by
    rw [hsquare]
    nlinarith [sq_nonneg (cubeRoot x + (1 / 2 : ℝ))]
  have hq0 : 1 + cubeRoot x + cubeRoot (x ^ 2) ≠ 0 := ne_of_gt hq
  have hq0sq : 1 + cubeRoot x + cubeRoot x ^ 2 ≠ 0 := by
    rw [← hsquare]
    exact hq0
  have hu_lt : cubeRoot x < 1 := by
    by_contra h
    have hu_ge : 1 ≤ cubeRoot x := le_of_not_gt h
    have hfactor :
        0 ≤ (cubeRoot x - 1) *
          (cubeRoot x ^ 2 + cubeRoot x + 1) := by
      apply mul_nonneg (sub_nonneg.mpr hu_ge)
      nlinarith [sq_nonneg (cubeRoot x + (1 / 2 : ℝ))]
    nlinarith [hcube, hfactor]
  have hnum0 : 1 - cubeRoot x ≠ 0 := ne_of_gt (sub_pos.mpr hu_lt)
  have hcubeden0 : 1 - cubeRoot x ^ 3 ≠ 0 := by
    rw [hcube]
    exact ne_of_gt (sub_pos.mpr hx1)
  have hsqrt3 : Real.sqrt 3 ≠ 0 := by positivity
  have hsqrt3sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hatanDen :
      1 + ((1 + 2 * cubeRoot x) / Real.sqrt 3) ^ 2 =
        4 * (1 + cubeRoot x + cubeRoot (x ^ 2)) / 3 := by
    rw [hsquare]
    field_simp [hsqrt3]
    nlinarith [hsqrt3sq]
  calc
    expanded943 x =
        -(1 / ((1 - cubeRoot x ^ 3) * cubeRoot x)) := by
      unfold expanded943
      rw [hatanDen, hsquare]
      field_simp [ht0, hv0, hq0, hq0sq, hnum0, hcubeden0, hsqrt3] <;> ring
    _ = final943 x := by
      unfold final943
      rw [hcube]

theorem gap6 (x : ℝ) (hx0 : x ≠ 0) (hx1 : x < 1) :
    HasDerivAt y943 (final943 x) x := by
  rw [← gap5 x hx0 hx1]
  exact gap4 x hx0 hx1

end

end ProofGap.Exercise942
