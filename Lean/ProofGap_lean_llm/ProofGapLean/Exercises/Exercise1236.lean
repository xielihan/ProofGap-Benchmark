import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace ProofGap.Exercise1236

noncomputable section

def signedCbrt (x : ℝ) : ℝ :=
  if 0 ≤ x then Real.rpow x (1 / 3 : ℝ) else -Real.rpow (-x) (1 / 3 : ℝ)

def f (x : ℝ) : ℝ :=
  1 - signedCbrt (x ^ 2)

private def twoThirdPower (x : ℝ) : ℝ := signedCbrt x ^ 2

private theorem rpow_third_cube (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x (1 / 3 : ℝ) ^ 3 = x := by
  calc
    Real.rpow x (1 / 3 : ℝ) ^ 3 =
        Real.rpow (Real.rpow x (1 / 3 : ℝ)) (3 : ℝ) := by
      exact (Real.rpow_natCast _ 3).symm
    _ = Real.rpow x ((1 / 3 : ℝ) * 3) := by
      exact (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private theorem signedCbrt_cube (x : ℝ) : signedCbrt x ^ 3 = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [signedCbrt, if_neg (not_le.mpr hx)]
    rw [show (-Real.rpow (-x) (1 / 3 : ℝ)) ^ 3 =
      -(Real.rpow (-x) (1 / 3 : ℝ) ^ 3) by ring,
      rpow_third_cube (-x) (by linarith)]
    ring
  · norm_num [signedCbrt]
  · rw [signedCbrt, if_pos hx.le]
    exact rpow_third_cube x hx.le

private theorem cube_injective {u v : ℝ} (h : u ^ 3 = v ^ 3) : u = v :=
  (show Odd 3 by decide).strictMono_pow.injective h

private theorem signedCbrt_sq (u : ℝ) :
    signedCbrt (u ^ 2) = signedCbrt u ^ 2 := by
  apply cube_injective
  calc
    signedCbrt (u ^ 2) ^ 3 = u ^ 2 := signedCbrt_cube _
    _ = (signedCbrt u ^ 3) ^ 2 := by rw [signedCbrt_cube]
    _ = (signedCbrt u ^ 2) ^ 3 := by ring

private theorem signedCbrt_ne_zero {u : ℝ} (hu : u ≠ 0) :
    signedCbrt u ≠ 0 := by
  intro h
  have hc := signedCbrt_cube u
  rw [h] at hc
  apply hu
  simpa using hc.symm

private theorem hasDerivAt_twoThird {u : ℝ} (hu : u ≠ 0) :
    HasDerivAt twoThirdPower (2 / (3 * signedCbrt u)) u := by
  have hu2 : 0 < u ^ 2 := sq_pos_of_ne_zero hu
  have hsquare : HasDerivAt (fun z : ℝ => z ^ 2) (2 * u) u := by
    simpa [id, mul_comm] using (hasDerivAt_id u).pow 2
  have houter :
      HasDerivAt (fun w : ℝ => Real.rpow w (1 / 3 : ℝ))
        ((1 / 3 : ℝ) * Real.rpow (u ^ 2) ((1 / 3 : ℝ) - 1))
        (u ^ 2) :=
    Real.hasDerivAt_rpow_const (Or.inl hu2.ne')
  have hraw :
      HasDerivAt (fun z : ℝ => Real.rpow (z ^ 2) (1 / 3 : ℝ))
        (((1 / 3 : ℝ) * Real.rpow (u ^ 2) ((1 / 3 : ℝ) - 1)) *
          (2 * u)) u := by
    convert houter.comp_of_eq u hsquare rfl using 1 <;>
      simp [id, pow_two] <;> ring
  have hfun :
      twoThirdPower = fun z : ℝ => Real.rpow (z ^ 2) (1 / 3 : ℝ) := by
    funext z
    unfold twoThirdPower
    rw [← signedCbrt_sq]
    simp [signedCbrt, sq_nonneg]
  rw [hfun]
  convert hraw using 1
  have hr1 :
      Real.rpow (u ^ 2) (1 / 3 : ℝ) = signedCbrt u ^ 2 := by
    rw [← signedCbrt_sq]
    simp [signedCbrt, sq_nonneg]
  have hr2 :
      Real.rpow (u ^ 2) (2 / 3 : ℝ) = (signedCbrt u ^ 2) ^ 2 := by
    calc
      Real.rpow (u ^ 2) (2 / 3 : ℝ) =
          Real.rpow (u ^ 2) ((1 / 3 : ℝ) * 2) := by congr 1 <;> ring
      _ = Real.rpow (Real.rpow (u ^ 2) (1 / 3 : ℝ)) (2 : ℝ) :=
        Real.rpow_mul hu2.le _ _
      _ = (signedCbrt u ^ 2) ^ 2 := by
        rw [hr1]
        exact Real.rpow_two _
  have hneg :
      Real.rpow (u ^ 2) (-(2 / 3 : ℝ)) =
        (Real.rpow (u ^ 2) (2 / 3 : ℝ))⁻¹ :=
    Real.rpow_neg hu2.le _
  rw [show (1 / 3 : ℝ) - 1 = -(2 / 3 : ℝ) by ring, hneg, hr2]
  field_simp [signedCbrt_ne_zero hu]
  have hc := signedCbrt_cube u
  nlinarith

private theorem slope_zero_eq (t : ℝ) (ht : 0 < t) :
    t⁻¹ • (f (0 + t) - f 0) =
      -Real.rpow t (-(1 / 3 : ℝ)) := by
  have hr :
      Real.rpow (t ^ 2) (1 / 3 : ℝ) =
        Real.rpow t (2 / 3 : ℝ) := by
    calc
      Real.rpow (t ^ 2) (1 / 3 : ℝ) =
          Real.rpow t ((2 : ℝ) * (1 / 3 : ℝ)) :=
        (Real.rpow_natCast_mul ht.le 2 (1 / 3 : ℝ)).symm
      _ = Real.rpow t (2 / 3 : ℝ) := by congr 1 <;> ring
  rw [show -(1 / 3 : ℝ) = 2 / 3 - 1 by ring]
  have hsub :
      Real.rpow t (2 / 3 - 1 : ℝ) =
        Real.rpow t (2 / 3 : ℝ) / Real.rpow t 1 :=
    Real.rpow_sub ht _ _
  rw [hsub]
  have hf0 : f 0 = 1 := by
    norm_num [f, signedCbrt]
  have hft :
      f t = 1 - Real.rpow (t ^ 2) (1 / 3 : ℝ) := by
    simp [f, signedCbrt, sq_nonneg]
  rw [zero_add, hft, hf0, hr]
  simp only [smul_eq_mul]
  have hone : Real.rpow t 1 = t := Real.rpow_one t
  rw [hone]
  field_simp [ht.ne']
  ring

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    deriv f x = -2 / (3 * signedCbrt x) := by
  have hfun : f = fun t : ℝ => 1 - twoThirdPower t := by
    funext t
    unfold f twoThirdPower
    rw [signedCbrt_sq]
  rw [hfun]
  convert ((hasDerivAt_const x (1 : ℝ)).sub
    (hasDerivAt_twoThird hx)).deriv using 1 <;> ring

theorem gap2 (x : ℝ) (hxI : x ∈ Set.Icc (-1 : ℝ) 1) (hx : x ≠ 0) :
    deriv f x ≠ 0 := by
  rw [gap1 x hx]
  exact div_ne_zero (by norm_num)
    (mul_ne_zero (by norm_num) (signedCbrt_ne_zero hx))

theorem gap3 :
    ¬DifferentiableAt ℝ f 0 := by
  intro hd
  let d := deriv f 0
  have hfinite :
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds d) := by
    exact hd.hasDerivAt.tendsto_slope_zero_right
  have htop :
      Filter.Tendsto (fun t : ℝ => Real.rpow t (-(1 / 3 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    simpa using
      (tendsto_rpow_neg_nhdsGT_zero
        (show (-(1 / 3 : ℝ)) < 0 by norm_num))
  have hbot :
      Filter.Tendsto (fun t : ℝ => -Real.rpow t (-(1 / 3 : ℝ)))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atBot := by
    simpa [Function.comp_def] using
      Filter.tendsto_neg_atTop_atBot.comp htop
  have heq :
      (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0)) =ᶠ[
        nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        (fun t : ℝ => -Real.rpow t (-(1 / 3 : ℝ))) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact slope_zero_eq t ht
  have hslopeBot :
      Filter.Tendsto (fun t : ℝ => t⁻¹ • (f (0 + t) - f 0))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atBot :=
    hbot.congr' heq.symm
  have hlower :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        d - 1 < t⁻¹ • (f (0 + t) - f 0) :=
    hfinite.eventually
      (isOpen_Ioi.mem_nhds (show d ∈ Set.Ioi (d - 1) by simp))
  have hupper :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        t⁻¹ • (f (0 + t) - f 0) < d - 2 :=
    hslopeBot.eventually_lt_atBot (d - 2)
  rcases (hlower.and hupper).exists with ⟨t, hlow, hupp⟩
  linarith

end

end ProofGap.Exercise1236
