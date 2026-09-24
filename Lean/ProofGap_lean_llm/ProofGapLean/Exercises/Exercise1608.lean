import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1608

noncomputable section

def radius (a φ : ℝ) := Real.sqrt (a ^ 2 * Real.cos (2 * φ))
def powThreeHalves (u : ℝ) := u * Real.sqrt u
def curvatureRadius (a φ : ℝ) :=
  powThreeHalves ((radius a φ) ^ 2 + (deriv (radius a) φ) ^ 2) /
    ((radius a φ) ^ 2 + 2 * (deriv (radius a) φ) ^ 2 -
      radius a φ * deriv (deriv (radius a)) φ)

private theorem radius_pos (a φ : ℝ) (ha : 0 < a)
    (hc : 0 < Real.cos (2 * φ)) : 0 < radius a φ := by
  unfold radius
  exact Real.sqrt_pos.2 (mul_pos (pow_pos ha 2) hc)

private theorem radius_sq (a φ : ℝ) (ha : 0 < a)
    (hc : 0 < Real.cos (2 * φ)) :
    (radius a φ) ^ 2 = a ^ 2 * Real.cos (2 * φ) := by
  unfold radius
  exact Real.sq_sqrt (mul_pos (pow_pos ha 2) hc).le

private theorem radius_hasDerivAt (a φ : ℝ) (ha : 0 < a)
    (hc : 0 < Real.cos (2 * φ)) :
    HasDerivAt (radius a)
      (-(a ^ 2 * Real.sin (2 * φ) / radius a φ)) φ := by
  have hpos : 0 < a ^ 2 * Real.cos (2 * φ) :=
    mul_pos (pow_pos ha 2) hc
  have hrs : radius a φ ≠ 0 := (radius_pos a φ ha hc).ne'
  have hinner : HasDerivAt (fun x : ℝ => 2 * x) 2 φ := by
    simpa using (hasDerivAt_id φ).const_mul 2
  have hcos :
      HasDerivAt (fun x : ℝ => Real.cos (2 * x))
        ((-Real.sin (2 * φ)) * 2) φ := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_cos (2 * φ)).comp φ hinner
  have harg :
      HasDerivAt (fun x : ℝ => a ^ 2 * Real.cos (2 * x))
        (a ^ 2 * ((-Real.sin (2 * φ)) * 2)) φ :=
    hcos.const_mul (a ^ 2)
  have hroot := (Real.hasDerivAt_sqrt hpos.ne').comp φ harg
  have hroot' :
      HasDerivAt (radius a)
        (1 / (2 * radius a φ) *
          (a ^ 2 * ((-Real.sin (2 * φ)) * 2))) φ := by
    simpa only [radius, Function.comp_apply] using hroot
  convert hroot' using 1 <;> field_simp [hrs] <;> ring

theorem gap1 (a φ : ℝ) (ha : 0 < a) (hc : 0 < Real.cos (2 * φ)) :
    deriv (radius a) φ =
      -(a ^ 2 * Real.sin (2 * φ) / radius a φ) := by
  exact (radius_hasDerivAt a φ ha hc).deriv
theorem gap2 (a φ : ℝ) (ha : 0 < a) (hc : 0 < Real.cos (2 * φ)) :
    deriv (deriv (radius a)) φ =
      -(((radius a φ) ^ 4 + a ^ 4) / (radius a φ) ^ 3) := by
  have hrpos : 0 < radius a φ := radius_pos a φ ha hc
  have hrs : radius a φ ≠ 0 := hrpos.ne'
  have hrsq := radius_sq a φ ha hc
  have hinner : HasDerivAt (fun x : ℝ => 2 * x) 2 φ := by
    simpa using (hasDerivAt_id φ).const_mul 2
  have hsin :
      HasDerivAt (fun x : ℝ => Real.sin (2 * x))
        (2 * Real.cos (2 * φ)) φ := by
    convert (Real.hasDerivAt_sin (2 * φ)).comp φ hinner using 1 <;> ring
  have hnum :
      HasDerivAt (fun x : ℝ => a ^ 2 * Real.sin (2 * x))
        (a ^ 2 * (2 * Real.cos (2 * φ))) φ :=
    hsin.const_mul (a ^ 2)
  have hneg :
      HasDerivAt
        (fun x : ℝ => -(a ^ 2 * Real.sin (2 * x) / radius a x))
        (-(((a ^ 2 * (2 * Real.cos (2 * φ))) * radius a φ -
              (a ^ 2 * Real.sin (2 * φ)) *
                (-(a ^ 2 * Real.sin (2 * φ) / radius a φ))) /
            (radius a φ) ^ 2)) φ :=
    (hnum.div (radius_hasDerivAt a φ ha hc) hrs).neg
  have hopen : IsOpen {x : ℝ | 0 < Real.cos (2 * x)} :=
    isOpen_lt continuous_const
      (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have heq :
      deriv (radius a) =ᶠ[nhds φ]
        (fun x : ℝ => -(a ^ 2 * Real.sin (2 * x) / radius a x)) := by
    filter_upwards [hopen.mem_nhds hc] with x hx
    exact gap1 a x ha hx
  have hfour :
      (radius a φ) ^ 4 = a ^ 4 * (Real.cos (2 * φ)) ^ 2 := by
    calc
      (radius a φ) ^ 4 = ((radius a φ) ^ 2) ^ 2 := by ring
      _ = (a ^ 2 * Real.cos (2 * φ)) ^ 2 := by rw [hrsq]
      _ = a ^ 4 * (Real.cos (2 * φ)) ^ 2 := by ring
  have hnumid :
      2 * a ^ 2 * Real.cos (2 * φ) * (radius a φ) ^ 2 +
          a ^ 4 * (Real.sin (2 * φ)) ^ 2 =
        (radius a φ) ^ 4 + a ^ 4 := by
    calc
      2 * a ^ 2 * Real.cos (2 * φ) * (radius a φ) ^ 2 +
            a ^ 4 * (Real.sin (2 * φ)) ^ 2 =
          2 * a ^ 2 * Real.cos (2 * φ) *
              (a ^ 2 * Real.cos (2 * φ)) +
            a ^ 4 * (Real.sin (2 * φ)) ^ 2 := by rw [hrsq]
      _ = a ^ 4 *
            (2 * (Real.cos (2 * φ)) ^ 2 +
              (Real.sin (2 * φ)) ^ 2) := by ring
      _ = a ^ 4 * ((Real.cos (2 * φ)) ^ 2 + 1) := by
        rw [← Real.sin_sq_add_cos_sq (2 * φ)]
        ring
      _ = (radius a φ) ^ 4 + a ^ 4 := by rw [hfour]; ring
  calc
    deriv (deriv (radius a)) φ =
        deriv (fun x : ℝ =>
          -(a ^ 2 * Real.sin (2 * x) / radius a x)) φ := heq.deriv_eq
    _ = -(((a ^ 2 * (2 * Real.cos (2 * φ))) * radius a φ -
              (a ^ 2 * Real.sin (2 * φ)) *
                (-(a ^ 2 * Real.sin (2 * φ) / radius a φ))) /
            (radius a φ) ^ 2) := hneg.deriv
    _ = -((2 * a ^ 2 * Real.cos (2 * φ) * (radius a φ) ^ 2 +
              a ^ 4 * (Real.sin (2 * φ)) ^ 2) /
            (radius a φ) ^ 3) := by
      field_simp [hrs]
      <;> ring
    _ = -(((radius a φ) ^ 4 + a ^ 4) / (radius a φ) ^ 3) := by
      rw [hnumid]
theorem gap3 (a φ : ℝ) (ha : 0 < a) (hc : 0 < Real.cos (2 * φ)) :
    (radius a φ) ^ 2 + 2 * (deriv (radius a) φ) ^ 2 -
        radius a φ * deriv (deriv (radius a)) φ =
      3 * a ^ 4 / (radius a φ) ^ 2 := by
  have hrpos : 0 < radius a φ := radius_pos a φ ha hc
  have hrs : radius a φ ≠ 0 := hrpos.ne'
  have hrsq := radius_sq a φ ha hc
  have hfour :
      (radius a φ) ^ 4 = a ^ 4 * (Real.cos (2 * φ)) ^ 2 := by
    calc
      (radius a φ) ^ 4 = ((radius a φ) ^ 2) ^ 2 := by ring
      _ = (a ^ 2 * Real.cos (2 * φ)) ^ 2 := by rw [hrsq]
      _ = a ^ 4 * (Real.cos (2 * φ)) ^ 2 := by ring
  have hthree :
      2 * (radius a φ) ^ 4 +
          2 * a ^ 4 * (Real.sin (2 * φ)) ^ 2 + a ^ 4 =
        3 * a ^ 4 := by
    calc
      2 * (radius a φ) ^ 4 +
            2 * a ^ 4 * (Real.sin (2 * φ)) ^ 2 + a ^ 4 =
          2 * a ^ 4 *
              ((Real.sin (2 * φ)) ^ 2 + (Real.cos (2 * φ)) ^ 2) +
            a ^ 4 := by rw [hfour]; ring
      _ = 3 * a ^ 4 := by
        rw [Real.sin_sq_add_cos_sq]
        ring
  rw [gap2 a φ ha hc, gap1 a φ ha hc]
  calc
    (radius a φ) ^ 2 +
          2 * (-(a ^ 2 * Real.sin (2 * φ) / radius a φ)) ^ 2 -
          radius a φ *
            (-(((radius a φ) ^ 4 + a ^ 4) / (radius a φ) ^ 3)) =
        (2 * (radius a φ) ^ 4 +
            2 * a ^ 4 * (Real.sin (2 * φ)) ^ 2 + a ^ 4) /
          (radius a φ) ^ 2 := by
      field_simp [hrs]
      <;> ring
    _ = 3 * a ^ 4 / (radius a φ) ^ 2 := by rw [hthree]
theorem gap4 (a φ : ℝ) (ha : 0 < a) (hc : 0 < Real.cos (2 * φ)) :
    powThreeHalves ((radius a φ) ^ 2 + (deriv (radius a) φ) ^ 2) =
      a ^ 6 / (radius a φ) ^ 3 := by
  have hrpos : 0 < radius a φ := radius_pos a φ ha hc
  have hrs : radius a φ ≠ 0 := hrpos.ne'
  have hrsq := radius_sq a φ ha hc
  have hfour :
      (radius a φ) ^ 4 = a ^ 4 * (Real.cos (2 * φ)) ^ 2 := by
    calc
      (radius a φ) ^ 4 = ((radius a φ) ^ 2) ^ 2 := by ring
      _ = (a ^ 2 * Real.cos (2 * φ)) ^ 2 := by rw [hrsq]
      _ = a ^ 4 * (Real.cos (2 * φ)) ^ 2 := by ring
  have hunit :
      (radius a φ) ^ 4 + a ^ 4 * (Real.sin (2 * φ)) ^ 2 =
        a ^ 4 := by
    calc
      (radius a φ) ^ 4 + a ^ 4 * (Real.sin (2 * φ)) ^ 2 =
          a ^ 4 *
            ((Real.sin (2 * φ)) ^ 2 + (Real.cos (2 * φ)) ^ 2) := by
        rw [hfour]
        ring
      _ = a ^ 4 := by
        rw [Real.sin_sq_add_cos_sq]
        simp
  have hsum :
      (radius a φ) ^ 2 + (deriv (radius a) φ) ^ 2 =
        a ^ 4 / (radius a φ) ^ 2 := by
    rw [gap1 a φ ha hc]
    calc
      (radius a φ) ^ 2 +
            (-(a ^ 2 * Real.sin (2 * φ) / radius a φ)) ^ 2 =
          ((radius a φ) ^ 4 +
              a ^ 4 * (Real.sin (2 * φ)) ^ 2) /
            (radius a φ) ^ 2 := by
        field_simp [hrs]
        <;> ring
      _ = a ^ 4 / (radius a φ) ^ 2 := by rw [hunit]
  have hratio :
      a ^ 4 / (radius a φ) ^ 2 =
        (a ^ 2 / radius a φ) ^ 2 := by
    field_simp [hrs]
    <;> ring
  have hquotpos : 0 < a ^ 2 / radius a φ :=
    div_pos (pow_pos ha 2) hrpos
  have hsqrt :
      Real.sqrt (a ^ 4 / (radius a φ) ^ 2) =
        a ^ 2 / radius a φ := by
    rw [hratio, Real.sqrt_sq_eq_abs, abs_of_pos hquotpos]
  unfold powThreeHalves
  rw [hsum, hsqrt]
  field_simp [hrs]
  <;> ring
theorem gap5 (a φ : ℝ) (ha : 0 < a) (hc : 0 < Real.cos (2 * φ)) :
    curvatureRadius a φ =
      (a ^ 6 / (radius a φ) ^ 3) / (3 * a ^ 4 / (radius a φ) ^ 2) := by
  unfold curvatureRadius
  rw [gap4 a φ ha hc, gap3 a φ ha hc]
theorem gap6 (a φ : ℝ) (ha : 0 < a) (hc : 0 < Real.cos (2 * φ)) :
    curvatureRadius a φ = a ^ 2 / (3 * radius a φ) := by
  have hrs : radius a φ ≠ 0 := (radius_pos a φ ha hc).ne'
  rw [gap5 a φ ha hc]
  field_simp [hrs, ha.ne']
  <;> ring

end
end ProofGap.Exercise1608
