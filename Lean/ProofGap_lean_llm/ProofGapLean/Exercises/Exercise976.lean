import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise976

noncomputable section

def arccot (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x
def u (a x : ℝ) : ℝ := Real.rpow a x

def Y (t : ℝ) : ℝ :=
  t / (1 + t ^ 2) - (1 - t ^ 2) / (1 + t ^ 2) * arccot t⁻¹

def y (a x : ℝ) : ℝ :=
  Real.rpow a x / (1 + Real.rpow a (2 * x)) -
    (1 - Real.rpow a (2 * x)) / (1 + Real.rpow a (2 * x)) *
      arccot (Real.rpow a (-x))

def rawDU (t : ℝ) : ℝ :=
  (1 + t ^ 2 - 2 * t ^ 2) / (1 + t ^ 2) ^ 2 -
    ((-2 * t * (1 + t ^ 2) - 2 * t * (1 - t ^ 2)) /
      (1 + t ^ 2) ^ 2) * arccot t⁻¹ -
    (1 - t ^ 2) / (1 + t ^ 2) * (1 / (t ^ 2 * (1 + 1 / t ^ 2)))

def reducedDU (t : ℝ) : ℝ :=
  4 * t * arccot t⁻¹ / (1 + t ^ 2) ^ 2

def finalDerivative (a x : ℝ) : ℝ :=
  4 * Real.rpow a (2 * x) * Real.log a /
      (1 + Real.rpow a (2 * x)) ^ 2 *
    arccot (Real.rpow a (-x))

private theorem rpow_twice (a x : ℝ) (ha : 0 < a) :
    Real.rpow a (2 * x) = (Real.rpow a x) ^ 2 := by
  calc
    Real.rpow a (2 * x) = Real.exp (Real.log a * (2 * x)) :=
      Real.rpow_def_of_pos ha (2 * x)
    _ = (Real.exp (Real.log a * x)) ^ 2 := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ = (Real.rpow a x) ^ 2 :=
      congrArg (fun z : ℝ => z ^ 2) (Real.rpow_def_of_pos ha x).symm

private theorem rpow_neg_eq_inv (a x : ℝ) (ha : 0 < a) :
    Real.rpow a (-x) = (Real.rpow a x)⁻¹ := by
  calc
    Real.rpow a (-x) = Real.exp (Real.log a * (-x)) :=
      Real.rpow_def_of_pos ha (-x)
    _ = (Real.exp (Real.log a * x))⁻¹ := by
      rw [show Real.log a * (-x) = -(Real.log a * x) by ring, Real.exp_neg]
    _ = (Real.rpow a x)⁻¹ :=
      congrArg (fun z : ℝ => z⁻¹) (Real.rpow_def_of_pos ha x).symm

private theorem u_pos (a x : ℝ) (ha : 0 < a) : 0 < u a x := by
  unfold u
  exact Real.rpow_pos_of_pos ha x

private theorem hasDerivAt_Y_raw_of_pos (t : ℝ) (ht : 0 < t) :
    HasDerivAt Y (rawDU t) t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hden0 : 1 + t ^ 2 ≠ 0 := by positivity
  have hinvden0 : 1 + (t⁻¹) ^ 2 ≠ 0 := by positivity
  have hdivden0 : 1 + 1 / t ^ 2 ≠ 0 := by positivity
  have hsq : HasDerivAt (fun z : ℝ => z ^ 2) (2 * t) t := by
    simpa [Function.id_def] using (hasDerivAt_id t).pow 2
  have hden : HasDerivAt (fun z : ℝ => 1 + z ^ 2) (2 * t) t := by
    exact hsq.const_add 1
  have hnum : HasDerivAt (fun z : ℝ => 1 - z ^ 2) (-2 * t) t := by
    convert hsq.const_sub 1 using 1 <;> ring
  have hfirst :
      HasDerivAt (fun z : ℝ => z / (1 + z ^ 2))
        ((1 + t ^ 2 - 2 * t ^ 2) / (1 + t ^ 2) ^ 2) t := by
    convert (hasDerivAt_id t).div hden hden0 using 1 <;>
      dsimp only [Function.comp_apply, Function.id_def] <;> ring
  have hquot :
      HasDerivAt (fun z : ℝ => (1 - z ^ 2) / (1 + z ^ 2))
        ((-2 * t * (1 + t ^ 2) - 2 * t * (1 - t ^ 2)) /
          (1 + t ^ 2) ^ 2) t := by
    convert hnum.div hden hden0 using 1 <;>
      dsimp only [Function.comp_apply, Function.id_def] <;> ring
  have hinv : HasDerivAt (fun z : ℝ => z⁻¹) (-1 / t ^ 2) t := by
    convert (hasDerivAt_id t).inv ht0 using 1 <;>
      dsimp only [Function.comp_apply, Function.id_def] <;>
      field_simp [ht0] <;> ring
  have hatan := (Real.hasDerivAt_arctan (t⁻¹)).comp t hinv
  have harccot :
      HasDerivAt (fun z : ℝ => arccot z⁻¹)
        (1 / (t ^ 2 * (1 + 1 / t ^ 2))) t := by
    unfold arccot
    convert (hasDerivAt_const t (Real.pi / 2)).sub hatan using 1 <;>
      dsimp only [Function.comp_apply, Function.id_def] <;>
      field_simp [ht0, hinvden0, hdivden0] <;> ring
  unfold Y rawDU
  convert hfirst.sub (hquot.mul harccot) using 1 <;>
    dsimp only [Function.comp_apply, Function.id_def] <;> ring

private theorem rawDU_eq_reducedDU_of_pos (t : ℝ) (ht : 0 < t) :
    rawDU t = reducedDU t := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hden0 : 1 + t ^ 2 ≠ 0 := by positivity
  have hdivden0 : 1 + 1 / t ^ 2 ≠ 0 := by positivity
  unfold rawDU reducedDU
  field_simp [ht0, hden0, hdivden0] <;> ring

theorem gap1 (a x : ℝ) (ha : 0 < a) :
    y a x = Y (u a x) := by
  unfold y Y u
  rw [rpow_twice a x ha, rpow_neg_eq_inv a x ha]

theorem gap2 (a x : ℝ) (ha : 0 < a) :
    HasDerivAt Y (rawDU (u a x)) (u a x) := by
  exact hasDerivAt_Y_raw_of_pos (u a x) (u_pos a x ha)

theorem gap3 (a x : ℝ) (ha : 0 < a) :
    HasDerivAt Y (reducedDU (u a x)) (u a x) := by
  have hu : 0 < u a x := u_pos a x ha
  rw [← rawDU_eq_reducedDU_of_pos (u a x) hu]
  exact hasDerivAt_Y_raw_of_pos (u a x) hu

theorem gap4 (a x : ℝ) (ha : 0 < a) :
    reducedDU (u a x) =
      4 * Real.rpow a x * arccot (Real.rpow a (-x)) /
        (1 + Real.rpow a (2 * x)) ^ 2 := by
  unfold reducedDU u
  rw [rpow_twice a x ha, rpow_neg_eq_inv a x ha]

theorem gap5 (a x : ℝ) (ha : 0 < a) :
    HasDerivAt Y
      (4 * Real.rpow a x * arccot (Real.rpow a (-x)) /
        (1 + Real.rpow a (2 * x)) ^ 2) (u a x) := by
  rw [← gap4 a x ha]
  exact gap3 a x ha

theorem gap6 (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (u a) (Real.rpow a x * Real.log a) x := by
  have hinner :
      HasDerivAt (fun z : ℝ => Real.log a * z) (Real.log a) x := by
    simpa [Function.id_def] using
      (hasDerivAt_const x (Real.log a)).mul (hasDerivAt_id x)
  have hu_exp : u a = fun z : ℝ => Real.exp (Real.log a * z) := by
    funext z
    unfold u
    exact Real.rpow_def_of_pos ha z
  have hax : Real.exp (Real.log a * x) = Real.rpow a x := by
    exact (Real.rpow_def_of_pos ha x).symm
  rw [hu_exp]
  simpa only [Function.comp_apply, hax] using
    (Real.hasDerivAt_exp (Real.log a * x)).comp x hinner

theorem gap7 (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (fun z => Y (u a z))
      (reducedDU (u a x) * (Real.rpow a x * Real.log a)) x := by
  simpa only [Function.comp_apply] using
    (gap3 a x ha).comp x (gap6 a x ha)

theorem gap8 (a x : ℝ) (ha : 0 < a) :
    reducedDU (u a x) * (Real.rpow a x * Real.log a) =
      finalDerivative a x := by
  rw [gap4 a x ha]
  unfold finalDerivative
  rw [rpow_twice a x ha]
  ring

theorem gap9 (a x : ℝ) (ha : 0 < a) :
    HasDerivAt (y a) (finalDerivative a x) x := by
  have hy : y a = fun z => Y (u a z) := by
    funext z
    exact gap1 a z ha
  rw [hy, ← gap8 a x ha]
  exact gap7 a x ha

end

end ProofGap.Exercise976
