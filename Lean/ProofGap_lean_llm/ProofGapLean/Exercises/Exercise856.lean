import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

namespace ProofGap.Exercise856

noncomputable section

/-- The positive-real `k`th-root expression used by the source exercise. -/
def nthRoot (k : ℕ) (u : ℝ) : ℝ :=
  Real.rpow u (1 / (k : ℝ))

def radicand (m n : ℕ) (x : ℝ) : ℝ :=
  (1 - x) ^ m * (1 + x) ^ n

def y (m n : ℕ) (x : ℝ) : ℝ :=
  nthRoot (m + n) (radicand m n x)

/-- Source: `proof_gap/exercise_856/1.txt`.
Positive exponents and `-1 < x < 1` supply the omitted root domain. -/
private theorem hasDerivAt_y_base (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (y m n)
      (((1 / ((m + n : ℕ) : ℝ)) *
          Real.rpow (radicand m n x)
            (1 / ((m + n : ℕ) : ℝ) - 1)) *
        (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
          (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m)) x := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hleft_pos : 0 < 1 - x := by linarith
  have hright_pos : 0 < 1 + x := by linarith
  have hrad_pos : 0 < radicand m n x := by
    unfold radicand
    exact mul_pos (pow_pos hleft_pos m) (pow_pos hright_pos n)
  have hleft : HasDerivAt (fun t : ℝ => 1 - t) (-1) x := by
    simpa using
      ((hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x))
  have hright : HasDerivAt (fun t : ℝ => 1 + t) 1 x := by
    simpa using
      ((hasDerivAt_const (x := x) (c := (1 : ℝ))).add (hasDerivAt_id x))
  have hrad :
      HasDerivAt (radicand m n)
        (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
          (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) x := by
    unfold radicand
    convert (hleft.pow m).mul (hright.pow n) using 1 <;>
      simp only [Pi.pow_apply] <;> ring_nf
  have hroot :
      HasDerivAt
        (fun u : ℝ => Real.rpow u (1 / ((m + n : ℕ) : ℝ)))
        ((1 / ((m + n : ℕ) : ℝ)) *
          Real.rpow (radicand m n x)
            (1 / ((m + n : ℕ) : ℝ) - 1))
        (radicand m n x) := by
    exact Real.hasDerivAt_rpow_const (Or.inl hrad_pos.ne')
  unfold y nthRoot
  convert hroot.comp x hrad using 1 <;> ring

theorem gap1 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (y m n)
      ((-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
          (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) /
        (((m + n : ℕ) : ℝ) *
          nthRoot (m + n) ((radicand m n x) ^ (m + n - 1)))) x := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hleft : 0 < 1 - x := by linarith
  have hright : 0 < 1 + x := by linarith
  have hrad : 0 < radicand m n x := by
    unfold radicand
    exact mul_pos (pow_pos hleft m) (pow_pos hright n)
  have hk : 0 < m + n := Nat.add_pos_left hm n
  have hk_one : 1 ≤ m + n := hk
  have hk_real : 0 < ((m + n : ℕ) : ℝ) := by
    simp only [Nat.cast_add]
    exact add_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
  have hrpow_def (z : ℝ) :
      Real.rpow (radicand m n x) z =
        Real.exp (Real.log (radicand m n x) * z) := by
    exact Real.rpow_def_of_pos hrad z
  have hpow_rpow_def :
      Real.rpow ((radicand m n x) ^ (m + n - 1))
          (1 / ((m + n : ℕ) : ℝ)) =
        Real.exp
          (Real.log ((radicand m n x) ^ (m + n - 1)) *
            (1 / ((m + n : ℕ) : ℝ))) := by
    exact
      Real.rpow_def_of_pos (pow_pos hrad (m + n - 1))
        (1 / ((m + n : ℕ) : ℝ))
  have hden_rpow_def :
      Real.rpow (radicand m n x)
          (1 - 1 / ((m + n : ℕ) : ℝ)) =
        Real.exp
          (Real.log (radicand m n x) *
            (1 - 1 / ((m + n : ℕ) : ℝ))) :=
    hrpow_def (1 - 1 / ((m + n : ℕ) : ℝ))
  have hden :
      nthRoot (m + n) ((radicand m n x) ^ (m + n - 1)) =
        Real.rpow (radicand m n x)
          (1 - 1 / ((m + n : ℕ) : ℝ)) := by
    unfold nthRoot
    rw [hpow_rpow_def, hden_rpow_def]
    congr 1
    rw [Real.log_pow, Nat.cast_sub hk_one]
    field_simp [hk_real.ne'] <;> ring
  have hp_def :
      Real.rpow (radicand m n x)
          (1 / ((m + n : ℕ) : ℝ) - 1) =
        Real.exp
          (Real.log (radicand m n x) *
            (1 / ((m + n : ℕ) : ℝ) - 1)) :=
    hrpow_def (1 / ((m + n : ℕ) : ℝ) - 1)
  have hq_def :
      Real.rpow (radicand m n x)
          (1 - 1 / ((m + n : ℕ) : ℝ)) =
        Real.exp
          (Real.log (radicand m n x) *
            (1 - 1 / ((m + n : ℕ) : ℝ))) :=
    hrpow_def (1 - 1 / ((m + n : ℕ) : ℝ))
  have hpow :
      Real.rpow (radicand m n x)
          (1 / ((m + n : ℕ) : ℝ) - 1) *
        Real.rpow (radicand m n x)
          (1 - 1 / ((m + n : ℕ) : ℝ)) = 1 := by
    rw [hp_def, hq_def, ← Real.exp_add]
    have hexp :
        Real.log (radicand m n x) *
              (1 / ((m + n : ℕ) : ℝ) - 1) +
            Real.log (radicand m n x) *
              (1 - 1 / ((m + n : ℕ) : ℝ)) = 0 := by
      ring
    rw [hexp, Real.exp_zero]
  have hden_pos :
      0 < Real.rpow (radicand m n x)
        (1 - 1 / ((m + n : ℕ) : ℝ)) :=
    Real.rpow_pos_of_pos hrad _
  have hcoef_mul :
      ((1 / ((m + n : ℕ) : ℝ)) *
          Real.rpow (radicand m n x)
            (1 / ((m + n : ℕ) : ℝ) - 1)) *
        (((m + n : ℕ) : ℝ) *
          Real.rpow (radicand m n x)
            (1 - 1 / ((m + n : ℕ) : ℝ))) = 1 := by
    calc
      ((1 / ((m + n : ℕ) : ℝ)) *
            Real.rpow (radicand m n x)
              (1 / ((m + n : ℕ) : ℝ) - 1)) *
          (((m + n : ℕ) : ℝ) *
            Real.rpow (radicand m n x)
              (1 - 1 / ((m + n : ℕ) : ℝ))) =
        Real.rpow (radicand m n x)
              (1 / ((m + n : ℕ) : ℝ) - 1) *
          Real.rpow (radicand m n x)
              (1 - 1 / ((m + n : ℕ) : ℝ)) := by
            field_simp [hk_real.ne'] <;> ring
      _ = 1 := hpow
  have hcoef :
      (1 / ((m + n : ℕ) : ℝ)) *
          Real.rpow (radicand m n x)
            (1 / ((m + n : ℕ) : ℝ) - 1) =
        1 /
          (((m + n : ℕ) : ℝ) *
            Real.rpow (radicand m n x)
              (1 - 1 / ((m + n : ℕ) : ℝ))) := by
    exact
      (eq_div_iff (mul_ne_zero hk_real.ne' hden_pos.ne')).2 hcoef_mul
  have hderivEq :
      ((1 / ((m + n : ℕ) : ℝ)) *
          Real.rpow (radicand m n x)
            (1 / ((m + n : ℕ) : ℝ) - 1)) *
          (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
            (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) =
        (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
            (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) /
          (((m + n : ℕ) : ℝ) *
            nthRoot (m + n)
              ((radicand m n x) ^ (m + n - 1))) := by
    rw [hden, hcoef]
    ring
  have hbase := hasDerivAt_y_base m n hm hn x ⟨hxlo, hxhi⟩
  rw [hderivEq] at hbase
  exact hbase

/-- Source: `proof_gap/exercise_856/2.txt`.
The source's last denominator is algebraically incorrect for general `m,n`;
the factor `(1-x^2)` and the numerator factor `y(x)` are restored. -/
theorem gap2 (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (x : ℝ)
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    HasDerivAt (y m n)
      ((((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) * y m n x) /
        (((m + n : ℕ) : ℝ) * (1 - x ^ 2))) x := by
  rcases hx with ⟨hxlo, hxhi⟩
  have hleft : 0 < 1 - x := by linarith
  have hright : 0 < 1 + x := by linarith
  have hrad : 0 < radicand m n x := by
    unfold radicand
    exact mul_pos (pow_pos hleft m) (pow_pos hright n)
  have hk_real : 0 < ((m + n : ℕ) : ℝ) := by
    simp only [Nat.cast_add]
    exact add_pos (Nat.cast_pos.mpr hm) (Nat.cast_pos.mpr hn)
  have hsquare : 0 < 1 - x ^ 2 := by
    have hsquare_eq : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [hsquare_eq]
    exact mul_pos hleft hright
  have hmpow :
      (1 - x) ^ m = (1 - x) ^ (m - 1) * (1 - x) := by
    calc
      (1 - x) ^ m = (1 - x) ^ ((m - 1) + 1) := by
        rw [Nat.sub_add_cancel hm]
      _ = (1 - x) ^ (m - 1) * (1 - x) := by rw [pow_succ]
  have hnpow :
      (1 + x) ^ n = (1 + x) ^ (n - 1) * (1 + x) := by
    calc
      (1 + x) ^ n = (1 + x) ^ ((n - 1) + 1) := by
        rw [Nat.sub_add_cancel hn]
      _ = (1 + x) ^ (n - 1) * (1 + x) := by rw [pow_succ]
  have hradicand_deriv :
      (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
          (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) *
          (1 - x ^ 2) =
        ((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) *
          radicand m n x := by
    unfold radicand
    rw [hmpow, hnpow]
    simp only [Nat.cast_add]
    ring
  have hp_def :
      Real.rpow (radicand m n x)
          (1 / ((m + n : ℕ) : ℝ) - 1) =
        Real.exp
          (Real.log (radicand m n x) *
            (1 / ((m + n : ℕ) : ℝ) - 1)) := by
    exact
      Real.rpow_def_of_pos hrad
        (1 / ((m + n : ℕ) : ℝ) - 1)
  have hroot_def :
      Real.rpow (radicand m n x)
          (1 / ((m + n : ℕ) : ℝ)) =
        Real.exp
          (Real.log (radicand m n x) *
            (1 / ((m + n : ℕ) : ℝ))) := by
    exact
      Real.rpow_def_of_pos hrad
        (1 / ((m + n : ℕ) : ℝ))
  have hrootrel :
      Real.rpow (radicand m n x)
          (1 / ((m + n : ℕ) : ℝ) - 1) *
        radicand m n x = nthRoot (m + n) (radicand m n x) := by
    unfold nthRoot
    rw [hp_def, hroot_def]
    calc
      Real.exp
              (Real.log (radicand m n x) *
                (1 / ((m + n : ℕ) : ℝ) - 1)) *
            radicand m n x =
          Real.exp
                (Real.log (radicand m n x) *
                  (1 / ((m + n : ℕ) : ℝ) - 1)) *
            Real.exp (Real.log (radicand m n x)) := by
              rw [Real.exp_log hrad]
      _ = Real.exp
            (Real.log (radicand m n x) *
              (1 / ((m + n : ℕ) : ℝ))) := by
            rw [← Real.exp_add]
            congr 1
            ring
  have hderivEq :
      ((1 / ((m + n : ℕ) : ℝ)) *
          Real.rpow (radicand m n x)
            (1 / ((m + n : ℕ) : ℝ) - 1)) *
          (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
            (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) =
        (((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) *
            nthRoot (m + n) (radicand m n x)) /
          (((m + n : ℕ) : ℝ) * (1 - x ^ 2)) := by
    calc
      ((1 / ((m + n : ℕ) : ℝ)) *
            Real.rpow (radicand m n x)
              (1 / ((m + n : ℕ) : ℝ) - 1)) *
          (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
            (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) =
        (Real.rpow (radicand m n x)
              (1 / ((m + n : ℕ) : ℝ) - 1) *
            (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
              (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m)) /
          ((m + n : ℕ) : ℝ) := by ring
      _ =
        (Real.rpow (radicand m n x)
              (1 / ((m + n : ℕ) : ℝ) - 1) *
            (-(m : ℝ) * (1 - x) ^ (m - 1) * (1 + x) ^ n +
              (n : ℝ) * (1 + x) ^ (n - 1) * (1 - x) ^ m) *
            (1 - x ^ 2)) /
          (((m + n : ℕ) : ℝ) * (1 - x ^ 2)) := by
            field_simp [hk_real.ne', hsquare.ne']
      _ =
        (Real.rpow (radicand m n x)
              (1 / ((m + n : ℕ) : ℝ) - 1) *
            (((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) *
              radicand m n x)) /
          (((m + n : ℕ) : ℝ) * (1 - x ^ 2)) := by
            rw [mul_assoc, hradicand_deriv]
      _ =
        (((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) *
            nthRoot (m + n) (radicand m n x)) /
          (((m + n : ℕ) : ℝ) * (1 - x ^ 2)) := by
            congr 1
            calc
              Real.rpow (radicand m n x)
                    (1 / ((m + n : ℕ) : ℝ) - 1) *
                  (((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) *
                    radicand m n x) =
                ((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) *
                  (Real.rpow (radicand m n x)
                      (1 / ((m + n : ℕ) : ℝ) - 1) *
                    radicand m n x) := by ring
              _ =
                ((n : ℝ) - (m : ℝ) - ((m + n : ℕ) : ℝ) * x) *
                  nthRoot (m + n) (radicand m n x) := by
                    rw [hrootrel]
  have hbase := hasDerivAt_y_base m n hm hn x ⟨hxlo, hxhi⟩
  rw [hderivEq] at hbase
  simpa only [y] using hbase

end

end ProofGap.Exercise856
