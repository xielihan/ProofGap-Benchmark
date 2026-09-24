import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Real

abbrev Point3 := ℝ × ℝ × ℝ
abbrev Fun3 := Point3 -> ℝ

axiom SurfaceInt : Set Point3 -> Fun3 -> ℝ
axiom VolumeInt : Set Point3 -> Fun3 -> ℝ

noncomputable abbrev pd3 (f : Fun3) (i k : ℕ) : Fun3 := fun _ => 0

-- exercise: exercise_4380
-- Exercise 4380

noncomputable abbrev curlP (Q R : Fun3) : Fun3 :=
  fun p => pd3 R 2 1 p - pd3 Q 3 1 p

noncomputable abbrev curlQ (P R : Fun3) : Fun3 :=
  fun p => pd3 P 3 1 p - pd3 R 1 1 p

noncomputable abbrev curlR (P Q : Fun3) : Fun3 :=
  fun p => pd3 Q 1 1 p - pd3 P 2 1 p

theorem proof_gap_exercise_4380_1
  (S V : Set Point3)
  (P Q R P_star Q_star R_star : Fun3)
  (hP : ContDiff ℝ (2 : ℕ∞) P)
  (hQ : ContDiff ℝ (2 : ℕ∞) Q)
  (hR : ContDiff ℝ (2 : ℕ∞) R)
  (hPstar : P_star = curlP Q R)
  (hQstar : Q_star = curlQ P R)
  (hRstar : R_star = curlR P Q)
  : ∀ x y z : ℝ,
      pd3 P_star 1 1 (x, y, z) + pd3 Q_star 2 1 (x, y, z) + pd3 R_star 3 1 (x, y, z) = 0 := by
  sorry

theorem proof_gap_exercise_4380_2
  (S V : Set Point3)
  (P Q R P_star Q_star R_star : Fun3)
  (hP : ContDiff ℝ (2 : ℕ∞) P)
  (hQ : ContDiff ℝ (2 : ℕ∞) Q)
  (hR : ContDiff ℝ (2 : ℕ∞) R)
  (hPstar : P_star = curlP Q R)
  (hQstar : Q_star = curlQ P R)
  (hRstar : R_star = curlR P Q)
  (hdiv : ∀ x y z : ℝ,
      pd3 P_star 1 1 (x, y, z) + pd3 Q_star 2 1 (x, y, z) + pd3 R_star 3 1 (x, y, z) = 0)
  : SurfaceInt S (fun p => P_star p + Q_star p + R_star p) =
      VolumeInt V (fun _ => 0) := by
  sorry

theorem proof_gap_exercise_4380_3
  (S V : Set Point3)
  (P Q R P_star Q_star R_star : Fun3)
  (hP : ContDiff ℝ (2 : ℕ∞) P)
  (hQ : ContDiff ℝ (2 : ℕ∞) Q)
  (hR : ContDiff ℝ (2 : ℕ∞) R)
  (hPstar : P_star = curlP Q R)
  (hQstar : Q_star = curlQ P R)
  (hRstar : R_star = curlR P Q)
  (hdiv : ∀ x y z : ℝ,
      pd3 P_star 1 1 (x, y, z) + pd3 Q_star 2 1 (x, y, z) + pd3 R_star 3 1 (x, y, z) = 0)
  (hgauss : SurfaceInt S (fun p => P_star p + Q_star p + R_star p) =
      VolumeInt V (fun _ => 0))
  : SurfaceInt S (fun p => (pd3 R 2 1 p - pd3 Q 3 1 p) +
      (pd3 P 3 1 p - pd3 R 1 1 p) + (pd3 Q 1 1 p - pd3 P 2 1 p)) = 0 := by
  sorry
