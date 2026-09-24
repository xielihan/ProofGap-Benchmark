import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Nat

-- exercise: exercise_3300

noncomputable abbrev P3 := ℝ × ℝ × ℝ

noncomputable def px (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 1 (fun t : ℝ => f (t, p.2.1, p.2.2)) p.1

noncomputable def py (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 1 (fun t : ℝ => f (p.1, t, p.2.2)) p.2.1

noncomputable def pz (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 1 (fun t : ℝ => f (p.1, p.2.1, t)) p.2.2

noncomputable def pxx (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ => f (t, p.2.1, p.2.2)) p.1

noncomputable def pyy (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ => f (p.1, t, p.2.2)) p.2.1

noncomputable def pzz (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ => f (p.1, p.2.1, t)) p.2.2

noncomputable def pxy (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 1 (fun t : ℝ => px f (p.1, t, p.2.2)) p.2.1

noncomputable def pxz (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 1 (fun t : ℝ => px f (p.1, p.2.1, t)) p.2.2

noncomputable def pyz (f : P3 -> ℝ) (p : P3) : ℝ :=
  iteratedDeriv 1 (fun t : ℝ => py f (p.1, p.2.1, t)) p.2.2

theorem proof_gap_exercise_3300_1
  (a b c : ℝ)
  (f u : P3 -> ℝ)
  (h1 : ContDiff ℝ (2 : ℕ∞) f)
  (h2 : ∀ x y z : ℝ, u (x, y, z) = f (a * x, b * y, c * z))
  : ∀ x y z dx dy dz : ℝ,
      px u (x, y, z) * dx + py u (x, y, z) * dy + pz u (x, y, z) * dz =
        a * px f (a * x, b * y, c * z) * dx +
        b * py f (a * x, b * y, c * z) * dy +
        c * pz f (a * x, b * y, c * z) * dz := by
  sorry

theorem proof_gap_exercise_3300_2
  (a b c : ℝ)
  (f u : P3 -> ℝ)
  (h1 : ContDiff ℝ (2 : ℕ∞) f)
  (h2 : ∀ x y z : ℝ, u (x, y, z) = f (a * x, b * y, c * z))
  (h3 : ∀ x y z dx dy dz : ℝ,
      px u (x, y, z) * dx + py u (x, y, z) * dy + pz u (x, y, z) * dz =
        a * px f (a * x, b * y, c * z) * dx +
        b * py f (a * x, b * y, c * z) * dy +
        c * pz f (a * x, b * y, c * z) * dz)
  : ∀ x y z dx dy dz : ℝ,
      pxx u (x, y, z) * dx ^ 2 + pyy u (x, y, z) * dy ^ 2 + pzz u (x, y, z) * dz ^ 2 +
          2 * pxy u (x, y, z) * dx * dy + 2 * pxz u (x, y, z) * dx * dz +
          2 * pyz u (x, y, z) * dy * dz =
        a ^ 2 * pxx f (a * x, b * y, c * z) * dx ^ 2 +
          b ^ 2 * pyy f (a * x, b * y, c * z) * dy ^ 2 +
          c ^ 2 * pzz f (a * x, b * y, c * z) * dz ^ 2 +
          2 * a * b * pxy f (a * x, b * y, c * z) * dx * dy +
          2 * a * c * pxz f (a * x, b * y, c * z) * dx * dz +
          2 * b * c * pyz f (a * x, b * y, c * z) * dy * dz := by
  sorry
