import Mathlib

noncomputable section

abbrev F := ℝ × ℝ → ℝ

def RDomain : Set ℝ := {x : ℝ | x = x}

def frac (x y : ℝ) : ℝ := x / y

def px (f : F) (p : ℝ × ℝ) : ℝ := deriv (fun x => f (x, p.2)) p.1
def py (f : F) (p : ℝ × ℝ) : ℝ := deriv (fun y => f (p.1, y)) p.2
def pxx (f : F) (p : ℝ × ℝ) : ℝ := px (fun q => px f q) p
def pyy (f : F) (p : ℝ × ℝ) : ℝ := py (fun q => py f q) p
def pxy (f : F) (p : ℝ × ℝ) : ℝ := py (fun q => px f q) p
def pu (f : F) (p : ℝ × ℝ) : ℝ := px f p
def pv (f : F) (p : ℝ × ℝ) : ℝ := py f p
def puu (f : F) (p : ℝ × ℝ) : ℝ := pxx f p
def pvv (f : F) (p : ℝ × ℝ) : ℝ := pyy f p
def puv (f : F) (p : ℝ × ℝ) : ℝ := pxy f p
def C2 (f : F) : Prop := ContDiff ℝ 2 f
def C2One (f : ℝ → ℝ) : Prop := ContDiff ℝ 2 f

namespace exercise_3502

variable (z φ ψ : F) (I du dv dx dy : ℝ)

def conformal3502 : Prop := ∀ u v : ℝ, pu φ (u,v) = pv ψ (u,v) ∧ pv φ (u,v) = -pu ψ (u,v)

theorem proof_gap_exercise_3502_1 : ∀ x u v : ℝ, dx = pu φ (u,v) * du + pv φ (u,v) * dv := by sorry
theorem proof_gap_exercise_3502_2 : ∀ y u v : ℝ, dy = pu ψ (u,v) * du + pv ψ (u,v) * dv := by sorry
theorem proof_gap_exercise_3502_3 : ∀ y v u : ℝ, dy = -pv φ (u,v) * du + pu φ (u,v) * dv := by sorry
theorem proof_gap_exercise_3502_4 : ∀ u v : ℝ, I = pu φ (u,v)^2 + pv φ (u,v)^2 := by sorry
theorem proof_gap_exercise_3502_5 : ∀ u v : ℝ, pu φ (u,v)^2 + pv φ (u,v)^2 ≠ 0 := by sorry
theorem proof_gap_exercise_3502_6 : I ≠ 0 := by sorry
theorem proof_gap_exercise_3502_7 : ∀ u v x y : ℝ, du = frac 1 I * (pu φ (u,v) * dx - pv φ (u,v) * dy) := by sorry
theorem proof_gap_exercise_3502_8 : ∀ v u x y : ℝ, dv = frac 1 I * (pv φ (u,v) * dx + pu φ (u,v) * dy) := by sorry
theorem proof_gap_exercise_3502_9 : ∀ u x y v : ℝ, deriv (fun x => u) x = frac 1 I * pu φ (u,v) := by sorry
theorem proof_gap_exercise_3502_10 : ∀ v y x u : ℝ, deriv (fun y => v) y = frac 1 I * pu φ (u,v) := by sorry
theorem proof_gap_exercise_3502_11 : ∀ u y x v : ℝ, deriv (fun y => u) y = -frac 1 I * pv φ (u,v) := by sorry
theorem proof_gap_exercise_3502_12 : ∀ v x y u : ℝ, deriv (fun x => v) x = frac 1 I * pv φ (u,v) := by sorry
theorem proof_gap_exercise_3502_13 : ∀ u x y v : ℝ, deriv (fun x => u) x = deriv (fun y => v) y := by sorry
theorem proof_gap_exercise_3502_14 : ∀ u y x v : ℝ, deriv (fun y => u) y = -deriv (fun x => v) x := by sorry
theorem proof_gap_exercise_3502_15 : ∀ u x y : ℝ, deriv (fun x => u) x ^ 2 + deriv (fun y => u) y ^ 2 = frac 1 I := by sorry
theorem proof_gap_exercise_3502_16 : ∀ x y u v : ℝ, pxx z (x,y) + pyy z (x,y) = (deriv (fun x => u) x^2 + deriv (fun y => u) y^2) * (puu z (u,v) + pvv z (u,v)) := by sorry
theorem proof_gap_exercise_3502_17 : ∀ x y u v : ℝ, pxx z (x,y) + pyy z (x,y) = frac 1 I * (puu z (u,v) + pvv z (u,v)) := by sorry
theorem proof_gap_exercise_3502_18 : ∀ u v : ℝ, puu z (u,v) + pvv z (u,v) = 0 := by sorry
theorem proof_gap_exercise_3502_19 : ∀ u v : ℝ, puu z (u,v) + pvv z (u,v) = 0 := by sorry

end exercise_3502
