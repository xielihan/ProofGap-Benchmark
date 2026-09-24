import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise1156

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := x * (2 * x - 1) ^ 2 * (x + 3) ^ 3

private theorem sixth_deriv_y (x : ℝ) : nthDeriv 6 y x = 2880 := by
  have h1 : deriv y = fun x : ℝ =>
      24 * x ^ 5 + 160 * x ^ 4 + 292 * x ^ 3 + 27 * x ^ 2 +
        (-162) * x + 27 := by
    funext x
    have hx := hasDerivAt_id x
    have hlin : HasDerivAt (fun t : ℝ => 2 * t - 1) 2 x := by
      simpa [id_eq] using ((hx.const_mul (2 : ℝ)).sub_const (1 : ℝ))
    have hsq := hlin.pow 2
    have hcube := (hx.add_const (3 : ℝ)).pow 3
    convert (((hx.mul hsq).mul hcube).deriv) using 1 <;>
      simp [y, id_eq] <;> ring
  have h2 :
      deriv (fun x : ℝ =>
        24 * x ^ 5 + 160 * x ^ 4 + 292 * x ^ 3 + 27 * x ^ 2 +
          (-162) * x + 27) =
        fun x : ℝ =>
          120 * x ^ 4 + 640 * x ^ 3 + 876 * x ^ 2 + 54 * x + (-162) := by
    funext x
    have hx := hasDerivAt_id x
    have ha := (hx.pow 5).const_mul (24 : ℝ)
    have hb := (hx.pow 4).const_mul (160 : ℝ)
    have hc := (hx.pow 3).const_mul (292 : ℝ)
    have hd := (hx.pow 2).const_mul (27 : ℝ)
    have he := hx.const_mul (-162 : ℝ)
    have hf := hasDerivAt_const (x := x) (c := (27 : ℝ))
    convert (((((ha.add hb).add hc).add hd).add he).add hf).deriv using 1 <;>
      simp [id_eq] <;> ring
  have h3 :
      deriv (fun x : ℝ =>
        120 * x ^ 4 + 640 * x ^ 3 + 876 * x ^ 2 + 54 * x + (-162)) =
        fun x : ℝ => 480 * x ^ 3 + 1920 * x ^ 2 + 1752 * x + 54 := by
    funext x
    have hx := hasDerivAt_id x
    have ha := (hx.pow 4).const_mul (120 : ℝ)
    have hb := (hx.pow 3).const_mul (640 : ℝ)
    have hc := (hx.pow 2).const_mul (876 : ℝ)
    have hd := hx.const_mul (54 : ℝ)
    have he := hasDerivAt_const (x := x) (c := (-162 : ℝ))
    convert ((((ha.add hb).add hc).add hd).add he).deriv using 1 <;>
      simp [id_eq] <;> ring
  have h4 :
      deriv (fun x : ℝ => 480 * x ^ 3 + 1920 * x ^ 2 + 1752 * x + 54) =
        fun x : ℝ => 1440 * x ^ 2 + 3840 * x + 1752 := by
    funext x
    have hx := hasDerivAt_id x
    have ha := (hx.pow 3).const_mul (480 : ℝ)
    have hb := (hx.pow 2).const_mul (1920 : ℝ)
    have hc := hx.const_mul (1752 : ℝ)
    have hd := hasDerivAt_const (x := x) (c := (54 : ℝ))
    convert (((ha.add hb).add hc).add hd).deriv using 1 <;>
      simp [id_eq] <;> ring
  have h5 :
      deriv (fun x : ℝ => 1440 * x ^ 2 + 3840 * x + 1752) =
        fun x : ℝ => 2880 * x + 3840 := by
    funext x
    have hx := hasDerivAt_id x
    have ha := (hx.pow 2).const_mul (1440 : ℝ)
    have hb := hx.const_mul (3840 : ℝ)
    have hc := hasDerivAt_const (x := x) (c := (1752 : ℝ))
    convert ((ha.add hb).add hc).deriv using 1 <;>
      simp [id_eq] <;> ring
  have h6 :
      deriv (fun x : ℝ => 2880 * x + 3840) = fun _ : ℝ => 2880 := by
    funext x
    have hx := hasDerivAt_id x
    have ha := hx.const_mul (2880 : ℝ)
    have hb := hasDerivAt_const (x := x) (c := (3840 : ℝ))
    convert (ha.add hb).deriv using 1 <;>
      simp [id_eq] <;> ring
  simp only [nthDeriv]
  rw [h1, h2, h3, h4, h5, h6]

theorem gap1 (x : ℝ) :
    nthDeriv 6 y x =
      (1 : ℝ) * 2 ^ 2 * 1 ^ 3 * ((Nat.factorial 6 : ℕ) : ℝ) := by
  rw [sixth_deriv_y]
  norm_num [Nat.factorial]

theorem gap2 :
    (1 : ℝ) * 2 ^ 2 * 1 ^ 3 * ((Nat.factorial 6 : ℕ) : ℝ) =
      4 * ((Nat.factorial 6 : ℕ) : ℝ) := by
  norm_num

theorem gap3 :
    (4 : ℝ) * ((Nat.factorial 6 : ℕ) : ℝ) = 2880 := by
  norm_num [Nat.factorial]
theorem gap4 (x : ℝ) : nthDeriv 6 y x = 2880 := by
  exact sixth_deriv_y x
theorem gap5 (x : ℝ) : nthDeriv 7 y x = 0 := by
  change deriv (nthDeriv 6 y) x = 0
  have h : nthDeriv 6 y = fun _ : ℝ => 2880 := by
    funext z
    exact sixth_deriv_y z
  rw [h]
  simp

end

end ProofGap.Exercise1156
