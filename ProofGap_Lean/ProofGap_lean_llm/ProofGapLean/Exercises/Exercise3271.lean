import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3271

noncomputable section

def u (x y : ℝ) : ℝ :=
  Real.log (x + y)

def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) g

def directional (n : ℕ) (x y dx dy : ℝ) : ℝ :=
  iterDeriv n (fun s => u (x + s * dx) (y + s * dy)) 0

private theorem iterDeriv_log_affine
    (n : ℕ) (A B s : ℝ) (hs : 0 < A + s * B) :
    iterDeriv (n + 1) (fun t : ℝ => Real.log (A + t * B)) s =
      (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * B ^ (n + 1) *
        (A + s * B)⁻¹ ^ (n + 1) := by
  induction n generalizing s with
  | zero =>
      have hq : HasDerivAt (fun t : ℝ => A + t * B) B s := by
        convert
          (hasDerivAt_const s A).add ((hasDerivAt_id s).mul_const B) using 1 <;>
          simp [Pi.add_apply]
      have hlog := hq.log (ne_of_gt hs)
      simpa [iterDeriv, div_eq_mul_inv] using hlog.deriv
  | succ n ih =>
      change iterDeriv (Nat.succ (n + 1))
        (fun t : ℝ => Real.log (A + t * B)) s = _
      rw [iterDeriv, Function.iterate_succ_apply']
      change deriv
        (iterDeriv (n + 1) (fun t : ℝ => Real.log (A + t * B))) s = _
      have hq : HasDerivAt (fun t : ℝ => A + t * B) B s := by
        convert
          (hasDerivAt_const s A).add ((hasDerivAt_id s).mul_const B) using 1 <;>
          simp [Pi.add_apply]
      have hpos : ∀ᶠ t in nhds s, 0 < A + t * B :=
        hq.continuousAt (Ioi_mem_nhds hs)
      have heq :
          (fun t => iterDeriv (n + 1)
            (fun r : ℝ => Real.log (A + r * B)) t) =ᶠ[nhds s]
          (fun t => (-1 : ℝ) ^ n * (Nat.factorial n : ℝ) *
            B ^ (n + 1) * (A + t * B)⁻¹ ^ (n + 1)) :=
        hpos.mono (fun t ht => ih t ht)
      have hne : A + s * B ≠ 0 := ne_of_gt hs
      have hinv :
          HasDerivAt (fun t : ℝ => (A + t * B)⁻¹)
            (-B * (A + s * B)⁻¹ ^ 2) s := by
        simpa [div_eq_mul_inv, inv_pow] using hq.inv hne
      have hd :
          HasDerivAt
            (fun t : ℝ =>
              ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * B ^ (n + 1)) *
                (A + t * B)⁻¹ ^ (n + 1))
            (((-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * B ^ (n + 1)) *
              (((n + 1 : ℕ) : ℝ) * (A + s * B)⁻¹ ^ (n + 1 - 1) *
                (-B * (A + s * B)⁻¹ ^ 2))) s := by
        simpa only using
          (hinv.pow (n + 1)).const_mul
            ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ) * B ^ (n + 1))
      rw [heq.deriv_eq, hd.deriv]
      simp [Nat.factorial_succ, pow_succ]
      <;> ring

theorem gap1 (x y dx dy : ℝ) (hxy : 0 < x + y) :
    directional 1 x y dx dy = (dx + dy) / (x + y) := by
  have hfun :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        (fun s : ℝ => Real.log ((x + y) + s * (dx + dy))) := by
    funext s
    simp only [u]
    congr 1
    ring
  change iterDeriv 1 (fun s : ℝ => u (x + s * dx) (y + s * dy)) 0 = _
  rw [hfun]
  simpa [div_eq_mul_inv] using
    (iterDeriv_log_affine 0 (x + y) (dx + dy) 0 (by simpa using hxy))

theorem gap2 (x y dx dy : ℝ) (hxy : 0 < x + y) :
    directional 10 x y dx dy =
      -((Nat.factorial 9 : ℝ) / (x + y) ^ 10) * (dx + dy) ^ 10 := by
  have hfun :
      (fun s : ℝ => u (x + s * dx) (y + s * dy)) =
        (fun s : ℝ => Real.log ((x + y) + s * (dx + dy))) := by
    funext s
    simp only [u]
    congr 1
    ring
  change iterDeriv 10 (fun s : ℝ => u (x + s * dx) (y + s * dy)) 0 = _
  rw [hfun]
  have h :=
    iterDeriv_log_affine 9 (x + y) (dx + dy) 0 (by simpa using hxy)
  rw [h]
  simp only [zero_mul, add_zero, inv_pow]
  simp [div_eq_mul_inv]
  ring

end

end ProofGap.Exercise3271
