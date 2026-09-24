import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1212

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (x : ℝ) : ℝ := Real.log x / x
def nthDifferential (n : ℕ) (f : ℝ → ℝ) (x dx : ℝ) : ℝ :=
  iterDeriv n f x * dx ^ n

def harmonic (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k

def leibnizForm (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    (Nat.choose n k : ℝ) *
      iterDeriv k (fun t : ℝ => 1 / t) x *
      iterDeriv (n - k) Real.log x

def closedForm (n : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / x ^ (n + 1)) *
    (Real.log x - harmonic n)

private theorem harmonic_succ (n : ℕ) :
    harmonic (n + 1) = harmonic n + (1 : ℝ) / (n + 1) := by
  have hIcc : Finset.Icc 1 (n + 1) =
      insert (n + 1) (Finset.Icc 1 n) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  have hnot : n + 1 ∉ Finset.Icc 1 n := by
    simp
  unfold harmonic
  rw [hIcc, Finset.sum_insert hnot]
  simp [Nat.cast_add, add_comm]

private theorem leibniz_identity (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iterDeriv n y x = leibnizForm n x := by
  have hf : ContDiffAt ℝ ⊤ (fun t : ℝ => 1 / t) x := by
    exact contDiffAt_const.div contDiffAt_id hx.ne'
  have hg : ContDiffAt ℝ ⊤ Real.log x := by
    exact (Real.contDiffAt_log).2 hx.ne'
  have hf' : ContDiffAt ℝ n (fun t : ℝ => 1 / t) x :=
    hf.of_le le_top
  have hg' : ContDiffAt ℝ n Real.log x := hg.of_le le_top
  have h := iteratedDeriv_mul (n := n) (x := x)
    (f := fun t : ℝ => 1 / t) (g := Real.log) hf' hg'
  have hy : y = (fun t : ℝ => 1 / t) * Real.log := by
    funext t
    simp [y, div_eq_mul_inv, mul_comm]
  rw [hy]
  simpa only [iteratedDeriv_eq_iterate, iterDeriv, leibnizForm, mul_assoc]
    using h

private theorem iterDeriv_y_closed (n : ℕ) (x : ℝ) (hx : 0 < x) :
    iterDeriv n y x =
      ((-1 : ℝ) ^ n * (Nat.factorial n : ℝ) / x ^ (n + 1)) *
        (Real.log x - harmonic n) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, y, harmonic, div_eq_mul_inv, mul_comm]
  | succ n ih =>
      have hs : iterDeriv (n + 1) y x = deriv (iterDeriv n y) x := by
        simp [iterDeriv, Function.iterate_succ_apply']
      rw [hs]
      let C : ℝ := (-1 : ℝ) ^ n * (Nat.factorial n : ℝ)
      have heq : Filter.EventuallyEq (nhds x) (iterDeriv n y)
          (fun z : ℝ => C * (z ^ (n + 1))⁻¹ *
            (Real.log z - harmonic n)) := by
        filter_upwards [eventually_gt_nhds hx] with z hz
        simpa [C, div_eq_mul_inv] using ih z hz
      rw [heq.deriv_eq]
      have hpow :
          HasDerivAt (fun z : ℝ => z ^ (n + 1))
            ((n + 1 : ℕ) * x ^ n) x :=
        hasDerivAt_pow (n + 1) x
      have hbase :=
        ((hpow.inv (pow_ne_zero (n + 1) hx.ne')).const_mul C).mul
          ((Real.hasDerivAt_log hx.ne').sub_const (harmonic n))
      have hd :
          deriv (fun z : ℝ => C * (z ^ (n + 1))⁻¹ *
            (Real.log z - harmonic n)) x =
            C * (-(((n + 1 : ℕ) : ℝ) * x ^ n) /
                (x ^ (n + 1)) ^ 2) *
                (Real.log x - harmonic n) +
              C * (x ^ (n + 1))⁻¹ * x⁻¹ := by
        simpa using hbase.deriv
      rw [hd, harmonic_succ]
      simp only [C, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one, pow_succ]
      field_simp [hx.ne']
      ring

theorem gap1 (n : ℕ) (x dx : ℝ) (hx : 0 < x) :
    nthDifferential n y x dx = iterDeriv n y x * dx ^ n := by
  rfl

theorem gap2 (n : ℕ) (x dx : ℝ) (hx : 0 < x) :
    iterDeriv n y x * dx ^ n = leibnizForm n x * dx ^ n := by
  rw [leibniz_identity n x hx]

theorem gap3 (n : ℕ) (x dx : ℝ) (hx : 0 < x) :
    nthDifferential n y x dx = leibnizForm n x * dx ^ n := by
  rw [gap1 n x dx hx, gap2 n x dx hx]

theorem gap4 (n : ℕ) (x dx : ℝ) (hx : 0 < x) :
    nthDifferential n y x dx = closedForm n x * dx ^ n := by
  unfold nthDifferential closedForm
  rw [iterDeriv_y_closed n x hx]

end

end ProofGap.Exercise1212
