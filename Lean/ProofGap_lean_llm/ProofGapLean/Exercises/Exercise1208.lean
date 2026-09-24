import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1208

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (a b x : ℝ) : ℝ := Real.log ((a + b * x) / (a - b * x))

def nthFormula (a b : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((-1 : ℝ) ^ (n - 1) * b ^ n * (Nat.factorial (n - 1) : ℝ)) /
      (a + b * x) ^ n +
    (b ^ n * (Nat.factorial (n - 1) : ℝ)) / (a - b * x) ^ n

private theorem nthFormula_hasDerivAt_succ
    (a b x : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : a + b * x ≠ 0) (hm : a - b * x ≠ 0) :
    HasDerivAt (nthFormula a b n) (nthFormula a b (n + 1) x) x := by
  have hplus : HasDerivAt (fun z : ℝ => a + b * z) b x := by
    simpa only [mul_one] using
      (((hasDerivAt_id x).const_mul b).const_add a)
  have hminus : HasDerivAt (fun z : ℝ => a - b * z) (-b) x := by
    simpa only [mul_one, neg_mul, sub_eq_add_neg] using
      (((hasDerivAt_id x).const_mul (-b)).const_add a)
  have hnform : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
  have hfacNat : Nat.factorial n = n * Nat.factorial (n - 1) := by
    calc
      Nat.factorial n = Nat.factorial (n - 1 + 1) :=
        congrArg Nat.factorial hnform
      _ = (n - 1 + 1) * Nat.factorial (n - 1) := Nat.factorial_succ _
      _ = n * Nat.factorial (n - 1) := by rw [Nat.sub_add_cancel hn]
  have hfac : (Nat.factorial n : ℝ) =
      (n : ℝ) * (Nat.factorial (n - 1) : ℝ) := by
    rw [hfacNat, Nat.cast_mul]
  have hsign : (-1 : ℝ) ^ n = -((-1 : ℝ) ^ (n - 1)) := by
    calc
      (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n - 1 + 1) :=
        congrArg (fun k : ℕ => (-1 : ℝ) ^ k) hnform
      _ = -((-1 : ℝ) ^ (n - 1)) := by rw [pow_succ]; ring
  have hp_pow : (a + b * x) ^ n =
      (a + b * x) ^ (n - 1) * (a + b * x) := by
    calc
      (a + b * x) ^ n = (a + b * x) ^ (n - 1 + 1) :=
        congrArg (fun k : ℕ => (a + b * x) ^ k) hnform
      _ = (a + b * x) ^ (n - 1) * (a + b * x) := pow_succ _ _
  have hm_pow : (a - b * x) ^ n =
      (a - b * x) ^ (n - 1) * (a - b * x) := by
    calc
      (a - b * x) ^ n = (a - b * x) ^ (n - 1 + 1) :=
        congrArg (fun k : ℕ => (a - b * x) ^ k) hnform
      _ = (a - b * x) ^ (n - 1) * (a - b * x) := pow_succ _ _
  unfold nthFormula
  have h :=
    (((hasDerivAt_const x
        (((-1 : ℝ) ^ (n - 1)) * b ^ n *
          (Nat.factorial (n - 1) : ℝ))).div
        (hplus.pow n) (pow_ne_zero n hp)).add
      ((hasDerivAt_const x
        (b ^ n * (Nat.factorial (n - 1) : ℝ))).div
        (hminus.pow n) (pow_ne_zero n hm)))
  convert h using 1 <;>
    simp only [Nat.add_sub_cancel, hfac, hsign, pow_succ, Pi.pow_apply,
      zero_mul, zero_sub]
  rw [hp_pow, hm_pow]
  field_simp [hp, hm]

theorem gap1 (a b x : ℝ) (hp : a + b * x ≠ 0) (hm : a - b * x ≠ 0) :
    deriv (y a b) x = b / (a + b * x) + b / (a - b * x) := by
  unfold y
  have hplus : HasDerivAt (fun z : ℝ => a + b * z) b x := by
    simpa only [mul_one] using
      (((hasDerivAt_id x).const_mul b).const_add a)
  have hminus : HasDerivAt (fun z : ℝ => a - b * z) (-b) x := by
    simpa only [mul_one, neg_mul, sub_eq_add_neg] using
      (((hasDerivAt_id x).const_mul (-b)).const_add a)
  have hquot := hplus.div hminus hm
  have harg : (a + b * x) / (a - b * x) ≠ 0 := div_ne_zero hp hm
  have hlog := (Real.hasDerivAt_log harg).comp x hquot
  convert hlog.deriv using 1
  field_simp [hp, hm]
  <;> ring

theorem gap2 (a b x : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : a + b * x ≠ 0) (hm : a - b * x ≠ 0) :
    iterDeriv n (y a b) x = nthFormula a b n x := by
  have hiter : ∀ (k : ℕ) (z : ℝ),
      a + b * z ≠ 0 → a - b * z ≠ 0 →
        iterDeriv (k + 1) (y a b) z = nthFormula a b (k + 1) z := by
    intro k
    induction k with
    | zero =>
        intro z hpz hmz
        simpa [iterDeriv, nthFormula] using gap1 a b z hpz hmz
    | succ k ih =>
        intro z hpz hmz
        have hpc : ContinuousAt (fun w : ℝ => a + b * w) z := by
          exact continuousAt_const.add
            (continuousAt_const.mul continuousAt_id)
        have hmc : ContinuousAt (fun w : ℝ => a - b * w) z := by
          exact continuousAt_const.sub
            (continuousAt_const.mul continuousAt_id)
        have hpe : ∀ᶠ w in nhds z, a + b * w ≠ 0 := by
          simpa using hpc.eventually_ne hpz
        have hme : ∀ᶠ w in nhds z, a - b * w ≠ 0 := by
          simpa using hmc.eventually_ne hmz
        have heq :
            iterDeriv (k + 1) (y a b) =ᶠ[nhds z]
              nthFormula a b (k + 1) :=
          (hpe.and hme).mono (fun w hw => ih w hw.1 hw.2)
        have hstep := nthFormula_hasDerivAt_succ a b z (k + 1)
          (Nat.succ_le_succ (Nat.zero_le k)) hpz hmz
        calc
          iterDeriv (Nat.succ k + 1) (y a b) z =
              deriv (iterDeriv (k + 1) (y a b)) z := by
                simp only [iterDeriv, Function.iterate_succ_apply']
          _ = deriv (nthFormula a b (k + 1)) z := heq.deriv_eq
          _ = nthFormula a b ((k + 1) + 1) z := hstep.deriv
  have hidx : n - 1 + 1 = n := Nat.sub_add_cancel hn
  simpa only [hidx] using hiter (n - 1) x hp hm

theorem gap3 (a b x : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (hp : a + b * x ≠ 0) (hm : a - b * x ≠ 0) :
    iterDeriv n (y a b) x =
      ((Nat.factorial (n - 1) : ℝ) * b ^ n /
          (a ^ 2 - b ^ 2 * x ^ 2) ^ n) *
        ((a + b * x) ^ n + (-1 : ℝ) ^ (n - 1) * (a - b * x) ^ n) := by
  rw [gap2 a b x n hn hp hm]
  unfold nthFormula
  have hprod :
      a ^ 2 - b ^ 2 * x ^ 2 = (a + b * x) * (a - b * x) := by
    ring
  rw [hprod, mul_pow]
  field_simp [hp, hm]
  ring

end

end ProofGap.Exercise1208
