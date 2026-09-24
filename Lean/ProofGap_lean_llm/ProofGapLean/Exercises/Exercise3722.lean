import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise3722

noncomputable section

open scoped Interval

def integralFunction (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, f t * (x - t) ^ (n - 1)

def nthDerivative (m : ℕ) (g : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[m]) g

private lemma hasDerivAt_const_sub_pow (x t : ℝ) (k : ℕ) :
    HasDerivAt (fun s : ℝ => (x - s) ^ k)
      (-((k : ℝ) * (x - t) ^ (k - 1))) t := by
  convert ((hasDerivAt_const t x).sub (hasDerivAt_id t)).pow k using 1 <;>
    simp only [Pi.sub_apply, Function.const_apply, id_eq] <;> ring

private lemma integralFunction_succ_succ (k : ℕ) (f : ℝ → ℝ)
    (hf : Continuous f) (x : ℝ) :
    integralFunction (k + 2) f x =
      (k + 1 : ℝ) *
        integralFunction (k + 1) (fun s => ∫ t in (0 : ℝ)..s, f t) x := by
  let F : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, f t
  have hFderiv : ∀ s : ℝ, HasDerivAt F (f s) s := by
    intro s
    exact (hf.integral_hasStrictDerivAt 0 s).hasDerivAt
  have hFcont : Continuous F :=
    continuous_iff_continuousAt.2 fun s => (hFderiv s).continuousAt
  have hip := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (0 : ℝ)) (b := x)
    (u := fun s : ℝ => (x - s) ^ (k + 1))
    (v := F)
    (u' := fun s : ℝ => -((k + 1 : ℝ) * (x - s) ^ k))
    (v' := f)
    (fun s _ => by
      simpa [Nat.add_sub_cancel] using hasDerivAt_const_sub_pow x s (k + 1))
    (fun s _ => hFderiv s)
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow k)).neg
      |>.intervalIntegrable 0 x)
    (hf.intervalIntegrable 0 x)
  have hk : k + 2 - 1 = k + 1 := by omega
  simp only [integralFunction, hk, Nat.add_sub_cancel] at ⊢
  calc
    (∫ t in (0 : ℝ)..x, f t * (x - t) ^ (k + 1)) =
        ∫ t in (0 : ℝ)..x, (x - t) ^ (k + 1) * f t := by
          congr 1
          funext t
          ring
    _ = (x - x) ^ (k + 1) * F x -
          (x - 0) ^ (k + 1) * F 0 -
          ∫ t in (0 : ℝ)..x,
            (-((k + 1 : ℝ) * (x - t) ^ k)) * F t := hip
    _ = (k + 1 : ℝ) *
          ∫ t in (0 : ℝ)..x, F t * (x - t) ^ k := by
          simp only [F, intervalIntegral.integral_same, sub_self,
            zero_pow (Nat.succ_ne_zero k), zero_mul, mul_zero, sub_zero]
          rw [zero_sub]
          change
            -(∫ t in (0 : ℝ)..x,
                (-((k + 1 : ℝ) * (x - t) ^ k)) *
                  (∫ r in (0 : ℝ)..t, f r)) =
              (k + 1 : ℝ) *
                ∫ t in (0 : ℝ)..x,
                  (∫ r in (0 : ℝ)..t, f r) * (x - t) ^ k
          calc
            -(∫ t in (0 : ℝ)..x,
                (-((k + 1 : ℝ) * (x - t) ^ k)) *
                  (∫ r in (0 : ℝ)..t, f r)) =
                ∫ t in (0 : ℝ)..x,
                  (k + 1 : ℝ) *
                    ((∫ r in (0 : ℝ)..t, f r) * (x - t) ^ k) := by
                    rw [← intervalIntegral.integral_neg]
                    apply intervalIntegral.integral_congr
                    intro t _
                    ring
            _ = (k + 1 : ℝ) *
                ∫ t in (0 : ℝ)..x,
                  (∫ r in (0 : ℝ)..t, f r) * (x - t) ^ k :=
              intervalIntegral.integral_const_mul _ _

private lemma continuous_intervalAntiderivative (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (fun x => ∫ t in (0 : ℝ)..x, f t) :=
  continuous_iff_continuousAt.2 fun x =>
    (hf.integral_hasStrictDerivAt 0 x).hasDerivAt.continuousAt

private lemma integralFunction_hasDerivAt_succ_succ
    (k : ℕ) (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    HasDerivAt (integralFunction (k + 2) f)
      ((k + 1 : ℝ) * integralFunction (k + 1) f x) x := by
  induction k generalizing f x with
  | zero =>
      let F : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, f t
      have hFcont : Continuous F := continuous_intervalAntiderivative f hf
      have hfun :
          integralFunction 2 f =
            fun y => integralFunction 1 F y := by
        funext y
        simpa [F] using integralFunction_succ_succ 0 f hf y
      rw [hfun]
      simpa [integralFunction, F] using
        (hFcont.integral_hasStrictDerivAt 0 x).hasDerivAt
  | succ k ih =>
      let F : ℝ → ℝ := fun s => ∫ t in (0 : ℝ)..s, f t
      have hFcont : Continuous F := continuous_intervalAntiderivative f hf
      have hfun :
          integralFunction (k + 1 + 2) f =
            fun y => (k + 2 : ℝ) * integralFunction (k + 2) F y := by
        funext y
        convert integralFunction_succ_succ (k + 1) f hf y using 1 <;>
          simp only [F, Nat.cast_add, Nat.cast_one] <;> ring
      rw [hfun]
      have hd := HasDerivAt.const_mul (k + 2 : ℝ) (ih F hFcont x)
      have hrec := integralFunction_succ_succ k f hf x
      convert hd using 1 <;>
        simp only [Nat.cast_add, Nat.cast_one] at hrec ⊢ <;> nlinarith

private lemma deriv_integrand_formula (n : ℕ) (f : ℝ → ℝ) (t x : ℝ) :
    deriv (fun y : ℝ => f t * (y - t) ^ (n - 1)) x =
      ((n - 1 : ℕ) : ℝ) * (f t * (x - t) ^ (n - 2)) := by
  have hd :=
    HasDerivAt.const_mul (f t)
      (((hasDerivAt_id x).sub_const t).pow (n - 1))
  convert hd.deriv using 1 <;>
    simp only [id_eq, Pi.pow_apply, Pi.sub_apply, Nat.sub_sub] <;> ring

private lemma integral_deriv_integrand_formula (n : ℕ) (f : ℝ → ℝ) (x : ℝ) :
    (∫ t in (0 : ℝ)..x,
        deriv (fun y : ℝ => f t * (y - t) ^ (n - 1)) x) =
      ((n - 1 : ℕ) : ℝ) *
        ∫ t in (0 : ℝ)..x, f t * (x - t) ^ (n - 2) := by
  simp_rw [deriv_integrand_formula]
  exact intervalIntegral.integral_const_mul _ _

theorem gap1 (n : ℕ) (f : ℝ → ℝ) (hn : 2 ≤ n)
    (hf : Continuous f) :
    ∀ x : ℝ,
      deriv (integralFunction n f) x =
        ∫ t in (0 : ℝ)..x,
          deriv (fun y : ℝ => f t * (y - t) ^ (n - 1)) x := by
  intro x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [integral_deriv_integrand_formula]
  have hd := integralFunction_hasDerivAt_succ_succ k f hf x
  have hsub1 : 2 + k - 1 = k + 1 := by omega
  have hsub2 : 2 + k - 2 = k := by omega
  simpa [integralFunction, hsub1, hsub2, Nat.add_comm,
    Nat.cast_add, Nat.cast_one] using hd.deriv

theorem gap2 (n : ℕ) (f : ℝ → ℝ) :
    ∀ x : ℝ,
      (∫ t in (0 : ℝ)..x,
          deriv (fun y : ℝ => f t * (y - t) ^ (n - 1)) x) =
        ((n - 1 : ℕ) : ℝ) *
          ∫ t in (0 : ℝ)..x, f t * (x - t) ^ (n - 2) := by
  exact integral_deriv_integrand_formula n f

theorem gap3 (n : ℕ) (f : ℝ → ℝ) (hn : 2 ≤ n)
    (hf : Continuous f) :
    ∀ x : ℝ,
      deriv (integralFunction n f) x =
        ((n - 1 : ℕ) : ℝ) *
          ∫ t in (0 : ℝ)..x, f t * (x - t) ^ (n - 2) := by
  intro x
  rw [gap1 n f hn hf x]
  exact gap2 n f x

theorem gap4 (n : ℕ) (f : ℝ → ℝ) (hn : 3 ≤ n)
    (hf : Continuous f) :
    ∀ x : ℝ,
      nthDerivative 2 (integralFunction n f) x =
        ((n - 1 : ℕ) : ℝ) * ((n - 2 : ℕ) : ℝ) *
          ∫ t in (0 : ℝ)..x, f t * (x - t) ^ (n - 3) := by
  intro x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hfirst :
      deriv (integralFunction (3 + k) f) =
        fun y => ((2 + k : ℕ) : ℝ) * integralFunction (2 + k) f y := by
    funext y
    have hd := integralFunction_hasDerivAt_succ_succ k.succ f hf y
    have hidx : k.succ + 2 = 3 + k := by omega
    have hinner : k.succ + 1 = 2 + k := by omega
    rw [← hidx, hd.deriv]
    rw [hinner]
    simp only [Nat.cast_succ, Nat.cast_add, Nat.cast_one]
    ring
  have hd2 := integralFunction_hasDerivAt_succ_succ k f hf x
  rw [show nthDerivative 2 (integralFunction (3 + k) f) x =
      deriv (deriv (integralFunction (3 + k) f)) x by
        rfl, hfirst]
  have hscaled := HasDerivAt.const_mul ((2 + k : ℕ) : ℝ) hd2
  have hsub1 : 3 + k - 1 = k + 2 := by omega
  have hsub2 : 3 + k - 2 = k + 1 := by omega
  have hsub3 : 3 + k - 3 = k := by omega
  have hk1 : k + 1 - 1 = k := by omega
  convert hscaled.deriv using 1 <;>
    simp only [integralFunction, hsub1, hsub2, hsub3, hk1,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] <;> ring

private lemma iterate_deriv_const_mul (m : ℕ) (c : ℝ) (g : ℝ → ℝ) :
    (deriv^[m]) (fun x => c * g x) =
      fun x => c * (deriv^[m]) g x := by
  induction m generalizing g with
  | zero => rfl
  | succ m ih =>
      rw [Function.iterate_succ_apply, deriv_const_mul_field', ih,
        Function.iterate_succ_apply]

private lemma iterate_deriv_integralFunction_succ
    (k : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    (deriv^[k]) (integralFunction (k + 1) f) =
      fun x => (Nat.factorial k : ℝ) * integralFunction 1 f x := by
  induction k generalizing f with
  | zero =>
      funext x
      simp
  | succ k ih =>
      have hfirst :
          deriv (integralFunction (k.succ + 1) f) =
            fun x => (k + 1 : ℝ) * integralFunction (k + 1) f x := by
        funext x
        have hd := integralFunction_hasDerivAt_succ_succ k f hf x
        have hidx : k.succ + 1 = k + 2 := by omega
        rw [hidx, hd.deriv]
      rw [Function.iterate_succ_apply, hfirst,
        iterate_deriv_const_mul, ih f hf]
      funext x
      simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
        Nat.cast_one]
      ring

theorem gap5 (n : ℕ) (f : ℝ → ℝ) (hn : 1 ≤ n)
    (hf : Continuous f) :
    ∀ x : ℝ,
      nthDerivative (n - 1) (integralFunction n f) x =
        (Nat.factorial (n - 1) : ℝ) * ∫ t in (0 : ℝ)..x, f t := by
  intro x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hsub : 1 + k - 1 = k := by omega
  have hiter := congrFun (iterate_deriv_integralFunction_succ k f hf) x
  simpa [nthDerivative, integralFunction, hsub, Nat.add_comm] using hiter

theorem gap6 (n : ℕ) (f : ℝ → ℝ) (hn : 1 ≤ n)
    (hf : Continuous f) :
    ∀ x : ℝ,
      nthDerivative n (integralFunction n f) x =
        (Nat.factorial (n - 1) : ℝ) * f x := by
  intro x
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hidx : 1 + k = k.succ := by omega
  rw [hidx]
  change (deriv^[k.succ]) (integralFunction (k + 1) f) x =
    (Nat.factorial (k.succ - 1) : ℝ) * f x
  rw [Function.iterate_succ_apply',
    iterate_deriv_integralFunction_succ k f hf]
  have hfun :
      integralFunction 1 f =
        fun u => ∫ t in (0 : ℝ)..u, f t := by
    funext u
    simp [integralFunction]
  have hbase :
      HasDerivAt (integralFunction 1 f) (f x) x := by
    rw [hfun]
    exact (hf.integral_hasStrictDerivAt 0 x).hasDerivAt
  rw [(HasDerivAt.const_mul (Nat.factorial k : ℝ) hbase).deriv]
  have hk : k.succ - 1 = k := by omega
  rw [hk]

end

end ProofGap.Exercise3722
