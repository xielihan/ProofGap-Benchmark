import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise3263

noncomputable section

def u (x y : ℝ) : ℝ :=
  (x + y) / (x - y)

def partialXOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g t y) x

def partialYOrder (n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun t => g x t) y

def mixedOrder (m n : ℕ) (g : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  partialYOrder n (fun a b => partialXOrder m g a b) x y

def reciprocalPower (m : ℕ) (x y : ℝ) : ℝ :=
  1 / (x - y) ^ (m + 1)

def rising (a n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, ((a + k : ℕ) : ℝ)

def leibnizForm (m n : ℕ) (x y : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
    (y * partialYOrder n (reciprocalPower m) x y +
      (Nat.choose n 1 : ℝ) *
        partialYOrder (n - 1) (reciprocalPower m) x y)

def risingForm (m n : ℕ) (x y : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
    (rising (m + 1) n * y / (x - y) ^ (m + n + 1) +
      (n : ℝ) * rising (m + 1) (n - 1) /
        (x - y) ^ (m + n))

def closedForm (m n : ℕ) (x y : ℝ) : ℝ :=
  2 * (-1 : ℝ) ^ m * (Nat.factorial (m + n - 1) : ℝ) *
      ((n : ℝ) * x + (m : ℝ) * y) /
    (x - y) ^ (m + n + 1)

private theorem rising_succ (a n : ℕ) :
    rising a (n + 1) = rising a n * ((a + n : ℕ) : ℝ) := by
  simp [rising, Finset.prod_range_succ]

private theorem factorial_mul_rising (m n : ℕ) :
    (Nat.factorial m : ℝ) * rising (m + 1) n =
      (Nat.factorial (m + n) : ℝ) := by
  induction n with
  | zero => simp [rising]
  | succ n ih =>
      rw [rising_succ]
      calc
        (Nat.factorial m : ℝ) *
            (rising (m + 1) n * (((m + 1 + n : ℕ) : ℝ))) =
            ((Nat.factorial m : ℝ) * rising (m + 1) n) *
              (((m + 1 + n : ℕ) : ℝ)) := by ring
        _ = (Nat.factorial (m + n) : ℝ) * (((m + n + 1 : ℕ) : ℝ)) := by
          rw [ih]
          congr 2 <;> omega
        _ = (Nat.factorial (m + (n + 1)) : ℝ) := by
          rw [show m + (n + 1) = (m + n) + 1 by omega,
            Nat.factorial_succ]
          push_cast
          ring

private theorem hasDerivAt_sub_pow_x
    (m : ℕ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (t - y) ^ (m + 1))
      (((m + 1 : ℕ) : ℝ) * (x - y) ^ m) x := by
  induction m with
  | zero =>
      simpa using (hasDerivAt_id x).sub_const y
  | succ m ih =>
      have hd := ih.mul ((hasDerivAt_id x).sub_const y)
      convert hd using 1 <;>
        simp [pow_succ, Nat.cast_add, Nat.cast_one] <;>
        ring

private theorem hasDerivAt_sub_pow_y
    (m : ℕ) (x y : ℝ) :
    HasDerivAt (fun t : ℝ => (x - t) ^ (m + 1))
      (-(((m + 1 : ℕ) : ℝ)) * (x - y) ^ m) y := by
  induction m with
  | zero =>
      simpa using (hasDerivAt_const y x).sub (hasDerivAt_id y)
  | succ m ih =>
      have hd := ih.mul
        ((hasDerivAt_const y x).sub (hasDerivAt_id y))
      convert hd using 1 <;>
        simp [pow_succ, Nat.cast_add, Nat.cast_one] <;>
        ring

private theorem hasDerivAt_reciprocalPower_x
    (m : ℕ) {x y : ℝ} (hxy : x ≠ y) :
    HasDerivAt (fun t => reciprocalPower m t y)
      (-((m + 1 : ℕ) : ℝ) * reciprocalPower (m + 1) x y) x := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hpowm : (x - y) ^ m ≠ 0 := pow_ne_zero _ hsub
  have hpow : (x - y) ^ (m + 1) ≠ 0 := pow_ne_zero _ hsub
  have hdPow := hasDerivAt_sub_pow_x m x y
  have hdInv := hdPow.inv hpow
  change HasDerivAt
      (fun t : ℝ => ((t - y) ^ (m + 1))⁻¹)
      (-(((m + 1 : ℕ) : ℝ) * (x - y) ^ m) /
        ((x - y) ^ (m + 1)) ^ 2) x at hdInv
  have hcoef :
      -(((m + 1 : ℕ) : ℝ) * (x - y) ^ m) /
          ((x - y) ^ (m + 1)) ^ 2 =
        -((m + 1 : ℕ) : ℝ) * reciprocalPower (m + 1) x y := by
    unfold reciprocalPower
    simp only [pow_succ, pow_zero]
    field_simp [hsub, hpowm] <;> ring
  rw [← hcoef]
  simpa only [reciprocalPower, one_div] using hdInv

private theorem hasDerivAt_reciprocalPower_y
    (m : ℕ) {x y : ℝ} (hxy : x ≠ y) :
    HasDerivAt (fun t => reciprocalPower m x t)
      (((m + 1 : ℕ) : ℝ) * reciprocalPower (m + 1) x y) y := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hpowm : (x - y) ^ m ≠ 0 := pow_ne_zero _ hsub
  have hpow : (x - y) ^ (m + 1) ≠ 0 := pow_ne_zero _ hsub
  have hdPow := hasDerivAt_sub_pow_y m x y
  have hdInv := hdPow.inv hpow
  change HasDerivAt
      (fun t : ℝ => ((x - t) ^ (m + 1))⁻¹)
      (-(-(((m + 1 : ℕ) : ℝ)) * (x - y) ^ m) /
        ((x - y) ^ (m + 1)) ^ 2) y at hdInv
  have hcoef :
      -(-(((m + 1 : ℕ) : ℝ)) * (x - y) ^ m) /
          ((x - y) ^ (m + 1)) ^ 2 =
        (((m + 1 : ℕ) : ℝ) * reciprocalPower (m + 1) x y) := by
    unfold reciprocalPower
    simp only [pow_succ, pow_zero]
    field_simp [hsub, hpowm] <;> ring
  rw [← hcoef]
  simpa only [reciprocalPower, one_div] using hdInv

private theorem iterate_deriv_congr_off
    (n : ℕ) (f g : ℝ → ℝ) (a x : ℝ)
    (hfg : ∀ z, z ≠ a → f z = g z) (hxa : x ≠ a) :
    (deriv^[n]) f x = (deriv^[n]) g x := by
  induction n generalizing x with
  | zero => simpa using hfg x hxa
  | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      have heq : (deriv^[n]) f =ᶠ[nhds x] (deriv^[n]) g := by
        filter_upwards [eventually_ne_nhds hxa] with z hz
        exact ih z hz
      exact heq.deriv_eq

private theorem iter_deriv_x_u_succ (n : ℕ) :
    ∀ x y : ℝ, x ≠ y →
      (deriv^[n + 1]) (fun t => u t y) x =
        (-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ) *
          (2 * y * reciprocalPower (n + 1) x y) := by
  induction n with
  | zero =>
      intro x y hxy
      change deriv (fun t => (t + y) / (t - y)) x = _
      have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
      have hd0 := ((hasDerivAt_id x).add_const y).div
        ((hasDerivAt_id x).sub_const y) hsub
      change HasDerivAt (fun t : ℝ => (t + y) / (t - y))
          ((1 * (x - y) - (x + y) * 1) / (x - y) ^ 2) x at hd0
      have hcoef :
          (1 * (x - y) - (x + y) * 1) / (x - y) ^ 2 =
            -2 * y * reciprocalPower 1 x y := by
        norm_num [reciprocalPower] <;> ring
      have hd : HasDerivAt (fun t : ℝ => (t + y) / (t - y))
          (-2 * y * reciprocalPower 1 x y) x := by
        rw [← hcoef]
        exact hd0
      calc
        deriv (fun t => (t + y) / (t - y)) x =
            -2 * y * reciprocalPower 1 x y := hd.deriv
        _ = _ := by norm_num <;> ring
  | succ n ih =>
      intro x y hxy
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      rw [Function.iterate_succ_apply']
      let A : ℝ := (-1 : ℝ) ^ (n + 1) * (Nat.factorial (n + 1) : ℝ)
      have heq :
          (deriv^[n + 1]) (fun t => u t y) =ᶠ[nhds x]
            (fun z => A * (2 * y * reciprocalPower (n + 1) z y)) := by
        filter_upwards [eventually_ne_nhds hxy] with z hz
        simpa [A] using ih z y hz
      have hdR := hasDerivAt_reciprocalPower_x (n + 1) hxy
      have hd : HasDerivAt
          (fun z => A * (2 * y * reciprocalPower (n + 1) z y))
          (A * (2 * y *
            (-(((n + 1) + 1 : ℕ) : ℝ) *
              reciprocalPower ((n + 1) + 1) x y))) x := by
        convert (hasDerivAt_const x A).mul
          ((hasDerivAt_const x (2 * y)).mul hdR) using 1 <;>
            simp <;> ring
      calc
        deriv ((deriv^[n + 1]) (fun t => u t y)) x =
            deriv
              (fun z => A * (2 * y * reciprocalPower (n + 1) z y)) x :=
          heq.deriv_eq
        _ = A * (2 * y *
            (-(((n + 1) + 1 : ℕ) : ℝ) *
              reciprocalPower ((n + 1) + 1) x y)) := hd.deriv
        _ = _ := by
          simp [A, Nat.factorial_succ, pow_succ] <;> ring

private theorem partial_x_formula
    (m : ℕ) (hm : 1 ≤ m) (x y : ℝ) (hxy : x ≠ y) :
    partialXOrder m u x y =
      (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
        (2 * y / (x - y) ^ (m + 1)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
  change (deriv^[1 + n]) (fun t => u t y) x = _
  rw [show 1 + n = n + 1 by omega]
  rw [iter_deriv_x_u_succ n x y hxy]
  simpa [reciprocalPower, div_eq_mul_inv, mul_assoc]

private theorem iter_deriv_y_reciprocal
    (m n : ℕ) (x y : ℝ) (hxy : x ≠ y) :
    partialYOrder n (reciprocalPower m) x y =
      rising (m + 1) n * reciprocalPower (m + n) x y := by
  induction n generalizing y with
  | zero => simp [partialYOrder, rising]
  | succ n ih =>
      unfold partialYOrder
      rw [Function.iterate_succ_apply']
      have heq :
          (deriv^[n]) (fun t => reciprocalPower m x t) =ᶠ[nhds y]
            (fun z => rising (m + 1) n * reciprocalPower (m + n) x z) := by
        filter_upwards [eventually_ne_nhds hxy.symm] with z hz
        have hxz : x ≠ z := hz.symm
        simpa [partialYOrder] using ih z hxz
      have hdR := hasDerivAt_reciprocalPower_y (m + n) hxy
      have hd : HasDerivAt
          (fun z => rising (m + 1) n * reciprocalPower (m + n) x z)
          (rising (m + 1) n *
            (((m + n + 1 : ℕ) : ℝ) *
              reciprocalPower (m + n + 1) x y)) y := by
        convert (hasDerivAt_const y (rising (m + 1) n)).mul hdR using 1 <;>
          simp <;> ring
      calc
        deriv ((deriv^[n]) (fun t => reciprocalPower m x t)) y =
            deriv
              (fun z => rising (m + 1) n *
                reciprocalPower (m + n) x z) y := heq.deriv_eq
        _ = rising (m + 1) n *
            (((m + n + 1 : ℕ) : ℝ) *
              reciprocalPower (m + n + 1) x y) := hd.deriv
        _ = rising (m + 1) (n + 1) *
            reciprocalPower (m + (n + 1)) x y := by
          rw [rising_succ]
          have hcoef : m + 1 + n = m + n + 1 := by omega
          have hidx : m + (n + 1) = m + n + 1 := by omega
          rw [hcoef, hidx]
          push_cast
          ring

private theorem iter_deriv_y_weighted_succ
    (c : ℝ) (m n : ℕ) :
    ∀ x y : ℝ, x ≠ y →
      (deriv^[n + 1]) (fun t => c * t * reciprocalPower m x t) y =
        c * rising (m + 1) (n + 1) * y *
            reciprocalPower (m + n + 1) x y +
          c * ((n + 1 : ℕ) : ℝ) * rising (m + 1) n *
            reciprocalPower (m + n) x y := by
  induction n with
  | zero =>
      intro x y hxy
      change deriv (fun t => c * t * reciprocalPower m x t) y = _
      have hdR := hasDerivAt_reciprocalPower_y m hxy
      have hdLinear : HasDerivAt (fun t : ℝ => c * t) c y := by
        simpa using (hasDerivAt_const y c).mul (hasDerivAt_id y)
      have hd : HasDerivAt
          (fun t => c * t * reciprocalPower m x t)
          (c * reciprocalPower m x y +
            c * y * (((m + 1 : ℕ) : ℝ) *
              reciprocalPower (m + 1) x y)) y := by
        convert hdLinear.mul hdR using 1 <;> simp <;> ring
      calc
        deriv (fun t => c * t * reciprocalPower m x t) y =
            c * reciprocalPower m x y +
              c * y * (((m + 1 : ℕ) : ℝ) *
                reciprocalPower (m + 1) x y) := hd.deriv
        _ = _ := by
          simp [rising, Nat.add_assoc] <;> ring
  | succ n ih =>
      intro x y hxy
      rw [show Nat.succ n + 1 = (n + 1) + 1 by omega]
      rw [Function.iterate_succ_apply']
      have heq :
          (deriv^[n + 1]) (fun t => c * t * reciprocalPower m x t) =ᶠ[nhds y]
            (fun z =>
              c * rising (m + 1) (n + 1) * z *
                  reciprocalPower (m + n + 1) x z +
                c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n *
                  reciprocalPower (m + n) x z) := by
        filter_upwards [eventually_ne_nhds hxy.symm] with z hz
        exact ih x z hz.symm
      have hdR1 := hasDerivAt_reciprocalPower_y (m + n + 1) hxy
      have hdR0 := hasDerivAt_reciprocalPower_y (m + n) hxy
      have hdLinear1 : HasDerivAt
          (fun z : ℝ => (c * rising (m + 1) (n + 1)) * z)
          (c * rising (m + 1) (n + 1)) y := by
        simpa using (hasDerivAt_const y
          (c * rising (m + 1) (n + 1))).mul (hasDerivAt_id y)
      have hd1 : HasDerivAt
          (fun z => c * rising (m + 1) (n + 1) * z *
            reciprocalPower (m + n + 1) x z)
          (c * rising (m + 1) (n + 1) *
              reciprocalPower (m + n + 1) x y +
            c * rising (m + 1) (n + 1) * y *
              (((m + n + 1 + 1 : ℕ) : ℝ) *
                reciprocalPower (m + n + 1 + 1) x y)) y := by
        convert hdLinear1.mul hdR1 using 1 <;> simp <;> ring
      have hd2 : HasDerivAt
          (fun z =>
            c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n *
              reciprocalPower (m + n) x z)
          ((c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n) *
            (((m + n + 1 : ℕ) : ℝ) *
              reciprocalPower (m + n + 1) x y)) y := by
        convert (hasDerivAt_const y
          (c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n)).mul hdR0
            using 1 <;> simp <;> ring
      have hd : HasDerivAt
          (fun z =>
            c * rising (m + 1) (n + 1) * z *
                reciprocalPower (m + n + 1) x z +
              c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n *
                reciprocalPower (m + n) x z)
          ((c * rising (m + 1) (n + 1) *
                reciprocalPower (m + n + 1) x y +
              c * rising (m + 1) (n + 1) * y *
                (((m + n + 1 + 1 : ℕ) : ℝ) *
                  reciprocalPower (m + n + 1 + 1) x y)) +
            (c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n) *
              (((m + n + 1 : ℕ) : ℝ) *
                reciprocalPower (m + n + 1) x y)) y := by
        convert (hd1.add hd2) using 1 <;> simp <;> ring
      calc
        deriv
            ((deriv^[n + 1])
              (fun t => c * t * reciprocalPower m x t)) y =
            deriv
              (fun z =>
                c * rising (m + 1) (n + 1) * z *
                    reciprocalPower (m + n + 1) x z +
                  c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n *
                    reciprocalPower (m + n) x z) y := heq.deriv_eq
        _ = (c * rising (m + 1) (n + 1) *
                reciprocalPower (m + n + 1) x y +
              c * rising (m + 1) (n + 1) * y *
                (((m + n + 1 + 1 : ℕ) : ℝ) *
                  reciprocalPower (m + n + 1 + 1) x y)) +
            (c * (((n + 1 : ℕ) : ℝ)) * rising (m + 1) n) *
              (((m + n + 1 : ℕ) : ℝ) *
                reciprocalPower (m + n + 1) x y) := hd.deriv
        _ = _ := by
          simp [rising_succ, Nat.succ_eq_add_one, Nat.add_assoc] <;>
            push_cast <;> ring

private theorem iter_deriv_y_weighted
    (c : ℝ) (m n : ℕ) (x y : ℝ) (hxy : x ≠ y) :
    (deriv^[n]) (fun t => c * t * reciprocalPower m x t) y =
      c * (rising (m + 1) n * y * reciprocalPower (m + n) x y +
        (n : ℝ) * rising (m + 1) (n - 1) *
          reciprocalPower (m + (n - 1)) x y) := by
  cases n with
  | zero =>
      simp [rising] <;> ring
  | succ n =>
      rw [iter_deriv_y_weighted_succ c m n x y hxy]
      simp only [Nat.add_sub_cancel]
      ring

private theorem mixed_weighted_formula
    (m n : ℕ) (hm : 1 ≤ m) (x y : ℝ) (hxy : x ≠ y) :
    mixedOrder m n u x y =
      (2 * ((-1 : ℝ) ^ m * (Nat.factorial m : ℝ))) *
        (rising (m + 1) n * y * reciprocalPower (m + n) x y +
          (n : ℝ) * rising (m + 1) (n - 1) *
            reciprocalPower (m + (n - 1)) x y) := by
  unfold mixedOrder
  change (deriv^[n]) (fun b => partialXOrder m u x b) y = _
  let c : ℝ := 2 * ((-1 : ℝ) ^ m * (Nat.factorial m : ℝ))
  have hpoint : ∀ z : ℝ, z ≠ x →
      partialXOrder m u x z = c * z * reciprocalPower m x z := by
    intro z hzx
    rw [partial_x_formula m hm x z hzx.symm]
    simp [c, reciprocalPower]
    ring
  calc
    (deriv^[n]) (fun b => partialXOrder m u x b) y =
        (deriv^[n]) (fun b => c * b * reciprocalPower m x b) y :=
      iterate_deriv_congr_off n _ _ x y hpoint hxy.symm
    _ = c *
        (rising (m + 1) n * y * reciprocalPower (m + n) x y +
          (n : ℝ) * rising (m + 1) (n - 1) *
            reciprocalPower (m + (n - 1)) x y) :=
      iter_deriv_y_weighted c m n x y hxy
    _ = _ := by rfl

private theorem risingForm_eq_closedForm
    (m n : ℕ) (hm : 1 ≤ m) (x y : ℝ) (hxy : x ≠ y) :
    risingForm m n x y = closedForm m n x y := by
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hxy
  cases n with
  | zero =>
      obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := by
        exact ⟨m - 1, by omega⟩
      subst m
      simp [risingForm, closedForm, rising, Nat.factorial_succ,
        div_eq_mul_inv]
      ring
  | succ n =>
      unfold risingForm closedForm
      simp only [Nat.add_sub_cancel]
      have hfac1 := factorial_mul_rising m (n + 1)
      have hfac0 := factorial_mul_rising m n
      have hfm : (Nat.factorial m : ℝ) ≠ 0 := by positivity
      have hr1 : rising (m + 1) (n + 1) =
          (Nat.factorial (m + (n + 1)) : ℝ) /
            (Nat.factorial m : ℝ) := by
        apply (eq_div_iff hfm).2
        simpa [mul_comm] using hfac1
      have hr0 : rising (m + 1) n =
          (Nat.factorial (m + n) : ℝ) /
            (Nat.factorial m : ℝ) := by
        apply (eq_div_iff hfm).2
        simpa [mul_comm] using hfac0
      rw [hr1, hr0]
      have hadd : m + (n + 1) = m + n + 1 := by omega
      rw [hadd]
      simp only [Nat.add_sub_cancel]
      rw [Nat.factorial_succ]
      field_simp [hsub, hfm]
      push_cast
      ring

theorem gap1 :
    ∀ x y, x ≠ y →
      u x y = 1 + 2 * y / (x - y) := by
  intro x y hxy
  unfold u
  field_simp [sub_ne_zero.mpr hxy]
  <;> ring

theorem gap2 :
    ∀ m : ℕ, 1 ≤ m →
      ∀ x y, x ≠ y →
        partialXOrder m u x y =
          (-1 : ℝ) ^ m * (Nat.factorial m : ℝ) *
            (2 * y / (x - y) ^ (m + 1)) := by
  intro m hm x y hxy
  exact partial_x_formula m hm x y hxy

theorem gap3 :
    ∀ m n : ℕ, 1 ≤ m →
      ∀ x y, x ≠ y →
        mixedOrder m n u x y = leibnizForm m n x y := by
  intro m n hm x y hxy
  rw [mixed_weighted_formula m n hm x y hxy]
  unfold leibnizForm
  rw [iter_deriv_y_reciprocal m n x y hxy]
  rw [iter_deriv_y_reciprocal m (n - 1) x y hxy]
  simp [Nat.choose_one_right]
  ring

theorem gap4 :
    ∀ m n : ℕ, 1 ≤ m →
      ∀ x y, x ≠ y →
        mixedOrder m n u x y = risingForm m n x y := by
  intro m n hm x y hxy
  rw [mixed_weighted_formula m n hm x y hxy]
  cases n with
  | zero =>
      simpa [risingForm, reciprocalPower, rising, div_eq_mul_inv, mul_assoc]
  | succ n =>
      simpa [risingForm, reciprocalPower, div_eq_mul_inv, Nat.add_assoc,
        mul_assoc]

theorem gap5 :
    ∀ m n : ℕ, 1 ≤ m →
      ∀ x y, x ≠ y →
        mixedOrder m n u x y = closedForm m n x y := by
  intro m n hm x y hxy
  rw [gap4 m n hm x y hxy]
  exact risingForm_eq_closedForm m n hm x y hxy

end

end ProofGap.Exercise3263
