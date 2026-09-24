import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import ProofGapLean.Prelude.Discrete
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace ProofGap.Exercise1160

open scoped BigOperators

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := (1 + x) / Real.sqrt (1 - x)
def linear (x : ℝ) : ℝ := 1 + x
def rootInv (x : ℝ) : ℝ := (Real.sqrt (1 - x))⁻¹
def oddDF (n : ℕ) : ℕ := ∏ k ∈ Finset.range n, (2 * k + 1)

def leibniz100 (x : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 101,
    (Nat.choose 100 i : ℝ) * nthDeriv i linear x *
      nthDeriv (100 - i) rootInv x

def expanded100 (x : ℝ) : ℝ :=
  (1 + x) * (oddDF 100 : ℝ) / 2 ^ 100 *
      Real.rpow (1 - x) (-201 / 2 : ℝ) +
    100 * (oddDF 99 : ℝ) / 2 ^ 99 *
      Real.rpow (1 - x) (-199 / 2 : ℝ)

def final100 (x : ℝ) : ℝ :=
  (oddDF 99 : ℝ) * (399 - x) /
    (2 ^ 100 * (1 - x) ^ 100 * Real.sqrt (1 - x))

private theorem hasDerivAt_one_sub_rpow (p x : ℝ) (hx : x < 1) :
    HasDerivAt (fun z : ℝ => Real.rpow (1 - z) p)
      (-p * Real.rpow (1 - x) (p - 1)) x := by
  have ht : 0 < 1 - x := sub_pos.mpr hx
  have hlin : HasDerivAt (fun z : ℝ => 1 - z) (-1) x := by
    simpa using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub (hasDerivAt_id x)
  have hr : HasDerivAt (fun u : ℝ => Real.rpow u p)
      (p * Real.rpow (1 - x) (p - 1)) (1 - x) := by
    simpa using
      (Real.hasDerivAt_rpow_const (p := p) (Or.inl (ne_of_gt ht)))
  simpa [Function.comp_def] using hr.comp x hlin

private theorem rootInv_value (n : ℕ) (x : ℝ) (hx : x < 1) :
    nthDeriv n rootInv x =
      (oddDF n : ℝ) / 2 ^ n *
        Real.rpow (1 - x) (-(2 * (n : ℝ) + 1) / 2) := by
  induction n generalizing x with
  | zero =>
      have ht : 0 ≤ 1 - x := (sub_pos.mpr hx).le
      simp only [nthDeriv]
      unfold rootInv
      rw [Real.sqrt_eq_rpow]
      norm_num [oddDF]
      symm
      change (1 - x) ^ (-(1 / 2 : ℝ)) =
        ((1 - x) ^ (1 / 2 : ℝ))⁻¹
      exact Real.rpow_neg ht (1 / 2 : ℝ)
  | succ n ih =>
      let p : ℝ := -(2 * (n : ℝ) + 1) / 2
      let c : ℝ := (oddDF n : ℝ) / 2 ^ n
      have heq : nthDeriv n rootInv =ᶠ[nhds x]
          (fun z : ℝ => c * Real.rpow (1 - z) p) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with z hz
        simpa [c, p] using ih z hz
      have hd : HasDerivAt (fun z : ℝ => c * Real.rpow (1 - z) p)
          (c * (-p * Real.rpow (1 - x) (p - 1))) x := by
        simpa using
          (hasDerivAt_const (x := x) (c := c)).mul
            (hasDerivAt_one_sub_rpow p x hx)
      have hp : p - 1 = -(2 * ((n + 1 : ℕ) : ℝ) + 1) / 2 := by
        simp [p, Nat.cast_add]
        ring
      have hodd : oddDF (n + 1) = oddDF n * (2 * n + 1) := by
        simpa [oddDF] using
          (Finset.prod_range_succ (f := fun k : ℕ => 2 * k + 1) n)
      change deriv (nthDeriv n rootInv) x =
        (oddDF (n + 1) : ℝ) / 2 ^ (n + 1) *
          Real.rpow (1 - x)
            (-(2 * ((n + 1 : ℕ) : ℝ) + 1) / 2)
      rw [heq.deriv_eq, hd.deriv, hp, hodd, Nat.cast_mul, pow_succ]
      simp [c, p, Nat.cast_add, Nat.cast_mul]
      ring_nf

private theorem rootInv_hasDerivAt (n : ℕ) (x : ℝ) (hx : x < 1) :
    HasDerivAt (nthDeriv n rootInv) (nthDeriv (n + 1) rootInv x) x := by
  let p : ℝ := -(2 * (n : ℝ) + 1) / 2
  let c : ℝ := (oddDF n : ℝ) / 2 ^ n
  have heq : nthDeriv n rootInv =ᶠ[nhds x]
      (fun z : ℝ => c * Real.rpow (1 - z) p) := by
    filter_upwards [isOpen_Iio.mem_nhds hx] with z hz
    simpa [c, p] using rootInv_value n z hz
  have hd : HasDerivAt (fun z : ℝ => c * Real.rpow (1 - z) p)
      (c * (-p * Real.rpow (1 - x) (p - 1))) x := by
    simpa using
      (hasDerivAt_const (x := x) (c := c)).mul
        (hasDerivAt_one_sub_rpow p x hx)
  have hp : p - 1 = -(2 * ((n + 1 : ℕ) : ℝ) + 1) / 2 := by
    simp [p, Nat.cast_add]
    ring
  have hodd : oddDF (n + 1) = oddDF n * (2 * n + 1) := by
    simpa [oddDF] using
      (Finset.prod_range_succ (f := fun k : ℕ => 2 * k + 1) n)
  rw [rootInv_value (n + 1) x hx, hodd, Nat.cast_mul, pow_succ]
  convert hd.congr_of_eventuallyEq heq using 1
  simp [c, p, Nat.cast_add, Nat.cast_mul]
  ring_nf

private theorem y_nth_value (n : ℕ) (x : ℝ) (hx : x < 1) :
    nthDeriv n y x =
      (1 + x) * nthDeriv n rootInv x +
        (n : ℝ) * nthDeriv (n - 1) rootInv x := by
  induction n generalizing x with
  | zero =>
      simp [nthDeriv, y, rootInv, div_eq_mul_inv]
  | succ n ih =>
      have heq : nthDeriv n y =ᶠ[nhds x]
          (fun z : ℝ =>
            (1 + z) * nthDeriv n rootInv z +
              (n : ℝ) * nthDeriv (n - 1) rootInv z) := by
        filter_upwards [isOpen_Iio.mem_nhds hx] with z hz
        exact ih z hz
      have hlin : HasDerivAt (fun z : ℝ => 1 + z) 1 x := by
        simpa using
          (hasDerivAt_const (x := x) (c := (1 : ℝ))).add (hasDerivAt_id x)
      have hfirst :
          HasDerivAt (fun z : ℝ => (1 + z) * nthDeriv n rootInv z)
            (nthDeriv n rootInv x +
              (1 + x) * nthDeriv (n + 1) rootInv x) x := by
        simpa [add_comm, add_left_comm, add_assoc] using
          hlin.mul (rootInv_hasDerivAt n x hx)
      have hsecond :
          HasDerivAt
            (fun z : ℝ => (n : ℝ) * nthDeriv (n - 1) rootInv z)
            ((n : ℝ) * nthDeriv n rootInv x) x := by
        cases n with
        | zero =>
            simpa using hasDerivAt_const (x := x) (c := (0 : ℝ))
        | succ m =>
            simpa using
              (rootInv_hasDerivAt m x hx).const_mul ((m + 1 : ℕ) : ℝ)
      change deriv (nthDeriv n y) x =
        (1 + x) * nthDeriv (n + 1) rootInv x +
          ((n + 1 : ℕ) : ℝ) * nthDeriv (n + 1 - 1) rootInv x
      rw [heq.deriv_eq]
      calc
        deriv (fun z : ℝ =>
            (1 + z) * nthDeriv n rootInv z +
              (n : ℝ) * nthDeriv (n - 1) rootInv z) x =
            (nthDeriv n rootInv x +
                (1 + x) * nthDeriv (n + 1) rootInv x) +
              (n : ℝ) * nthDeriv n rootInv x :=
          (hfirst.add hsecond).deriv
        _ = (1 + x) * nthDeriv (n + 1) rootInv x +
            ((n + 1 : ℕ) : ℝ) * nthDeriv (n + 1 - 1) rootInv x := by
          simp [Nat.cast_add]
          ring

private theorem linear_deriv : deriv linear = fun _ : ℝ => 1 := by
  funext z
  have h : HasDerivAt linear 1 z := by
    simpa [linear] using
      (hasDerivAt_const (x := z) (c := (1 : ℝ))).add (hasDerivAt_id z)
  exact h.deriv

private theorem linear_high_deriv (n : ℕ) :
    nthDeriv (n + 2) linear = fun _ : ℝ => 0 := by
  induction n with
  | zero =>
      norm_num
      simp only [nthDeriv]
      rw [linear_deriv]
      funext z
      simp
  | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, nthDeriv, ih]
      funext z
      simp

private theorem leibniz_value (x : ℝ) :
    leibniz100 x =
      (1 + x) * nthDeriv 100 rootInv x +
        100 * nthDeriv 99 rootInv x := by
  classical
  have hterm (i : ℕ) :
      (Nat.choose 100 i : ℝ) * nthDeriv i linear x *
          nthDeriv (100 - i) rootInv x =
        (if i = 0 then (1 + x) * nthDeriv 100 rootInv x else 0) +
          (if i = 1 then 100 * nthDeriv 99 rootInv x else 0) := by
    cases i with
    | zero =>
        norm_num [nthDeriv, linear]
    | succ i =>
        cases i with
        | zero =>
            have hd : nthDeriv 1 linear x = 1 := by
              simp only [nthDeriv]
              rw [linear_deriv]
            rw [hd]
            norm_num
        | succ i =>
            have hz : nthDeriv (Nat.succ (Nat.succ i)) linear x = 0 := by
              simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                congrFun (linear_high_deriv i) x
            have hi0 : Nat.succ (Nat.succ i) ≠ 0 := by omega
            have hi1 : Nat.succ (Nat.succ i) ≠ 1 := by omega
            rw [hz, if_neg hi0, if_neg hi1]
            ring
  unfold leibniz100
  calc
    (∑ i ∈ Finset.range 101,
        (Nat.choose 100 i : ℝ) * nthDeriv i linear x *
          nthDeriv (100 - i) rootInv x) =
        ∑ i ∈ Finset.range 101,
          ((if i = 0 then (1 + x) * nthDeriv 100 rootInv x else 0) +
            (if i = 1 then 100 * nthDeriv 99 rootInv x else 0)) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact hterm i
    _ = (1 + x) * nthDeriv 100 rootInv x +
          100 * nthDeriv 99 rootInv x := by
            rw [Finset.sum_add_distrib]
            set_option maxRecDepth 4096 in
              simp

theorem gap1 (x : ℝ) (hx : x < 1) :
    y x = (1 + x) * Real.rpow (1 - x) (-1 / 2 : ℝ) := by
  unfold y
  rw [div_eq_mul_inv, Real.sqrt_eq_rpow]
  have ht : 0 ≤ 1 - x := (sub_pos.mpr hx).le
  rw [← Real.rpow_neg ht (1 / 2 : ℝ)]
  norm_num

theorem gap2 (x : ℝ) (hx : x < 1) :
    nthDeriv 100 y x = leibniz100 x := by
  rw [y_nth_value 100 x hx, leibniz_value x]
  norm_num

theorem gap3 (x : ℝ) (hx : x < 1) :
    leibniz100 x =
      (1 + x) * nthDeriv 100 rootInv x +
        100 * nthDeriv 99 rootInv x := by
  exact leibniz_value x

theorem gap4 (x : ℝ) (hx : x < 1) :
    nthDeriv 100 y x =
      (1 + x) * nthDeriv 100 rootInv x +
        100 * nthDeriv 99 rootInv x := by
  simpa using y_nth_value 100 x hx

theorem gap5 (x : ℝ) (hx : x < 1) :
    nthDeriv 100 y x = expanded100 x := by
  rw [y_nth_value 100 x hx, rootInv_value 100 x hx,
    rootInv_value 99 x hx]
  norm_num [expanded100]
  ring

theorem gap6 (x : ℝ) (hx : x < 1) :
    nthDeriv 100 y x = final100 x := by
  rw [gap5 x hx]
  let t : ℝ := 1 - x
  have ht : 0 < t := sub_pos.mpr hx
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.2 ht
  have hs0 : Real.sqrt t ≠ 0 := ne_of_gt hs
  have hnat100 : Real.rpow t (100 : ℝ) = t ^ (100 : ℕ) := by
    simpa only using (Real.rpow_natCast t 100)
  have hnat99 : Real.rpow t (99 : ℝ) = t ^ (99 : ℕ) := by
    simpa only using (Real.rpow_natCast t 99)
  have hhalf : Real.rpow t (1 / 2 : ℝ) = Real.sqrt t := by
    exact (Real.sqrt_eq_rpow t).symm
  have h201 : Real.rpow t (-201 / 2 : ℝ) =
      (t ^ 100 * Real.sqrt t)⁻¹ := by
    calc
      Real.rpow t (-201 / 2 : ℝ) =
          Real.rpow t (-(100 + 1 / 2 : ℝ)) := by norm_num
      _ = (Real.rpow t (100 + 1 / 2 : ℝ))⁻¹ := by
        change t ^ (-(100 + 1 / 2 : ℝ)) =
          (t ^ (100 + 1 / 2 : ℝ))⁻¹
        rw [Real.rpow_neg ht.le]
      _ = (Real.rpow t (100 : ℝ) * Real.rpow t (1 / 2 : ℝ))⁻¹ := by
        change (t ^ (100 + 1 / 2 : ℝ))⁻¹ =
          (t ^ (100 : ℝ) * t ^ (1 / 2 : ℝ))⁻¹
        rw [Real.rpow_add ht]
      _ = (t ^ 100 * Real.sqrt t)⁻¹ := by
        apply congrArg (fun u : ℝ => u⁻¹)
        exact congrArg₂ (fun a b : ℝ => a * b) hnat100 hhalf
  have h199 : Real.rpow t (-199 / 2 : ℝ) =
      (t ^ 99 * Real.sqrt t)⁻¹ := by
    calc
      Real.rpow t (-199 / 2 : ℝ) =
          Real.rpow t (-(99 + 1 / 2 : ℝ)) := by norm_num
      _ = (Real.rpow t (99 + 1 / 2 : ℝ))⁻¹ := by
        change t ^ (-(99 + 1 / 2 : ℝ)) =
          (t ^ (99 + 1 / 2 : ℝ))⁻¹
        rw [Real.rpow_neg ht.le]
      _ = (Real.rpow t (99 : ℝ) * Real.rpow t (1 / 2 : ℝ))⁻¹ := by
        change (t ^ (99 + 1 / 2 : ℝ))⁻¹ =
          (t ^ (99 : ℝ) * t ^ (1 / 2 : ℝ))⁻¹
        rw [Real.rpow_add ht]
      _ = (t ^ 99 * Real.sqrt t)⁻¹ := by
        apply congrArg (fun u : ℝ => u⁻¹)
        exact congrArg₂ (fun a b : ℝ => a * b) hnat99 hhalf
  have hoddNat : oddDF 100 = oddDF 99 * 199 := by
    simpa [oddDF] using
      (Finset.prod_range_succ (f := fun k : ℕ => 2 * k + 1) 99)
  have hodd : (oddDF 100 : ℝ) = (oddDF 99 : ℝ) * 199 := by
    exact_mod_cast hoddNat
  change
    (1 + x) * (oddDF 100 : ℝ) / 2 ^ 100 *
          Real.rpow t (-201 / 2 : ℝ) +
        100 * (oddDF 99 : ℝ) / 2 ^ 99 *
          Real.rpow t (-199 / 2 : ℝ) =
      (oddDF 99 : ℝ) * (399 - x) /
        (2 ^ 100 * t ^ 100 * Real.sqrt t)
  rw [h201, h199, hodd]
  field_simp [ht0, hs0]
  ring

end

end ProofGap.Exercise1160
