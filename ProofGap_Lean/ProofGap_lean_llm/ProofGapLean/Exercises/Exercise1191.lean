import ProofGapLean.Prelude.Elementary
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1191

noncomputable section

open scoped BigOperators

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ :=
  (deriv^[n]) f

def y (x : ℝ) : ℝ := 1 / Real.sqrt (1 - 2 * x)

def oddDoubleFactorial (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (2 * k + 1 : ℕ)

def rawClosed (n : ℕ) (x : ℝ) : ℝ :=
  (∏ k ∈ Finset.range n, (-((2 * k + 1 : ℝ) / 2))) *
    (-2 : ℝ) ^ n *
    Real.rpow (1 - 2 * x) (-((2 * n + 1 : ℝ) / 2))

def compactClosed (n : ℕ) (x : ℝ) : ℝ :=
  oddDoubleFactorial n /
    Real.rpow (1 - 2 * x) ((n : ℝ) + 1 / 2)

private theorem rpow_neg_eq_inv {a p : ℝ} (ha : 0 < a) :
    Real.rpow a (-p) = (Real.rpow a p)⁻¹ := by
  change a ^ (-p) = (a ^ p)⁻¹
  rw [Real.rpow_neg ha.le]

private theorem one_div_sqrt_eq_rpow_neg_half {a : ℝ} (ha : 0 < a) :
    1 / Real.sqrt a = Real.rpow a (-(1 / 2 : ℝ)) := by
  rw [Real.sqrt_eq_rpow]
  simpa [div_eq_mul_inv] using
    (rpow_neg_eq_inv (a := a) (p := (1 / 2 : ℝ)) ha).symm

private theorem hasDerivAt_rawClosed (n : ℕ) (x : ℝ)
    (hx : x < 1 / 2) :
    HasDerivAt (rawClosed n) (rawClosed (n + 1) x) x := by
  have hbase : 0 < 1 - 2 * x := by
    linarith
  let p : ℝ := -((2 * n + 1 : ℝ) / 2)
  let c : ℝ :=
    (∏ k ∈ Finset.range n, (-((2 * k + 1 : ℝ) / 2))) *
      (-2 : ℝ) ^ n
  have hlinear : HasDerivAt (fun t : ℝ => 1 - 2 * t) (-2) x := by
    simpa using
      (hasDerivAt_const (x := x) (c := (1 : ℝ))).sub
        ((hasDerivAt_id x).const_mul 2)
  have hout :
      HasDerivAt (fun z : ℝ => Real.rpow z p)
        (p * Real.rpow (1 - 2 * x) (p - 1)) (1 - 2 * x) := by
    first
    | exact Real.hasDerivAt_rpow_const hbase p
    | exact Real.hasDerivAt_rpow_const hbase
    | exact Real.hasDerivAt_rpow_const hbase.ne' p
    | exact Real.hasDerivAt_rpow_const hbase.ne'
    | exact Real.hasDerivAt_rpow_const (Or.inl hbase.ne')
  have hpow :
      HasDerivAt (fun t : ℝ => Real.rpow (1 - 2 * t) p)
        ((p * Real.rpow (1 - 2 * x) (p - 1)) * (-2)) x := by
    simpa only [Function.comp_apply] using hout.comp x hlinear
  have hp :
      p - 1 = -((2 * ((n + 1 : ℕ) : ℝ) + 1) / 2) := by
    dsimp [p]
    norm_num [Nat.cast_add]
    ring
  have hval :
      c * ((p * Real.rpow (1 - 2 * x) (p - 1)) * (-2)) =
        rawClosed (n + 1) x := by
    rw [hp]
    simp only [rawClosed, Finset.prod_range_succ, pow_succ]
    dsimp [c, p]
    ring
  rw [← hval]
  simpa only [rawClosed, c, p] using hpow.const_mul c

private theorem iterDeriv_eq_raw (n : ℕ) (x : ℝ) (hx : x < 1 / 2) :
    iterDeriv n y x = rawClosed n x := by
  induction n generalizing x with
  | zero =>
      have hbase : 0 < 1 - 2 * x := by
        linarith
      simpa [iterDeriv, y, rawClosed] using
        one_div_sqrt_eq_rpow_neg_half hbase
  | succ n ih =>
      have hlocal : iterDeriv n y =ᶠ[nhds x] rawClosed n := by
        filter_upwards [Iio_mem_nhds hx] with t ht
        exact ih t ht
      simp only [iterDeriv, Function.iterate_succ_apply']
      calc
        deriv ((deriv^[n]) y) x = deriv (rawClosed n) x := hlocal.deriv_eq
        _ = rawClosed (n + 1) x := (hasDerivAt_rawClosed n x hx).deriv

private theorem rawCoefficient_eq (n : ℕ) :
    (∏ k ∈ Finset.range n, (-((2 * k + 1 : ℝ) / 2))) *
        (-2 : ℝ) ^ n =
      oddDoubleFactorial n := by
  induction n with
  | zero =>
      simp [oddDoubleFactorial]
  | succ n ih =>
      calc
        (∏ k ∈ Finset.range (n + 1), (-((2 * k + 1 : ℝ) / 2))) *
              (-2 : ℝ) ^ (n + 1) =
            ((∏ k ∈ Finset.range n, (-((2 * k + 1 : ℝ) / 2))) *
                (-2 : ℝ) ^ n) * (2 * (n : ℝ) + 1) := by
          rw [Finset.prod_range_succ, pow_succ]
          ring
        _ = oddDoubleFactorial n * (2 * (n : ℝ) + 1) := by
          rw [ih]
        _ = oddDoubleFactorial (n + 1) := by
          simp [oddDoubleFactorial, Finset.prod_range_succ, Nat.cast_add,
            Nat.cast_mul]

theorem gap1 (n : ℕ) (x : ℝ) (hx : x < 1 / 2) :
    iterDeriv n y x = rawClosed n x := by
  exact iterDeriv_eq_raw n x hx

theorem gap2 (n : ℕ) (x : ℝ) (hx : x < 1 / 2) :
    rawClosed n x = compactClosed n x := by
  have hbase : 0 < 1 - 2 * x := by
    linarith
  have hq :
      -((2 * n + 1 : ℝ) / 2) = -((n : ℝ) + 1 / 2) := by
    norm_num [Nat.cast_add]
    ring
  simp only [rawClosed, compactClosed]
  rw [rawCoefficient_eq n, hq,
    rpow_neg_eq_inv (a := 1 - 2 * x) (p := (n : ℝ) + 1 / 2) hbase]
  simp [div_eq_mul_inv]

theorem gap3 (n : ℕ) (x : ℝ) (hx : x < 1 / 2) :
    iterDeriv n y x = compactClosed n x := by
  exact (gap1 n x hx).trans (gap2 n x hx)

end

end ProofGap.Exercise1191
