import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1637

noncomputable section

def domain : Set ℝ := Set.Ioi 0
def original (x : ℝ) : ℝ :=
  (Real.sqrt (2 * x) - Real.cbrt (3 * x)) ^ 2 / x
def powers (x : ℝ) : ℝ :=
  2 - 2 * Real.rpow 72 (1 / 6) * Real.rpow x (-(1 / 6)) +
    Real.cbrt 9 * Real.rpow x (-(1 / 3))
def primitive (x : ℝ) : ℝ :=
  2 * x - (12 / 5) * Real.rpow (72 * x ^ 5) (1 / 6) +
    (3 / 2) * Real.cbrt (9 * x ^ 2)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem pos_rpow_add (x a b : ℝ) (hx : 0 < x) :
    Real.rpow x (a + b) = Real.rpow x a * Real.rpow x b := by
  change x ^ (a + b) = x ^ a * x ^ b
  simp only [Real.rpow_def_of_pos hx, ← Real.exp_add]
  congr 1
  ring

private theorem mul_rpow_nonneg (x y p : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.rpow (x * y) p = Real.rpow x p * Real.rpow y p := by
  change (x * y) ^ p = x ^ p * y ^ p
  exact Real.mul_rpow hx hy

private theorem pow_rpow_pos (x p : ℝ) (n : ℕ) (hx : 0 < x) :
    Real.rpow (x ^ n) p = Real.rpow x ((n : ℝ) * p) := by
  change (x ^ n) ^ p = x ^ ((n : ℝ) * p)
  rw [Real.rpow_def_of_pos (pow_pos hx n), Real.rpow_def_of_pos hx]
  congr 1
  rw [Real.log_pow]
  ring

private theorem rpow_cross_constant :
    Real.rpow 2 (1 / 2) * Real.rpow 3 (1 / 3) =
      Real.rpow 72 (1 / 6) := by
  change (2 : ℝ) ^ (1 / 2 : ℝ) * (3 : ℝ) ^ (1 / 3 : ℝ) =
    (72 : ℝ) ^ (1 / 6 : ℝ)
  simp only [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3),
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 72), ← Real.exp_add]
  congr 1
  rw [show (72 : ℝ) = 2 ^ 3 * 3 ^ 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
  norm_num
  ring

private theorem original_eq_powers (x : ℝ) (hx : x ∈ domain) :
    original x = powers x := by
  have hx' : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hx'
  have h2 : (0 : ℝ) < 2 := by norm_num
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hsqrt : Real.sqrt (2 * x) =
      Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact mul_rpow_nonneg 2 x (1 / 2) h2.le hx'.le
  have hcbrt : Real.cbrt (3 * x) =
      Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3) := by
    unfold Real.cbrt
    exact mul_rpow_nonneg 3 x (1 / 3) h3.le hx'.le
  have h2half : Real.rpow 2 (1 / 2) * Real.rpow 2 (1 / 2) = 2 := by
    calc
      Real.rpow 2 (1 / 2) * Real.rpow 2 (1 / 2) =
          Real.rpow 2 ((1 / 2 : ℝ) + 1 / 2) :=
        (pos_rpow_add 2 (1 / 2) (1 / 2) h2).symm
      _ = 2 := by norm_num
  have hxhalf : Real.rpow x (1 / 2) * Real.rpow x (1 / 2) = x := by
    calc
      Real.rpow x (1 / 2) * Real.rpow x (1 / 2) =
          Real.rpow x ((1 / 2 : ℝ) + 1 / 2) :=
        (pos_rpow_add x (1 / 2) (1 / 2) hx').symm
      _ = x := by norm_num
  have h3third : Real.rpow 3 (1 / 3) * Real.rpow 3 (1 / 3) =
      Real.cbrt 9 := by
    calc
      Real.rpow 3 (1 / 3) * Real.rpow 3 (1 / 3) =
          Real.rpow 3 ((1 / 3 : ℝ) + 1 / 3) :=
        (pos_rpow_add 3 (1 / 3) (1 / 3) h3).symm
      _ = Real.rpow 3 (2 / 3) := by norm_num
      _ = Real.cbrt 9 := by
        unfold Real.cbrt
        rw [show (9 : ℝ) = 3 ^ 2 by norm_num,
          pow_rpow_pos 3 (1 / 3) 2 h3]
        norm_num
  have hxthird : Real.rpow x (1 / 3) * Real.rpow x (1 / 3) =
      Real.rpow x (-(1 / 3)) * x := by
    calc
      Real.rpow x (1 / 3) * Real.rpow x (1 / 3) =
          Real.rpow x ((1 / 3 : ℝ) + 1 / 3) :=
        (pos_rpow_add x (1 / 3) (1 / 3) hx').symm
      _ = Real.rpow x (-(1 / 3) + 1) := by norm_num
      _ = Real.rpow x (-(1 / 3)) * Real.rpow x 1 :=
        pos_rpow_add x (-(1 / 3)) 1 hx'
      _ = Real.rpow x (-(1 / 3)) * x := by norm_num
  have hxcross : Real.rpow x (1 / 2) * Real.rpow x (1 / 3) =
      Real.rpow x (-(1 / 6)) * x := by
    calc
      Real.rpow x (1 / 2) * Real.rpow x (1 / 3) =
          Real.rpow x ((1 / 2 : ℝ) + 1 / 3) :=
        (pos_rpow_add x (1 / 2) (1 / 3) hx').symm
      _ = Real.rpow x (-(1 / 6) + 1) := by norm_num
      _ = Real.rpow x (-(1 / 6)) * Real.rpow x 1 :=
        pos_rpow_add x (-(1 / 6)) 1 hx'
      _ = Real.rpow x (-(1 / 6)) * x := by norm_num
  have hsq :
      (Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2)) ^ 2 / x = 2 := by
    apply (div_eq_iff hx0).2
    calc
      (Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2)) ^ 2 =
          (Real.rpow 2 (1 / 2) * Real.rpow 2 (1 / 2)) *
            (Real.rpow x (1 / 2) * Real.rpow x (1 / 2)) := by ring
      _ = 2 * x := by rw [h2half, hxhalf]
  have hcubesq :
      (Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3)) ^ 2 / x =
        Real.cbrt 9 * Real.rpow x (-(1 / 3)) := by
    apply (div_eq_iff hx0).2
    calc
      (Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3)) ^ 2 =
          (Real.rpow 3 (1 / 3) * Real.rpow 3 (1 / 3)) *
            (Real.rpow x (1 / 3) * Real.rpow x (1 / 3)) := by ring
      _ = (Real.cbrt 9 * Real.rpow x (-(1 / 3))) * x := by
        rw [h3third, hxthird]
        ring
  have hcross :
      (Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2)) *
          (Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3)) / x =
        Real.rpow 72 (1 / 6) * Real.rpow x (-(1 / 6)) := by
    apply (div_eq_iff hx0).2
    calc
      (Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2)) *
          (Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3)) =
        (Real.rpow 2 (1 / 2) * Real.rpow 3 (1 / 3)) *
          (Real.rpow x (1 / 2) * Real.rpow x (1 / 3)) := by ring
      _ = (Real.rpow 2 (1 / 2) * Real.rpow 3 (1 / 3)) *
          (Real.rpow x (-(1 / 6)) * x) := by rw [hxcross]
      _ = (Real.rpow 72 (1 / 6) * Real.rpow x (-(1 / 6))) * x := by
        rw [rpow_cross_constant]
        ring
  unfold original powers
  rw [hsqrt, hcbrt]
  calc
    ((Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2) -
        Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3)) ^ 2) / x =
      (Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2)) ^ 2 / x -
        2 * ((Real.rpow 2 (1 / 2) * Real.rpow x (1 / 2)) *
          (Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3)) / x) +
        (Real.rpow 3 (1 / 3) * Real.rpow x (1 / 3)) ^ 2 / x := by ring
    _ = 2 - 2 * Real.rpow 72 (1 / 6) * Real.rpow x (-(1 / 6)) +
        Real.cbrt 9 * Real.rpow x (-(1 / 3)) := by
      rw [hsq, hcross, hcubesq]
      ring

private def canonicalPrimitive (x : ℝ) : ℝ :=
  2 * x - (12 / 5) * Real.rpow 72 (1 / 6) * Real.rpow x (5 / 6) +
    (3 / 2) * Real.cbrt 9 * Real.rpow x (2 / 3)

private theorem primitive_eq_canonicalPrimitive (x : ℝ) (hx : x ∈ domain) :
    primitive x = canonicalPrimitive x := by
  have hx' : 0 < x := hx
  have h72mul : Real.rpow (72 * x ^ 5) (1 / 6) =
      Real.rpow 72 (1 / 6) * Real.rpow (x ^ 5) (1 / 6) :=
    mul_rpow_nonneg 72 (x ^ 5) (1 / 6) (by norm_num)
      (le_of_lt (pow_pos hx' 5))
  have h72 : Real.rpow (72 * x ^ 5) (1 / 6) =
      Real.rpow 72 (1 / 6) * Real.rpow x (5 / 6) := by
    rw [h72mul, pow_rpow_pos x (1 / 6) 5 hx']
    norm_num
  have h9mul : Real.rpow (9 * x ^ 2) (1 / 3) =
      Real.rpow 9 (1 / 3) * Real.rpow (x ^ 2) (1 / 3) :=
    mul_rpow_nonneg 9 (x ^ 2) (1 / 3) (by norm_num)
      (le_of_lt (pow_pos hx' 2))
  have h9 : Real.cbrt (9 * x ^ 2) =
      Real.cbrt 9 * Real.rpow x (2 / 3) := by
    unfold Real.cbrt
    rw [h9mul, pow_rpow_pos x (1 / 3) 2 hx']
    norm_num
  unfold primitive canonicalPrimitive
  rw [h72, h9]
  ring

private theorem canonicalPrimitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt canonicalPrimitive (powers x) x := by
  have hx' : 0 < x := hx
  have hx0 : x ≠ 0 := ne_of_gt hx'
  have h56 : HasDerivAt (fun y : ℝ => Real.rpow y (5 / 6))
      ((5 / 6) * Real.rpow x ((5 / 6) - 1)) x :=
    Real.hasDerivAt_rpow_const (x := x) (p := (5 / 6 : ℝ)) (Or.inl hx0)
  have h23 : HasDerivAt (fun y : ℝ => Real.rpow y (2 / 3))
      ((2 / 3) * Real.rpow x ((2 / 3) - 1)) x :=
    Real.hasDerivAt_rpow_const (x := x) (p := (2 / 3 : ℝ)) (Or.inl hx0)
  unfold canonicalPrimitive powers
  convert (((hasDerivAt_id x).const_mul 2).sub
    (h56.const_mul ((12 / 5) * Real.rpow 72 (1 / 6)))).add
      (h23.const_mul ((3 / 2) * Real.cbrt 9)) using 1 <;>
    norm_num <;> ring

private theorem primitive_hasDerivAt (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (powers x) x := by
  have hev : primitive =ᶠ[nhds x] canonicalPrimitive := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
    exact primitive_eq_canonicalPrimitive y hy
  exact (canonicalPrimitive_hasDerivAt x hx).congr_of_eventuallyEq hev

theorem gap1 : AntiderivativesOn original = AntiderivativesOn powers := by
  ext F
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [← original_eq_powers x hx]
    exact hderiv x hx
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    rw [original_eq_powers x hx]
    exact hderiv x hx

theorem gap2 : AntiderivativesOn powers = PrimitiveFamily primitive := by
  ext F
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    let C : ℝ := F 1 - primitive 1
    refine ⟨C, ?_⟩
    intro x hx
    let b : ℝ := max x 1 + 1
    have hxb : x ∈ Set.Ioo (0 : ℝ) b := by
      constructor
      · exact hx
      · dsimp [b]
        have hle : x ≤ max x 1 := le_max_left _ _
        linarith
    have h1b : (1 : ℝ) ∈ Set.Ioo (0 : ℝ) b := by
      constructor
      · norm_num
      · dsimp [b]
        have hle : (1 : ℝ) ≤ max x 1 := le_max_right _ _
        linarith
    have hsubDiff : DifferentiableOn ℝ (fun y => F y - primitive y)
        (Set.Ioo (0 : ℝ) b) := by
      intro y hy
      have hyDomain : y ∈ domain := hy.1
      have hFy : DifferentiableWithinAt ℝ F (Set.Ioo (0 : ℝ) b) y :=
        (hFdiff y hyDomain).mono (by
          intro z hz
          exact hz.1)
      change DifferentiableWithinAt ℝ (F - primitive) (Set.Ioo (0 : ℝ) b) y
      exact hFy.sub
        (primitive_hasDerivAt y hyDomain).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ Set.Ioo (0 : ℝ) b,
        deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      have hyDomain : y ∈ domain := hy.1
      have hFd : DifferentiableAt ℝ F y :=
        (hFdiff y hyDomain).differentiableAt (isOpen_Ioi.mem_nhds hyDomain)
      have hsub := (hFd.hasDerivAt.sub (primitive_hasDerivAt y hyDomain)).deriv
      rw [hFderiv y hyDomain] at hsub
      simpa using hsub
    have hsame : F x - primitive x = F 1 - primitive 1 :=
      isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
        hsubDiff hzero hxb h1b
    dsimp [C]
    linarith
  · rintro ⟨C, hEq⟩
    have hlocal : ∀ x ∈ domain, HasDerivAt F (powers x) x := by
      intro x hx
      have hev : F =ᶠ[nhds x] (fun y => primitive y + C) := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact hEq y hy
      have hg : HasDerivAt (fun y => primitive y + C) (powers x) x :=
        (primitive_hasDerivAt x hx).add_const C
      exact hg.congr_of_eventuallyEq hev
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hlocal x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hlocal x hx).deriv

theorem gap3 : AntiderivativesOn original = PrimitiveFamily primitive := by
  exact gap1.trans gap2

end
end ProofGap.Exercise1637
