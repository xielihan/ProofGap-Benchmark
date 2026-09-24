import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1731

noncomputable section

def domain : Set ℝ := Set.Iio (1 / 3)
def u (x : ℝ) : ℝ := 1 - 3 * x
def original (x : ℝ) : ℝ := x / Real.cbrt (u x)
def substituted (x : ℝ) : ℝ :=
  -(1 / 3) * (Real.rpow (u x) (2 / 3) - Real.rpow (u x) (-(1 / 3)))
def powers (x : ℝ) : ℝ :=
  (1 / 3) * (Real.rpow (u x) (-(1 / 3)) - Real.rpow (u x) (2 / 3))
def primitive₁ (x : ℝ) : ℝ :=
  (1 / 15) * Real.rpow (u x) (5 / 3) -
    (1 / 6) * Real.rpow (u x) (2 / 3)
def primitive₂ (x : ℝ) : ℝ :=
  -((1 + 2 * x) / 10) * Real.rpow (u x) (2 / 3)
def AntiderivativesOn (g : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = g x}
def PrimitiveFamily (p : ℝ → ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C : ℝ, ∀ x ∈ domain, F x = p x + C}

private theorem domain_u_pos {x : ℝ} (hx : x ∈ domain) : 0 < u x := by
  change x < (1 : ℝ) / 3 at hx
  change 0 < 1 - 3 * x
  linarith

private theorem original_eq_powers {x : ℝ} (hx : x ∈ domain) :
    original x = powers x := by
  have hu : 0 < u x := domain_u_pos hx
  have hc : Real.cbrt (u x) = Real.rpow (u x) (1 / 3) := by
    simp [Real.cbrt]
  have hinv :
      (Real.rpow (u x) (1 / 3))⁻¹ = Real.rpow (u x) (-(1 / 3)) := by
    change ((u x) ^ (1 / 3 : ℝ))⁻¹ = (u x) ^ (-(1 / 3) : ℝ)
    exact (Real.rpow_neg hu.le (1 / 3)).symm
  have hmul :
      Real.rpow (u x) (2 / 3) =
        u x * Real.rpow (u x) (-(1 / 3)) := by
    change (u x) ^ (2 / 3 : ℝ) =
      u x * (u x) ^ (-(1 / 3) : ℝ)
    calc
      (u x) ^ (2 / 3 : ℝ) =
          (u x) ^ (1 + (-(1 / 3)) : ℝ) := by norm_num
      _ = (u x) ^ (1 : ℝ) * (u x) ^ (-(1 / 3) : ℝ) := by
        exact Real.rpow_add hu (1 : ℝ) (-(1 / 3) : ℝ)
      _ = u x * (u x) ^ (-(1 / 3) : ℝ) := by
        rw [Real.rpow_one]
  rw [original, powers, hc, div_eq_mul_inv, hinv, hmul]
  unfold u
  ring

private theorem substituted_eq_powers : substituted = powers := by
  funext x
  unfold substituted powers
  ring

private theorem primitive₁_hasDerivAt {x : ℝ} (hx : x ∈ domain) :
    HasDerivAt primitive₁ (powers x) x := by
  have hu : 0 < u x := domain_u_pos hx
  have hthree : HasDerivAt (fun y : ℝ => 3 * y) 3 x := by
    simpa using
      ((hasDerivAt_const x (3 : ℝ)).mul (hasDerivAt_id x))
  have huDeriv : HasDerivAt u (-3) x := by
    simpa [u] using
      ((hasDerivAt_const x (1 : ℝ)).sub hthree)
  have hpow (a : ℝ) :
      HasDerivAt (fun y : ℝ => Real.rpow (u y) a)
        (a * Real.rpow (u x) (a - 1) * (-3)) x := by
    change HasDerivAt (fun y : ℝ => (u y) ^ a)
      (a * (u x) ^ (a - 1) * (-3)) x
    have hout :
        HasDerivAt (fun z : ℝ => z ^ a)
          (a * (u x) ^ (a - 1)) (u x) := by
      exact Real.hasDerivAt_rpow_const (p := a) (Or.inl hu.ne')
    exact hout.comp x huDeriv
  convert
    ((hpow (5 / 3)).const_mul (1 / 15)).sub
      ((hpow (2 / 3)).const_mul (1 / 6)) using 1 <;>
    norm_num [primitive₁, powers] <;> ring

private theorem primitive₁_eq_primitive₂ {x : ℝ} (hx : x ∈ domain) :
    primitive₁ x = primitive₂ x := by
  have hu : 0 < u x := domain_u_pos hx
  have hpow :
      Real.rpow (u x) (5 / 3) = u x * Real.rpow (u x) (2 / 3) := by
    change (u x) ^ (5 / 3 : ℝ) =
      u x * (u x) ^ (2 / 3 : ℝ)
    calc
      (u x) ^ (5 / 3 : ℝ) =
          (u x) ^ (1 + 2 / 3 : ℝ) := by norm_num
      _ = (u x) ^ (1 : ℝ) * (u x) ^ (2 / 3 : ℝ) := by
        exact Real.rpow_add hu (1 : ℝ) (2 / 3 : ℝ)
      _ = u x * (u x) ^ (2 / 3 : ℝ) := by
        rw [Real.rpow_one]
  rw [primitive₁, primitive₂, hpow]
  unfold u
  ring

theorem gap1 : AntiderivativesOn original = AntiderivativesOn substituted := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = original x) ↔
      (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = substituted x)
  constructor
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hderiv x hx).trans
      ((original_eq_powers hx).trans (congrFun substituted_eq_powers x).symm)
  · rintro ⟨hF, hderiv⟩
    refine ⟨hF, ?_⟩
    intro x hx
    exact (hderiv x hx).trans
      ((congrFun substituted_eq_powers x).trans (original_eq_powers hx).symm)

theorem gap2 : AntiderivativesOn substituted = AntiderivativesOn powers := by
  rw [substituted_eq_powers]

theorem gap3 : AntiderivativesOn original = AntiderivativesOn powers := by
  calc
    AntiderivativesOn original = AntiderivativesOn substituted := gap1
    _ = AntiderivativesOn powers := gap2

theorem gap4 : AntiderivativesOn original = PrimitiveFamily primitive₁ := by
  apply Set.ext
  intro F
  change
    (DifferentiableOn ℝ F domain ∧ ∀ x ∈ domain, deriv F x = original x) ↔
      ∃ C : ℝ, ∀ x ∈ domain, F x = primitive₁ x + C
  have hopen : IsOpen domain := by
    simpa [domain] using (isOpen_Iio : IsOpen (Set.Iio ((1 : ℝ) / 3)))
  have hzero : (0 : ℝ) ∈ domain := by
    norm_num [domain]
  constructor
  · rintro ⟨hFdiff, hFderiv⟩
    have hpDiff : DifferentiableOn ℝ primitive₁ domain := by
      intro x hx
      exact (primitive₁_hasDerivAt hx).differentiableAt.differentiableWithinAt
    have hqDiff :
        DifferentiableOn ℝ (fun y => F y - primitive₁ y) domain :=
      hFdiff.sub hpDiff
    have hqDeriv :
        ∀ x ∈ domain, deriv (fun y => F y - primitive₁ y) x = 0 := by
      intro x hx
      have hFat : DifferentiableAt ℝ F x :=
        (hFdiff x hx).differentiableAt (hopen.mem_nhds hx)
      have hd := hFat.hasDerivAt.sub (primitive₁_hasDerivAt hx)
      have hdval := hd.deriv
      rw [hFderiv x hx, original_eq_powers hx] at hdval
      simpa using hdval
    have hqDiff' :
        DifferentiableOn ℝ (fun y => F y - primitive₁ y)
          (Set.Iio ((1 : ℝ) / 3)) := by
      simpa [domain] using hqDiff
    have hqDeriv' :
        ∀ x ∈ Set.Iio ((1 : ℝ) / 3),
          deriv (fun y => F y - primitive₁ y) x = 0 := by
      simpa [domain] using hqDeriv
    refine ⟨F 0 - primitive₁ 0, ?_⟩
    intro x hx
    have hx' : x ∈ Set.Iio ((1 : ℝ) / 3) := by
      simpa [domain] using hx
    have hzero' : (0 : ℝ) ∈ Set.Iio ((1 : ℝ) / 3) := by
      norm_num
    have hxconst : F x - primitive₁ x = F 0 - primitive₁ 0 := by
      exact
        isOpen_Iio.is_const_of_deriv_eq_zero
          ((convex_Iio ((1 : ℝ) / 3) :
            Convex ℝ (Set.Iio ((1 : ℝ) / 3))).isPreconnected)
          hqDiff' hqDeriv' hx' hzero'
    linarith
  · rintro ⟨C, hFC⟩
    have hHas : ∀ x ∈ domain, HasDerivAt F (original x) x := by
      intro x hx
      have heq :
          Filter.EventuallyEq (nhds x) F (fun y => C + primitive₁ y) := by
        filter_upwards [hopen.mem_nhds hx] with y hy
        simpa [add_comm] using hFC y hy
      have hFpow : HasDerivAt F (powers x) x :=
        ((primitive₁_hasDerivAt hx).const_add C).congr_of_eventuallyEq heq
      rw [← original_eq_powers hx] at hFpow
      exact hFpow
    refine ⟨?_, ?_⟩
    · intro x hx
      exact (hHas x hx).differentiableAt.differentiableWithinAt
    · intro x hx
      exact (hHas x hx).deriv

theorem gap5 : PrimitiveFamily primitive₁ = PrimitiveFamily primitive₂ := by
  apply Set.ext
  intro F
  change
    (∃ C : ℝ, ∀ x ∈ domain, F x = primitive₁ x + C) ↔
      ∃ C : ℝ, ∀ x ∈ domain, F x = primitive₂ x + C
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [← primitive₁_eq_primitive₂ hx]
    exact hC x hx
  · rintro ⟨C, hC⟩
    refine ⟨C, ?_⟩
    intro x hx
    rw [primitive₁_eq_primitive₂ hx]
    exact hC x hx

theorem gap6 : AntiderivativesOn original = PrimitiveFamily primitive₂ := by
  calc
    AntiderivativesOn original = PrimitiveFamily primitive₁ := gap4
    _ = PrimitiveFamily primitive₂ := gap5

end
end ProofGap.Exercise1731
