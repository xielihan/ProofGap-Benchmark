import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.MeanValue

namespace ProofGap.Exercise1686

noncomputable section

def inner (x : ℝ) : ℝ := 8 * x ^ 3 + 27
def integrand (x : ℝ) : ℝ := x ^ 2 / (Real.cbrt (inner x)) ^ 2
def primitive (x : ℝ) : ℝ := (1 / 8 : ℝ) * Real.cbrt (inner x)
def domain : Set ℝ := {x | 0 < inner x}

def IsAntiderivativeOn (F f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, HasDerivAt F (f x) x
def Family (f : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | IsAntiderivativeOn F f s}
def Translates (P : ℝ → ℝ) (s : Set ℝ) : Set (ℝ → ℝ) :=
  {F | ∃ C, ∀ x ∈ s, F x = P x + C}

private theorem inner_hasDerivAt (x : ℝ) :
    HasDerivAt inner (24 * x ^ 2) x := by
  unfold inner
  convert (((hasDerivAt_id x).pow 3).const_mul (8 : ℝ)).add_const (27 : ℝ) using 1 <;>
    norm_num <;> ring

private theorem cbrt_cubed_of_nonneg (x : ℝ) (hx : 0 ≤ x) :
    (Real.cbrt x) ^ 3 = x := by
  unfold Real.cbrt
  rw [← Real.rpow_natCast]
  calc
    (x ^ (1 / 3 : ℝ)) ^ (3 : ℝ) =
        x ^ ((1 / 3 : ℝ) * 3) := (Real.rpow_mul hx _ _).symm
    _ = x := by norm_num

private theorem cbrt_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < Real.cbrt x := by
  unfold Real.cbrt
  exact Real.rpow_pos_of_pos hx _

private theorem rpow_third_sub_one_eq {x : ℝ} (hx : 0 < x) :
    x ^ ((1 / 3 : ℝ) - 1) = 1 / (Real.cbrt x) ^ 2 := by
  have hcpos := cbrt_pos_of_pos hx
  have hcubed := cbrt_cubed_of_nonneg x hx.le
  rw [Real.rpow_sub hx, Real.rpow_one]
  change Real.cbrt x / x = 1 / (Real.cbrt x) ^ 2
  field_simp [hcpos.ne']
  nlinarith [hcubed]

theorem gap1 (x : ℝ) (hx : x ∈ domain) :
    integrand x =
      (1 / 24 : ℝ) * deriv inner x / (Real.cbrt (inner x)) ^ 2 := by
  simp only [integrand]
  rw [(inner_hasDerivAt x).deriv]
  ring

theorem gap2 (x : ℝ) (hx : x ∈ domain) :
    HasDerivAt primitive (integrand x) x := by
  have hxpos : 0 < inner x := hx
  have hroot :
      HasDerivAt (fun z : ℝ => Real.cbrt (inner z))
        ((24 * x ^ 2) * (1 / 3 : ℝ) *
          (inner x) ^ ((1 / 3 : ℝ) - 1)) x := by
    unfold Real.cbrt
    convert (inner_hasDerivAt x).rpow_const (p := (1 / 3 : ℝ))
      (Or.inl hxpos.ne') using 1 <;> ring
  have hprim : HasDerivAt primitive
      ((1 / 8 : ℝ) *
        ((24 * x ^ 2) * (1 / 3 : ℝ) *
          (inner x) ^ ((1 / 3 : ℝ) - 1))) x := by
    unfold primitive
    convert hroot.const_mul (1 / 8 : ℝ) using 1 <;> ring
  apply hprim.congr_deriv
  unfold integrand
  rw [rpow_third_sub_one_eq hxpos]
  ring

theorem gap3 (s : Set ℝ) (hopen : IsOpen s) (hs : IsPreconnected s)
    (hdom : s ⊆ domain) :
    Family integrand s = Translates primitive s := by
  ext F
  constructor
  · intro hF
    change IsAntiderivativeOn F integrand s at hF
    change F ∈ Translates primitive s
    have hderiv : ∀ y ∈ s,
        HasDerivAt (fun z => F z - primitive z) 0 y := by
      intro y hy
      simpa using (hF y hy).sub (gap2 y (hdom hy))
    have hdiff : DifferentiableOn ℝ (fun z => F z - primitive z) s := by
      intro y hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    have hzero : ∀ y ∈ s, deriv (fun z => F z - primitive z) y = 0 := by
      intro y hy
      exact (hderiv y hy).deriv
    by_cases hsne : s.Nonempty
    · rcases hsne with ⟨x₀, hx₀⟩
      refine ⟨F x₀ - primitive x₀, ?_⟩
      intro x hx
      have heq :
          F x - primitive x = F x₀ - primitive x₀ :=
        hopen.is_const_of_deriv_eq_zero hs hdiff hzero hx hx₀
      calc
        F x = primitive x + (F x - primitive x) := by ring
        _ = primitive x + (F x₀ - primitive x₀) := by rw [heq]
    · refine ⟨0, ?_⟩
      intro x hx
      exact (hsne ⟨x, hx⟩).elim
  · intro hF
    change F ∈ Translates primitive s at hF
    change IsAntiderivativeOn F integrand s
    rcases hF with ⟨C, hFC⟩
    intro x hx
    have hs_nhds : ∀ᶠ y in nhds x, y ∈ s := hopen.mem_nhds hx
    have hEq : F =ᶠ[nhds x] fun y => primitive y + C := by
      filter_upwards [hs_nhds] with y hy
      exact hFC y hy
    exact ((gap2 x (hdom hx)).add_const C).congr_of_eventuallyEq hEq

end

end ProofGap.Exercise1686
