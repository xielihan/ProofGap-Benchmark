import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1126

noncomputable section

def d₂ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => deriv f t) x
def d₃ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => d₂ f t) x

def TwiceDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => deriv f t) x

def ThreeTimesDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableOn ℝ (fun t => deriv f t) (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => d₂ f t) x

def y (f : ℝ → ℝ) (x : ℝ) : ℝ := f (1 / x)

def expandedThird (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(6 / x ^ 4) * deriv f (1 / x) -
    (2 / x ^ 5) * d₂ f (1 / x) -
    (4 / x ^ 5) * d₂ f (1 / x) -
    (1 / x ^ 6) * d₃ f (1 / x)

def finalThird (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(1 / x ^ 6) * d₃ f (1 / x) -
    (6 / x ^ 5) * d₂ f (1 / x) -
    (6 / x ^ 4) * deriv f (1 / x)

private theorem hasDerivAt_one_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
  have hfun : (fun t : ℝ => 1 / t) = id⁻¹ := by
    funext t
    simp [one_div]
  rw [hfun]
  exact (hasDerivAt_id x).inv hx

private theorem hasDerivAt_neg_one_div_sq (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => -(1 / t ^ 2)) (2 / x ^ 3) x := by
  have hfun : (fun t : ℝ => -(1 / t ^ 2)) =
      (fun t : ℝ => -((1 / t) * (1 / t))) := by
    funext t
    simp [one_div, pow_two]
  rw [hfun]
  convert ((hasDerivAt_one_div x hx).mul
    (hasDerivAt_one_div x hx)).neg using 1 <;>
    field_simp [hx] <;> ring

private theorem hasDerivAt_two_div_cube (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 2 / t ^ 3) (-(6 / x ^ 4)) x := by
  have hfun : (fun t : ℝ => 2 / t ^ 3) =
      (fun t : ℝ => 2 * (((1 / t) * (1 / t)) * (1 / t))) := by
    funext t
    simp [one_div]
    ring
  rw [hfun]
  have hone := hasDerivAt_one_div x hx
  convert ((hone.mul hone).mul hone).const_mul 2 using 1 <;>
    simp only [Pi.mul_apply, Pi.pow_apply] <;>
    field_simp [hx] <;> ring

private theorem hasDerivAt_one_div_fourth (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t ^ 4) (-(4 / x ^ 5)) x := by
  have hfun : (fun t : ℝ => 1 / t ^ 4) =
      (fun t : ℝ => (((1 / t) * (1 / t)) * (1 / t)) * (1 / t)) := by
    funext t
    simp [one_div]
    ring
  rw [hfun]
  have hone := hasDerivAt_one_div x hx
  convert ((hone.mul hone).mul hone).mul hone using 1 <;>
    simp only [Pi.mul_apply, Pi.pow_apply] <;>
    field_simp [hx] <;> ring

private theorem twiceAt_of_interval (f : ℝ → ℝ) {a b z : ℝ}
    (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hdf : DifferentiableOn ℝ (fun t => deriv f t) (Set.Ioo a b))
    (hz : z ∈ Set.Ioo a b) : TwiceDifferentiableAt f z := by
  let ε := min (z - a) (b - z)
  have hε : 0 < ε := by
    exact lt_min (sub_pos.mpr hz.1) (sub_pos.mpr hz.2)
  refine ⟨ε, hε, ?_, ?_⟩
  · refine hf.mono ?_
    intro t ht
    constructor
    · have hmin := min_le_left (z - a) (b - z)
      dsimp [ε] at ht
      linarith [ht.1, hmin]
    · have hmin := min_le_right (z - a) (b - z)
      dsimp [ε] at ht
      linarith [ht.2, hmin]
  · exact (hdf z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)

theorem gap1 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hf : DifferentiableAt ℝ f (1 / x)) :
    deriv (y f) x = -(1 / x ^ 2) * deriv f (1 / x) := by
  change deriv (fun t : ℝ => f (1 / t)) x = _
  have hcomp := hf.hasDerivAt.comp x (hasDerivAt_one_div x hx)
  calc
    deriv (fun t : ℝ => f (1 / t)) x =
        deriv f (1 / x) * (-1 / x ^ 2) := hcomp.deriv
    _ = -(1 / x ^ 2) * deriv f (1 / x) := by ring

theorem gap2 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hf : TwiceDifferentiableAt f (1 / x)) :
    d₂ (y f) x =
      (2 / x ^ 3) * deriv f (1 / x) + (1 / x ^ 4) * d₂ f (1 / x) := by
  rcases hf with ⟨ε, hε, hf₀, hf₁⟩
  have hz : 1 / x ∈ Set.Ioo (1 / x - ε) (1 / x + ε) := by
    constructor <;> linarith
  have hmem : ∀ᶠ t in nhds x,
      1 / t ∈ Set.Ioo (1 / x - ε) (1 / x + ε) :=
    (hasDerivAt_one_div x hx).continuousAt.eventually
      (isOpen_Ioo.mem_nhds hz)
  have heq : (fun t => deriv (y f) t) =ᶠ[nhds x]
      (fun t => -(1 / t ^ 2) * deriv f (1 / t)) := by
    filter_upwards [eventually_ne_nhds hx, hmem] with t ht htmem
    exact gap1 f t ht
      ((hf₀ (1 / t) htmem).differentiableAt
        (isOpen_Ioo.mem_nhds htmem))
  have hcomp : HasDerivAt (fun t => deriv f (1 / t))
      (d₂ f (1 / x) * (-1 / x ^ 2)) x := by
    simpa [d₂, Function.comp_def, one_div] using
      hf₁.hasDerivAt.comp x (hasDerivAt_one_div x hx)
  have hrhs : HasDerivAt
      (fun t => -(1 / t ^ 2) * deriv f (1 / t))
      ((2 / x ^ 3) * deriv f (1 / x) +
        (1 / x ^ 4) * d₂ f (1 / x)) x := by
    convert (hasDerivAt_neg_one_div_sq x hx).mul hcomp using 1 <;>
      field_simp [hx] <;> ring
  simpa [d₂] using (hrhs.congr_of_eventuallyEq heq).deriv

theorem gap3 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hf : ThreeTimesDifferentiableAt f (1 / x)) :
    d₃ (y f) x = expandedThird f x := by
  rcases hf with ⟨ε, hε, hf₀, hf₁, hf₂⟩
  have hz : 1 / x ∈ Set.Ioo (1 / x - ε) (1 / x + ε) := by
    constructor <;> linarith
  have hmem : ∀ᶠ t in nhds x,
      1 / t ∈ Set.Ioo (1 / x - ε) (1 / x + ε) :=
    (hasDerivAt_one_div x hx).continuousAt.eventually
      (isOpen_Ioo.mem_nhds hz)
  have heq : (fun t => d₂ (y f) t) =ᶠ[nhds x]
      (fun t => (2 / t ^ 3) * deriv f (1 / t) +
        (1 / t ^ 4) * d₂ f (1 / t)) := by
    filter_upwards [eventually_ne_nhds hx, hmem] with t ht htmem
    exact gap2 f t ht (twiceAt_of_interval f hf₀ hf₁ htmem)
  have hf₁x : DifferentiableAt ℝ (fun t => deriv f t) (1 / x) :=
    (hf₁ _ hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hcomp₁ : HasDerivAt (fun t => deriv f (1 / t))
      (d₂ f (1 / x) * (-1 / x ^ 2)) x := by
    simpa [d₂, Function.comp_def, one_div] using
      hf₁x.hasDerivAt.comp x (hasDerivAt_one_div x hx)
  have hcomp₂ : HasDerivAt (fun t => d₂ f (1 / t))
      (d₃ f (1 / x) * (-1 / x ^ 2)) x := by
    simpa [d₃, Function.comp_def, one_div] using
      hf₂.hasDerivAt.comp x (hasDerivAt_one_div x hx)
  have hfirst : HasDerivAt
      (fun t => (2 / t ^ 3) * deriv f (1 / t))
      ((-(6 / x ^ 4)) * deriv f (1 / x) +
        (2 / x ^ 3) * (d₂ f (1 / x) * (-1 / x ^ 2))) x :=
    (hasDerivAt_two_div_cube x hx).mul hcomp₁
  have hsecond : HasDerivAt
      (fun t => (1 / t ^ 4) * d₂ f (1 / t))
      ((-(4 / x ^ 5)) * d₂ f (1 / x) +
        (1 / x ^ 4) * (d₃ f (1 / x) * (-1 / x ^ 2))) x :=
    (hasDerivAt_one_div_fourth x hx).mul hcomp₂
  have hrhs : HasDerivAt
      (fun t => (2 / t ^ 3) * deriv f (1 / t) +
        (1 / t ^ 4) * d₂ f (1 / t))
      (expandedThird f x) x := by
    convert hfirst.add hsecond using 1 <;>
      unfold expandedThird <;>
      field_simp [hx] <;> ring
  simpa [d₃] using (hrhs.congr_of_eventuallyEq heq).deriv

theorem gap4 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0) :
    expandedThird f x = finalThird f x := by
  unfold expandedThird finalThird
  ring

theorem gap5 (f : ℝ → ℝ) (x : ℝ) (hx : x ≠ 0)
    (hf : ThreeTimesDifferentiableAt f (1 / x)) :
    d₃ (y f) x = finalThird f x := by
  calc
    d₃ (y f) x = expandedThird f x := gap3 f x hx hf
    _ = finalThird f x := gap4 f x hx

end

end ProofGap.Exercise1126
