import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1128

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

def y (f : ℝ → ℝ) (x : ℝ) : ℝ := f (Real.log x)

def expandedSecond (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(1 / x ^ 2) * deriv f (Real.log x) +
    (1 / x ^ 2) * d₂ f (Real.log x)

def expandedThird (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  -(2 / x ^ 3) * (d₂ f (Real.log x) - deriv f (Real.log x)) +
    (1 / x ^ 3) * (d₃ f (Real.log x) - d₂ f (Real.log x))

def finalThird (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / x ^ 3) *
    (d₃ f (Real.log x) - 3 * d₂ f (Real.log x) +
      2 * deriv f (Real.log x))

private theorem hasDerivAt_one_div (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
  have hfun : (fun t : ℝ => 1 / t) = id⁻¹ := by
    funext t
    simp [one_div]
  rw [hfun]
  exact (hasDerivAt_id x).inv hx

private theorem hasDerivAt_one_div_sq (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun t : ℝ => 1 / t ^ 2) (-(2 / x ^ 3)) x := by
  have hfun : (fun t : ℝ => 1 / t ^ 2) =
      (fun t : ℝ => (1 / t) * (1 / t)) := by
    funext t
    simp [one_div, pow_two]
  rw [hfun]
  convert (hasDerivAt_one_div x hx).mul (hasDerivAt_one_div x hx) using 1 <;>
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

theorem gap1 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hf : DifferentiableAt ℝ f (Real.log x)) :
    deriv (y f) x = (1 / x) * deriv f (Real.log x) := by
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  simpa [y, mul_comm] using (hf.hasDerivAt.comp x hlog).deriv

theorem gap2 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hf : TwiceDifferentiableAt f (Real.log x)) :
    d₂ (y f) x = expandedSecond f x := by
  rcases hf with ⟨ε, hε, hf₀, hf₁⟩
  have hz : Real.log x ∈ Set.Ioo (Real.log x - ε) (Real.log x + ε) := by
    constructor <;> linarith
  have hmem : ∀ᶠ t in nhds x,
      Real.log t ∈ Set.Ioo (Real.log x - ε) (Real.log x + ε) :=
    (Real.continuousAt_log hx.ne').eventually (isOpen_Ioo.mem_nhds hz)
  have heq : (fun t => deriv (y f) t) =ᶠ[nhds x]
      (fun t => (1 / t) * deriv f (Real.log t)) := by
    filter_upwards [eventually_gt_nhds hx, hmem] with t ht htmem
    exact gap1 f t ht
      ((hf₀ (Real.log t) htmem).differentiableAt
        (isOpen_Ioo.mem_nhds htmem))
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hcomp : HasDerivAt (fun t => deriv f (Real.log t))
      (d₂ f (Real.log x) * (1 / x)) x := by
    simpa [d₂] using hf₁.hasDerivAt.comp x hlog
  have hrhs : HasDerivAt
      (fun t => (1 / t) * deriv f (Real.log t))
      (expandedSecond f x) x := by
    convert (hasDerivAt_one_div x hx.ne').mul hcomp using 1 <;>
      unfold expandedSecond <;>
      field_simp [hx.ne'] <;> ring
  simpa [d₂] using (hrhs.congr_of_eventuallyEq heq).deriv

theorem gap3 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x) :
    expandedSecond f x =
      (1 / x ^ 2) * (d₂ f (Real.log x) - deriv f (Real.log x)) := by
  unfold expandedSecond
  ring

theorem gap4 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hf : TwiceDifferentiableAt f (Real.log x)) :
    d₂ (y f) x =
      (1 / x ^ 2) * (d₂ f (Real.log x) - deriv f (Real.log x)) := by
  calc
    d₂ (y f) x = expandedSecond f x := gap2 f x hx hf
    _ = (1 / x ^ 2) *
        (d₂ f (Real.log x) - deriv f (Real.log x)) := gap3 f x hx

theorem gap5 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hf : ThreeTimesDifferentiableAt f (Real.log x)) :
    d₃ (y f) x = expandedThird f x := by
  rcases hf with ⟨ε, hε, hf₀, hf₁, hf₂⟩
  have hz : Real.log x ∈ Set.Ioo (Real.log x - ε) (Real.log x + ε) := by
    constructor <;> linarith
  have hmem : ∀ᶠ t in nhds x,
      Real.log t ∈ Set.Ioo (Real.log x - ε) (Real.log x + ε) :=
    (Real.continuousAt_log hx.ne').eventually (isOpen_Ioo.mem_nhds hz)
  have heq : (fun t => d₂ (y f) t) =ᶠ[nhds x]
      (fun t => (1 / t ^ 2) *
        (d₂ f (Real.log t) - deriv f (Real.log t))) := by
    filter_upwards [eventually_gt_nhds hx, hmem] with t ht htmem
    exact gap4 f t ht (twiceAt_of_interval f hf₀ hf₁ htmem)
  have hlog : HasDerivAt Real.log (1 / x) x := by
    simpa [one_div] using Real.hasDerivAt_log hx.ne'
  have hf₁x : DifferentiableAt ℝ (fun t => deriv f t) (Real.log x) :=
    (hf₁ _ hz).differentiableAt (isOpen_Ioo.mem_nhds hz)
  have hcomp₂ : HasDerivAt (fun t => d₂ f (Real.log t))
      (d₃ f (Real.log x) * (1 / x)) x := by
    simpa [d₃] using hf₂.hasDerivAt.comp x hlog
  have hcomp₁ : HasDerivAt (fun t => deriv f (Real.log t))
      (d₂ f (Real.log x) * (1 / x)) x := by
    simpa [d₂] using hf₁x.hasDerivAt.comp x hlog
  have hdiff : HasDerivAt
      (fun t => d₂ f (Real.log t) - deriv f (Real.log t))
      ((d₃ f (Real.log x) - d₂ f (Real.log x)) * (1 / x)) x := by
    convert hcomp₂.sub hcomp₁ using 1 <;> ring
  have hrhs : HasDerivAt
      (fun t => (1 / t ^ 2) *
        (d₂ f (Real.log t) - deriv f (Real.log t)))
      (expandedThird f x) x := by
    convert (hasDerivAt_one_div_sq x hx.ne').mul hdiff using 1 <;>
      unfold expandedThird <;>
      field_simp [hx.ne'] <;> ring
  simpa [d₃] using (hrhs.congr_of_eventuallyEq heq).deriv

theorem gap6 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x) :
    expandedThird f x = finalThird f x := by
  unfold expandedThird finalThird
  ring

theorem gap7 (f : ℝ → ℝ) (x : ℝ) (hx : 0 < x)
    (hf : ThreeTimesDifferentiableAt f (Real.log x)) :
    d₃ (y f) x = finalThird f x := by
  calc
    d₃ (y f) x = expandedThird f x := gap5 f x hx hf
    _ = finalThird f x := gap6 f x hx

end

end ProofGap.Exercise1128
