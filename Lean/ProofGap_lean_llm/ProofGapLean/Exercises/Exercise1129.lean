import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1129

noncomputable section

def d₂ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => deriv f t) x
def d₃ (f : ℝ → ℝ) (x : ℝ) : ℝ := deriv (fun t => d₂ f t) x

def ThreeTimesDifferentiableAt (f : ℝ → ℝ) (x : ℝ) : Prop :=
  ∃ ε > 0,
    DifferentiableOn ℝ f (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableOn ℝ (fun t => deriv f t) (Set.Ioo (x - ε) (x + ε)) ∧
      DifferentiableAt ℝ (fun t => d₂ f t) x

def y (f φ : ℝ → ℝ) (x : ℝ) : ℝ := f (φ x)

private theorem second_chain_on
    (f φ : ℝ → ℝ) (x : ℝ) (u v : Set ℝ)
    (hu : IsOpen u) (hx : x ∈ u)
    (hv : IsOpen v) (hφx : φ x ∈ v)
    (hf₀ : DifferentiableOn ℝ f v)
    (hf₁ : DifferentiableOn ℝ (fun t => deriv f t) v)
    (hφ₀ : DifferentiableOn ℝ φ u)
    (hφ₁ : DifferentiableOn ℝ (fun t => deriv φ t) u) :
    d₂ (y f φ) x =
      deriv φ x ^ 2 * d₂ f (φ x) + d₂ φ x * deriv f (φ x) := by
  have hφ_at : DifferentiableAt ℝ φ x :=
    (hφ₀ x hx).differentiableAt (hu.mem_nhds hx)
  have hφ₁_at : DifferentiableAt ℝ (fun t => deriv φ t) x :=
    (hφ₁ x hx).differentiableAt (hu.mem_nhds hx)
  have hf₁_at : DifferentiableAt ℝ (fun t => deriv f t) (φ x) :=
    (hf₁ (φ x) hφx).differentiableAt (hv.mem_nhds hφx)
  have hlocal :
      (fun z => deriv (y f φ) z) =ᶠ[nhds x]
        (fun z => deriv φ z * deriv f (φ z)) := by
    have hxu : ∀ᶠ z in nhds x, z ∈ u := hu.mem_nhds hx
    have hxv : ∀ᶠ z in nhds x, φ z ∈ v :=
      hφ_at.continuousAt (hv.mem_nhds hφx)
    filter_upwards [hxu, hxv] with z hzu hzv
    have hφz : DifferentiableAt ℝ φ z :=
      (hφ₀ z hzu).differentiableAt (hu.mem_nhds hzu)
    have hfz : DifferentiableAt ℝ f (φ z) :=
      (hf₀ (φ z) hzv).differentiableAt (hv.mem_nhds hzv)
    simpa [y, mul_comm] using
      (hfz.hasDerivAt.comp z hφz.hasDerivAt).deriv
  have hprod :=
    hφ₁_at.hasDerivAt.mul
      (hf₁_at.hasDerivAt.comp x hφ_at.hasDerivAt)
  change deriv (fun z => deriv (y f φ) z) x = _
  rw [hlocal.deriv_eq]
  change deriv
    ((fun z => deriv φ z) * ((fun z => deriv f z) ∘ φ)) x = _
  rw [hprod.deriv]
  simp only [d₂, Function.comp_apply, Pi.mul_apply]
  ring

theorem gap1 (f φ : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    deriv (y f φ) x = deriv φ x * deriv f (φ x) := by
  simpa [y, mul_comm] using
    (hf.hasDerivAt.comp x hφ.hasDerivAt).deriv

theorem gap2 (f φ : ℝ → ℝ) (x : ℝ)
    (hf : ThreeTimesDifferentiableAt f (φ x))
    (hφ : ThreeTimesDifferentiableAt φ x) :
    d₂ (y f φ) x =
      deriv φ x ^ 2 * d₂ f (φ x) + d₂ φ x * deriv f (φ x) := by
  rcases hf with ⟨εf, hεf, hf₀, hf₁, _⟩
  rcases hφ with ⟨εφ, hεφ, hφ₀, hφ₁, _⟩
  have hx_u : x ∈ Set.Ioo (x - εφ) (x + εφ) :=
    ⟨sub_lt_self x hεφ, lt_add_of_pos_right x hεφ⟩
  have hφx_v : φ x ∈ Set.Ioo (φ x - εf) (φ x + εf) :=
    ⟨sub_lt_self (φ x) hεf, lt_add_of_pos_right (φ x) hεf⟩
  exact second_chain_on (f := f) (φ := φ) (x := x)
    (u := Set.Ioo (x - εφ) (x + εφ))
    (v := Set.Ioo (φ x - εf) (φ x + εf))
    isOpen_Ioo hx_u isOpen_Ioo hφx_v hf₀ hf₁ hφ₀ hφ₁

theorem gap3 (f φ : ℝ → ℝ) (x : ℝ)
    (hf : ThreeTimesDifferentiableAt f (φ x))
    (hφ : ThreeTimesDifferentiableAt φ x) :
    d₃ (y f φ) x =
      deriv φ x ^ 3 * d₃ f (φ x) +
        3 * deriv φ x * d₂ φ x * d₂ f (φ x) +
        d₃ φ x * deriv f (φ x) := by
  rcases hf with ⟨εf, hεf, hf₀, hf₁, hf₂⟩
  rcases hφ with ⟨εφ, hεφ, hφ₀, hφ₁, hφ₂⟩
  let u : Set ℝ := Set.Ioo (x - εφ) (x + εφ)
  let v : Set ℝ := Set.Ioo (φ x - εf) (φ x + εf)
  have hu : IsOpen u := by
    simpa [u] using isOpen_Ioo
  have hv : IsOpen v := by
    simpa [v] using isOpen_Ioo
  have hx_u : x ∈ u := by
    change x ∈ Set.Ioo (x - εφ) (x + εφ)
    exact ⟨sub_lt_self x hεφ, lt_add_of_pos_right x hεφ⟩
  have hφx_v : φ x ∈ v := by
    change φ x ∈ Set.Ioo (φ x - εf) (φ x + εf)
    exact ⟨sub_lt_self (φ x) hεf, lt_add_of_pos_right (φ x) hεf⟩
  have hφ_at : DifferentiableAt ℝ φ x :=
    (hφ₀ x hx_u).differentiableAt (hu.mem_nhds hx_u)
  have hφ₁_at : DifferentiableAt ℝ (fun t => deriv φ t) x :=
    (hφ₁ x hx_u).differentiableAt (hu.mem_nhds hx_u)
  have hf₁_at : DifferentiableAt ℝ (fun t => deriv f t) (φ x) :=
    (hf₁ (φ x) hφx_v).differentiableAt (hv.mem_nhds hφx_v)
  have hsecond :
      (fun t => d₂ (y f φ) t) =ᶠ[nhds x]
        (fun t => (deriv φ t * deriv φ t) * d₂ f (φ t) +
          d₂ φ t * deriv f (φ t)) := by
    have hxu : ∀ᶠ t in nhds x, t ∈ u := hu.mem_nhds hx_u
    have hxv : ∀ᶠ t in nhds x, φ t ∈ v :=
      hφ_at.continuousAt (hv.mem_nhds hφx_v)
    filter_upwards [hxu, hxv] with t htu htv
    simpa [pow_two] using
      (second_chain_on (f := f) (φ := φ) (x := t)
        (u := u) (v := v) hu htu hv htv hf₀ hf₁ hφ₀ hφ₁)
  have hcalc : HasDerivAt
      (fun t => (deriv φ t * deriv φ t) * d₂ f (φ t) +
        d₂ φ t * deriv f (φ t))
      (((d₂ φ x * deriv φ x + deriv φ x * d₂ φ x) * d₂ f (φ x) +
          (deriv φ x * deriv φ x) * (d₃ f (φ x) * deriv φ x)) +
        (d₃ φ x * deriv f (φ x) +
          d₂ φ x * (d₂ f (φ x) * deriv φ x))) x := by
    simpa only [d₂, d₃, Function.comp_apply, Pi.mul_apply, Pi.add_apply] using
      ((hφ₁_at.hasDerivAt.mul hφ₁_at.hasDerivAt).mul
        (hf₂.hasDerivAt.comp x hφ_at.hasDerivAt)).add
        (hφ₂.hasDerivAt.mul
          (hf₁_at.hasDerivAt.comp x hφ_at.hasDerivAt))
  change deriv (fun t => d₂ (y f φ) t) x = _
  rw [hsecond.deriv_eq]
  rw [hcalc.deriv]
  ring

end

end ProofGap.Exercise1129
