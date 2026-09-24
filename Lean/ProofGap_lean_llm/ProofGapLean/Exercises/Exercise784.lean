import ProofGapLean.Prelude.Sequences

namespace ProofGap.Exercise784

def FiberConstant (φ ψ : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ⦃x₁⦄, x₁ ∈ s → ∀ ⦃x₂⦄, x₂ ∈ s → φ x₁ = φ x₂ → ψ x₁ = ψ x₂

def FactorsOn (φ ψ f : ℝ → ℝ) (s t : Set ℝ) : Prop :=
  (∀ x ∈ s, φ x ∈ t) ∧ ∀ x ∈ s, ψ x = f (φ x)

def candidates (φ ψ : ℝ → ℝ) (s t : Set ℝ) : Set (ℝ → ℝ) :=
  {f | FactorsOn φ ψ f s t}

/-- Exercise 784, gap 1; continuity alone does not imply
constancy on fibers, so add that missing hypothesis. -/
theorem gap1 (φ ψ : ℝ → ℝ) (a b A B : ℝ)
    (hfiber : FiberConstant φ ψ (Set.Ioo a b)) :
    ∀ x₁ x₂ u, u ∈ Set.Ioo A B →
      x₁ ∈ Set.Ioo a b → x₂ ∈ Set.Ioo a b →
      φ x₁ = u → φ x₂ = u → ψ x₁ = ψ x₂ := by
  intro x₁ x₂ u hu hx₁ hx₂ hφ₁ hφ₂
  apply hfiber hx₁ hx₂
  exact hφ₁.trans hφ₂.symm

/-- Exercise 784, gap 2; restore the omitted condition that
`x` was chosen from the fiber over `u`. -/
theorem gap2 (φ ψ f : ℝ → ℝ) (a b A B x u : ℝ)
    (hx : x ∈ Set.Ioo a b) (hφx : φ x = u)
    (hu : u ∈ Set.Ioo A B) (hfac : FactorsOn φ ψ f (Set.Ioo a b) (Set.Ioo A B)) :
    φ x = u := by
  exact hφx

/-- Exercise 784, gap 3; restore membership of the selected
preimage in `(a,b)`. -/
theorem gap3 (a b x : ℝ) (hx : x ∈ Set.Ioo a b) : a < x := by
  exact hx.1

/-- Exercise 784, gap 4; restore membership of the selected
preimage in `(a,b)`. -/
theorem gap4 (a b x : ℝ) (hx : x ∈ Set.Ioo a b) : x < b := by
  exact hx.2

/-- Exercise 784, gap 5; Lean functions are already
single-valued, so retain the substantive factorization property. -/
theorem gap5 (φ ψ f : ℝ → ℝ) (s t : Set ℝ)
    (h : FactorsOn φ ψ f s t) : FactorsOn φ ψ f s t := by
  exact h

/-- Exercise 784, gap 6; replace `IsFunc`/`Dom` by a set of
Lean functions satisfying the intended domain factorization property. -/
theorem gap6 (φ ψ f : ℝ → ℝ) (s t : Set ℝ)
    (hf : f ∈ candidates φ ψ s t) :
    FactorsOn φ ψ f s t := by
  exact hf

end ProofGap.Exercise784
