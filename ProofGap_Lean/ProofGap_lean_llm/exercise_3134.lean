import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

local notation:70 x " /. " y => ((x : ℝ) / (y : ℝ))

def lpUniformConvergent (σ : ℕ × ℝ -> ℝ) (s : Set ℝ) (f : ℝ -> ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ x ∈ s, |σ (n, x) - f x| < ε

def lpContinuousFuncOn (f : ℝ -> ℝ) (s : Set ℝ) : Prop :=
  ContinuousOn f s

def lpContinuousFuncAt (f : ℝ -> ℝ) (x : ℝ) : Prop :=
  ContinuousAt f x

def fejerFormula (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ) : Prop :=
  ∀ (x : ℝ) (n : ℕ), 0 < n →
    σ (n, x) =
      a 0 / 2 +
        ∑ i ∈ Finset.Icc 1 (n - 1),
          (1 - (i /. n)) * (a i * Real.cos (i * x) + b i * Real.sin (i * x))

noncomputable def endpointLimit3134 (x : ℝ) : ℝ :=
  if -Real.pi < x ∧ x < Real.pi then x else 0

-- exercise: exercise_3134
-- The original solution corrects the stated theorem and then gives f(x)=x as a counterexample.

theorem proof_gap_exercise_3134_1
  : ∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
    lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ fejerFormula a b σ →
      ∀ η : ℝ, η > 0 → lpUniformConvergent σ (Set.Icc (-Real.pi + η) (Real.pi - η)) f := by
  sorry

theorem proof_gap_exercise_3134_2
  (h1 : ∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
    lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ fejerFormula a b σ →
      ∀ η : ℝ, η > 0 → lpUniformConvergent σ (Set.Icc (-Real.pi + η) (Real.pi - η)) f)
  : ∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
    lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ f (-Real.pi) = f Real.pi ∧ fejerFormula a b σ →
      lpUniformConvergent σ (Set.Icc (-Real.pi) Real.pi) f := by
  sorry

theorem proof_gap_exercise_3134_3
  (H1 : ∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
    lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ fejerFormula a b σ →
      ∀ η : ℝ, η > 0 → lpUniformConvergent σ (Set.Icc (-Real.pi + η) (Real.pi - η)) f)
  (H2 : ∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
    lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ f (-Real.pi) = f Real.pi ∧ fejerFormula a b σ →
      lpUniformConvergent σ (Set.Icc (-Real.pi) Real.pi) f)
  (f : ℝ -> ℝ) (hf : f = fun x => x)
  : lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) := by
  sorry

theorem proof_gap_exercise_3134_4
  (H1 H2 : Prop) (f : ℝ -> ℝ)
  (hf : f = fun x => x)
  (hc : lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi))
  : f (-Real.pi) ≠ f Real.pi := by
  sorry

theorem proof_gap_exercise_3134_5
  (H1 H2 : Prop) (f : ℝ -> ℝ)
  (hf : f = fun x => x)
  (hc : lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi))
  (hne : f (-Real.pi) ≠ f Real.pi)
  (Sseq : ℕ × ℝ -> ℝ) (Slim : ℝ -> ℝ)
  (hSlim : Slim = endpointLimit3134)
  : ∀ x : ℝ, x ∈ Set.Icc (-Real.pi) Real.pi → Filter.Tendsto (fun n : ℕ => Sseq (n, x)) Filter.atTop (𝓝 (Slim x)) := by
  sorry

theorem proof_gap_exercise_3134_6
  (H1 H2 : Prop) (f : ℝ -> ℝ)
  (hf : f = fun x => x)
  (hc : lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi))
  (hne : f (-Real.pi) ≠ f Real.pi)
  (Sseq : ℕ × ℝ -> ℝ) (Slim : ℝ -> ℝ)
  (hSlim : Slim = endpointLimit3134)
  (h7 : ∀ x : ℝ, x ∈ Set.Icc (-Real.pi) Real.pi → Filter.Tendsto (fun n : ℕ => Sseq (n, x)) Filter.atTop (𝓝 (Slim x)))
  : ∀ (σ : ℕ × ℝ -> ℝ) (x : ℝ), x ∈ Set.Icc (-Real.pi) Real.pi →
      Filter.Tendsto (fun n : ℕ => σ (n, x)) Filter.atTop (𝓝 (Slim x)) := by
  sorry

theorem proof_gap_exercise_3134_7
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  (hbase : True)
  : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) Slim := by
  sorry

theorem proof_gap_exercise_3134_8
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  (h7 : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) Slim)
  : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      lpUniformConvergent σ (Set.Icc (-Real.pi) Real.pi) Slim := by
  sorry

theorem proof_gap_exercise_3134_9
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      ∀ n : ℕ, 0 < n → lpContinuousFuncOn (fun x => σ (n, x)) (Set.Icc (-Real.pi) Real.pi) := by
  sorry

theorem proof_gap_exercise_3134_10
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  (h9 : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      ∀ n : ℕ, 0 < n → lpContinuousFuncOn (fun x => σ (n, x)) (Set.Icc (-Real.pi) Real.pi))
  : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      lpContinuousFuncOn Slim (Set.Icc (-Real.pi) Real.pi) := by
  sorry

theorem proof_gap_exercise_3134_11
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      ¬ lpContinuousFuncAt Slim Real.pi := by
  sorry

theorem proof_gap_exercise_3134_12
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      ¬ lpContinuousFuncAt Slim (-Real.pi) := by
  sorry

theorem proof_gap_exercise_3134_13
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  (h10 : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      lpContinuousFuncOn Slim (Set.Icc (-Real.pi) Real.pi))
  (h11 : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      ¬ lpContinuousFuncAt Slim Real.pi)
  (h12 : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f →
      ¬ lpContinuousFuncAt Slim (-Real.pi))
  : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f → False := by
  sorry

theorem proof_gap_exercise_3134_14
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  (hfalse : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f → False)
  : ¬ (∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
      lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ fejerFormula a b σ →
        lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f) := by
  sorry

theorem proof_gap_exercise_3134_15
  (H1 H2 : Prop) (f Slim : ℝ -> ℝ)
  (hfalse : ∀ (σ : ℕ × ℝ -> ℝ), lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f → False)
  (hnot : ¬ (∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
      lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ fejerFormula a b σ →
        lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f))
  : ¬ (∀ (f : ℝ -> ℝ) (a b : ℕ -> ℝ) (σ : ℕ × ℝ -> ℝ),
      lpContinuousFuncOn f (Set.Icc (-Real.pi) Real.pi) ∧ fejerFormula a b σ →
        lpUniformConvergent σ (Set.Ioo (-Real.pi) Real.pi) f) := by
  sorry
