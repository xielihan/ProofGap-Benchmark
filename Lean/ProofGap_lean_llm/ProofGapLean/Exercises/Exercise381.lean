import ProofGapLean.Prelude.Core
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

namespace ProofGap.Exercise381

noncomputable section

def IsRational (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

noncomputable def rationalRepresentative (x : ℝ) (h : IsRational x) : ℚ :=
  Classical.choose h

noncomputable def f (x : ℝ) : ℝ := by
  classical
  exact if h : IsRational x
    then ((rationalRepresentative x h).den : ℝ)
    else 0

def BoundedOn (g : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∃ M : ℝ, 0 < M ∧ ∀ x ∈ s, |g x| ≤ M

/-- Source: `proof_gap/exercise_381/1.txt`; use the unique reduced rational denominator. -/
theorem gap1 : ∀ x₀ : ℝ, ∃ M : ℝ, f x₀ = M := by
  intro x₀
  exact ⟨f x₀, rfl⟩

/-- Source: `proof_gap/exercise_381/2.txt`. -/
theorem gap2 : ∀ x₀ : ℝ, ∀ δ > 0,
    Set.Infinite {x : ℝ | IsRational x ∧ x₀ - δ < x ∧ x < x₀ + δ} := by
  intro x₀ δ hδ
  have hab : x₀ - δ < x₀ + δ := by linarith
  obtain ⟨s : ℚ, has, hsb⟩ := exists_rat_btwn hab
  obtain ⟨r : ℚ, har, hrs⟩ := exists_rat_btwn has
  let d : ℚ := s - r
  have hd : 0 < d := by
    dsimp [d]
    apply sub_pos.mpr
    exact_mod_cast hrs
  let g : ℕ → ℚ := fun n => r + d / ((n + 1 : ℕ) : ℚ)
  have hg_strict : StrictAnti g := by
    intro m n hmn
    have hmn' : (((m + 1 : ℕ) : ℚ)) < (((n + 1 : ℕ) : ℚ)) := by
      exact_mod_cast Nat.add_lt_add_right hmn 1
    have hmpos : (0 : ℚ) < ((m + 1 : ℕ) : ℚ) := by positivity
    have hnpos : (0 : ℚ) < ((n + 1 : ℕ) : ℚ) := by positivity
    have hdiv : d / (((n + 1 : ℕ) : ℚ)) < d / (((m + 1 : ℕ) : ℚ)) := by
      apply (div_lt_div_iff₀ hnpos hmpos).2
      exact mul_lt_mul_of_pos_left hmn' hd
    simpa [g, add_comm] using add_lt_add_left hdiv r
  have hg_strict_real : StrictAnti (fun n : ℕ => ((g n : ℚ) : ℝ)) := by
    intro m n hmn
    have hq : g n < g m := hg_strict hmn
    have hr : (g n : ℝ) < (g m : ℝ) := by
      exact_mod_cast hq
    simpa only using hr
  have hg_inj : Function.Injective (fun n : ℕ => ((g n : ℚ) : ℝ)) :=
    hg_strict_real.injective
  refine (Set.infinite_range_of_injective hg_inj).mono ?_
  rintro x ⟨n, rfl⟩
  have hkpos : (0 : ℚ) < (((n + 1 : ℕ) : ℚ)) := by positivity
  have hkone : (1 : ℚ) ≤ (((n + 1 : ℕ) : ℚ)) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hfracpos : 0 < d / (((n + 1 : ℕ) : ℚ)) := div_pos hd hkpos
  have hfracle : d / (((n + 1 : ℕ) : ℚ)) ≤ d := by
    apply (div_le_iff₀ hkpos).2
    have hmul := mul_le_mul_of_nonneg_left hkone hd.le
    simpa using hmul
  have hrg : r < g n := by
    dsimp [g]
    exact lt_add_of_pos_right r hfracpos
  have hgs : g n ≤ s := by
    calc
      g n = r + d / (((n + 1 : ℕ) : ℚ)) := rfl
      _ ≤ r + d := by
        simpa [add_comm] using add_le_add_left hfracle r
      _ = s := by dsimp [d]; linarith
  have hrg_real : (r : ℝ) < (g n : ℝ) := by exact_mod_cast hrg
  have hgs_real : (g n : ℝ) ≤ (s : ℝ) := by exact_mod_cast hgs
  exact ⟨⟨g n, rfl⟩, lt_trans har hrg_real, lt_of_le_of_lt hgs_real hsb⟩

/-- Source: `proof_gap/exercise_381/3.txt`; keep the bound local to the chosen interval. -/
theorem gap3 : ∀ x₀ : ℝ, ∀ δ > 0,
    BoundedOn f (Set.Ioo (x₀ - δ) (x₀ + δ)) →
      ∃ M : ℝ, 0 < M ∧
        ∀ x ∈ Set.Ioo (x₀ - δ) (x₀ + δ), |f x| ≤ M := by
  intro x₀ δ hδ h
  simpa [BoundedOn] using h

/-- Source: `proof_gap/exercise_381/4.txt`; compare the reduced denominator directly with the local real bound. -/
theorem gap4 : ∀ x₀ : ℝ, ∀ δ > 0, ∀ M > 0,
    (∀ x ∈ Set.Ioo (x₀ - δ) (x₀ + δ), |f x| ≤ M) →
      ∀ x ∈ Set.Ioo (x₀ - δ) (x₀ + δ),
        IsRational x → f x ≤ M := by
  intro x₀ δ hδ M hM hbound x hx hrat
  exact (le_abs_self (f x)).trans (hbound x hx)

/-- Source: `proof_gap/exercise_381/5.txt`; bind the rational representative instead of using global existential numerators. -/
theorem gap5 : ∀ x₀ : ℝ, ∀ δ > 0, ∀ M > 0, ∀ q : ℚ,
    (q : ℝ) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) →
      (q.den : ℝ) ≤ M →
        (x₀ - δ) * (q.den : ℝ) < (q.num : ℝ) := by
  intro x₀ δ hδ M hM q hq hden
  have hd : (0 : ℝ) < (q.den : ℝ) := by
    exact_mod_cast q.den_pos
  have h := hq.1
  rw [Rat.cast_def] at h
  exact (lt_div_iff₀ hd).mp h

/-- Source: `proof_gap/exercise_381/6.txt`. -/
theorem gap6 : ∀ x₀ : ℝ, ∀ δ > 0, ∀ M > 0, ∀ q : ℚ,
    (q : ℝ) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) →
      (q.den : ℝ) ≤ M →
        (q.num : ℝ) < (x₀ + δ) * (q.den : ℝ) := by
  intro x₀ δ hδ M hM q hq hden
  have hd : (0 : ℝ) < (q.den : ℝ) := by
    exact_mod_cast q.den_pos
  have h := hq.2
  rw [Rat.cast_def] at h
  exact (div_lt_iff₀ hd).mp h

/-- Source: `proof_gap/exercise_381/7.txt`. -/
theorem gap7 : ∀ x₀ : ℝ, ∀ δ > 0, ∀ M > 0,
    (x₀ - δ) * M < (x₀ + δ) * M := by
  intro x₀ δ hδ M hM
  apply mul_lt_mul_of_pos_right _ hM
  linarith

/-- Source: `proof_gap/exercise_381/8.txt`; use reduced rationals to obtain the intended finite set. -/
theorem gap8 : ∀ x₀ : ℝ, ∀ δ > 0, ∀ M > 0,
    Set.Finite {q : ℚ |
      (q : ℝ) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) ∧ (q.den : ℝ) ≤ M} := by
  intro x₀ δ hδ M hM
  let C : ℝ := |x₀ - δ| + |x₀ + δ| + 1
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max M (C * M))
  have hMN : M < (N : ℝ) :=
    lt_of_le_of_lt (le_max_left M (C * M)) hN
  have hCMN : C * M < (N : ℝ) :=
    lt_of_le_of_lt (le_max_right M (C * M)) hN
  have hleft : (Set.Icc (-(N : ℤ)) (N : ℤ)).Finite := Set.finite_Icc _ _
  have hright : (Set.Icc (1 : ℕ) N).Finite := Set.finite_Icc _ _
  have hrect :
      (Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc (1 : ℕ) N).Finite :=
    hleft.prod hright
  refine (hrect.image (fun p : ℤ × ℕ => (p.1 : ℚ) / (p.2 : ℚ))).subset ?_
  intro q hq
  have hd : (0 : ℝ) < (q.den : ℝ) := by
    exact_mod_cast q.den_pos
  have hqlower : -C < (q : ℝ) := by
    dsimp [C]
    nlinarith [neg_abs_le (x₀ - δ), abs_nonneg (x₀ + δ), hq.1.1]
  have qupper : (q : ℝ) < C := by
    dsimp [C]
    nlinarith [le_abs_self (x₀ + δ), abs_nonneg (x₀ - δ), hq.1.2]
  have hCd : C * (q.den : ℝ) ≤ C * M :=
    mul_le_mul_of_nonneg_left hq.2 hC
  have hCdN : C * (q.den : ℝ) < (N : ℝ) :=
    lt_of_le_of_lt hCd hCMN
  have hnumlowerC : -C * (q.den : ℝ) < (q.num : ℝ) := by
    apply (lt_div_iff₀ hd).mp
    simpa only [Rat.cast_def] using hqlower
  have hnumupperC : (q.num : ℝ) < C * (q.den : ℝ) := by
    apply (div_lt_iff₀ hd).mp
    simpa only [Rat.cast_def] using qupper
  have hnumlower : (-(N : ℤ) : ℝ) < (q.num : ℝ) := by
    norm_num
    nlinarith
  have hnumupper : (q.num : ℝ) < ((N : ℕ) : ℝ) := by
    exact lt_trans hnumupperC hCdN
  have hnumlowerZ : -(N : ℤ) ≤ q.num := by
    exact_mod_cast le_of_lt hnumlower
  have hnumupperZ : q.num ≤ (N : ℤ) := by
    exact_mod_cast le_of_lt hnumupper
  have hdenlower : 1 ≤ q.den := q.den_pos
  have hdenupper : q.den ≤ N := by
    exact_mod_cast le_of_lt (lt_of_le_of_lt hq.2 hMN)
  refine ⟨(q.num, q.den), ⟨⟨hnumlowerZ, hnumupperZ⟩, hdenlower, hdenupper⟩, ?_⟩
  simpa using Rat.num_div_den q

/-- Source: `proof_gap/exercise_381/9.txt`. -/
theorem gap9 : ∀ x₀ : ℝ, ∀ δ > 0,
    BoundedOn f (Set.Ioo (x₀ - δ) (x₀ + δ)) → False := by
  intro x₀ δ hδ hb
  obtain ⟨M, hM, hbound⟩ := gap3 x₀ δ hδ hb
  have hQ :
      Set.Finite {q : ℚ |
        (q : ℝ) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) ∧ (q.den : ℝ) ≤ M} :=
    gap8 x₀ δ hδ M hM
  have hImage :
      Set.Finite ((fun q : ℚ => (q : ℝ)) ''
        {q : ℚ |
          (q : ℝ) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) ∧ (q.den : ℝ) ≤ M}) :=
    hQ.image _
  have hFinite :
      Set.Finite {x : ℝ |
        IsRational x ∧ x₀ - δ < x ∧ x < x₀ + δ} := by
    apply hImage.subset
    intro x hx
    let q : ℚ := rationalRepresentative x hx.1
    have hqeq : (q : ℝ) = x := by
      exact Classical.choose_spec hx.1
    have hxIoo : x ∈ Set.Ioo (x₀ - δ) (x₀ + δ) := ⟨hx.2.1, hx.2.2⟩
    have hqIoo : (q : ℝ) ∈ Set.Ioo (x₀ - δ) (x₀ + δ) := by
      simpa [hqeq] using hxIoo
    have hf_le : f x ≤ M := gap4 x₀ δ hδ M hM hbound x hxIoo hx.1
    have hf : f x = (q.den : ℝ) := by
      simp [f, q, hx.1]
    rw [hf] at hf_le
    exact ⟨q, ⟨hqIoo, hf_le⟩, hqeq⟩
  exact (gap2 x₀ δ hδ) hFinite

/-- Source: `proof_gap/exercise_381/10.txt`. -/
theorem gap10 : ∀ x₀ : ℝ, ∀ δ > 0,
    ¬BoundedOn f (Set.Ioo (x₀ - δ) (x₀ + δ)) := by
  intro x₀ δ hδ hb
  exact gap9 x₀ δ hδ hb

/-- Source: `proof_gap/exercise_381/11.txt`; repair the shadowed denominator witnesses in the source definition. -/
theorem gap11 :
    (∀ x : ℝ, ∃ M : ℝ, f x = M) ∧
      ∀ x₀ : ℝ, ∀ δ > 0,
        ¬BoundedOn f (Set.Ioo (x₀ - δ) (x₀ + δ)) := by
  exact ⟨gap1, gap10⟩

end

end ProofGap.Exercise381
