import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic

namespace ProofGap.Exercise2765

noncomputable section

def differenceQuotient (n : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  n * (f (x + 1 / n) - f x)

def UniformlyConvergesOn
    (u : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ s, |u n x - F x| < ε

theorem gap1 :
    ∀ a α : ℝ, a < α → ∃ α' : ℝ, a < α' ∧ α' < α := by
  intro a α h
  refine ⟨(a + α) / 2, ?_, ?_⟩ <;> linarith

theorem gap2 :
    ∀ a α : ℝ, a < α → ∃ α' : ℝ, a < α' ∧ α' < α := by
  exact gap1

theorem gap3 :
    ∀ α β : ℝ, α < β → α < β := by
  intro α β h
  exact h

theorem gap4 :
    ∀ β b : ℝ, β < b → ∃ β' : ℝ, β < β' ∧ β' < b := by
  intro β b h
  refine ⟨(β + b) / 2, ?_, ?_⟩ <;> linarith

theorem gap5 :
    ∀ β b : ℝ, β < b → ∃ β' : ℝ, β < β' ∧ β' < b := by
  exact gap4

theorem gap6 :
    ∀ a α β b : ℝ, a < α → α < β → β < b → a < b := by
  intro a α β b ha hαβ hβb
  linarith

theorem gap7 :
    ∀ (a b α' β' : ℝ) (f' : ℝ → ℝ),
      Set.Icc α' β' ⊆ Set.Ioo a b → ContinuousOn f' (Set.Ioo a b) →
        ContinuousOn f' (Set.Icc α' β') := by
  intro a b α' β' f' hsub hcont
  exact hcont.mono hsub

theorem gap8 :
    ∀ (n : ℕ) (f : ℝ → ℝ) (x : ℝ),
      differenceQuotient n f x = n * (f (x + 1 / n) - f x) := by
  intro n f x
  rfl

theorem gap9 :
    ∀ (a b : ℝ) (f f' : ℝ → ℝ) (n : ℕ) (x : ℝ),
      0 < n → x ∈ Set.Ioo a b → x + 1 / n ∈ Set.Ioo a b →
      (∀ y ∈ Set.Icc x (x + 1 / n), HasDerivAt f (f' y) y) →
        ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
          differenceQuotient n f x = f' (x + θ / n) := by
  intro a b f f' n x hn hx hxn hder
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  have hxy : x < x + 1 / (n : ℝ) := by
    have hi : 0 < 1 / (n : ℝ) := one_div_pos.mpr hnR
    linarith
  have hcont : ContinuousOn f (Set.Icc x (x + 1 / (n : ℝ))) := by
    intro y hy
    exact (hder y hy).continuousAt.continuousWithinAt
  have hder' :
      ∀ y ∈ Set.Ioo x (x + 1 / (n : ℝ)), HasDerivAt f (f' y) y := by
    intro y hy
    exact hder y ⟨le_of_lt hy.1, le_of_lt hy.2⟩
  obtain ⟨c, hc, hmc⟩ :=
    exists_hasDerivAt_eq_slope f f' hxy hcont hder'
  refine ⟨(c - x) * (n : ℝ), ?_, ?_⟩
  · constructor
    · exact mul_pos (sub_pos.mpr hc.1) hnR
    · calc
        (c - x) * (n : ℝ) < (1 / (n : ℝ)) * (n : ℝ) := by
          apply mul_lt_mul_of_pos_right _ hnR
          linarith [hc.2]
        _ = 1 := by field_simp [hn0]
  · have hvalue : x + ((c - x) * (n : ℝ)) / (n : ℝ) = c := by
      field_simp [hn0] <;> ring
    rw [hvalue]
    calc
      differenceQuotient n f x =
          (f (x + 1 / (n : ℝ)) - f x) /
            ((x + 1 / (n : ℝ)) - x) := by
              unfold differenceQuotient
              field_simp [hn0] <;> ring
      _ = f' c := by
        simpa [slope] using hmc.symm

theorem gap10 :
    ∀ (n : ℕ) (f' : ℝ → ℝ) (x θ : ℝ), 0 < n →
      n * f' (x + θ / n) * (1 / n) = f' (x + θ / n) := by
  intro n f' x θ hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp [hn0] <;> ring

theorem gap11 :
    ∀ (a b : ℝ) (f f' : ℝ → ℝ) (n : ℕ) (x : ℝ),
      0 < n → x ∈ Set.Ioo a b → x + 1 / n ∈ Set.Ioo a b →
      (∀ y ∈ Set.Icc x (x + 1 / n), HasDerivAt f (f' y) y) →
        ∃ θ ∈ Set.Ioo (0 : ℝ) 1,
          differenceQuotient n f x = f' (x + θ / n) := by
  exact gap9

theorem gap12 :
    ∀ (α' β' : ℝ) (f' : ℝ → ℝ),
      ContinuousOn f' (Set.Icc α' β') →
        UniformContinuousOn f' (Set.Icc α' β') := by
  intro α' β' f' hcont
  exact isCompact_Icc.uniformContinuousOn_of_continuous hcont

theorem gap13 :
    ∀ (α' β' : ℝ) (f' : ℝ → ℝ),
      UniformContinuousOn f' (Set.Icc α' β') →
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
          ∀ x' ∈ Set.Icc α' β', ∀ x'' ∈ Set.Icc α' β',
            |x' - x''| < δ → |f' x' - f' x''| < ε := by
  intro α' β' f' hunif ε hε
  obtain ⟨δ, hδ, hmod⟩ := (Metric.uniformContinuousOn_iff.mp hunif) ε hε
  refine ⟨δ, hδ, ?_⟩
  intro x' hx' x'' hx'' hdist
  simpa [Real.dist_eq] using hmod x' hx' x'' hx'' hdist

theorem gap14 :
    ∀ N n : ℕ, 0 < N → N < n → 1 / (n : ℝ) < 1 / (N : ℝ) := by
  intro N n hN hNn
  have hNR : (0 : ℝ) < (N : ℝ) := Nat.cast_pos.mpr hN
  have hNnR : (N : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hNn
  exact one_div_lt_one_div_of_lt hNR hNnR

theorem gap15 :
    ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, 0 < N ∧ 1 / (N : ℝ) < δ := by
  intro δ hδ
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  have hinv : 0 < 1 / δ := one_div_pos.mpr hδ
  have hNR : (0 : ℝ) < (N : ℝ) := lt_trans hinv hN
  have hNpos : 0 < N := Nat.cast_pos.mp hNR
  refine ⟨N, hNpos, ?_⟩
  apply (div_lt_iff₀ hNR).mpr
  have hprod : 1 < (N : ℝ) * δ := (div_lt_iff₀ hδ).mp hN
  simpa [mul_comm] using hprod

theorem gap16 :
    ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n : ℕ, N < n → 1 / (n : ℝ) < δ := by
  intro δ hδ
  obtain ⟨N, hNpos, hNδ⟩ := gap15 δ hδ
  refine ⟨N, ?_⟩
  intro n hNn
  exact lt_trans (gap14 N n hNpos hNn) hNδ

theorem gap17 :
    ∀ α' α β β' x : ℝ, α' < α → α ≤ x → x ≤ β → β < β' →
      x ∈ Set.Icc α' β' := by
  intro α' α β β' x hleft hxleft hxright hright
  constructor <;> linarith

theorem gap18 :
    ∀ α' α β β' : ℝ, α' < α → α ≤ β → β < β' →
      ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x : ℝ, x ∈ Set.Icc α β →
        ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
          x + θ / n ∈ Set.Icc α' β' := by
  intro α' α β β' hleft hαβ hright
  have hmargin : 0 < β' - β := sub_pos.mpr hright
  obtain ⟨N, hN⟩ := gap16 (β' - β) hmargin
  refine ⟨N, ?_⟩
  intro n hNn x hx θ hθ
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hNn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hrec : 1 / (n : ℝ) < β' - β := hN n hNn
  have hquot_nonneg : 0 ≤ θ / (n : ℝ) := div_nonneg hθ.1 (le_of_lt hnR)
  have hquot_le : θ / (n : ℝ) ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ hnR hnR).mpr
    exact mul_le_mul_of_nonneg_right hθ.2 (le_of_lt hnR)
  constructor
  · exact le_trans (le_trans (le_of_lt hleft) hx.1)
      (le_add_of_nonneg_right hquot_nonneg)
  · have hshift_le : x + θ / (n : ℝ) ≤ β + 1 / (n : ℝ) :=
      add_le_add hx.2 hquot_le
    have hbound : β + 1 / (n : ℝ) < β' := by
      linarith
    exact le_of_lt (lt_of_le_of_lt hshift_le hbound)

theorem gap19 :
    ∀ (f f' : ℝ → ℝ) (n : ℕ) (x θ : ℝ),
      differenceQuotient n f x = f' (x + θ / n) →
        |differenceQuotient n f x - f' x| = |f' (x + θ / n) - f' x| := by
  intro f f' n x θ h
  rw [h]

theorem gap20 :
    ∀ (α' α β β' : ℝ) (f' : ℝ → ℝ),
      α' < α → α ≤ β → β < β' →
      UniformContinuousOn f' (Set.Icc α' β') →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x : ℝ, x ∈ Set.Icc α β →
          ∀ θ : ℝ, θ ∈ Set.Icc (0 : ℝ) 1 →
            |f' (x + θ / n) - f' x| < ε := by
  intro α' α β β' f' hleft hαβ hright hunif ε hε
  obtain ⟨δ, hδ, hmod⟩ := gap13 α' β' f' hunif ε hε
  obtain ⟨Nδ, hNδ⟩ := gap16 δ hδ
  obtain ⟨Ngeo, hNgeo⟩ := gap18 α' α β β' hleft hαβ hright
  refine ⟨max Nδ Ngeo, ?_⟩
  intro n hn x hx θ hθ
  have hnδ : Nδ < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
  have hngeo : Ngeo < n := lt_of_le_of_lt (Nat.le_max_right _ _) hn
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have hnR : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.mpr hnpos
  have hxwide : x ∈ Set.Icc α' β' := gap17 α' α β β' x hleft hx.1 hx.2 hright
  have hshiftwide : x + θ / (n : ℝ) ∈ Set.Icc α' β' :=
    hNgeo n hngeo x hx θ hθ
  have hrec : 1 / (n : ℝ) < δ := hNδ n hnδ
  have hquot_nonneg : 0 ≤ θ / (n : ℝ) := div_nonneg hθ.1 (le_of_lt hnR)
  have hquot_le : θ / (n : ℝ) ≤ 1 / (n : ℝ) := by
    apply (div_le_div_iff₀ hnR hnR).mpr
    exact mul_le_mul_of_nonneg_right hθ.2 (le_of_lt hnR)
  have hdist : |(x + θ / (n : ℝ)) - x| < δ := by
    have heq : (x + θ / (n : ℝ)) - x = θ / (n : ℝ) := by ring
    rw [heq, abs_of_nonneg hquot_nonneg]
    exact lt_of_le_of_lt hquot_le hrec
  exact hmod (x + θ / (n : ℝ)) hshiftwide x hxwide hdist

theorem gap21 :
    ∀ (a α β b : ℝ) (f f' : ℝ → ℝ),
      a < α → α ≤ β → β < b →
      ContinuousOn f' (Set.Ioo a b) →
      (∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) →
      ∀ ε : ℝ, 0 < ε →
        ∃ N : ℕ, ∀ n : ℕ, N < n → ∀ x ∈ Set.Icc α β,
          |differenceQuotient n f x - f' x| < ε := by
  intro a α β b f f' ha hαβ hb hcont hder ε hε
  obtain ⟨α', haα', hα'α⟩ := gap1 a α ha
  obtain ⟨β', hββ', hβ'b⟩ := gap4 β b hb
  have hsub : Set.Icc α' β' ⊆ Set.Ioo a b := by
    intro y hy
    exact ⟨lt_of_lt_of_le haα' hy.1, lt_of_le_of_lt hy.2 hβ'b⟩
  have hcont' : ContinuousOn f' (Set.Icc α' β') :=
    gap7 a b α' β' f' hsub hcont
  have hunif : UniformContinuousOn f' (Set.Icc α' β') :=
    gap12 α' β' f' hcont'
  obtain ⟨Nerr, hNerr⟩ :=
    gap20 α' α β β' f' hα'α hαβ hββ' hunif ε hε
  obtain ⟨Ngeo, hNgeo⟩ := gap18 α' α β β' hα'α hαβ hββ'
  refine ⟨max Nerr Ngeo, ?_⟩
  intro n hn x hx
  have hnerr : Nerr < n := lt_of_le_of_lt (Nat.le_max_left _ _) hn
  have hngeo : Ngeo < n := lt_of_le_of_lt (Nat.le_max_right _ _) hn
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le _) hn
  have hxopen : x ∈ Set.Ioo a b :=
    ⟨lt_of_lt_of_le ha hx.1, lt_of_le_of_lt hx.2 hb⟩
  have hendwide : x + 1 / (n : ℝ) ∈ Set.Icc α' β' := by
    apply hNgeo n hngeo x hx 1
    exact ⟨zero_le_one, le_rfl⟩
  have hendopen : x + 1 / (n : ℝ) ∈ Set.Ioo a b :=
    ⟨lt_of_lt_of_le haα' hendwide.1, lt_of_le_of_lt hendwide.2 hβ'b⟩
  have hsegment :
      ∀ y ∈ Set.Icc x (x + 1 / (n : ℝ)), HasDerivAt f (f' y) y := by
    intro y hy
    apply hder y
    exact ⟨lt_of_lt_of_le hxopen.1 hy.1, lt_of_le_of_lt hy.2 hendopen.2⟩
  obtain ⟨θ, hθ, hmvt⟩ := gap9 a b f f' n x hnpos hxopen hendopen hsegment
  have herr := hNerr n hnerr x hx θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  calc
    |differenceQuotient n f x - f' x| =
        |f' (x + θ / (n : ℝ)) - f' x| := gap19 f f' n x θ hmvt
    _ < ε := herr

theorem gap22 :
    ∀ (a α β b : ℝ) (f f' : ℝ → ℝ),
      a < α → α ≤ β → β < b →
      ContinuousOn f' (Set.Ioo a b) →
      (∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) →
        UniformlyConvergesOn
          (fun n x => differenceQuotient n f x) f' (Set.Icc α β) := by
  intro a α β b f f' ha hαβ hb hcont hder
  unfold UniformlyConvergesOn
  exact gap21 a α β b f f' ha hαβ hb hcont hder

theorem gap23 :
    ∀ (a α β b : ℝ) (f f' : ℝ → ℝ),
      a < α → α ≤ β → β < b →
      ContinuousOn f' (Set.Ioo a b) →
      (∀ x ∈ Set.Ioo a b, HasDerivAt f (f' x) x) →
        UniformlyConvergesOn
          (fun n x => differenceQuotient n f x) f' (Set.Icc α β) := by
  exact gap22

end

end ProofGap.Exercise2765
