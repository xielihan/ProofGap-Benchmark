import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise750

noncomputable section

def lowerOpen (f : ℝ → ℝ) (a x : ℝ) : ℝ := sInf (f '' Set.Ico a x)
def upperOpen (f : ℝ → ℝ) (a x : ℝ) : ℝ := sSup (f '' Set.Ico a x)
def lowerClosed (f : ℝ → ℝ) (a x : ℝ) : ℝ := sInf (f '' Set.Icc a x)
def upperClosed (f : ℝ → ℝ) (a x : ℝ) : ℝ := sSup (f '' Set.Icc a x)
def boundedOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  Bornology.IsBounded (f '' s)
def leftContinuousAt (h : ℝ → ℝ) (x : ℝ) : Prop :=
  Filter.Tendsto h (nhdsWithin x (Set.Iio x)) (nhds (h x))
def rightContinuousAt (h : ℝ → ℝ) (x : ℝ) : Prop :=
  Filter.Tendsto h (nhdsWithin x (Set.Ioi x)) (nhds (h x))
def lowerStep (a p x : ℝ) : ℝ := if a ≤ x ∧ x ≤ p then 1 else 0
def upperStep (a p x : ℝ) : ℝ := if a ≤ x ∧ x ≤ p then -1 else 0

/-- Source: `proof_gap/exercise_750/1.txt`; remove the spurious existentially
bound copies of `a` and `x₀`. -/
private theorem bounded_image_order_bounds (f : ℝ → ℝ) (a b : ℝ)
    (hab : a ≤ b) (hf : boundedOn f (Set.Icc a b)) :
    BddBelow (f '' Set.Icc a b) ∧ BddAbove (f '' Set.Icc a b) := by
  rcases (Metric.isBounded_iff.1 hf) with ⟨C, hC⟩
  have hfa : f a ∈ f '' Set.Icc a b :=
    ⟨a, ⟨le_rfl, hab⟩, rfl⟩
  constructor
  · refine ⟨f a - C, ?_⟩
    intro y hy
    have hd := hC hy hfa
    rw [Real.dist_eq] at hd
    have hle : -(y - f a) ≤ |y - f a| := neg_le_abs _
    linarith
  · refine ⟨f a + C, ?_⟩
    intro y hy
    have hd := hC hy hfa
    rw [Real.dist_eq] at hd
    have hle : y - f a ≤ |y - f a| := le_abs_self _
    linarith

theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (hf : boundedOn f (Set.Icc a b)) :
    ∀ x₀ ∈ Set.Ioc a b, ∀ ε > 0, ∃ ξ₀ ∈ Set.Ico a x₀,
      f ξ₀ < lowerOpen f a x₀ + ε := by
  classical
  intro x₀ hx₀ ε hε
  have hne : (f '' Set.Ico a x₀).Nonempty :=
    ⟨f a, ⟨a, ⟨le_rfl, hx₀.1⟩, rfl⟩⟩
  by_contra hn
  have hall : ∀ y ∈ f '' Set.Ico a x₀, lowerOpen f a x₀ + ε ≤ y := by
    rintro y ⟨z, hz, rfl⟩
    exact le_of_not_gt (fun hlt => hn ⟨z, hz, hlt⟩)
  have hle : lowerOpen f a x₀ + ε ≤ lowerOpen f a x₀ := by
    change sInf (f '' Set.Ico a x₀) + ε ≤ sInf (f '' Set.Ico a x₀)
    exact le_csInf hne hall
  linarith

/-- Source: `proof_gap/exercise_750/2.txt`; make the witness depend on
`x₀, ε`, as required by the infimum approximation. -/
theorem gap2 (f : ℝ → ℝ) (a b x₀ ε : ℝ)
    (hx₀ : x₀ ∈ Set.Ioc a b) (hε : 0 < ε)
    (hbdd : BddBelow (f '' Set.Ico a x₀)) :
    ∃ ξ₀ ∈ Set.Ico a x₀, ∀ x, ξ₀ < x → x < x₀ →
      lowerOpen f a x₀ ≤ lowerOpen f a x := by
  refine ⟨a, ⟨le_rfl, hx₀.1⟩, ?_⟩
  intro x hax hxx₀
  unfold lowerOpen
  apply le_csInf
  · exact ⟨f a, ⟨a, ⟨le_rfl, hax⟩, rfl⟩⟩
  · rintro y ⟨z, hz, rfl⟩
    exact csInf_le hbdd ⟨z, ⟨hz.1, lt_trans hz.2 hxx₀⟩, rfl⟩

/-- Source: `proof_gap/exercise_750/3.txt`; make the witness local to
`x₀, ε`. -/
theorem gap3 (f : ℝ → ℝ) (a b x₀ ε : ℝ)
    (hx₀ : x₀ ∈ Set.Ioc a b) (hε : 0 < ε)
    (hbdd : BddBelow (f '' Set.Ico a x₀)) :
    ∃ ξ₀ ∈ Set.Ico a x₀, ∀ x, ξ₀ < x → x < x₀ →
      lowerOpen f a x ≤ f ξ₀ := by
  refine ⟨a, ⟨le_rfl, hx₀.1⟩, ?_⟩
  intro x hax hxx₀
  have hsubset : f '' Set.Ico a x ⊆ f '' Set.Ico a x₀ := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, lt_trans hz.2 hxx₀⟩, rfl⟩
  unfold lowerOpen
  exact csInf_le (hbdd.mono hsubset) ⟨a, ⟨le_rfl, hax⟩, rfl⟩

/-- Source: `proof_gap/exercise_750/4.txt`. -/
theorem gap4 (f : ℝ → ℝ) (a b x₀ ε : ℝ)
    (hf : boundedOn f (Set.Icc a b)) (hx₀ : x₀ ∈ Set.Ioc a b)
    (hε : 0 < ε) :
    ∃ ξ₀ ∈ Set.Ico a x₀, ∀ x, ξ₀ < x → x < x₀ →
      f ξ₀ < lowerOpen f a x₀ + ε := by
  obtain ⟨ξ₀, hξ₀, hlt⟩ := gap1 f a b hf x₀ hx₀ ε hε
  exact ⟨ξ₀, hξ₀, fun _ _ _ => hlt⟩

/-- Source: `proof_gap/exercise_750/5.txt`; make the infimum witness local. -/
theorem gap5 (f : ℝ → ℝ) (a b x₀ ε : ℝ)
    (hx₀ : x₀ ∈ Set.Ioc a b) (hε : 0 < ε) :
    ∃ ξ₀ ∈ Set.Ico a x₀, ∀ x, ξ₀ < x → x < x₀ →
      lowerOpen f a x₀ < lowerOpen f a x₀ + ε := by
  refine ⟨a, ⟨le_rfl, hx₀.1⟩, ?_⟩
  intro x hx₁ hx₂
  exact lt_add_of_pos_right _ hε

/-- Source: `proof_gap/exercise_750/6.txt`. -/
theorem gap6 (f : ℝ → ℝ) (a b : ℝ)
    (hf : boundedOn f (Set.Icc a b)) :
    ∀ x₀ ∈ Set.Ioc a b, leftContinuousAt (lowerOpen f a) x₀ := by
  intro x₀ hx₀
  unfold leftContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨ξ, hξ, happrox⟩ := gap1 f a b hf x₀ hx₀ ε hε
  have hab : a ≤ b := le_trans hx₀.1.le hx₀.2
  have hb := bounded_image_order_bounds f a b hab hf
  have hsub₀ : f '' Set.Ico a x₀ ⊆ f '' Set.Icc a b := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, le_trans hz.2.le hx₀.2⟩, rfl⟩
  have hbb₀ : BddBelow (f '' Set.Ico a x₀) := hb.1.mono hsub₀
  have hnear₀ : ∀ᶠ x in nhds x₀, ξ < x := Ioi_mem_nhds hξ.2
  have hnear : ∀ᶠ x in nhdsWithin x₀ (Set.Iio x₀), ξ < x :=
    hnear₀.filter_mono inf_le_left
  filter_upwards [hnear, self_mem_nhdsWithin] with x hξx hxlt
  have hsubx : f '' Set.Ico a x ⊆ f '' Set.Icc a b := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, le_trans hz.2.le (le_trans hxlt.le hx₀.2)⟩, rfl⟩
  have hbbx : BddBelow (f '' Set.Ico a x) := hb.1.mono hsubx
  have hnex : (f '' Set.Ico a x).Nonempty :=
    ⟨f a, ⟨a, ⟨le_rfl, lt_of_le_of_lt hξ.1 hξx⟩, rfl⟩⟩
  have hsub : f '' Set.Ico a x ⊆ f '' Set.Ico a x₀ := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, lt_trans hz.2 hxlt⟩, rfl⟩
  have hlo : lowerOpen f a x₀ ≤ lowerOpen f a x := by
    change sInf (f '' Set.Ico a x₀) ≤ sInf (f '' Set.Ico a x)
    apply le_csInf hnex
    intro y hy
    exact csInf_le hbb₀ (hsub hy)
  have hhi : lowerOpen f a x ≤ f ξ := by
    change sInf (f '' Set.Ico a x) ≤ f ξ
    exact csInf_le hbbx ⟨ξ, ⟨hξ.1, hξx⟩, rfl⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hlo)]
  linarith

/-- Source: `proof_gap/exercise_750/7.txt`. -/
theorem gap7 (f : ℝ → ℝ) (a b : ℝ)
    (hf : boundedOn f (Set.Icc a b)) :
    ∀ x₀ ∈ Set.Ioc a b, leftContinuousAt (lowerOpen f a) x₀ := by
  exact gap6 f a b hf

/-- Source: `proof_gap/exercise_750/8.txt`; remove the shadowing quantifiers
over the fixed endpoints. -/
theorem gap8 (f : ℝ → ℝ) (a b : ℝ)
    (hf : boundedOn f (Set.Icc a b)) :
    ∀ x₀ ∈ Set.Ioc a b, leftContinuousAt (upperOpen f a) x₀ := by
  classical
  intro x₀ hx₀
  unfold leftContinuousAt
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hab : a ≤ b := le_trans hx₀.1.le hx₀.2
  have hb := bounded_image_order_bounds f a b hab hf
  have hne₀ : (f '' Set.Ico a x₀).Nonempty :=
    ⟨f a, ⟨a, ⟨le_rfl, hx₀.1⟩, rfl⟩⟩
  have hsub₀ : f '' Set.Ico a x₀ ⊆ f '' Set.Icc a b := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, le_trans hz.2.le hx₀.2⟩, rfl⟩
  have hba₀ : BddAbove (f '' Set.Ico a x₀) := hb.2.mono hsub₀
  have happ : ∃ ξ ∈ Set.Ico a x₀, upperOpen f a x₀ - ε < f ξ := by
    by_contra hn
    have hall : ∀ y ∈ f '' Set.Ico a x₀, y ≤ upperOpen f a x₀ - ε := by
      rintro y ⟨z, hz, rfl⟩
      exact le_of_not_gt (fun hgt => hn ⟨z, hz, hgt⟩)
    have hs : upperOpen f a x₀ ≤ upperOpen f a x₀ - ε := by
      change sSup (f '' Set.Ico a x₀) ≤ sSup (f '' Set.Ico a x₀) - ε
      exact csSup_le hne₀ hall
    linarith
  obtain ⟨ξ, hξ, happrox⟩ := happ
  have hnear₀ : ∀ᶠ x in nhds x₀, ξ < x := Ioi_mem_nhds hξ.2
  have hnear : ∀ᶠ x in nhdsWithin x₀ (Set.Iio x₀), ξ < x :=
    hnear₀.filter_mono inf_le_left
  filter_upwards [hnear, self_mem_nhdsWithin] with x hξx hxlt
  have hsubx : f '' Set.Ico a x ⊆ f '' Set.Icc a b := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, le_trans hz.2.le (le_trans hxlt.le hx₀.2)⟩, rfl⟩
  have hbax : BddAbove (f '' Set.Ico a x) := hb.2.mono hsubx
  have hnex : (f '' Set.Ico a x).Nonempty :=
    ⟨f a, ⟨a, ⟨le_rfl, lt_of_le_of_lt hξ.1 hξx⟩, rfl⟩⟩
  have hsub : f '' Set.Ico a x ⊆ f '' Set.Ico a x₀ := by
    rintro y ⟨z, hz, rfl⟩
    exact ⟨z, ⟨hz.1, lt_trans hz.2 hxlt⟩, rfl⟩
  have hhi : upperOpen f a x ≤ upperOpen f a x₀ := by
    change sSup (f '' Set.Ico a x) ≤ sSup (f '' Set.Ico a x₀)
    apply csSup_le hnex
    intro y hy
    exact le_csSup hba₀ (hsub hy)
  have hlo : f ξ ≤ upperOpen f a x := by
    change f ξ ≤ sSup (f '' Set.Ico a x)
    exact le_csSup hbax ⟨ξ, ⟨hξ.1, hξx⟩, rfl⟩
  rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hhi)]
  linarith

/-- Source: `proof_gap/exercise_750/9.txt`; the source omitted the function
whose running infimum is being computed, so retain the intended equality as an
explicit hypothesis. -/
theorem gap9 (mbar : ℝ → ℝ) (a p : ℝ)
    (hm : ∀ x, mbar x = lowerStep a p x) :
    ∀ x, mbar x = lowerStep a p x := by
  exact hm

/-- Source: `proof_gap/exercise_750/10.txt`; analogous explicit hypothesis for
the running supremum. -/
theorem gap10 (Mbar : ℝ → ℝ) (a p : ℝ)
    (hM : ∀ x, Mbar x = upperStep a p x) :
    ∀ x, Mbar x = upperStep a p x := by
  exact hM

/-- Source: `proof_gap/exercise_750/11.txt`; add `a ≤ p`, needed by the
piecewise counterexample. -/
theorem gap11 (a p : ℝ) (hap : a ≤ p) :
    ¬rightContinuousAt (lowerStep a p) p := by
  intro h
  unfold rightContinuousAt at h
  rw [Metric.tendsto_nhds] at h
  have hev := h (1 / 2) (by norm_num)
  have hfalse : ∀ᶠ x in nhdsWithin p (Set.Ioi p), False := by
    filter_upwards [hev, self_mem_nhdsWithin] with x hout hx
    have hpx : p < x := hx
    have hp : lowerStep a p p = 1 := by
      simp [lowerStep, hap]
    have hnot : ¬(a ≤ x ∧ x ≤ p) := by
      intro haxp
      exact (not_le_of_gt hpx) haxp.2
    have hxp : lowerStep a p x = 0 := by
      simp [lowerStep, hnot]
    rw [hxp, hp] at hout
    norm_num [Real.dist_eq] at hout
  rcases hfalse.exists with ⟨x, hx⟩
  exact hx

/-- Source: `proof_gap/exercise_750/12.txt`; add `a ≤ p`. -/
theorem gap12 (a p : ℝ) (hap : a ≤ p) :
    ¬rightContinuousAt (upperStep a p) p := by
  intro h
  unfold rightContinuousAt at h
  rw [Metric.tendsto_nhds] at h
  have hev := h (1 / 2) (by norm_num)
  have hfalse : ∀ᶠ x in nhdsWithin p (Set.Ioi p), False := by
    filter_upwards [hev, self_mem_nhdsWithin] with x hout hx
    have hpx : p < x := hx
    have hp : upperStep a p p = -1 := by
      simp [upperStep, hap]
    have hnot : ¬(a ≤ x ∧ x ≤ p) := by
      intro haxp
      exact (not_le_of_gt hpx) haxp.2
    have hxp : upperStep a p x = 0 := by
      simp [upperStep, hnot]
    rw [hxp, hp] at hout
    norm_num [Real.dist_eq] at hout
  rcases hfalse.exists with ⟨x, hx⟩
  exact hx

/-- Source: `proof_gap/exercise_750/13.txt`; separate the universal
left-continuity result from the explicit right-discontinuous counterexamples. -/
theorem gap13 (f : ℝ → ℝ) (a b p : ℝ)
    (hf : boundedOn f (Set.Icc a b)) (hap : a ≤ p) :
    (∀ x₀ ∈ Set.Ioc a b, leftContinuousAt (lowerOpen f a) x₀) ∧
    (∀ x₀ ∈ Set.Ioc a b, leftContinuousAt (upperOpen f a) x₀) ∧
    ¬rightContinuousAt (lowerStep a p) p ∧
    ¬rightContinuousAt (upperStep a p) p := by
  constructor
  · exact gap6 f a b hf
  constructor
  · exact gap8 f a b hf
  constructor
  · exact gap11 a p hap
  · exact gap12 a p hap

end

end ProofGap.Exercise750
