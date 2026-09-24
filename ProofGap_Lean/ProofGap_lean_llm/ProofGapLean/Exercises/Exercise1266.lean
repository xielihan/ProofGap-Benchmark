import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1266

noncomputable section

def secondDeriv (f : ℝ → ℝ) : ℝ → ℝ := deriv (deriv f)

theorem gap1 (f : ℝ → ℝ) (a b x x₀ : ℝ) (hab : a < b)
    (hx : x ∈ Set.Icc a b) (hx₀ : x₀ ∈ Set.Icc a b)
    (hxne : x ≠ x₀)
    (hf : DifferentiableOn ℝ f (Set.Icc a b))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Icc a b)) :
    ∃ ξ ∈ Set.Ioo (min x x₀) (max x x₀),
      f x = f x₀ + deriv f x₀ * (x - x₀) +
        (1 / 2 : ℝ) * (x - x₀) ^ 2 * secondDeriv f ξ := by
  let F : ℝ → ℝ :=
    fun t ↦ f t - f x₀ - deriv f x₀ * (t - x₀)
  let F' : ℝ → ℝ := fun t ↦ deriv f t - deriv f x₀
  let G : ℝ → ℝ := fun t ↦ (t - x₀) ^ 2
  let G' : ℝ → ℝ := fun t ↦ 2 * (t - x₀)
  rcases lt_or_gt_of_ne hxne with hxx₀ | hxx₀
  · have hsub : Set.Icc x x₀ ⊆ Set.Icc a b := by
      intro y hy
      exact ⟨hx.1.trans hy.1, hy.2.trans hx₀.2⟩
    have hfd : DifferentiableOn ℝ f (Set.Icc x x₀) := hf.mono hsub
    have hFcont : ContinuousOn F (Set.Icc x x₀) := by
      exact ((hfd.continuousOn.sub continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    have hFderiv : ∀ t ∈ Set.Ioo x x₀, HasDerivAt F (F' t) t := by
      intro t ht
      have hft : DifferentiableAt ℝ f t :=
        (hfd t ⟨ht.1.le, ht.2.le⟩).differentiableAt
          (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)
      dsimp [F, F']
      convert (hft.hasDerivAt.sub_const (f x₀)).sub
        (((hasDerivAt_id t).sub_const x₀).const_mul (deriv f x₀)) using 1 <;> ring
    have hGcont : ContinuousOn G (Set.Icc x x₀) :=
      (continuousOn_id.sub continuousOn_const).pow 2
    have hGderiv : ∀ t ∈ Set.Ioo x x₀, HasDerivAt G (G' t) t := by
      intro t _
      dsimp [G, G']
      convert (((hasDerivAt_id t).sub_const x₀).pow 2) using 1 <;>
        simp [id] <;> ring
    obtain ⟨c, hc, hcEq⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope F F' hxx₀ hFcont hFderiv
        G G' hGcont hGderiv
    have hcEq' :
        (x - x₀) ^ 2 * (deriv f c - deriv f x₀) =
          (f x - f x₀ - deriv f x₀ * (x - x₀)) * (2 * (c - x₀)) := by
      dsimp [F, F', G, G'] at hcEq
      nlinarith
    have hdc : DifferentiableOn ℝ (deriv f) (Set.Icc c x₀) := by
      apply hf'.mono
      intro y hy
      apply hsub
      exact ⟨hc.1.le.trans hy.1, hy.2⟩
    obtain ⟨ξ, hξ, hξEq⟩ :=
      exists_deriv_eq_slope (deriv f) hc.2 hdc.continuousOn
        (hdc.mono Set.Ioo_subset_Icc_self)
    change secondDeriv f ξ =
      (deriv f x₀ - deriv f c) / (x₀ - c) at hξEq
    have hden : x₀ - c ≠ 0 := sub_ne_zero.mpr hc.2.ne'
    have hξEq' : secondDeriv f ξ * (c - x₀) =
        deriv f c - deriv f x₀ := by
      have := (eq_div_iff hden).mp hξEq
      nlinarith
    have hmul :
        (c - x₀) * ((x - x₀) ^ 2 * secondDeriv f ξ) =
          (c - x₀) *
            (2 * (f x - f x₀ - deriv f x₀ * (x - x₀))) := by
      calc
        (c - x₀) * ((x - x₀) ^ 2 * secondDeriv f ξ) =
            (x - x₀) ^ 2 * (secondDeriv f ξ * (c - x₀)) := by ring
        _ = (x - x₀) ^ 2 * (deriv f c - deriv f x₀) := by rw [hξEq']
        _ = (f x - f x₀ - deriv f x₀ * (x - x₀)) * (2 * (c - x₀)) := hcEq'
        _ = (c - x₀) *
            (2 * (f x - f x₀ - deriv f x₀ * (x - x₀))) := by ring
    have hmain : (x - x₀) ^ 2 * secondDeriv f ξ =
        2 * (f x - f x₀ - deriv f x₀ * (x - x₀)) :=
      mul_left_cancel₀ (sub_ne_zero.mpr hc.2.ne) hmul
    refine ⟨ξ, ?_, ?_⟩
    · simpa [min_eq_left hxx₀.le, max_eq_right hxx₀.le] using
        ⟨hc.1.trans hξ.1, hξ.2⟩
    · nlinarith
  · have hsub : Set.Icc x₀ x ⊆ Set.Icc a b := by
      intro y hy
      exact ⟨hx₀.1.trans hy.1, hy.2.trans hx.2⟩
    have hfd : DifferentiableOn ℝ f (Set.Icc x₀ x) := hf.mono hsub
    have hFcont : ContinuousOn F (Set.Icc x₀ x) := by
      exact ((hfd.continuousOn.sub continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const)))
    have hFderiv : ∀ t ∈ Set.Ioo x₀ x, HasDerivAt F (F' t) t := by
      intro t ht
      have hft : DifferentiableAt ℝ f t :=
        (hfd t ⟨ht.1.le, ht.2.le⟩).differentiableAt
          (Filter.mem_of_superset (Ioo_mem_nhds ht.1 ht.2) Set.Ioo_subset_Icc_self)
      dsimp [F, F']
      convert (hft.hasDerivAt.sub_const (f x₀)).sub
        (((hasDerivAt_id t).sub_const x₀).const_mul (deriv f x₀)) using 1 <;> ring
    have hGcont : ContinuousOn G (Set.Icc x₀ x) :=
      (continuousOn_id.sub continuousOn_const).pow 2
    have hGderiv : ∀ t ∈ Set.Ioo x₀ x, HasDerivAt G (G' t) t := by
      intro t _
      dsimp [G, G']
      convert (((hasDerivAt_id t).sub_const x₀).pow 2) using 1 <;>
        simp [id] <;> ring
    obtain ⟨c, hc, hcEq⟩ :=
      exists_ratio_hasDerivAt_eq_ratio_slope F F' hxx₀ hFcont hFderiv
        G G' hGcont hGderiv
    have hcEq' :
        (x - x₀) ^ 2 * (deriv f c - deriv f x₀) =
          (f x - f x₀ - deriv f x₀ * (x - x₀)) * (2 * (c - x₀)) := by
      simpa [F, F', G, G'] using hcEq
    have hdc : DifferentiableOn ℝ (deriv f) (Set.Icc x₀ c) := by
      apply hf'.mono
      intro y hy
      apply hsub
      exact ⟨hy.1, hy.2.trans hc.2.le⟩
    obtain ⟨ξ, hξ, hξEq⟩ :=
      exists_deriv_eq_slope (deriv f) hc.1 hdc.continuousOn
        (hdc.mono Set.Ioo_subset_Icc_self)
    change secondDeriv f ξ =
      (deriv f c - deriv f x₀) / (c - x₀) at hξEq
    have hden : c - x₀ ≠ 0 := sub_ne_zero.mpr hc.1.ne'
    have hξEq' : secondDeriv f ξ * (c - x₀) =
        deriv f c - deriv f x₀ :=
      (eq_div_iff hden).mp hξEq
    have hmul :
        (c - x₀) * ((x - x₀) ^ 2 * secondDeriv f ξ) =
          (c - x₀) *
            (2 * (f x - f x₀ - deriv f x₀ * (x - x₀))) := by
      calc
        (c - x₀) * ((x - x₀) ^ 2 * secondDeriv f ξ) =
            (x - x₀) ^ 2 * (secondDeriv f ξ * (c - x₀)) := by ring
        _ = (x - x₀) ^ 2 * (deriv f c - deriv f x₀) := by rw [hξEq']
        _ = (f x - f x₀ - deriv f x₀ * (x - x₀)) * (2 * (c - x₀)) := hcEq'
        _ = (c - x₀) *
            (2 * (f x - f x₀ - deriv f x₀ * (x - x₀))) := by ring
    have hmain : (x - x₀) ^ 2 * secondDeriv f ξ =
        2 * (f x - f x₀ - deriv f x₀ * (x - x₀)) :=
      mul_left_cancel₀ hden hmul
    refine ⟨ξ, ?_, ?_⟩
    · simpa [min_eq_right hxx₀.le, max_eq_left hxx₀.le] using
        ⟨hξ.1, hξ.2.trans hc.2⟩
    · nlinarith

theorem gap2 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Icc a b))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Icc a b))
    (ha : deriv f a = 0) :
    ∃ c₁ ∈ Set.Ioo a ((a + b) / 2),
      f ((a + b) / 2) =
        f a + (b - a) ^ 2 / 8 * secondDeriv f c₁ := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  obtain ⟨c₁, hc₁, heq⟩ := gap1 f a b ((a + b) / 2) a hab
    ⟨ham.le, hmb.le⟩ ⟨le_rfl, hab.le⟩ (ne_of_gt ham) hf hf'
  refine ⟨c₁, ?_, ?_⟩
  · simpa [min_eq_right ham.le, max_eq_left ham.le] using hc₁
  · rw [ha] at heq
    convert heq using 1 <;> ring

theorem gap3 (a b : ℝ) (hab : a < b) :
    ∃ c₁, a < c₁ := by
  exact ⟨b, hab⟩

theorem gap4 (a b : ℝ) (hab : a < b) :
    ∃ c₁, c₁ < (a + b) / 2 := by
  exact ⟨a, by linarith⟩

theorem gap5 (a b : ℝ) (hab : a < b) :
    a < (a + b) / 2 := by
  linarith

theorem gap6 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Icc a b))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Icc a b))
    (hb : deriv f b = 0) :
    ∃ c₂ ∈ Set.Ioo ((a + b) / 2) b,
      f ((a + b) / 2) =
        f b + (b - a) ^ 2 / 8 * secondDeriv f c₂ := by
  have ham : a < (a + b) / 2 := by linarith
  have hmb : (a + b) / 2 < b := by linarith
  obtain ⟨c₂, hc₂, heq⟩ := gap1 f a b ((a + b) / 2) b hab
    ⟨ham.le, hmb.le⟩ ⟨hab.le, le_rfl⟩ (ne_of_lt hmb) hf hf'
  refine ⟨c₂, ?_, ?_⟩
  · simpa [min_eq_left hmb.le, max_eq_right hmb.le] using hc₂
  · rw [hb] at heq
    convert heq using 1 <;> ring

theorem gap7 (a b : ℝ) (hab : a < b) :
    ∃ c₂, (a + b) / 2 < c₂ := by
  exact ⟨b, by linarith⟩

theorem gap8 (a b : ℝ) (hab : a < b) :
    ∃ c₂, c₂ < b := by
  exact ⟨a, hab⟩

theorem gap9 (a b : ℝ) (hab : a < b) :
    (a + b) / 2 < b := by
  linarith

theorem gap10 (f : ℝ → ℝ) (a b : ℝ) :
    |f b - f a| ≤
      |f b - f ((a + b) / 2)| + |f ((a + b) / 2) - f a| := by
  calc
    |f b - f a| =
        |(f b - f ((a + b) / 2)) + (f ((a + b) / 2) - f a)| := by
          congr 1
          ring
    _ ≤ |f b - f ((a + b) / 2)| + |f ((a + b) / 2) - f a| :=
      abs_add_le _ _

theorem gap11 (f : ℝ → ℝ) (a b c₁ c₂ : ℝ)
    (h₁ : f ((a + b) / 2) =
      f a + (b - a) ^ 2 / 8 * secondDeriv f c₁)
    (h₂ : f ((a + b) / 2) =
      f b + (b - a) ^ 2 / 8 * secondDeriv f c₂) :
    |f b - f ((a + b) / 2)| + |f ((a + b) / 2) - f a| =
      (b - a) ^ 2 / 8 *
        (|secondDeriv f c₁| + |secondDeriv f c₂|) := by
  have hleft : f b - f ((a + b) / 2) =
      -((b - a) ^ 2 / 8 * secondDeriv f c₂) := by
    rw [h₂]
    ring
  have hright : f ((a + b) / 2) - f a =
      (b - a) ^ 2 / 8 * secondDeriv f c₁ := by
    rw [h₁]
    ring
  have hcoef : 0 ≤ (b - a) ^ 2 / 8 := by positivity
  rw [hleft, hright, abs_neg, abs_mul, abs_mul]
  simp only [abs_of_nonneg hcoef]
  ring

theorem gap12 (f : ℝ → ℝ) (a b c₁ c₂ : ℝ)
    (h₁ : f ((a + b) / 2) =
      f a + (b - a) ^ 2 / 8 * secondDeriv f c₁)
    (h₂ : f ((a + b) / 2) =
      f b + (b - a) ^ 2 / 8 * secondDeriv f c₂) :
    |f b - f a| ≤ (b - a) ^ 2 / 8 *
      (|secondDeriv f c₁| + |secondDeriv f c₂|) := by
  calc
    |f b - f a| ≤
        |f b - f ((a + b) / 2)| + |f ((a + b) / 2) - f a| :=
      gap10 f a b
    _ = (b - a) ^ 2 / 8 *
        (|secondDeriv f c₁| + |secondDeriv f c₂|) :=
      gap11 f a b c₁ c₂ h₁ h₂

theorem gap13 (a c : ℝ) (hc : a < c) :
    a < c := by
  exact hc

theorem gap14 (b c : ℝ) (hc : c < b) :
    c < b := by
  exact hc

theorem gap15 (a b : ℝ) (hab : a < b) :
    a < b := by
  exact hab

theorem gap16 (f : ℝ → ℝ) (c c₁ c₂ : ℝ)
    (hc : |secondDeriv f c| =
      max |secondDeriv f c₁| |secondDeriv f c₂|) :
    |secondDeriv f c| =
      max |secondDeriv f c₁| |secondDeriv f c₂| := by
  exact hc

theorem gap17 (f : ℝ → ℝ) (a b c c₁ c₂ : ℝ)
    (hab : a < b)
    (hc : |secondDeriv f c| =
      max |secondDeriv f c₁| |secondDeriv f c₂|)
    (hbound : |f b - f a| ≤ (b - a) ^ 2 / 8 *
      (|secondDeriv f c₁| + |secondDeriv f c₂|)) :
    |f b - f a| ≤ (b - a) ^ 2 / 4 * |secondDeriv f c| := by
  have hc₁ : |secondDeriv f c₁| ≤ |secondDeriv f c| := by
    rw [hc]
    exact le_max_left _ _
  have hc₂ : |secondDeriv f c₂| ≤ |secondDeriv f c| := by
    rw [hc]
    exact le_max_right _ _
  have hcoef : 0 ≤ (b - a) ^ 2 / 8 := by positivity
  calc
    |f b - f a| ≤ (b - a) ^ 2 / 8 *
        (|secondDeriv f c₁| + |secondDeriv f c₂|) := hbound
    _ ≤ (b - a) ^ 2 / 8 *
        (|secondDeriv f c| + |secondDeriv f c|) :=
      mul_le_mul_of_nonneg_left (add_le_add hc₁ hc₂) hcoef
    _ = (b - a) ^ 2 / 4 * |secondDeriv f c| := by ring

theorem gap18 (f : ℝ → ℝ) (a b c : ℝ) (hab : a < b)
    (hbound : |f b - f a| ≤
      (b - a) ^ 2 / 4 * |secondDeriv f c|) :
    |secondDeriv f c| ≥ 4 / (b - a) ^ 2 * |f b - f a| := by
  have hsquare : 0 < (b - a) ^ 2 := sq_pos_of_pos (sub_pos.mpr hab)
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hsquare).2
  nlinarith

theorem gap19 (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hf : DifferentiableOn ℝ f (Set.Icc a b))
    (hf' : DifferentiableOn ℝ (deriv f) (Set.Icc a b))
    (ha : deriv f a = 0) (hb : deriv f b = 0) :
    ∃ c ∈ Set.Ioo a b,
      |secondDeriv f c| ≥ 4 / (b - a) ^ 2 * |f b - f a| := by
  obtain ⟨c₁, hc₁, h₁⟩ := gap2 f a b hab hf hf' ha
  obtain ⟨c₂, hc₂, h₂⟩ := gap6 f a b hab hf hf' hb
  have ham : a < (a + b) / 2 := gap5 a b hab
  have hmb : (a + b) / 2 < b := gap9 a b hab
  by_cases hmax : |secondDeriv f c₁| ≤ |secondDeriv f c₂|
  · refine ⟨c₂, ⟨ham.trans hc₂.1, hc₂.2⟩, ?_⟩
    apply gap18 f a b c₂ hab
    apply gap17 f a b c₂ c₁ c₂ hab
    · exact (max_eq_right hmax).symm
    · exact gap12 f a b c₁ c₂ h₁ h₂
  · have hmax' : |secondDeriv f c₂| ≤ |secondDeriv f c₁| :=
      le_of_not_ge hmax
    refine ⟨c₁, ⟨hc₁.1, hc₁.2.trans hmb⟩, ?_⟩
    apply gap18 f a b c₁ hab
    apply gap17 f a b c₁ c₁ c₂ hab
    · exact (max_eq_left hmax').symm
    · exact gap12 f a b c₁ c₂ h₁ h₂

end

end ProofGap.Exercise1266
