import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3363

open Filter
open scoped Topology

noncomputable section

def interval (a b : ℝ) : Set ℝ :=
  Set.Ioo a b

def ContinuousSolution (a b : ℝ) (f g y : ℝ → ℝ) : Prop :=
  ContinuousOn y (interval a b) ∧
    ∀ x ∈ interval a b, f x * y x = g x

def HasContinuousSolution (a b : ℝ) (f g : ℝ → ℝ) : Prop :=
  ∃ y : ℝ → ℝ, ContinuousSolution a b f g y

def HasUniqueContinuousSolution (a b : ℝ) (f g : ℝ → ℝ) : Prop :=
  ∃ y : ℝ → ℝ,
    ContinuousSolution a b f g y ∧
      ∀ y₁ : ℝ → ℝ, ContinuousSolution a b f g y₁ →
        Set.EqOn y₁ y (interval a b)

def ZeroCompatible (a b : ℝ) (f g : ℝ → ℝ) : Prop :=
  ∀ x ∈ interval a b, f x = 0 → g x = 0

def NonzeroDenseOn (a b : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃α β : ℝ⦄, α < β →
    Set.Ioo α β ⊆ interval a b →
      ∃ x ∈ Set.Ioo α β, f x ≠ 0

def QuotientLimitAtZero (a b : ℝ) (f g : ℝ → ℝ)
    (x₀ L : ℝ) : Prop :=
  ∀ s : ℕ → ℝ,
    (∀ n, s n ∈ interval a b ∧ f (s n) ≠ 0) →
      Tendsto s atTop (𝓝 x₀) →
        Tendsto (fun n => g (s n) / f (s n)) atTop (𝓝 L)

def QuotientCriterion (a b : ℝ) (f g : ℝ → ℝ) : Prop :=
  ZeroCompatible a b f g ∧
    NonzeroDenseOn a b f ∧
      ∀ x₀ ∈ interval a b, f x₀ = 0 →
        ∃! L : ℝ, QuotientLimitAtZero a b f g x₀ L

def RepresentsQuotientExtension (a b : ℝ) (f g y : ℝ → ℝ) : Prop :=
  (∀ x ∈ interval a b, f x ≠ 0 → y x = g x / f x) ∧
    ∀ x ∈ interval a b, f x = 0 →
      QuotientLimitAtZero a b f g x (y x)

def DistinctOnInterval (a b : ℝ) (y₁ y₂ : ℝ → ℝ) : Prop :=
  ∃ x ∈ interval a b, y₁ x ≠ y₂ x

private theorem twoSolutions_of_zero_interval
    (a b : ℝ) (f g : ℝ → ℝ) (α β : ℝ)
    (hexists : HasContinuousSolution a b f g)
    (hαβ : α < β)
    (hsub : Set.Ioo α β ⊆ interval a b)
    (hfzero : ∀ x ∈ Set.Ioo α β, f x = 0) :
    ∃ y₁ y₂ : ℝ → ℝ,
      ContinuousSolution a b f g y₁ ∧
        ContinuousSolution a b f g y₂ ∧
          DistinctOnInterval a b y₁ y₂ := by
  rcases hexists with ⟨y, hy⟩
  let p : ℝ → ℝ := fun x => max 0 ((x - α) * (β - x))
  have hpcont : Continuous p := by
    dsimp [p]
    exact continuous_const.max
      ((continuous_id.sub continuous_const).mul
        (continuous_const.sub continuous_id))
  have hy₂ : ContinuousSolution a b f g (fun x => y x + p x) := by
    refine ⟨hy.1.add hpcont.continuousOn, ?_⟩
    intro x hx
    by_cases hxi : x ∈ Set.Ioo α β
    · have hfx := hfzero x hxi
      have hgx : g x = 0 := by
        have h := hy.2 x hx
        rw [hfx, zero_mul] at h
        exact h.symm
      simp [hfx, hgx]
    · have hxcase : x ≤ α ∨ β ≤ x := by
        by_cases hxa : x ≤ α
        · exact Or.inl hxa
        · right
          have hax : α < x := lt_of_not_ge hxa
          exact le_of_not_gt (fun hxb => hxi ⟨hax, hxb⟩)
      have hprod : (x - α) * (β - x) ≤ 0 := by
        rcases hxcase with hxa | hbx
        · exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hxa)
            (sub_nonneg.mpr (le_trans hxa (le_of_lt hαβ)))
        · exact mul_nonpos_of_nonneg_of_nonpos
            (sub_nonneg.mpr (le_trans (le_of_lt hαβ) hbx))
            (sub_nonpos.mpr hbx)
      have hpx : p x = 0 := by
        dsimp [p]
        exact max_eq_left hprod
      simpa [hpx] using hy.2 x hx
  refine ⟨y, fun x => y x + p x, hy, hy₂, ?_⟩
  let m : ℝ := (α + β) / 2
  have hm : m ∈ Set.Ioo α β := by
    dsimp [m]
    constructor <;> linarith
  refine ⟨m, hsub hm, ?_⟩
  have hleft : 0 < m - α := by
    dsimp [m]
    linarith
  have hright : 0 < β - m := by
    dsimp [m]
    linarith
  have hpositive : 0 < (m - α) * (β - m) := mul_pos hleft hright
  dsimp [p]
  rw [max_eq_right (le_of_lt hpositive)]
  nlinarith

private theorem exists_nonzero_sequence
    (a b : ℝ) (f : ℝ → ℝ)
    (hdense : NonzeroDenseOn a b f)
    (x : ℝ) (hx : x ∈ interval a b) :
    ∃ s : ℕ → ℝ,
      (∀ n, s n ∈ interval a b ∧ f (s n) ≠ 0) ∧
        Tendsto s atTop (𝓝 x) := by
  let D : Set ℝ := {z | z ∈ interval a b ∧ f z ≠ 0}
  have hxa : 0 < x - a := by
    exact sub_pos.mpr hx.1
  have hbx : 0 < b - x := by
    exact sub_pos.mpr hx.2
  have hxcl : x ∈ closure D := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let r : ℝ := min (ε / 2) (min (x - a) (b - x) / 2)
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min (by linarith)
        (div_pos (lt_min hxa hbx) (by norm_num))
    have hrε : r < ε := by
      have hrle : r ≤ ε / 2 := min_le_left _ _
      linarith
    have hra : r < x - a := by
      have hrle : r ≤ min (x - a) (b - x) / 2 := min_le_right _ _
      have hmin : min (x - a) (b - x) ≤ x - a := min_le_left _ _
      linarith
    have hrb : r < b - x := by
      have hrle : r ≤ min (x - a) (b - x) / 2 := min_le_right _ _
      have hmin : min (x - a) (b - x) ≤ b - x := min_le_right _ _
      linarith
    have hsubset : Set.Ioo (x - r) (x + r) ⊆ interval a b := by
      intro z hz
      change a < z ∧ z < b
      constructor <;> linarith [hz.1, hz.2]
    obtain ⟨z, hz, hfz⟩ := hdense (by linarith) hsubset
    refine ⟨z, ⟨hsubset hz, hfz⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith [hz.1, hz.2]
  rcases mem_closure_iff_seq_limit.mp hxcl with ⟨s, hs, hsx⟩
  exact ⟨s, hs, hsx⟩

private theorem quotientLimit_tendsto
    (a b : ℝ) (f g : ℝ → ℝ) (x L : ℝ)
    (hdense : NonzeroDenseOn a b f)
    (hx : x ∈ interval a b)
    (hlimit : QuotientLimitAtZero a b f g x L) :
    Tendsto (fun z => g z / f z)
      (𝓝[{z | z ∈ interval a b ∧ f z ≠ 0}] x) (𝓝 L) := by
  classical
  rw [tendsto_iff_seq_tendsto]
  intro s hs
  obtain ⟨u, hu, _⟩ := exists_nonzero_sequence a b f hdense x hx
  have hs' := tendsto_nhdsWithin_iff.mp hs
  let t : ℕ → ℝ := fun n =>
    if h : s n ∈ {z | z ∈ interval a b ∧ f z ≠ 0} then s n else u 0
  have htmem : ∀ n, t n ∈ interval a b ∧ f (t n) ≠ 0 := by
    intro n
    change t n ∈ {z | z ∈ interval a b ∧ f z ≠ 0}
    unfold t
    split
    · assumption
    · exact hu 0
  have hts : t =ᶠ[atTop] s := hs'.2.mono (by
    intro n hn
    unfold t
    split
    · rfl
    · contradiction)
  have htx : Tendsto t atTop (𝓝 x) := hs'.1.congr' hts.symm
  have hout := hlimit t htmem htx
  have hqeq : (fun n => g (t n) / f (t n)) =ᶠ[atTop]
      (fun n => g (s n) / f (s n)) :=
    hts.mono (by
      intro n hn
      change g (t n) / f (t n) = g (s n) / f (s n)
      rw [hn])
  simpa [Function.comp_def] using hout.congr' hqeq

theorem gap1 (a b : ℝ) (f g : ℝ → ℝ)
    (hunique : HasUniqueContinuousSolution a b f g) :
    ZeroCompatible a b f g := by
  rcases hunique with ⟨y, hy, _⟩
  intro x hx hfx
  have h := hy.2 x hx
  rw [hfx, zero_mul] at h
  exact h.symm

theorem gap2 (a b : ℝ) (f g : ℝ → ℝ)
    (hunique : HasUniqueContinuousSolution a b f g) :
    NonzeroDenseOn a b f := by
  have hexists : HasContinuousSolution a b f g := by
    rcases hunique with ⟨y, hy, _⟩
    exact ⟨y, hy⟩
  intro α β hαβ hsub
  by_contra hnone
  have hfzero : ∀ x ∈ Set.Ioo α β, f x = 0 := by
    intro x hx
    by_contra hfx
    exact hnone ⟨x, hx, hfx⟩
  obtain ⟨y₁, y₂, hy₁, hy₂, hdist⟩ :=
    twoSolutions_of_zero_interval a b f g α β hexists hαβ hsub hfzero
  rcases hunique with ⟨y, _, huniq⟩
  rcases hdist with ⟨x, hx, hne⟩
  exact hne ((huniq y₁ hy₁ hx).trans (huniq y₂ hy₂ hx).symm)

theorem gap3 (a b : ℝ) (f g : ℝ → ℝ)
    (hunique : HasUniqueContinuousSolution a b f g) :
    ∀ x₀ ∈ interval a b, f x₀ = 0 →
      ∃! L : ℝ, QuotientLimitAtZero a b f g x₀ L := by
  have hdense := gap2 a b f g hunique
  rcases hunique with ⟨y, hy, _⟩
  intro x₀ hx₀ hfx₀
  have hyLimit : QuotientLimitAtZero a b f g x₀ (y x₀) := by
    intro s hs hsx
    have hsWithin : Tendsto s atTop (𝓝[interval a b] x₀) :=
      tendsto_nhdsWithin_iff.mpr
        ⟨hsx, Filter.Eventually.of_forall (fun n => (hs n).1)⟩
    have hyWithin : Tendsto y (𝓝[interval a b] x₀) (𝓝 (y x₀)) :=
      hy.1 x₀ hx₀
    have hyTendsto : Tendsto (fun n => y (s n)) atTop (𝓝 (y x₀)) := by
      simpa [Function.comp_def] using
        Filter.Tendsto.comp hyWithin hsWithin
    have heq : ∀ n, y (s n) = g (s n) / f (s n) := by
      intro n
      apply (eq_div_iff (hs n).2).2
      simpa [mul_comm] using hy.2 (s n) (hs n).1
    exact hyTendsto.congr' (Filter.Eventually.of_forall heq)
  refine ⟨y x₀, hyLimit, ?_⟩
  intro L hL
  obtain ⟨s, hs, hsx⟩ := exists_nonzero_sequence a b f hdense x₀ hx₀
  exact tendsto_nhds_unique (hL s hs hsx) (hyLimit s hs hsx)

theorem gap4 (a b : ℝ) (f g : ℝ → ℝ) :
    ¬ ZeroCompatible a b f g →
      ¬ HasContinuousSolution a b f g := by
  intro hnzero hexists
  apply hnzero
  rcases hexists with ⟨y, hy⟩
  intro x hx hfx
  have h := hy.2 x hx
  rw [hfx, zero_mul] at h
  exact h.symm

theorem gap5 (a b : ℝ) (f g : ℝ → ℝ)
    (hzero : ZeroCompatible a b f g) :
    ¬ ZeroCompatible a b f g → False := by
  intro hnzero
  exact hnzero hzero

theorem gap6 (a b : ℝ) (f g : ℝ → ℝ)
    (hzero : ZeroCompatible a b f g) :
    ¬ NonzeroDenseOn a b f →
      ∃ α β : ℝ, α < β ∧
        Set.Ioo α β ⊆ interval a b ∧
          ∀ x ∈ Set.Ioo α β, f x = 0 ∧ g x = 0 := by
  intro hndense
  have hvanish : ∃ α β : ℝ, α < β ∧
      Set.Ioo α β ⊆ interval a b ∧
        ∀ x ∈ Set.Ioo α β, f x = 0 := by
    simpa [NonzeroDenseOn] using hndense
  rcases hvanish with ⟨α, β, hαβ, hsub, hfzero⟩
  refine ⟨α, β, hαβ, hsub, ?_⟩
  intro x hx
  have hfx := hfzero x hx
  exact ⟨hfx, hzero x (hsub hx) hfx⟩

theorem gap7 (a b : ℝ) (f g : ℝ → ℝ)
    (hzero : ZeroCompatible a b f g)
    (hexists : HasContinuousSolution a b f g) :
    ¬ NonzeroDenseOn a b f →
      ∃ y₁ y₂ : ℝ → ℝ,
        ContinuousSolution a b f g y₁ ∧
          ContinuousSolution a b f g y₂ ∧
            DistinctOnInterval a b y₁ y₂ := by
  intro hndense
  obtain ⟨α, β, hαβ, hsub, hzeroInterval⟩ :=
    gap6 a b f g hzero hndense
  exact twoSolutions_of_zero_interval a b f g α β hexists hαβ hsub
    (fun x hx => (hzeroInterval x hx).1)

theorem gap8 (a b : ℝ) (f g : ℝ → ℝ)
    (hunique : HasUniqueContinuousSolution a b f g) :
    ¬ NonzeroDenseOn a b f → False := by
  intro hndense
  exact hndense (gap2 a b f g hunique)

theorem gap9 (a b : ℝ) (f g : ℝ → ℝ)
    (hcriterion : QuotientCriterion a b f g) :
    ∃ y₀ : ℝ → ℝ, RepresentsQuotientExtension a b f g y₀ := by
  classical
  let y₀ : ℝ → ℝ := fun x =>
    if h : x ∈ interval a b ∧ f x = 0 then
      Classical.choose (hcriterion.2.2 x h.1 h.2)
    else
      g x / f x
  refine ⟨y₀, ?_, ?_⟩
  · intro x hx hfx
    simp [y₀, hfx]
  · intro x hx hfx
    have hchoice := Classical.choose_spec (hcriterion.2.2 x hx hfx)
    simpa [y₀, hx, hfx] using hchoice.1

theorem gap10 (a b : ℝ) (f g y₀ : ℝ → ℝ)
    (hab : a < b) (hf : ContinuousOn f (interval a b))
    (hg : ContinuousOn g (interval a b))
    (hcriterion : QuotientCriterion a b f g)
    (hy₀ : RepresentsQuotientExtension a b f g y₀) :
    ContinuousOn y₀ (interval a b) := by
  have hdense := hcriterion.2.1
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hqLimit : QuotientLimitAtZero a b f g x (y₀ x) := by
    by_cases hfx : f x = 0
    · exact hy₀.2 x hx hfx
    · intro s hs hsx
      have hsWithin : Tendsto s atTop (𝓝[interval a b] x) :=
        tendsto_nhdsWithin_iff.mpr
          ⟨hsx, Filter.Eventually.of_forall (fun n => (hs n).1)⟩
      have hqWithin : Tendsto (g / f) (𝓝[interval a b] x)
          (𝓝 ((g / f) x)) :=
        (hg x hx).div (hf x hx) hfx
      have hq := Filter.Tendsto.comp hqWithin hsWithin
      simpa [Function.comp_def, hy₀.1 x hx hfx] using hq
  have hqTop := quotientLimit_tendsto a b f g x (y₀ x) hdense hx hqLimit
  obtain ⟨δ, hδ, hδq⟩ :=
    (Metric.tendsto_nhdsWithin_nhds.mp hqTop) (ε / 3) (by linarith)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro z hz hzx
  by_cases hfz : f z = 0
  · obtain ⟨s, hs, hsz⟩ := exists_nonzero_sequence a b f hdense z hz
    have hqz := hy₀.2 z hz hfz s hs hsz
    have hout : ∀ᶠ n in atTop,
        g (s n) / f (s n) ∈ Metric.ball (y₀ z) (ε / 3) :=
      hqz.eventually (Metric.ball_mem_nhds _ (by linarith))
    have hnear : ∀ᶠ n in atTop, s n ∈ Metric.ball z (δ / 2) :=
      hsz.eventually (Metric.ball_mem_nhds _ (by linarith))
    obtain ⟨n, hnout, hnnear⟩ := (hout.and hnear).exists
    have hnout' : dist (g (s n) / f (s n)) (y₀ z) < ε / 3 := by
      simpa [Metric.mem_ball] using hnout
    have hnnear' : dist (s n) z < δ / 2 := by
      simpa [Metric.mem_ball] using hnnear
    have hsnx : dist (s n) x < δ := by
      calc
        dist (s n) x ≤ dist (s n) z + dist z x := dist_triangle _ _ _
        _ < δ := by linarith
    have hnqx := hδq (hs n) hsnx
    calc
      dist (y₀ z) (y₀ x) ≤
          dist (y₀ z) (g (s n) / f (s n)) +
            dist (g (s n) / f (s n)) (y₀ x) := dist_triangle _ _ _
      _ < ε := by
        rw [dist_comm (y₀ z) (g (s n) / f (s n))]
        linarith
  · have hzx' : dist z x < δ := by linarith
    have hzq := hδq ⟨hz, hfz⟩ hzx'
    rw [hy₀.1 z hz hfz]
    linarith

theorem gap11 (a b : ℝ) (f g y₀ : ℝ → ℝ)
    (hzero : ZeroCompatible a b f g)
    (hy₀ : RepresentsQuotientExtension a b f g y₀) :
    ∀ x ∈ interval a b, f x * y₀ x = g x := by
  intro x hx
  by_cases hfx : f x = 0
  · have hgx := hzero x hx hfx
    simp [hfx, hgx]
  · rw [hy₀.1 x hx hfx]
    field_simp [hfx]

theorem gap12 (a b : ℝ) (f g y₁ : ℝ → ℝ)
    (hy₁ : ContinuousSolution a b f g y₁) :
    ∀ x₀ ∈ interval a b, f x₀ ≠ 0 →
      y₁ x₀ = g x₀ / f x₀ := by
  intro x₀ hx₀ hfx₀
  apply (eq_div_iff hfx₀).2
  simpa [mul_comm] using hy₁.2 x₀ hx₀

theorem gap13 (a b : ℝ) (f g y₀ : ℝ → ℝ)
    (hy₀ : RepresentsQuotientExtension a b f g y₀) :
    ∀ x₀ ∈ interval a b, f x₀ ≠ 0 →
      g x₀ / f x₀ = y₀ x₀ := by
  intro x₀ hx₀ hfx₀
  exact (hy₀.1 x₀ hx₀ hfx₀).symm

theorem gap14 (a b : ℝ) (f g y₀ y₁ : ℝ → ℝ)
    (hy₀ : RepresentsQuotientExtension a b f g y₀)
    (hy₁ : ContinuousSolution a b f g y₁) :
    ∀ x₀ ∈ interval a b, f x₀ ≠ 0 →
      y₁ x₀ = y₀ x₀ := by
  intro x₀ hx₀ hfx₀
  exact (gap12 a b f g y₁ hy₁ x₀ hx₀ hfx₀).trans
    (gap13 a b f g y₀ hy₀ x₀ hx₀ hfx₀)

theorem gap15 (a b : ℝ) (f g y₁ : ℝ → ℝ)
    (hy₁ : ContinuousSolution a b f g y₁)
    (s : ℕ → ℝ) (x₀ : ℝ)
    (hx₀ : x₀ ∈ interval a b)
    (hs : ∀ n, s n ∈ interval a b)
    (hsx : Tendsto s atTop (𝓝 x₀)) :
    Tendsto (fun n => y₁ (s n)) atTop (𝓝 (y₁ x₀)) := by
  have hsWithin : Tendsto s atTop (𝓝[interval a b] x₀) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hsx, Filter.Eventually.of_forall hs⟩
  have hyWithin : Tendsto y₁ (𝓝[interval a b] x₀) (𝓝 (y₁ x₀)) :=
    hy₁.1 x₀ hx₀
  simpa [Function.comp_def] using
    Filter.Tendsto.comp hyWithin hsWithin

theorem gap16 (a b : ℝ) (f g y₁ : ℝ → ℝ)
    (hy₁ : ContinuousSolution a b f g y₁)
    (s : ℕ → ℝ)
    (hs : ∀ n, s n ∈ interval a b ∧ f (s n) ≠ 0) :
    ∀ n, y₁ (s n) = g (s n) / f (s n) := by
  intro n
  exact gap12 a b f g y₁ hy₁ (s n) (hs n).1 (hs n).2

theorem gap17 (a b : ℝ) (f g y₀ : ℝ → ℝ)
    (hy₀ : RepresentsQuotientExtension a b f g y₀)
    (x₀ : ℝ) (hx₀ : x₀ ∈ interval a b) (hfx₀ : f x₀ = 0)
    (s : ℕ → ℝ)
    (hs : ∀ n, s n ∈ interval a b ∧ f (s n) ≠ 0)
    (hsx : Tendsto s atTop (𝓝 x₀)) :
    Tendsto (fun n => g (s n) / f (s n)) atTop (𝓝 (y₀ x₀)) := by
  exact hy₀.2 x₀ hx₀ hfx₀ s hs hsx

theorem gap18 (a b : ℝ) (f g y₀ y₁ : ℝ → ℝ)
    (hdense : NonzeroDenseOn a b f)
    (hy₀ : RepresentsQuotientExtension a b f g y₀)
    (hy₁ : ContinuousSolution a b f g y₁) :
    ∀ x₀ ∈ interval a b, f x₀ = 0 →
      y₁ x₀ = y₀ x₀ := by
  intro x₀ hx₀ hfx₀
  obtain ⟨s, hs, hsx⟩ := exists_nonzero_sequence a b f hdense x₀ hx₀
  have hyTendsto :=
    gap15 a b f g y₁ hy₁ s x₀ hx₀ (fun n => (hs n).1) hsx
  have heq := gap16 a b f g y₁ hy₁ s hs
  have hquotY₁ : Tendsto (fun n => g (s n) / f (s n)) atTop (𝓝 (y₁ x₀)) :=
    hyTendsto.congr' (Filter.Eventually.of_forall heq)
  have hquotY₀ := gap17 a b f g y₀ hy₀ x₀ hx₀ hfx₀ s hs hsx
  exact tendsto_nhds_unique hquotY₁ hquotY₀

theorem gap19 (a b : ℝ) (f g y₀ y₁ : ℝ → ℝ)
    (hdense : NonzeroDenseOn a b f)
    (hy₀ : RepresentsQuotientExtension a b f g y₀)
    (hy₁ : ContinuousSolution a b f g y₁) :
    Set.EqOn y₁ y₀ (interval a b) := by
  intro x hx
  by_cases hfx : f x = 0
  · exact gap18 a b f g y₀ y₁ hdense hy₀ hy₁ x hx hfx
  · exact gap14 a b f g y₀ y₁ hy₀ hy₁ x hx hfx

theorem gap20 (a b : ℝ) (f g : ℝ → ℝ)
    (hab : a < b) (hf : ContinuousOn f (interval a b))
    (hg : ContinuousOn g (interval a b)) :
    QuotientCriterion a b f g ↔
      HasUniqueContinuousSolution a b f g := by
  constructor
  · intro hcriterion
    obtain ⟨y₀, hy₀⟩ := gap9 a b f g hcriterion
    have hycont := gap10 a b f g y₀ hab hf hg hcriterion hy₀
    have hyeq := gap11 a b f g y₀ hcriterion.1 hy₀
    refine ⟨y₀, ⟨hycont, hyeq⟩, ?_⟩
    intro y₁ hy₁
    exact gap19 a b f g y₀ y₁ hcriterion.2.1 hy₀ hy₁
  · intro hunique
    exact ⟨gap1 a b f g hunique, gap2 a b f g hunique,
      gap3 a b f g hunique⟩

end

end ProofGap.Exercise3363
