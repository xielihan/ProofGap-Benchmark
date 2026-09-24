import ProofGapLean.Prelude.Sequences
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Order.OrderClosed

namespace ProofGap.Exercise1019_2

noncomputable section

open scoped Topology

def rightFilter (a : ℝ) : Filter ℝ := 𝓝[Set.Ioi a] a
def leftFilter (b : ℝ) : Filter ℝ := 𝓝[Set.Iio b] b

def RightPosInf (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto f (rightFilter a) atTop

def RightNegInf (f : ℝ → ℝ) (a : ℝ) : Prop :=
  Tendsto f (rightFilter a) atBot

def LeftPosInf (f : ℝ → ℝ) (b : ℝ) : Prop :=
  Tendsto f (leftFilter b) atTop

def DerivativeBoundedOn (f : ℝ → ℝ) (s : Set ℝ) (K : ℝ) : Prop :=
  ∀ x ∈ s, |deriv f x| ≤ K

def DerivativeUnboundedRight (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ δ > 0, ∀ K > 0, ∃ x ∈ Set.Ioo a (a + δ), K < |deriv f x|

def DerivativeUnboundedLeft (f : ℝ → ℝ) (b : ℝ) : Prop :=
  ∀ δ > 0, ∀ K > 0, ∃ x ∈ Set.Ioo (b - δ) b, K < |deriv f x|

def barrier (f : ℝ → ℝ) (x₀ K x : ℝ) : ℝ :=
  f x₀ + 2 * K * (x - x₀)

def gapFunction (f Y : ℝ → ℝ) (x : ℝ) : ℝ := f x - Y x

def secantSlope (f : ℝ → ℝ) (u v : ℝ) : ℝ :=
  (f v - f u) / (v - u)

private theorem Real.mem_ball (x y r : ℝ) :
    x ∈ Metric.ball y r ↔ dist x y < r := by
  exact Metric.mem_ball

theorem gap1 (f : ℝ → ℝ) (a b : ℝ)
    (hf : DifferentiableOn ℝ f (Set.Ioo a b)) :
    ContinuousOn f (Set.Ioo a b) := by
  exact hf.continuousOn

theorem gap2 (f : ℝ → ℝ) (a : ℝ) (h : RightPosInf f a) :
    RightPosInf f a ∨ RightNegInf f a := by
  exact Or.inl h

theorem gap3 (f : ℝ → ℝ) (a : ℝ) (h : RightPosInf f a) :
    RightPosInf f a := by
  exact h

theorem gap4 (f : ℝ → ℝ) (a : ℝ) (h : RightNegInf f a) :
    RightPosInf (fun x => -f x) a := by
  unfold RightPosInf RightNegInf at *
  intro s hs
  rcases Filter.mem_atTop_sets.mp hs with ⟨M, hM⟩
  have hIic : Set.Iic (-M) ∈ (atBot : Filter ℝ) := by
    refine Filter.mem_atBot_sets.mpr ⟨-M, ?_⟩
    intro y hy
    exact hy
  change (fun x => -f x) ⁻¹' s ∈ rightFilter a
  have he := h hIic
  change f ⁻¹' Set.Iic (-M) ∈ rightFilter a at he
  filter_upwards [he] with x hx
  apply hM
  change f x ≤ -M at hx
  change M ≤ -f x
  linarith

theorem gap5 (f : ℝ → ℝ) (a : ℝ) (h : RightPosInf f a) :
    ∀ M : ℝ, ∃ δ > 0, ∀ x ∈ Set.Ioo a (a + δ), M ≤ f x := by
  intro M
  have hIci : Set.Ici M ∈ (atTop : Filter ℝ) := by
    refine Filter.mem_atTop_sets.mpr ⟨M, ?_⟩
    intro y hy
    exact hy
  have he : {x : ℝ | M ≤ f x} ∈ rightFilter a := by
    have he' : f ⁻¹' Set.Ici M ∈ rightFilter a := h hIci
    exact he'
  rw [rightFilter, Metric.mem_nhdsWithin_iff] at he
  rcases he with ⟨δ, hδ, hsub⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  apply hsub
  constructor
  · rw [Real.mem_ball, Real.dist_eq]
    rw [abs_of_pos (sub_pos.mpr hx.1)]
    exact sub_lt_iff_lt_add.mpr (by simpa [add_comm] using hx.2)
  · exact hx.1

theorem gap6 (f : ℝ → ℝ) (a b M : ℝ)
    (hab : a < b) (h : RightPosInf f a) :
    ∃ x ∈ Set.Ioo a b, M ≤ f x := by
  obtain ⟨δ, hδ, hM⟩ := gap5 f a h M
  let d : ℝ := min δ (b - a)
  have hd : 0 < d := lt_min hδ (sub_pos.mpr hab)
  let x : ℝ := a + d / 2
  have hxa : a < x := by
    dsimp [x]
    linarith
  have hxd : x < a + δ := by
    have hle : d ≤ δ := min_le_left _ _
    dsimp [x]
    linarith
  have hxb : x < b := by
    have hle : d ≤ b - a := min_le_right _ _
    dsimp [x]
    linarith
  exact ⟨x, ⟨hxa, hxb⟩, hM x ⟨hxa, hxd⟩⟩

theorem gap7 (f : ℝ → ℝ) (x₀ K x : ℝ) :
    barrier f x₀ K x = f x₀ + 2 * K * (x - x₀) := by
  rfl

theorem gap8 (f : ℝ → ℝ) (x₀ K B : ℝ) :
    barrier f x₀ K B = f x₀ + 2 * K * (B - x₀) := by
  rfl

theorem gap9 (f : ℝ → ℝ) (x₀ K B δ : ℝ)
    (hB : B - x₀ = δ) :
    f x₀ + 2 * K * (B - x₀) = f x₀ + 2 * K * δ := by
  rw [hB]

theorem gap10 (f : ℝ → ℝ) (x₀ K B δ : ℝ)
    (hB : B - x₀ = δ) :
    barrier f x₀ K B = f x₀ + 2 * K * δ := by
  rw [gap8, hB]

theorem gap11 (f : ℝ → ℝ) (x₀ K B M₁ : ℝ)
    (hM : M₁ = f x₀ + 2 * K * (B - x₀)) :
    barrier f x₀ K B = M₁ := by
  rw [gap8, ← hM]

theorem gap12 (f : ℝ → ℝ) (a b M₁ : ℝ)
    (hab : a < b) (h : RightPosInf f a) :
    ∃ x₂ ∈ Set.Ioo a b, M₁ < f x₂ := by
  obtain ⟨x₂, hx₂, hM⟩ := gap6 f a b (M₁ + 1) hab h
  refine ⟨x₂, hx₂, ?_⟩
  linarith

theorem gap13 (f : ℝ → ℝ) (x₀ K : ℝ)
    (hf : HasDerivAt f (deriv f x₀) x₀) (hK : 0 < K) :
    ∀ ε, 0 < ε → ε < K / 2 →
      ∃ δ > 0, ∀ x, 0 < |x - x₀| → |x - x₀| < δ →
        |deriv f x₀ - secantSlope f x₀ x| < ε := by
  intro ε hε _
  have ht := (hasDerivAt_iff_tendsto_slope.mp hf)
  rw [Metric.tendsto_nhdsWithin_nhds] at ht
  rcases ht ε hε with ⟨δ, hδ, ht⟩
  refine ⟨δ, hδ, ?_⟩
  intro x hx0 hxd
  have hne : x ≠ x₀ := by
    intro hEq
    subst x
    simpa using hx0
  have hmem : x ∈ ({x₀}ᶜ : Set ℝ) := by
    simpa [Set.mem_compl_iff, Set.mem_singleton_iff] using hne
  have hs := ht hmem
  have hdist : dist x x₀ < δ := by
    simpa [Real.dist_eq] using hxd
  specialize hs hdist
  simpa [Real.dist_eq, secantSlope, slope, div_eq_mul_inv, mul_comm,
    abs_sub_comm] using hs

theorem gap14 (f : ℝ → ℝ) (x₀ x : ℝ) :
    |secantSlope f x₀ x| ≤
      |deriv f x₀| + |secantSlope f x₀ x - deriv f x₀| := by
  calc
    |secantSlope f x₀ x| =
        |deriv f x₀ + (secantSlope f x₀ x - deriv f x₀)| := by ring_nf
    _ ≤ |deriv f x₀| + |secantSlope f x₀ x - deriv f x₀| :=
      abs_add_le _ _

theorem gap15 (f : ℝ → ℝ) (x₀ x K ε : ℝ)
    (hderiv : |deriv f x₀| ≤ K)
    (hclose : |secantSlope f x₀ x - deriv f x₀| < ε) :
    |deriv f x₀| + |secantSlope f x₀ x - deriv f x₀| < K + ε := by
  linarith

theorem gap16 (K ε : ℝ) (hK : 0 < K) (hε : ε < K / 2) :
    K + ε < K + K / 2 := by
  linarith

theorem gap17 (K : ℝ) :
    K + K / 2 = (3 / 2 : ℝ) * K := by
  ring

theorem gap18 (f : ℝ → ℝ) (x₀ x K ε : ℝ)
    (hK : 0 < K) (hε : ε < K / 2)
    (hderiv : |deriv f x₀| ≤ K)
    (hclose : |secantSlope f x₀ x - deriv f x₀| < ε) :
    |secantSlope f x₀ x| < (3 / 2 : ℝ) * K := by
  calc
    |secantSlope f x₀ x| ≤
        |deriv f x₀| + |secantSlope f x₀ x - deriv f x₀| := gap14 f x₀ x
    _ < K + ε := gap15 f x₀ x K ε hderiv hclose
    _ < K + K / 2 := gap16 K ε hK hε
    _ = (3 / 2 : ℝ) * K := gap17 K

theorem gap19 (f : ℝ → ℝ) (x₀ x K : ℝ)
    (hx : x₀ < x)
    (hs : |secantSlope f x₀ x| < (3 / 2 : ℝ) * K) :
    |f x - f x₀| < (3 / 2 : ℝ) * K * |x - x₀| := by
  have hden : 0 < |x - x₀| := abs_pos.mpr (sub_ne_zero.mpr hx.ne')
  rw [secantSlope, abs_div] at hs
  exact (div_lt_iff₀ hden).mp hs

theorem gap20 (a x₂ : ℝ) (h : a < x₂) :
    ∃ x₁ ∈ Set.Ioo a x₂, a < x₁ := by
  refine ⟨(a + x₂) / 2, ?_, ?_⟩
  · constructor <;> linarith
  · linarith

theorem gap21 (x₁ x₂ : ℝ) (h : x₁ ∈ Set.Iio x₂) :
    x₁ < x₂ := by
  exact h

theorem gap22 (x₀ δ : ℝ) (hδ : 0 < δ) :
    ∃ x₁ ∈ Set.Ioo x₀ (x₀ + δ), x₁ < x₀ + δ := by
  refine ⟨x₀ + δ / 2, ?_, ?_⟩
  · constructor <;> linarith
  · linarith

theorem gap23 (f : ℝ → ℝ) (x₀ x₁ K : ℝ)
    (hx : x₀ < x₁)
    (h : |f x₁ - f x₀| < (3 / 2 : ℝ) * K * |x₁ - x₀|) :
    f x₁ - f x₀ < (3 / 2 : ℝ) * K * (x₁ - x₀) := by
  have hle : f x₁ - f x₀ ≤ |f x₁ - f x₀| := le_abs_self _
  have habs : |x₁ - x₀| = x₁ - x₀ := abs_of_pos (sub_pos.mpr hx)
  rw [habs] at h
  exact lt_of_le_of_lt hle h

theorem gap24 (K x₀ x₁ : ℝ) (hK : 0 < K) (hx : x₀ < x₁) :
    (3 / 2 : ℝ) * K * (x₁ - x₀) < 2 * K * (x₁ - x₀) := by
  have hp : 0 < K * (x₁ - x₀) := mul_pos hK (sub_pos.mpr hx)
  nlinarith

theorem gap25 (f : ℝ → ℝ) (x₀ x₁ K : ℝ) :
    2 * K * (x₁ - x₀) =
      barrier f x₀ K x₁ - f x₀ := by
  simp [barrier]

theorem gap26 (f Y : ℝ → ℝ) (x₀ x₁ : ℝ)
    (h : f x₁ - f x₀ < Y x₁ - f x₀) :
    f x₁ - f x₀ < Y x₁ - f x₀ := by
  exact h

theorem gap27 (f Y : ℝ → ℝ) (x₁ : ℝ)
    (h : f x₁ - Y x₁ < 0) :
    f x₁ < Y x₁ := by
  linarith

theorem gap28 (f Y : ℝ → ℝ) (x₁ : ℝ)
    (h : f x₁ < Y x₁) :
    gapFunction f Y x₁ < 0 := by
  unfold gapFunction
  linarith

theorem gap29 (f Y : ℝ → ℝ) (x₂ : ℝ)
    (h : Y x₂ < f x₂) :
    0 < gapFunction f Y x₂ := by
  unfold gapFunction
  linarith

theorem gap30 (G : ℝ → ℝ) (x₁ x₂ : ℝ)
    (hx : x₁ < x₂) (hcont : ContinuousOn G (Set.Icc x₁ x₂))
    (h₁ : G x₁ < 0) (h₂ : 0 < G x₂) :
    ∃ c ∈ Set.Ioo x₁ x₂, G c = 0 := by
  have hz : (0 : ℝ) ∈ Set.Icc (G x₁) (G x₂) :=
    ⟨le_of_lt h₁, le_of_lt h₂⟩
  rcases intermediate_value_Icc (le_of_lt hx) hcont hz with ⟨c, hc, hGc⟩
  have hcne₁ : c ≠ x₁ := by
    intro heq
    subst c
    linarith
  have hcne₂ : c ≠ x₂ := by
    intro heq
    subst c
    linarith
  refine ⟨c, ⟨lt_of_le_of_ne hc.1 (Ne.symm hcne₁), lt_of_le_of_ne hc.2 hcne₂⟩, ?_⟩
  exact hGc

theorem gap31 (G : ℝ → ℝ) (c x₂ : ℝ)
    (hc : c < x₂) (hcont : ContinuousAt G x₂) (h₂ : 0 < G x₂) :
    ∃ x ∈ Set.Ioo c x₂, 0 < G x := by
  rcases (Metric.continuousAt_iff.mp hcont) (G x₂) h₂ with ⟨δ, hδ, hd⟩
  let d : ℝ := min δ (x₂ - c)
  have hdpos : 0 < d := lt_min hδ (sub_pos.mpr hc)
  let x : ℝ := x₂ - d / 2
  have hxc : c < x := by
    have hle : d ≤ x₂ - c := min_le_right _ _
    dsimp [x]
    linarith
  have hxx₂ : x < x₂ := by
    dsimp [x]
    linarith
  have hdist : dist x x₂ < δ := by
    have hle : d ≤ δ := min_le_left _ _
    rw [Real.dist_eq]
    dsimp [x]
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hclose := hd hdist
  rw [Real.dist_eq] at hclose
  refine ⟨x, ⟨hxc, hxx₂⟩, ?_⟩
  have hlower : G x₂ - G x ≤ |G x - G x₂| := by
    rw [abs_sub_comm]
    exact le_abs_self _
  linarith

theorem gap32 (f Y : ℝ → ℝ) (x : ℝ)
    (h : 0 < gapFunction f Y x) :
    Y x < f x := by
  unfold gapFunction at h
  linarith

theorem gap33 (f Y : ℝ → ℝ) (c x : ℝ)
    (h : Y x < f x) :
    f x - f c > Y x - f c := by
  linarith

theorem gap34 (f Y : ℝ → ℝ) (c x : ℝ) (hc : f c = Y c) :
    Y x - f c = Y x - Y c := by
  rw [hc]

theorem gap35 (f Y : ℝ → ℝ) (c x : ℝ)
    (hc : f c = Y c) (h : Y x < f x) :
    f x - f c > Y x - Y c := by
  rw [hc]
  linarith

theorem gap36 (f Y : ℝ → ℝ) (c x : ℝ)
    (hcx : c < x) (h : f x - f c > Y x - Y c) :
    secantSlope f c x > secantSlope Y c x := by
  unfold secantSlope
  exact (div_lt_div_iff_of_pos_right (sub_pos.mpr hcx)).2 h

theorem gap37 (f Y : ℝ → ℝ) (c x : ℝ)
    (hcx : c < x)
    (hfc : ContinuousOn f (Set.Icc c x))
    (hYc : ContinuousOn Y (Set.Icc c x))
    (hfd : DifferentiableOn ℝ f (Set.Ioo c x))
    (hYd : DifferentiableOn ℝ Y (Set.Ioo c x))
    (hs : secantSlope f c x > secantSlope Y c x) :
    ∃ ξ ∈ Set.Ioo c x, deriv Y ξ ≤ deriv f ξ := by
  let H : ℝ → ℝ := fun t => f t - Y t
  have hHc : ContinuousOn H (Set.Icc c x) := by
    exact hfc.sub hYc
  have hHd : DifferentiableOn ℝ H (Set.Ioo c x) := by
    exact hfd.sub hYd
  have hHhas : ∀ z ∈ Set.Ioo c x, HasDerivAt H (deriv H z) z := by
    intro z hz
    exact ((hHd z hz).differentiableAt (isOpen_Ioo.mem_nhds hz)).hasDerivAt
  rcases exists_hasDerivAt_eq_slope H (fun z => deriv H z) hcx hHc hHhas with
    ⟨ξ, hξ, hξder⟩
  have hfξ : HasDerivAt f (deriv f ξ) ξ := by
    exact ((hfd ξ hξ).differentiableAt (isOpen_Ioo.mem_nhds hξ)).hasDerivAt
  have hYξ : HasDerivAt Y (deriv Y ξ) ξ := by
    exact ((hYd ξ hξ).differentiableAt (isOpen_Ioo.mem_nhds hξ)).hasDerivAt
  have hsub : HasDerivAt H (deriv f ξ - deriv Y ξ) ξ := by
    simpa [H] using hfξ.sub hYξ
  have hHder : deriv H ξ = deriv f ξ - deriv Y ξ := hsub.deriv
  have hsH : 0 < secantSlope H c x := by
    have heq : secantSlope H c x = secantSlope f c x - secantSlope Y c x := by
      unfold secantSlope
      dsimp [H]
      ring
    rw [heq]
    linarith
  have hpos : 0 < deriv H ξ := by
    rw [hξder]
    simpa [secantSlope] using hsH
  refine ⟨ξ, hξ, ?_⟩
  linarith

theorem gap38 (f : ℝ → ℝ) (x₀ K c : ℝ) :
    HasDerivAt (barrier f x₀ K) (2 * K) c := by
  simpa [barrier] using
    (hasDerivAt_const c (f x₀)).add
      (((hasDerivAt_id c).sub_const x₀).const_mul (2 * K))

theorem gap39 (f : ℝ → ℝ) (c K : ℝ)
    (h : 2 * K ≤ deriv f c) :
    deriv f c ≥ 2 * K := by
  exact h

theorem gap40 (c x₁ x₂ : ℝ) (h : c ∈ Set.Ioo x₁ x₂) :
    x₁ < c ∧ c < x₂ := by
  exact h

theorem gap41 (x₁ x₂ B₀ B : ℝ)
    (h₁ : B₀ ≤ x₁) (h₂ : x₂ ≤ B) :
    Set.Ioo x₁ x₂ ⊆ Set.Ico B₀ B := by
  intro c hc
  exact ⟨le_trans h₁ (le_of_lt hc.1), lt_of_lt_of_le hc.2 h₂⟩

theorem gap42 (c x₁ x₂ B₀ B : ℝ)
    (hc : c ∈ Set.Ioo x₁ x₂) (hsub : Set.Ioo x₁ x₂ ⊆ Set.Ico B₀ B) :
    c ∈ Set.Ico B₀ B := by
  exact hsub hc

theorem gap43 (f : ℝ → ℝ) (c K : ℝ)
    (hK : 0 < K) (h : 2 * K ≤ deriv f c) :
    K < |deriv f c| := by
  have hcpos : 0 < deriv f c := by
    linarith
  rw [abs_of_pos hcpos]
  linarith

theorem gap44 (f : ℝ → ℝ) (B₀ B c K : ℝ)
    (hbound : DerivativeBoundedOn f (Set.Ico B₀ B) K)
    (hc : c ∈ Set.Ico B₀ B) (hlarge : K < |deriv f c|) :
    False := by
  have hsmall := hbound c hc
  linarith

theorem gap45 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hlim : RightPosInf f a) :
    ¬ ∃ δ > 0, ∃ K > 0,
      DerivativeBoundedOn f (Set.Ioo a (a + δ)) K := by
  rintro ⟨δ, hδ, K, hK, hbound⟩
  let d : ℝ := min δ (b - a)
  have hd : 0 < d := lt_min hδ (sub_pos.mpr hab)
  let x₂ : ℝ := a + d / 2
  have hx₂a : a < x₂ := by
    dsimp [x₂]
    linarith
  have hx₂b : x₂ < b := by
    have hle : d ≤ b - a := min_le_right _ _
    dsimp [x₂]
    linarith
  have hx₂δ : x₂ < a + δ := by
    have hle : d ≤ δ := min_le_left _ _
    dsimp [x₂]
    linarith
  obtain ⟨x₁, hx₁, hlarge⟩ :=
    gap12 f a x₂ (f x₂ + 2 * K * (x₂ - a)) hx₂a hlim
  let Y : ℝ → ℝ := barrier f x₂ (-K)
  have hsec : secantSlope Y x₁ x₂ > secantSlope f x₁ x₂ := by
    have hden : x₂ - x₁ > 0 := sub_pos.mpr hx₁.2
    have hnum : f x₂ - f x₁ < -2 * K * (x₂ - x₁) := by
      have hx₁a : a < x₁ := hx₁.1
      nlinarith
    unfold secantSlope
    dsimp [Y, barrier]
    field_simp [ne_of_gt hden]
    nlinarith
  have hsubIcc : Set.Icc x₁ x₂ ⊆ Set.Ioo a b := by
    intro z hz
    exact ⟨lt_of_lt_of_le hx₁.1 hz.1, lt_of_le_of_lt hz.2 hx₂b⟩
  have hsubIoo : Set.Ioo x₁ x₂ ⊆ Set.Ioo a b := by
    intro z hz
    exact ⟨lt_trans hx₁.1 hz.1, lt_trans hz.2 hx₂b⟩
  have hfc : ContinuousOn f (Set.Icc x₁ x₂) :=
    (hf.mono hsubIcc).continuousOn
  have hYd : DifferentiableOn ℝ Y (Set.Ioo x₁ x₂) := by
    intro z hz
    exact (gap38 f x₂ (-K) z).differentiableAt.differentiableWithinAt
  have hYc : ContinuousOn Y (Set.Icc x₁ x₂) := by
    intro z hz
    exact (gap38 f x₂ (-K) z).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hder⟩ :=
    gap37 Y f x₁ x₂ hx₁.2 hYc hfc hYd (hf.mono hsubIoo) hsec
  have hξbound : ξ ∈ Set.Ioo a (a + δ) :=
    ⟨lt_trans hx₁.1 hξ.1, lt_trans hξ.2 hx₂δ⟩
  have hsmall := hbound ξ hξbound
  have hYder : deriv Y ξ = -2 * K := by
    simpa [Y] using (gap38 f x₂ (-K) ξ).deriv
  rw [hYder] at hder
  have hfneg : deriv f ξ < 0 := by
    linarith
  rw [abs_of_neg hfneg] at hsmall
  linarith

theorem gap46 (f : ℝ → ℝ) (A B : ℝ)
    (hAB : A < B) (hf : DifferentiableOn ℝ f (Set.Ioo A B))
    (hlim : LeftPosInf f B) :
    DerivativeUnboundedLeft f B := by
  intro δ hδ K hK
  by_contra hn
  have hbound : DerivativeBoundedOn f (Set.Ioo (B - δ) B) K := by
    intro x hx
    by_contra hle
    have hlarge : K < |deriv f x| := lt_of_not_ge hle
    exact hn ⟨x, hx, hlarge⟩
  let d : ℝ := min δ (B - A)
  have hd : 0 < d := lt_min hδ (sub_pos.mpr hAB)
  let x₁ : ℝ := B - d / 2
  have hx₁A : A < x₁ := by
    have hle : d ≤ B - A := min_le_right _ _
    dsimp [x₁]
    linarith
  have hx₁B : x₁ < B := by
    dsimp [x₁]
    linarith
  have hx₁δ : B - δ < x₁ := by
    have hle : d ≤ δ := min_le_left _ _
    dsimp [x₁]
    linarith
  let M : ℝ := f x₁ + 2 * K * (B - x₁) + 1
  have hIci : Set.Ici M ∈ (atTop : Filter ℝ) := by
    refine Filter.mem_atTop_sets.mpr ⟨M, ?_⟩
    intro y hy
    exact hy
  have he : {x : ℝ | M ≤ f x} ∈ leftFilter B := by
    have he' : f ⁻¹' Set.Ici M ∈ leftFilter B := hlim hIci
    exact he'
  rw [leftFilter, Metric.mem_nhdsWithin_iff] at he
  rcases he with ⟨ε, hε, hsub⟩
  let e : ℝ := min ε (B - x₁)
  have hepos : 0 < e := lt_min hε (sub_pos.mpr hx₁B)
  let x₂ : ℝ := B - e / 2
  have hx₂₁ : x₁ < x₂ := by
    have hle : e ≤ B - x₁ := min_le_right _ _
    dsimp [x₂]
    linarith
  have hx₂B : x₂ < B := by
    dsimp [x₂]
    linarith
  have hx₂ball : x₂ ∈ Metric.ball B ε := by
    rw [Real.mem_ball, Real.dist_eq]
    have hle : e ≤ ε := min_le_left _ _
    dsimp [x₂]
    rw [abs_of_nonpos]
    · linarith
    · linarith
  have hx₂large : M ≤ f x₂ := hsub ⟨hx₂ball, hx₂B⟩
  let Y : ℝ → ℝ := barrier f x₁ K
  have hsec : secantSlope f x₁ x₂ > secantSlope Y x₁ x₂ := by
    have hden : 0 < x₂ - x₁ := sub_pos.mpr hx₂₁
    have hnum : 2 * K * (x₂ - x₁) < f x₂ - f x₁ := by
      dsimp [M] at hx₂large
      nlinarith
    unfold secantSlope
    dsimp [Y, barrier]
    field_simp [ne_of_gt hden]
    nlinarith
  have hsubIcc : Set.Icc x₁ x₂ ⊆ Set.Ioo A B := by
    intro z hz
    exact ⟨lt_of_lt_of_le hx₁A hz.1, lt_of_le_of_lt hz.2 hx₂B⟩
  have hsubIoo : Set.Ioo x₁ x₂ ⊆ Set.Ioo A B := by
    intro z hz
    exact ⟨lt_trans hx₁A hz.1, lt_trans hz.2 hx₂B⟩
  have hfc : ContinuousOn f (Set.Icc x₁ x₂) :=
    (hf.mono hsubIcc).continuousOn
  have hYd : DifferentiableOn ℝ Y (Set.Ioo x₁ x₂) := by
    intro z hz
    exact (gap38 f x₁ K z).differentiableAt.differentiableWithinAt
  have hYc : ContinuousOn Y (Set.Icc x₁ x₂) := by
    intro z hz
    exact (gap38 f x₁ K z).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hder⟩ :=
    gap37 f Y x₁ x₂ hx₂₁ hfc hYc (hf.mono hsubIoo) hYd hsec
  have hξbound : ξ ∈ Set.Ioo (B - δ) B :=
    ⟨lt_trans hx₁δ hξ.1, lt_trans hξ.2 hx₂B⟩
  have hsmall := hbound ξ hξbound
  have hYder : deriv Y ξ = 2 * K := by
    simpa [Y] using (gap38 f x₁ K ξ).deriv
  rw [hYder] at hder
  have hfpos : 0 < deriv f ξ := by
    linarith
  rw [abs_of_pos hfpos] at hsmall
  linarith

theorem gap47 (f : ℝ → ℝ) (A B : ℝ)
    (hAB : A < B) (hf : DifferentiableOn ℝ f (Set.Ioo A B))
    (hlim : LeftPosInf f B) :
    DerivativeUnboundedLeft f B := by
  exact gap46 f A B hAB hf hlim

theorem gap48 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hlim : RightPosInf f a) :
    DerivativeUnboundedRight f a := by
  intro δ hδ K hK
  by_contra hn
  have hbound : DerivativeBoundedOn f (Set.Ioo a (a + δ)) K := by
    intro x hx
    by_contra hle
    have hlarge : K < |deriv f x| := lt_of_not_ge hle
    exact hn ⟨x, hx, hlarge⟩
  exact gap45 f a b hab hf hlim ⟨δ, hδ, K, hK, hbound⟩

theorem gap49 (f : ℝ → ℝ) (a b : ℝ)
    (hab : a < b) (hf : DifferentiableOn ℝ f (Set.Ioo a b))
    (hlim : RightPosInf f a) :
    DerivativeUnboundedRight f a := by
  exact gap48 f a b hab hf hlim

end

end ProofGap.Exercise1019_2
