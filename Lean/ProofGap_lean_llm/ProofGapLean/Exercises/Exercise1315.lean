import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity

namespace ProofGap.Exercise1315

noncomputable section

open Filter
open scoped Topology

def localParameter (x x₀ δ : ℝ) : ℝ :=
  |x - x₀| / δ

def increment (f : ℝ → ℝ) (x₀ h : ℝ) : ℝ :=
  f (x₀ + h) - f x₀

def secant (f : ℝ → ℝ) (x₀ h : ℝ) : ℝ :=
  increment f x₀ h / h

def HasFiniteRightSlopeAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (secant f x₀) (nhdsWithin 0 (Set.Ioi 0)) (nhds L)

def HasFiniteLeftSlopeAt (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ L : ℝ, Tendsto (secant f x₀) (nhdsWithin 0 (Set.Iio 0)) (nhds L)

private theorem convexOn_reflect (f : ℝ → ℝ) (a b : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f) :
    ConvexOn ℝ (Set.Ioo (-b) (-a)) (fun x => f (-x)) := by
  refine ⟨convex_Ioo _ _, ?_⟩
  intro x hx y hy s t hs ht hst
  have hx' : -x ∈ Set.Ioo a b :=
    ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hy' : -y ∈ Set.Ioo a b :=
    ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hc := hconv.2 hx' hy' hs ht hst
  have heq : -(s • x + t • y) = s • (-x) + t • (-y) := by
    simp [smul_eq_mul]
    ring
  change f (-(s • x + t • y)) ≤ s • f (-x) + t • f (-y)
  rw [heq]
  exact hc

private theorem tendsto_neg_left_zero :
    Tendsto (fun x : ℝ => -x) (nhdsWithin 0 (Set.Iio 0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
  · have hc : ContinuousAt (fun x : ℝ => -x) 0 := continuousAt_id.neg
    simpa using hc.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact neg_pos.mpr (show x < 0 from hx)

private theorem leftSlope_of_reflected_right (f : ℝ → ℝ) (x₀ L : ℝ)
    (h : Tendsto (secant (fun x => f (-x)) (-x₀))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds L)) :
    Tendsto (secant f x₀) (nhdsWithin 0 (Set.Iio 0)) (nhds (-L)) := by
  have hin := h.comp tendsto_neg_left_zero
  have hn : ContinuousAt (fun z : ℝ => -z) L := continuousAt_id.neg
  have ht := hn.tendsto.comp hin
  apply ht.congr'
  filter_upwards [] with z
  simp [Function.comp_apply, secant, increment]
  ring

private theorem tendsto_sub_right (x₀ : ℝ) :
    Tendsto (fun x : ℝ => x - x₀)
      (nhdsWithin x₀ (Set.Ioi x₀)) (nhdsWithin 0 (Set.Ioi 0)) := by
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
  · have hc : ContinuousAt (fun x : ℝ => x - x₀) x₀ :=
      continuousAt_id.sub continuousAt_const
    simpa using hc.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact sub_pos.mpr (show x₀ < x from hx)

private theorem tendsto_sub_left (x₀ : ℝ) :
    Tendsto (fun x : ℝ => x - x₀)
      (nhdsWithin x₀ (Set.Iio x₀)) (nhdsWithin 0 (Set.Iio 0)) := by
  refine tendsto_inf.2 ⟨?_, tendsto_principal.2 ?_⟩
  · have hc : ContinuousAt (fun x : ℝ => x - x₀) x₀ :=
      continuousAt_id.sub continuousAt_const
    simpa using hc.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact sub_neg.mpr (show x < x₀ from hx)

theorem gap1 (x x₀ δ : ℝ) (hδ : 0 < δ)
    (hx : 0 < |x - x₀|) :
    0 < localParameter x x₀ δ := by
  unfold localParameter
  exact div_pos hx hδ

theorem gap2 (x x₀ δ : ℝ) (hδ : 0 < δ)
    (hx : |x - x₀| < δ) :
    localParameter x x₀ δ < 1 := by
  unfold localParameter
  exact (div_lt_one hδ).2 hx

theorem gap3 : (0 : ℝ) < 1 := by
  norm_num

theorem gap4 (x x₀ δ : ℝ) (hδ : 0 < δ)
    (hx : x₀ < x) :
    x = localParameter x x₀ δ * (x₀ + δ) +
      (1 - localParameter x x₀ δ) * x₀ := by
  unfold localParameter
  rw [abs_of_pos (sub_pos.mpr hx)]
  have hδ0 : δ ≠ 0 := ne_of_gt hδ
  field_simp [hδ0]
  ring

theorem gap5 (x x₀ δ : ℝ) (hδ : 0 < δ)
    (hx : x₀ < x) :
    x₀ =
      (1 / (1 + localParameter x x₀ δ)) * x +
      (localParameter x x₀ δ / (1 + localParameter x x₀ δ)) *
        (x₀ - δ) := by
  let t := localParameter x x₀ δ
  have ht : 0 < t := by
    apply gap1 x x₀ δ hδ
    rw [abs_pos]
    exact ne_of_gt (sub_pos.mpr hx)
  have hden : 1 + t ≠ 0 := ne_of_gt (by linarith)
  have hg : x = t * (x₀ + δ) + (1 - t) * x₀ := by
    simpa [t] using gap4 x x₀ δ hδ hx
  change x₀ = (1 / (1 + t)) * x + (t / (1 + t)) * (x₀ - δ)
  calc
    x₀ = (x + t * (x₀ - δ)) / (1 + t) := by
      apply (eq_div_iff hden).2
      nlinarith [hg]
    _ = (1 / (1 + t)) * x + (t / (1 + t)) * (x₀ - δ) := by
      ring

theorem gap6 (f : ℝ → ℝ) (a b x x₀ δ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b)
    (hδ : 0 < δ) (hx0 : x₀ < x) (hx1 : x < x₀ + δ) :
    f x ≤
      localParameter x x₀ δ * f (x₀ + δ) +
        (1 - localParameter x x₀ δ) * f x₀ := by
  let t := localParameter x x₀ δ
  have habs : |x - x₀| < δ := by
    rw [abs_of_pos (sub_pos.mpr hx0)]
    linarith
  have ht0 : 0 ≤ t :=
    le_of_lt (gap1 x x₀ δ hδ (abs_pos.mpr (ne_of_gt (sub_pos.mpr hx0))))
  have ht1 : t ≤ 1 := le_of_lt (gap2 x x₀ δ hδ habs)
  have hp : x₀ + δ ∈ Set.Ioo a b := hsub ⟨by linarith, le_rfl⟩
  have hq : x₀ ∈ Set.Ioo a b := hsub ⟨by linarith, by linarith⟩
  have hc := hconv.2 hp hq ht0 (sub_nonneg.mpr ht1) (by ring)
  have heq := gap4 x x₀ δ hδ hx0
  calc
    f x = f (t * (x₀ + δ) + (1 - t) * x₀) := by
      simpa [t] using congrArg f heq
    _ ≤ t * f (x₀ + δ) + (1 - t) * f x₀ := by
      simpa [smul_eq_mul] using hc

theorem gap7 (f : ℝ → ℝ) (x₀ δ B t : ℝ)
    (ht : 0 ≤ t)
    (hB : f (x₀ + δ) ≤ B) :
    t * f (x₀ + δ) + (1 - t) * f x₀ ≤
      t * B + (1 - t) * f x₀ := by
  simpa [add_comm] using
    add_le_add_right (mul_le_mul_of_nonneg_left hB ht) ((1 - t) * f x₀)

theorem gap8 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (h1 : f x ≤
      localParameter x x₀ δ * f (x₀ + δ) +
        (1 - localParameter x x₀ δ) * f x₀)
    (ht : 0 ≤ localParameter x x₀ δ)
    (hB : f (x₀ + δ) ≤ B) :
    f x ≤ localParameter x x₀ δ * B +
      (1 - localParameter x x₀ δ) * f x₀ := by
  exact h1.trans (gap7 f x₀ δ B (localParameter x x₀ δ) ht hB)

theorem gap9 (f : ℝ → ℝ) (a b x x₀ δ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b)
    (hδ : 0 < δ) (hx0 : x₀ < x) (hx1 : x < x₀ + δ) :
    f x₀ ≤
      (1 / (1 + localParameter x x₀ δ)) * f x +
      (localParameter x x₀ δ / (1 + localParameter x x₀ δ)) *
        f (x₀ - δ) := by
  let t := localParameter x x₀ δ
  have ht : 0 < t :=
    gap1 x x₀ δ hδ (abs_pos.mpr (ne_of_gt (sub_pos.mpr hx0)))
  have hden : 0 < 1 + t := by linarith
  have hxmem : x ∈ Set.Ioo a b := hsub ⟨by linarith, by linarith⟩
  have hlmem : x₀ - δ ∈ Set.Ioo a b := hsub ⟨le_rfl, by linarith⟩
  have hw0 : 0 ≤ 1 / (1 + t) := by positivity
  have hw1 : 0 ≤ t / (1 + t) := by positivity
  have hsum : 1 / (1 + t) + t / (1 + t) = 1 := by
    field_simp [ne_of_gt hden]
  have hc := hconv.2 hxmem hlmem hw0 hw1 hsum
  have heq := gap5 x x₀ δ hδ hx0
  calc
    f x₀ = f ((1 / (1 + t)) * x + (t / (1 + t)) * (x₀ - δ)) := by
      simpa [t] using congrArg f heq
    _ ≤ (1 / (1 + t)) * f x + (t / (1 + t)) * f (x₀ - δ) := by
      simpa [smul_eq_mul] using hc

theorem gap10 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (hB : f (x₀ - δ) ≤ B)
    (ht : 0 ≤ localParameter x x₀ δ) :
    (f x + localParameter x x₀ δ * f (x₀ - δ)) /
        (1 + localParameter x x₀ δ) ≤
      (f x + localParameter x x₀ δ * B) /
        (1 + localParameter x x₀ δ) := by
  have hd : 0 < 1 + localParameter x x₀ δ := by linarith
  apply (div_le_div_iff_of_pos_right hd).2
  simpa [add_comm] using
    add_le_add_left (mul_le_mul_of_nonneg_left hB ht) (f x)

theorem gap11 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (hlower : f x₀ ≤
      (f x + localParameter x x₀ δ * f (x₀ - δ)) /
        (1 + localParameter x x₀ δ))
    (hupper :
      (f x + localParameter x x₀ δ * f (x₀ - δ)) /
          (1 + localParameter x x₀ δ) ≤
        (f x + localParameter x x₀ δ * B) /
          (1 + localParameter x x₀ δ)) :
    f x₀ ≤
      (f x + localParameter x x₀ δ * B) /
        (1 + localParameter x x₀ δ) := by
  exact hlower.trans hupper

theorem gap12 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (ht : 0 ≤ localParameter x x₀ δ)
    (h : f x₀ ≤
      (f x + localParameter x x₀ δ * B) /
        (1 + localParameter x x₀ δ)) :
    -(localParameter x x₀ δ) * (B - f x₀) ≤
      f x - f x₀ := by
  have hd : 0 < 1 + localParameter x x₀ δ := by linarith
  have hm := (le_div_iff₀ hd).1 h
  nlinarith

theorem gap13 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (h : f x ≤ localParameter x x₀ δ * B +
      (1 - localParameter x x₀ δ) * f x₀) :
    f x - f x₀ ≤
      localParameter x x₀ δ * (B - f x₀) := by
  nlinarith

theorem gap14 (f : ℝ → ℝ) (x₀ B : ℝ)
    (hB : f x₀ ≤ B) :
    0 ≤ B - f x₀ := by
  linarith

theorem gap15 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (hlower : -(localParameter x x₀ δ) * (B - f x₀) ≤
      f x - f x₀)
    (hupper : f x - f x₀ ≤
      localParameter x x₀ δ * (B - f x₀))
    (hnonneg : 0 ≤
      localParameter x x₀ δ * (B - f x₀)) :
    |f x - f x₀| ≤
      localParameter x x₀ δ * (B - f x₀) := by
  apply abs_le.mpr
  constructor
  · simpa only [neg_mul] using hlower
  · exact hupper

theorem gap16 (f : ℝ → ℝ) (x x₀ δ B : ℝ) :
    localParameter x x₀ δ * (B - f x₀) =
      ((B - f x₀) / δ) * |x - x₀| := by
  unfold localParameter
  ring

theorem gap17 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (h : |f x - f x₀| ≤
      localParameter x x₀ δ * (B - f x₀)) :
    |f x - f x₀| ≤
      ((B - f x₀) / δ) * |x - x₀| := by
  rw [gap16 f x x₀ δ B] at h
  exact h

theorem gap18 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (hlower : -(localParameter x x₀ δ) * (B - f x₀) ≤
      f x - f x₀)
    (hupper : f x - f x₀ ≤
      localParameter x x₀ δ * (B - f x₀))
    (hnonneg : 0 ≤
      localParameter x x₀ δ * (B - f x₀)) :
    |f x - f x₀| ≤
      localParameter x x₀ δ * (B - f x₀) := by
  exact gap15 f x x₀ δ B hlower hupper hnonneg

theorem gap19 (f : ℝ → ℝ) (x x₀ δ B : ℝ) :
    localParameter x x₀ δ * (B - f x₀) =
      ((B - f x₀) / δ) * |x - x₀| := by
  exact gap16 f x x₀ δ B

theorem gap20 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (h : |f x - f x₀| ≤
      localParameter x x₀ δ * (B - f x₀)) :
    |f x - f x₀| ≤
      ((B - f x₀) / δ) * |x - x₀| := by
  exact gap17 f x x₀ δ B h

theorem gap21 (f : ℝ → ℝ) (x x₀ δ B : ℝ)
    (hlower : -(localParameter x x₀ δ) * (B - f x₀) ≤
      f x - f x₀)
    (hupper : f x - f x₀ ≤
      localParameter x x₀ δ * (B - f x₀))
    (hnonneg : 0 ≤
      localParameter x x₀ δ * (B - f x₀)) :
    |f x - f x₀| ≤
      localParameter x x₀ δ * (B - f x₀) := by
  exact gap15 f x x₀ δ B hlower hupper hnonneg

theorem gap22 (f : ℝ → ℝ) (x x₀ δ B : ℝ) :
    localParameter x x₀ δ * (B - f x₀) =
      ((B - f x₀) / δ) * |x - x₀| := by
  exact gap16 f x x₀ δ B

theorem gap23 (f : ℝ → ℝ) (a b x x₀ δ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b)
    (hδ : 0 < δ) (hx : x ∈ Set.Ioo (x₀ - δ) (x₀ + δ)) :
    let B := max (f (x₀ - δ)) (f (x₀ + δ))
    |f x - f x₀| ≤
      ((B - f x₀) / δ) * |x - x₀| := by
  dsimp
  let B := max (f (x₀ - δ)) (f (x₀ + δ))
  have hleft : x₀ - δ ∈ Set.Ioo a b := hsub ⟨le_rfl, by linarith⟩
  have hright : x₀ + δ ∈ Set.Ioo a b := hsub ⟨by linarith, le_rfl⟩
  have hj := hconv.2 hleft hright
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid : f x₀ ≤ (1 / 2 : ℝ) * f (x₀ - δ) +
      (1 / 2 : ℝ) * f (x₀ + δ) := by
    convert hj using 1 <;> simp [smul_eq_mul] <;> ring
  have hB0 : f x₀ ≤ B := by
    have hl : f (x₀ - δ) ≤ B := le_max_left _ _
    have hr : f (x₀ + δ) ≤ B := le_max_right _ _
    nlinarith
  have right_bound : ∀ (g : ℝ → ℝ) (c d y y₀ K : ℝ),
      ConvexOn ℝ (Set.Ioo c d) g →
      Set.Icc (y₀ - δ) (y₀ + δ) ⊆ Set.Ioo c d →
      y₀ < y → y < y₀ + δ →
      g (y₀ - δ) ≤ K → g (y₀ + δ) ≤ K → g y₀ ≤ K →
      |g y - g y₀| ≤ ((K - g y₀) / δ) * |y - y₀| := by
    intro g c d y y₀ K hg hs hy0 hy1 hKl hKr hK0
    have ht : 0 ≤ localParameter y y₀ δ :=
      le_of_lt (gap1 y y₀ δ hδ
        (abs_pos.mpr (ne_of_gt (sub_pos.mpr hy0))))
    have hu0 := gap6 g c d y y₀ δ hg hs hδ hy0 hy1
    have hu1 := gap8 g y y₀ δ K hu0 ht hKr
    have hu := gap13 g y y₀ δ K hu1
    have hv0 := gap9 g c d y y₀ δ hg hs hδ hy0 hy1
    have hd : 0 < 1 + localParameter y y₀ δ := by linarith
    have hv1 : g y₀ ≤
        (g y + localParameter y y₀ δ * g (y₀ - δ)) /
          (1 + localParameter y y₀ δ) := by
      calc
        g y₀ ≤ (1 / (1 + localParameter y y₀ δ)) * g y +
            (localParameter y y₀ δ / (1 + localParameter y y₀ δ)) *
              g (y₀ - δ) := hv0
        _ = (g y + localParameter y y₀ δ * g (y₀ - δ)) /
            (1 + localParameter y y₀ δ) := by
              ring
    have hv2 := gap10 g y y₀ δ K hKl ht
    have hv3 := gap11 g y y₀ δ K hv1 hv2
    have hlower := gap12 g y y₀ δ K ht hv3
    have hn : 0 ≤ localParameter y y₀ δ * (K - g y₀) :=
      mul_nonneg ht (sub_nonneg.mpr hK0)
    exact gap17 g y y₀ δ K (gap15 g y y₀ δ K hlower hu hn)
  rcases lt_trichotomy x x₀ with hlt | heq | hgt
  · let g : ℝ → ℝ := fun y => f (-y)
    have hg : ConvexOn ℝ (Set.Ioo (-b) (-a)) g :=
      convexOn_reflect f a b hconv
    have hs : Set.Icc (-x₀ - δ) (-x₀ + δ) ⊆ Set.Ioo (-b) (-a) := by
      intro y hy
      have hny : -y ∈ Set.Icc (x₀ - δ) (x₀ + δ) := by
        constructor <;> linarith [hy.1, hy.2]
      have hm := hsub hny
      exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
    have hr := right_bound g (-b) (-a) (-x) (-x₀) B hg hs
      (by linarith) (by linarith [hx.1])
      (by
        dsimp only [g]
        convert (le_max_right (f (x₀ - δ)) (f (x₀ + δ))) using 1 <;> ring)
      (by
        dsimp only [g]
        convert (le_max_left (f (x₀ - δ)) (f (x₀ + δ))) using 1 <;> ring)
      (by simpa [g] using hB0)
    simp only [g, neg_neg, sub_neg_eq_add] at hr
    have habs : |-x + x₀| = |x - x₀| := by
      have he : -x + x₀ = -(x - x₀) := by ring
      rw [he, abs_neg]
    rw [habs] at hr
    exact hr
  · subst x
    simp
  · exact right_bound f a b x x₀ B hconv hsub hgt hx.2
      (le_max_left _ _) (le_max_right _ _) hB0

theorem gap24 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    Tendsto f (nhds x₀) (nhds (f x₀)) := by
  exact (hconv.continuousOn isOpen_Ioo).continuousAt
    (isOpen_Ioo.mem_nhds hx₀)

theorem gap25 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ContinuousAt f x₀ := by
  exact gap24 f a b x₀ hconv hx₀

theorem gap26 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧
      ∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 → |secant f x₀ h| ≤ C := by
  let δ : ℝ := min (x₀ - a) (b - x₀) / 2
  have hda : 0 < x₀ - a := by linarith [hx₀.1]
  have hdb : 0 < b - x₀ := by linarith [hx₀.2]
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hdleft : δ < x₀ - a := by
    dsimp [δ]
    have hm := min_le_left (x₀ - a) (b - x₀)
    nlinarith
  have hdright : δ < b - x₀ := by
    dsimp [δ]
    have hm := min_le_right (x₀ - a) (b - x₀)
    nlinarith
  have hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2]
  let B := max (f (x₀ - δ)) (f (x₀ + δ))
  have hleft := hsub (show x₀ - δ ∈ Set.Icc (x₀ - δ) (x₀ + δ) by
    constructor <;> linarith)
  have hright := hsub (show x₀ + δ ∈ Set.Icc (x₀ - δ) (x₀ + δ) by
    constructor <;> linarith)
  have hj := hconv.2 hleft hright
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hmid : f x₀ ≤ (1 / 2 : ℝ) * f (x₀ - δ) +
      (1 / 2 : ℝ) * f (x₀ + δ) := by
    convert hj using 1 <;> simp [smul_eq_mul] <;> ring
  have hB0 : f x₀ ≤ B := by
    have hl : f (x₀ - δ) ≤ B := le_max_left _ _
    have hr : f (x₀ + δ) ≤ B := le_max_right _ _
    nlinarith
  let C := (B - f x₀) / δ
  refine ⟨δ, C, hδ, ?_, ?_⟩
  · exact div_nonneg (sub_nonneg.mpr hB0) (le_of_lt hδ)
  · intro h hh hne
    have hx : x₀ + h ∈ Set.Ioo (x₀ - δ) (x₀ + δ) := by
      constructor <;> linarith [hh.1, hh.2]
    have hlip := gap23 f a b (x₀ + h) x₀ δ hconv hsub hδ hx
    have habsh : 0 < |h| := abs_pos.mpr hne
    rw [secant, increment, abs_div]
    apply (div_le_iff₀ habsh).2
    simpa [C, B, abs_sub_comm, mul_comm, mul_left_comm, mul_assoc] using hlip

theorem gap27 (f : ℝ → ℝ) (a b x₀ δ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b) :
    ConvexOn ℝ (Set.Icc (-δ) δ) (increment f x₀) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro u hu v hv s t hs ht hst
  have hu' : x₀ + u ∈ Set.Icc (x₀ - δ) (x₀ + δ) := by
    constructor <;> linarith [hu.1, hu.2]
  have hv' : x₀ + v ∈ Set.Icc (x₀ - δ) (x₀ + δ) := by
    constructor <;> linarith [hv.1, hv.2]
  have hc := hconv.2 (hsub hu') (hsub hv') hs ht hst
  simp only [smul_eq_mul] at hc ⊢
  have hxcoef : x₀ = s * x₀ + t * x₀ := by
    calc
      x₀ = (s + t) * x₀ := by simp [hst]
      _ = s * x₀ + t * x₀ := by ring
  have hfcoef : f x₀ = s * f x₀ + t * f x₀ := by
    calc
      f x₀ = (s + t) * f x₀ := by simp [hst]
      _ = s * f x₀ + t * f x₀ := by ring
  have heq : x₀ + (s * u + t * v) =
      s * (x₀ + u) + t * (x₀ + v) := by
    calc
      x₀ + (s * u + t * v) =
          (s * x₀ + t * x₀) + (s * u + t * v) := by rw [← hxcoef]
      _ = s * (x₀ + u) + t * (x₀ + v) := by ring
  have hweighted :
      (s * f (x₀ + u) + t * f (x₀ + v)) - f x₀ =
        s * (f (x₀ + u) - f x₀) +
          t * (f (x₀ + v) - f x₀) := by
    calc
      (s * f (x₀ + u) + t * f (x₀ + v)) - f x₀ =
          (s * f (x₀ + u) + t * f (x₀ + v)) -
            (s * f x₀ + t * f x₀) :=
        congrArg (fun z => (s * f (x₀ + u) + t * f (x₀ + v)) - z) hfcoef
      _ = s * (f (x₀ + u) - f x₀) +
          t * (f (x₀ + v) - f x₀) := by ring
  change f (x₀ + (s * u + t * v)) - f x₀ ≤
    s * (f (x₀ + u) - f x₀) + t * (f (x₀ + v) - f x₀)
  rw [heq]
  calc
    f (s * (x₀ + u) + t * (x₀ + v)) - f x₀ ≤
        (s * f (x₀ + u) + t * f (x₀ + v)) - f x₀ :=
      sub_le_sub_right hc (f x₀)
    _ = s * (f (x₀ + u) - f x₀) +
        t * (f (x₀ + v) - f x₀) := hweighted

theorem gap28 (f : ℝ → ℝ) (x₀ : ℝ) :
    increment f x₀ 0 = 0 := by
  simp [increment]

theorem gap29 (t₁ t₂ : ℝ) (h₁ : 0 < t₁) (h12 : t₁ < t₂) :
    t₁ = (t₁ / t₂) * t₂ + (1 - t₁ / t₂) * 0 := by
  have ht₂ : t₂ ≠ 0 := ne_of_gt (lt_trans h₁ h12)
  field_simp [ht₂]
  ring

theorem gap30 (φ : ℝ → ℝ) (δ t₁ t₂ : ℝ)
    (hconv : ConvexOn ℝ (Set.Icc 0 δ) φ)
    (hφ0 : φ 0 = 0) (h₁ : 0 < t₁) (h12 : t₁ < t₂)
    (h₂ : t₂ ≤ δ) :
    φ t₁ ≤ (t₁ / t₂) * φ t₂ +
      (1 - t₁ / t₂) * φ 0 := by
  have ht₂ : 0 < t₂ := lt_trans h₁ h12
  have hw0 : 0 ≤ t₁ / t₂ := div_nonneg (le_of_lt h₁) (le_of_lt ht₂)
  have hw1 : 0 ≤ 1 - t₁ / t₂ := by
    apply sub_nonneg.mpr
    exact (div_le_one ht₂).2 (le_of_lt h12)
  have h0 : (0 : ℝ) ∈ Set.Icc 0 δ := by constructor <;> linarith
  have htm : t₂ ∈ Set.Icc 0 δ := ⟨le_of_lt ht₂, h₂⟩
  have hc := hconv.2 htm h0 hw0 hw1 (show t₁ / t₂ + (1 - t₁ / t₂) = 1 by ring)
  have heq := gap29 t₁ t₂ h₁ h12
  calc
    φ t₁ = φ ((t₁ / t₂) * t₂ + (1 - t₁ / t₂) * 0) := by
      simpa using congrArg φ heq
    _ ≤ (t₁ / t₂) * φ t₂ + (1 - t₁ / t₂) * φ 0 := by
      simpa [smul_eq_mul] using hc

theorem gap31 (φ : ℝ → ℝ) (t₁ t₂ : ℝ)
    (hφ0 : φ 0 = 0) :
    (t₁ / t₂) * φ t₂ + (1 - t₁ / t₂) * φ 0 =
      (t₁ / t₂) * φ t₂ := by
  rw [hφ0]
  ring

theorem gap32 (φ : ℝ → ℝ) (t₁ t₂ : ℝ)
    (h : φ t₁ ≤ (t₁ / t₂) * φ t₂) :
    φ t₁ ≤ (t₁ / t₂) * φ t₂ := by
  exact h

theorem gap33 (φ : ℝ → ℝ) (t₁ t₂ : ℝ)
    (h₁ : 0 < t₁) (h12 : t₁ < t₂)
    (h : φ t₁ ≤ (t₁ / t₂) * φ t₂) :
    φ t₁ / t₁ ≤ φ t₂ / t₂ := by
  have ht₂ : 0 < t₂ := lt_trans h₁ h12
  have h' : φ t₁ ≤ (t₁ * φ t₂) / t₂ := by
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using h
  have hcross : φ t₁ * t₂ ≤ t₁ * φ t₂ :=
    (le_div_iff₀ ht₂).1 h'
  exact (div_le_div_iff₀ h₁ ht₂).2
    (by simpa [mul_comm] using hcross)

theorem gap34 (f : ℝ → ℝ) (a b x₀ δ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b) :
    MonotoneOn (secant f x₀) (Set.Ioo 0 δ) := by
  intro t₁ ht₁ t₂ ht₂ h12
  rcases eq_or_lt_of_le h12 with rfl | hlt
  · exact le_rfl
  · have hinc := gap27 f a b x₀ δ hconv hsub
    have hmono : ConvexOn ℝ (Set.Icc 0 δ) (increment f x₀) := by
      refine ⟨convex_Icc _ _, ?_⟩
      intro u hu v hv s t hs ht hst
      exact hinc.2
        ⟨by linarith [hu.1, hu.2], hu.2⟩
        ⟨by linarith [hv.1, hv.2], hv.2⟩
        hs ht hst
    have hc := gap30 (increment f x₀) δ t₁ t₂ hmono
      (gap28 f x₀) ht₁.1 hlt (le_of_lt ht₂.2)
    have hc' : increment f x₀ t₁ ≤
        (t₁ / t₂) * increment f x₀ t₂ := by
      simpa [gap28 f x₀] using hc
    exact gap33 (increment f x₀) t₁ t₂ ht₁.1 hlt hc'

theorem gap35 (f : ℝ → ℝ) (a b x₀ δ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b) :
    MonotoneOn (secant f x₀) (Set.Ioo (-δ) 0) := by
  let g : ℝ → ℝ := fun y => f (-y)
  have hg : ConvexOn ℝ (Set.Ioo (-b) (-a)) g :=
    convexOn_reflect f a b hconv
  have hs : Set.Icc (-x₀ - δ) (-x₀ + δ) ⊆ Set.Ioo (-b) (-a) := by
    intro y hy
    have hm := hsub (show -y ∈ Set.Icc (x₀ - δ) (x₀ + δ) by
      constructor <;> linarith [hy.1, hy.2])
    exact ⟨by linarith [hm.2], by linarith [hm.1]⟩
  have hm := gap34 g (-b) (-a) (-x₀) δ hg hs
  intro h₁ hh₁ h₂ hh₂ h12
  have hk₁ : -h₂ ∈ Set.Ioo 0 δ := by
    constructor <;> linarith [hh₂.1, hh₂.2]
  have hk₂ : -h₁ ∈ Set.Ioo 0 δ := by
    constructor <;> linarith [hh₁.1, hh₁.2]
  have hle := hm hk₁ hk₂ (by linarith)
  have heq (h : ℝ) : secant g (-x₀) (-h) = -secant f x₀ h := by
    simp [g, secant, increment]
    ring_nf
  rw [heq h₂, heq h₁] at hle
  linarith

theorem gap36 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 → |secant f x₀ h| ≤ C := by
  rcases gap26 f a b x₀ hconv hx₀ with ⟨δ, C, hδ, hC, hbound⟩
  exact ⟨δ, C, hδ, hbound⟩

theorem gap37 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ δ C : ℝ, 0 < δ ∧
      ∀ h ∈ Set.Ioo (-δ) δ \ {0}, |secant f x₀ h| ≤ C := by
  rcases gap36 f a b x₀ hconv hx₀ with ⟨δ, C, hδ, hbound⟩
  refine ⟨δ, C, hδ, ?_⟩
  intro h hh
  have hi : h ∈ Set.Ioo (-δ) δ := hh.1
  have hn : h ≠ 0 := by
    intro heq
    apply hh.2
    simpa [heq]
  exact hbound h hi hn

theorem gap38 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    HasFiniteRightSlopeAt f x₀ := by
  rcases gap36 f a b x₀ hconv hx₀ with ⟨δ₀, C, hδ₀, hbound₀⟩
  let ρ : ℝ := min (x₀ - a) (b - x₀) / 2
  have hxa : 0 < x₀ - a := by linarith [hx₀.1]
  have hxb : 0 < b - x₀ := by linarith [hx₀.2]
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  let δ : ℝ := min δ₀ ρ
  have hδ : 0 < δ := lt_min hδ₀ hρ
  have hδ₀' : δ ≤ δ₀ := min_le_left _ _
  have hδρ : δ ≤ ρ := min_le_right _ _
  have hρa : ρ ≤ (x₀ - a) / 2 := by
    dsimp [ρ]
    have hm := min_le_left (x₀ - a) (b - x₀)
    nlinarith
  have hρb : ρ ≤ (b - x₀) / 2 := by
    dsimp [ρ]
    have hm := min_le_right (x₀ - a) (b - x₀)
    nlinarith
  have hsub : Set.Icc (x₀ - δ) (x₀ + δ) ⊆ Set.Ioo a b := by
    intro y hy
    constructor <;> linarith [hy.1, hy.2, hδρ, hρa, hρb]
  have hbound : ∀ h ∈ Set.Ioo (-δ) δ, h ≠ 0 →
      |secant f x₀ h| ≤ C := by
    intro h hh hn
    apply hbound₀ h _ hn
    constructor <;> linarith [hh.1, hh.2, hδ₀']
  have hmono := gap34 f a b x₀ δ hconv hsub
  let S : Set ℝ := secant f x₀ '' Set.Ioo 0 δ
  have hSne : S.Nonempty := by
    refine ⟨secant f x₀ (δ / 2), ⟨δ / 2, ?_, rfl⟩⟩
    constructor <;> linarith
  have hSbdd : BddBelow S := by
    refine ⟨-C, ?_⟩
    intro z hz
    rcases hz with ⟨h, hh, rfl⟩
    have hb := hbound h ⟨by linarith [hh.1], hh.2⟩ (ne_of_gt hh.1)
    exact neg_le_of_abs_le hb
  refine ⟨sInf S, ?_⟩
  rw [tendsto_def]
  intro U hU
  rcases Metric.mem_nhds_iff.1 hU with ⟨ε, hε, hball⟩
  have hz : ∃ z ∈ S, z < sInf S + ε := by
    by_contra hn
    have hall : ∀ z ∈ S, sInf S + ε ≤ z := by
      intro z hz
      exact le_of_not_gt (fun hlt => hn ⟨z, hz, hlt⟩)
    have hi := le_csInf hSne hall
    linarith
  rcases hz with ⟨z, hzS, hzlt⟩
  rcases hzS with ⟨h, hh, rfl⟩
  have hevlt : ∀ᶠ y in 𝓝[>] (0 : ℝ), y < h :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hh.1)
  filter_upwards [self_mem_nhdsWithin, hevlt] with y hy hyh
  apply hball
  rw [Metric.mem_ball, Real.dist_eq]
  have hyI : y ∈ Set.Ioo 0 δ := ⟨hy, lt_trans hyh hh.2⟩
  have hleinf : sInf S ≤ secant f x₀ y :=
    csInf_le hSbdd ⟨y, hyI, rfl⟩
  have hymono : secant f x₀ y ≤ secant f x₀ h :=
    hmono hyI hh (le_of_lt hyh)
  rw [abs_of_nonneg (sub_nonneg.mpr hleinf)]
  linarith

theorem gap39 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ L : ℝ, Tendsto
      (fun x => (f x - f x₀) / (x - x₀))
      (nhdsWithin x₀ (Set.Ioi x₀)) (nhds L) := by
  rcases gap38 f a b x₀ hconv hx₀ with ⟨L, hL⟩
  refine ⟨L, ?_⟩
  have ht := hL.comp (tendsto_sub_right x₀)
  apply ht.congr'
  filter_upwards [] with x
  simp [Function.comp_apply, secant, increment]

theorem gap40 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ∃ L : ℝ, Tendsto
      (fun x => (f x - f x₀) / (x - x₀))
      (nhdsWithin x₀ (Set.Iio x₀)) (nhds L) := by
  let g : ℝ → ℝ := fun y => f (-y)
  have hg : ConvexOn ℝ (Set.Ioo (-b) (-a)) g :=
    convexOn_reflect f a b hconv
  have hxg : -x₀ ∈ Set.Ioo (-b) (-a) :=
    ⟨by linarith [hx₀.2], by linarith [hx₀.1]⟩
  rcases gap38 g (-b) (-a) (-x₀) hg hxg with ⟨L, hL⟩
  have hleft : Tendsto (secant f x₀) (nhdsWithin 0 (Set.Iio 0))
      (nhds (-L)) := leftSlope_of_reflected_right f x₀ L hL
  refine ⟨-L, ?_⟩
  have ht := hleft.comp (tendsto_sub_left x₀)
  apply ht.congr'
  filter_upwards [] with x
  simp [Function.comp_apply, secant, increment]

theorem gap41 (f : ℝ → ℝ) (a b x₀ : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f)
    (hx₀ : x₀ ∈ Set.Ioo a b) :
    ContinuousAt f x₀ ∧
      HasFiniteLeftSlopeAt f x₀ ∧ HasFiniteRightSlopeAt f x₀ := by
  refine ⟨gap25 f a b x₀ hconv hx₀, ?_, gap38 f a b x₀ hconv hx₀⟩
  let g : ℝ → ℝ := fun y => f (-y)
  have hg : ConvexOn ℝ (Set.Ioo (-b) (-a)) g :=
    convexOn_reflect f a b hconv
  have hxg : -x₀ ∈ Set.Ioo (-b) (-a) :=
    ⟨by linarith [hx₀.2], by linarith [hx₀.1]⟩
  rcases gap38 g (-b) (-a) (-x₀) hg hxg with ⟨L, hL⟩
  exact ⟨-L, leftSlope_of_reflected_right f x₀ L hL⟩

theorem gap42 (f : ℝ → ℝ) (a b : ℝ)
    (hconv : ConvexOn ℝ (Set.Ioo a b) f) :
    ContinuousOn f (Set.Ioo a b) ∧
      (∀ x ∈ Set.Ioo a b, HasFiniteLeftSlopeAt f x) ∧
      (∀ x ∈ Set.Ioo a b, HasFiniteRightSlopeAt f x) := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact (gap25 f a b x hconv hx).continuousWithinAt
  · intro x hx
    exact (gap41 f a b x hconv hx).2.1
  · intro x hx
    exact (gap41 f a b x hconv hx).2.2

end

end ProofGap.Exercise1315
