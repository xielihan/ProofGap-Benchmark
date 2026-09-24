import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise3196

noncomputable section

open Filter
open scoped Topology

def u (p : ℝ × ℝ) : ℝ :=
  (p.1 + p.2) / (p.1 ^ 3 + p.2 ^ 3)

def reduced (p : ℝ × ℝ) : ℝ :=
  1 / (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2)

def domain : Set (ℝ × ℝ) :=
  {p | p.1 ^ 3 + p.2 ^ 3 ≠ 0}

def SingularPoint (_f : (ℝ × ℝ) → ℝ) (p : ℝ × ℝ) : Prop :=
  p ∉ domain

private theorem quad_pos_of_sum_ne_zero {x y : ℝ} (h : x + y ≠ 0) :
    0 < x ^ 2 - x * y + y ^ 2 := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by
      intro hy
      apply h
      simp [hx, hy]
    simpa [hx] using sq_pos_of_ne_zero hy
  · nlinarith [sq_pos_of_ne_zero hx, sq_nonneg y, sq_nonneg (x - y)]

private theorem cube_sum_ne_zero_iff (x y : ℝ) :
    x ^ 3 + y ^ 3 ≠ 0 ↔ x + y ≠ 0 := by
  have hfactor :
      x ^ 3 + y ^ 3 = (x + y) * (x ^ 2 - x * y + y ^ 2) := by
    ring
  rw [hfactor]
  constructor
  · intro hprod hsum
    apply hprod
    simp [hsum]
  · intro hsum
    exact mul_ne_zero hsum (ne_of_gt (quad_pos_of_sum_ne_zero hsum))

private theorem u_eq_reduced_of_mem {p : ℝ × ℝ} (hp : p ∈ domain) :
    u p = reduced p := by
  have hfactor :
      p.1 ^ 3 + p.2 ^ 3 =
        (p.1 + p.2) * (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2) := by
    ring
  change p.1 ^ 3 + p.2 ^ 3 ≠ 0 at hp
  rw [hfactor] at hp
  have hsum : p.1 + p.2 ≠ 0 := by
    intro h
    apply hp
    simp [h]
  have hquad : p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2 ≠ 0 := by
    intro h
    apply hp
    simp [h]
  change
    (p.1 + p.2) / (p.1 ^ 3 + p.2 ^ 3) =
      1 / (p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2)
  rw [hfactor]
  field_simp [hsum, hquad]

private theorem u_eventuallyEq_reduced (p : ℝ × ℝ) :
    u =ᶠ[nhdsWithin p domain] reduced := by
  filter_upwards [self_mem_nhdsWithin] with q hq
  exact u_eq_reduced_of_mem hq

private theorem reduced_tendsto (a : ℝ) (ha : a ≠ 0) :
    Tendsto reduced (𝓝 (a, -a)) (𝓝 (1 / (3 * a ^ 2))) := by
  have hden : a ^ 2 - a * (-a) + (-a) ^ 2 ≠ 0 := by
    nlinarith [sq_pos_of_ne_zero ha]
  have hcden :
      ContinuousAt
        (fun p : ℝ × ℝ => p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2)
        (a, -a) :=
    ((continuousAt_fst.pow 2).sub
      (continuousAt_fst.mul continuousAt_snd)).add
      (continuousAt_snd.pow 2)
  have hc : ContinuousAt reduced (a, -a) := by
    unfold reduced
    exact continuousAt_const.div hcden (by simpa using hden)
  have hval : reduced (a, -a) = 1 / (3 * a ^ 2) := by
    simp only [reduced, Prod.fst, Prod.snd]
    congr 1
    ring
  rw [← hval]
  exact hc.tendsto

private theorem approach_domain_tendsto (a : ℝ) :
    Tendsto (fun t : ℝ => (a + t, -a)) (𝓝[>] 0)
      (nhdsWithin (a, -a) domain) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc1 : ContinuousAt (fun t : ℝ => a + t) 0 :=
      continuousAt_const.add continuousAt_id
    have hc2 : ContinuousAt (fun _ : ℝ => -a) 0 :=
      continuousAt_const
    have hc : ContinuousAt (fun t : ℝ => (a + t, -a)) 0 :=
      hc1.prodMk hc2
    simpa using hc.tendsto.mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change 0 < t at ht
    change (a + t) ^ 3 + (-a) ^ 3 ≠ 0
    rw [cube_sum_ne_zero_iff]
    nlinarith

theorem gap1 :
    ∀ a : ℝ, a ≠ 0 →
      ∀ L : ℝ,
        Tendsto u (nhdsWithin (a, -a) domain) (𝓝 L) ↔
          Tendsto reduced (𝓝 (a, -a)) (𝓝 L) := by
  intro a ha L
  constructor
  · intro hu
    have hredWithin :
        Tendsto reduced (nhdsWithin (a, -a) domain) (𝓝 L) :=
      (tendsto_congr' (u_eventuallyEq_reduced (a, -a))).mp hu
    have hg := approach_domain_tendsto a
    have hgFull :
        Tendsto (fun t : ℝ => (a + t, -a)) (𝓝[>] 0) (𝓝 (a, -a)) :=
      hg.mono_right inf_le_left
    have hseqL := hredWithin.comp hg
    have hseqValue := (reduced_tendsto a ha).comp hgFull
    have hL : L = 1 / (3 * a ^ 2) :=
      tendsto_nhds_unique hseqL hseqValue
    rw [hL]
    exact reduced_tendsto a ha
  · intro hr
    have hrWithin : Tendsto reduced (nhdsWithin (a, -a) domain) (𝓝 L) :=
      hr.mono_left inf_le_left
    exact (tendsto_congr' (u_eventuallyEq_reduced (a, -a))).mpr hrWithin

theorem gap2 :
    ∀ a : ℝ, a ≠ 0 →
      Tendsto reduced (𝓝 (a, -a)) (𝓝 (1 / (3 * a ^ 2))) := by
  intro a ha
  exact reduced_tendsto a ha

theorem gap3 :
    ∀ a : ℝ, a ≠ 0 →
      Tendsto u (nhdsWithin (a, -a) domain)
        (𝓝 (1 / (3 * a ^ 2))) := by
  intro a ha
  exact (gap1 a ha (1 / (3 * a ^ 2))).2 (gap2 a ha)

theorem gap4 :
    {p : ℝ × ℝ | SingularPoint u p} =
      {p : ℝ × ℝ | p.1 + p.2 = 0} := by
  ext p
  simpa only [SingularPoint, domain, Set.mem_setOf_eq, not_ne_iff] using
    not_congr (cube_sum_ne_zero_iff p.1 p.2)

theorem gap5 :
    ∀ a : ℝ, a ≠ 0 →
      Tendsto u (nhdsWithin (a, -a) domain)
        (𝓝 (1 / (3 * a ^ 2))) := by
  intro a ha
  exact gap3 a ha

theorem gap6 :
    Tendsto u (nhdsWithin ((0, 0) : ℝ × ℝ) domain) atTop := by
  let q : (ℝ × ℝ) → ℝ := fun p =>
    p.1 ^ 2 - p.1 * p.2 + p.2 ^ 2
  have hcq : ContinuousAt q ((0, 0) : ℝ × ℝ) := by
    dsimp [q]
    exact
      ((continuousAt_fst.pow 2).sub
        (continuousAt_fst.mul continuousAt_snd)).add
        (continuousAt_snd.pow 2)
  have hqZero :
      Tendsto q (nhdsWithin ((0, 0) : ℝ × ℝ) domain) (𝓝 0) := by
    simpa [q] using hcq.tendsto.mono_left inf_le_left
  have hqPos :
      ∀ᶠ p in nhdsWithin ((0, 0) : ℝ × ℝ) domain, q p ∈ Set.Ioi 0 := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    change p.1 ^ 3 + p.2 ^ 3 ≠ 0 at hp
    change 0 < q p
    apply quad_pos_of_sum_ne_zero
    exact (cube_sum_ne_zero_iff p.1 p.2).mp hp
  have hq :
      Tendsto q (nhdsWithin ((0, 0) : ℝ × ℝ) domain) (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqZero, hqPos⟩
  have hinv :
      Tendsto (fun p => (q p)⁻¹)
        (nhdsWithin ((0, 0) : ℝ × ℝ) domain) atTop :=
    tendsto_inv_nhdsGT_zero.comp hq
  have hreduced : reduced = fun p : ℝ × ℝ => (q p)⁻¹ := by
    funext p
    simp only [reduced, one_div, q]
  have hred :
      Tendsto reduced (nhdsWithin ((0, 0) : ℝ × ℝ) domain) atTop := by
    rw [hreduced]
    exact hinv
  exact
    (tendsto_congr'
      (u_eventuallyEq_reduced ((0, 0) : ℝ × ℝ))).mpr hred

end

end ProofGap.Exercise3196
