import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods
import Mathlib.Order.Filter.Tendsto

namespace ProofGap.Exercise3190

noncomputable section

open Filter
open scoped Topology

def radialSource (p : ℝ × ℝ) : ℝ :=
  ((p.1 ^ 2 + p.2 ^ 2) ^ 2 / 4) * Real.log (p.1 ^ 2 + p.2 ^ 2)

def radialModel (t : ℝ) : ℝ :=
  (1 / 4 : ℝ) * t ^ 2 * Real.log t

def exponentSource (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 * p.2 ^ 2 * Real.log (p.1 ^ 2 + p.2 ^ 2)

def originalPower (p : ℝ × ℝ) : ℝ :=
  Real.rpow (p.1 ^ 2 + p.2 ^ 2) (p.1 ^ 2 * p.2 ^ 2)

def exponentialForm (p : ℝ × ℝ) : ℝ :=
  Real.exp (exponentSource p)

def puncturedOrigin : Filter (ℝ × ℝ) :=
  nhdsWithin ((0, 0) : ℝ × ℝ)
    (({((0, 0) : ℝ × ℝ)} : Set (ℝ × ℝ))ᶜ)

private def radiusSq (p : ℝ × ℝ) : ℝ :=
  p.1 ^ 2 + p.2 ^ 2

private theorem radiusSq_pos_of_ne
    (p : ℝ × ℝ) (hp : p ≠ ((0, 0) : ℝ × ℝ)) :
    0 < radiusSq p := by
  unfold radiusSq
  have hx : 0 ≤ p.1 ^ 2 := sq_nonneg p.1
  have hy : 0 ≤ p.2 ^ 2 := sq_nonneg p.2
  by_contra h
  have hsum : p.1 ^ 2 + p.2 ^ 2 ≤ 0 := le_of_not_gt h
  have hxzero : p.1 = 0 := by
    nlinarith
  have hyzero : p.2 = 0 := by
    nlinarith
  apply hp
  exact Prod.ext hxzero hyzero

private theorem map_radiusSq_puncturedOrigin :
    Filter.map radiusSq puncturedOrigin = 𝓝[>] (0 : ℝ) := by
  apply le_antisymm
  · refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hcont : Continuous radiusSq := by
        unfold radiusSq
        exact (continuous_fst.pow 2).add (continuous_snd.pow 2)
      have hle :
          puncturedOrigin ≤ 𝓝 ((0, 0) : ℝ × ℝ) := by
        unfold puncturedOrigin
        exact inf_le_left
      simpa [radiusSq] using hcont.continuousAt.tendsto.mono_left hle
    · filter_upwards [self_mem_nhdsWithin] with p hp
      have hpne : p ≠ ((0, 0) : ℝ × ℝ) := by
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
      exact radiusSq_pos_of_ne p hpne
  · let path : ℝ → ℝ × ℝ := fun t => (Real.sqrt t, 0)
    have hpath :
        Tendsto path (𝓝[>] (0 : ℝ)) puncturedOrigin := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have hcont : ContinuousAt path 0 := by
          dsimp [path]
          exact Real.continuous_sqrt.continuousAt.prodMk continuousAt_const
        have hle : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ) := inf_le_left
        simpa [path] using hcont.tendsto.mono_left hle
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have hs : Real.sqrt t ≠ 0 :=
          ne_of_gt (Real.sqrt_pos.2 ht)
        simpa [path, hs]
    have heq :
        (radiusSq ∘ path) =ᶠ[𝓝[>] (0 : ℝ)] id := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      simpa [Function.comp_def, path, radiusSq] using
        Real.sq_sqrt (le_of_lt ht)
    calc
      𝓝[>] (0 : ℝ) = Filter.map id (𝓝[>] (0 : ℝ)) := by simp
      _ = Filter.map (radiusSq ∘ path) (𝓝[>] (0 : ℝ)) :=
        Filter.map_congr heq.symm
      _ = Filter.map radiusSq (Filter.map path (𝓝[>] (0 : ℝ))) := by
        rw [Filter.map_map]
      _ ≤ Filter.map radiusSq puncturedOrigin :=
        Filter.map_mono hpath

theorem gap1 :
    ∀ x y : ℝ,
      |x ^ 2 * y ^ 2 * Real.log (x ^ 2 + y ^ 2)| ≤
        ((x ^ 2 + y ^ 2) ^ 2 / 4) *
          |Real.log (x ^ 2 + y ^ 2)| := by
  intro x y
  have hx : 0 ≤ x ^ 2 := sq_nonneg x
  have hy : 0 ≤ y ^ 2 := sq_nonneg y
  have hxy :
      x ^ 2 * y ^ 2 ≤ (x ^ 2 + y ^ 2) ^ 2 / 4 := by
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2)]
  rw [abs_mul, abs_of_nonneg (mul_nonneg hx hy)]
  exact mul_le_mul_of_nonneg_right hxy (abs_nonneg _)

theorem gap2 :
    ∀ L : ℝ,
      Tendsto radialSource puncturedOrigin (𝓝 L) ↔
        Tendsto radialModel (𝓝[>] (0 : ℝ)) (𝓝 L) := by
  intro L
  have hsource : radialSource = radialModel ∘ radiusSq := by
    funext p
    unfold radialSource radialModel radiusSq
    simp only [Function.comp_apply]
    ring_nf
  rw [hsource]
  change
    Filter.map (radialModel ∘ radiusSq) puncturedOrigin ≤ 𝓝 L ↔
      Filter.map radialModel (𝓝[>] (0 : ℝ)) ≤ 𝓝 L
  rw [← Filter.map_map, map_radiusSq_puncturedOrigin]

theorem gap3 :
    Tendsto radialModel (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hid :
      Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left inf_le_left
  have hlower :
      Tendsto (fun t : ℝ => -t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.neg
  have hone :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    tendsto_const_nhds
  have hupper :
      Tendsto (fun t : ℝ => t ^ 2 * (t - 1))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa [pow_two] using
      (hid.mul hid).mul (hid.sub hone)
  have hlog :
      Tendsto (fun t : ℝ => t ^ 2 * Real.log t)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlower hupper ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := ht
      have htne : t ≠ 0 := ne_of_gt htpos
      have hloginv :
          Real.log (t⁻¹) ≤ t⁻¹ - 1 :=
        Real.log_le_sub_one_of_pos (inv_pos.mpr htpos)
      have hscaled :
          t * (-Real.log t) ≤ 1 - t := by
        calc
          t * (-Real.log t) = t * Real.log (t⁻¹) := by
            rw [Real.log_inv]
          _ ≤ t * (t⁻¹ - 1) :=
            mul_le_mul_of_nonneg_left hloginv (le_of_lt htpos)
          _ = 1 - t := by
            simp [mul_sub, htne]
      have hscaled' :
          t * (t * (-Real.log t)) ≤ t * (1 - t) :=
        mul_le_mul_of_nonneg_left hscaled (le_of_lt htpos)
      nlinarith [sq_nonneg t]
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have htpos : 0 < t := ht
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_sub_one_of_pos htpos) (sq_nonneg t)
  have hscaled :
      Tendsto (fun t : ℝ => (1 / 4 : ℝ) * (t ^ 2 * Real.log t))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul hlog :
        Tendsto (fun t : ℝ => (1 / 4 : ℝ) * (t ^ 2 * Real.log t))
          (𝓝[>] (0 : ℝ)) (𝓝 ((1 / 4 : ℝ) * 0)))
  change
    Tendsto (fun t : ℝ => (1 / 4 : ℝ) * t ^ 2 * Real.log t)
      (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [mul_assoc] using hscaled

theorem gap4
    (hchange :
      ∀ L : ℝ,
        Tendsto radialSource puncturedOrigin (𝓝 L) ↔
          Tendsto radialModel (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hmodel : Tendsto radialModel (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    Tendsto radialSource puncturedOrigin (𝓝 0) := by
  exact (hchange 0).2 hmodel

theorem gap5 :
    ∀ L : ℝ,
      Tendsto originalPower puncturedOrigin (𝓝 L) ↔
        Tendsto exponentialForm puncturedOrigin (𝓝 L) := by
  intro L
  have heq : originalPower =ᶠ[puncturedOrigin] exponentialForm := by
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hpne : p ≠ ((0, 0) : ℝ × ℝ) := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hp
    have hpos : 0 < radiusSq p := radiusSq_pos_of_ne p hpne
    have hpos' : 0 < p.1 ^ 2 + p.2 ^ 2 := by
      simpa [radiusSq] using hpos
    unfold originalPower exponentialForm exponentSource
    simpa only [mul_comm] using
      (Real.rpow_def_of_pos hpos' (p.1 ^ 2 * p.2 ^ 2))
  exact tendsto_congr' heq

theorem gap6
    (hbound :
      ∀ x y : ℝ,
        |x ^ 2 * y ^ 2 * Real.log (x ^ 2 + y ^ 2)| ≤
          ((x ^ 2 + y ^ 2) ^ 2 / 4) *
            |Real.log (x ^ 2 + y ^ 2)|)
    (hradial :
      Tendsto radialSource puncturedOrigin (𝓝 0)) :
    Tendsto exponentialForm puncturedOrigin
      (𝓝 (Real.exp 0)) := by
  have hdom : ∀ p : ℝ × ℝ,
      |exponentSource p| ≤ |radialSource p| := by
    intro p
    have hcoeff :
        0 ≤ (p.1 ^ 2 + p.2 ^ 2) ^ 2 / 4 :=
      div_nonneg (sq_nonneg _) (by norm_num)
    simpa [exponentSource, radialSource, abs_mul,
      abs_of_nonneg hcoeff] using hbound p.1 p.2
  have habs :
      Tendsto (fun p => |radialSource p|) puncturedOrigin (𝓝 0) := by
    simpa using hradial.abs
  have hneg :
      Tendsto (fun p => -|radialSource p|) puncturedOrigin (𝓝 0) := by
    simpa using habs.neg
  have hexponent :
      Tendsto exponentSource puncturedOrigin (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg habs ?_ ?_
    · exact Filter.Eventually.of_forall fun p => neg_le_of_abs_le (hdom p)
    · exact Filter.Eventually.of_forall fun p =>
        le_trans (le_abs_self (exponentSource p)) (hdom p)
  simpa [exponentialForm] using
    Real.continuous_exp.continuousAt.tendsto.comp hexponent

theorem gap7 : Real.exp 0 = 1 := by
  exact Real.exp_zero

theorem gap8 :
    Tendsto originalPower puncturedOrigin (𝓝 1) := by
  have hradial :
      Tendsto radialSource puncturedOrigin (𝓝 0) :=
    gap4 gap2 gap3
  have hexponential :
      Tendsto exponentialForm puncturedOrigin (𝓝 (Real.exp 0)) :=
    gap6 gap1 hradial
  rw [gap7] at hexponential
  exact (gap5 1).2 hexponential

end

end ProofGap.Exercise3190
