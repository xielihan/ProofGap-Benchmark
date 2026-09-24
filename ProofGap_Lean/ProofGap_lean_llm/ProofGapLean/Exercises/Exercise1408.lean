import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods

namespace ProofGap.Exercise1408

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def y (x : ℝ) := Real.rpow (1 + x) x - 1
def exponentialForm (x : ℝ) := Real.exp (x * Real.log (1 + x)) - 1
def logRemainder (x : ℝ) :=
  Real.log (1 + x) - (x - x ^ 2 / 2)
def exponentRemainder (x : ℝ) :=
  x * Real.log (1 + x) - (x ^ 2 - x ^ 3 / 2)

theorem gap1 (x : ℝ) (hx : -1 < x) :
    y x = exponentialForm x := by
  unfold y exponentialForm
  change (1 + x) ^ x - 1 = Real.exp (x * Real.log (1 + x)) - 1
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + x)]
  congr 2
  ring
theorem gap2 :
    Asymptotics.IsLittleO punctured logRemainder (fun x => x ^ 2) := by
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  have hxne : ∀ᶠ x : ℝ in punctured, x ≠ 0 := by
    unfold punctured
    filter_upwards [self_mem_nhdsWithin] with x hx
    simpa using hx
  have hnear_nhds : ∀ᶠ x : ℝ in 𝓝 0, -1 < x :=
    eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0)
  have hnear : ∀ᶠ x : ℝ in punctured, -1 < x :=
    hnear_nhds.filter_mono hp_le
  have hderiv : ∀ x : ℝ, -1 < x →
      HasDerivAt logRemainder (x ^ 2 / (1 + x)) x := by
    intro x hx
    unfold logRemainder
    have hl := (Real.hasDerivAt_log (by linarith : 1 + x ≠ 0)).comp x
      ((hasDerivAt_id x).const_add 1)
    have hp := (hasDerivAt_id x).sub (((hasDerivAt_id x).pow 2).div_const 2)
    convert hl.sub hp using 1 <;>
      simp only [Function.comp_apply, id_eq] <;>
      field_simp [show 1 + x ≠ 0 by linarith] <;>
      ring
  have hdf : ∀ᶠ x : ℝ in punctured,
      HasDerivAt logRemainder (x ^ 2 / (1 + x)) x := by
    filter_upwards [hnear] with x hx
    exact hderiv x hx
  have hdg : ∀ᶠ x : ℝ in punctured,
      HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    filter_upwards with x
    simpa [id_eq, mul_comm] using (hasDerivAt_id x).pow 2
  have hdgne : ∀ᶠ x : ℝ in punctured, 2 * x ≠ 0 := by
    filter_upwards [hxne] with x hx
    exact mul_ne_zero (by norm_num) hx
  have hf0 : Tendsto logRemainder (𝓝 (0 : ℝ)) (𝓝 0) := by
    have hc := (hderiv 0 (by norm_num)).continuousAt
    have hval : logRemainder 0 = 0 := by
      norm_num [logRemainder]
    change Tendsto logRemainder (𝓝 0) (𝓝 (logRemainder 0)) at hc
    simpa only [hval] using hc
  have hg0 : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 0) := by
    have hc := ((hasDerivAt_id (0 : ℝ)).pow 2).continuousAt
    change Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 (0 ^ 2)) at hc
    norm_num at hc
    exact hc
  have hid : Tendsto (fun x : ℝ => x) punctured (𝓝 0) :=
    tendsto_id.mono_left hp_le
  have hden : Tendsto (fun x : ℝ => 2 * (1 + x)) punctured (𝓝 2) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) punctured (𝓝 2)).mul
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) punctured (𝓝 1)).add hid))
  have hbase : Tendsto (fun x : ℝ => x / (2 * (1 + x))) punctured (𝓝 0) := by
    simpa using hid.div hden (by norm_num : (2 : ℝ) ≠ 0)
  have heq :
      (fun x : ℝ => (x ^ 2 / (1 + x)) / (2 * x)) =ᶠ[punctured]
        (fun x => x / (2 * (1 + x))) := by
    filter_upwards [hxne, hnear] with x hx hxnear
    field_simp
  have hlim : Tendsto (fun x : ℝ => (x ^ 2 / (1 + x)) / (2 * x))
      punctured (𝓝 0) :=
    hbase.congr' heq.symm
  have hGT_le : 𝓝[>] (0 : ℝ) ≤ punctured := by
    unfold punctured
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Ioi] at hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_gt hx
  have hLT_le : 𝓝[<] (0 : ℝ) ≤ punctured := by
    unfold punctured
    apply nhdsWithin_mono
    intro x hx
    simp only [Set.mem_Iio] at hx
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ne_of_lt hx
  have hratioGT : Tendsto (fun x : ℝ => logRemainder x / x ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    apply HasDerivAt.lhopital_zero_nhdsGT
      (f' := fun x : ℝ => x ^ 2 / (1 + x))
      (g' := fun x : ℝ => 2 * x)
    all_goals first | exact hdf.filter_mono hGT_le | exact hdg.filter_mono hGT_le |
      exact hdgne.filter_mono hGT_le | exact hf0.mono_left inf_le_left |
      exact hg0.mono_left inf_le_left | exact hlim.mono_left hGT_le
  have hratioLT : Tendsto (fun x : ℝ => logRemainder x / x ^ 2)
      (𝓝[<] 0) (𝓝 0) := by
    apply HasDerivAt.lhopital_zero_nhdsLT
      (f' := fun x : ℝ => x ^ 2 / (1 + x))
      (g' := fun x : ℝ => 2 * x)
    all_goals first | exact hdf.filter_mono hLT_le | exact hdg.filter_mono hLT_le |
      exact hdgne.filter_mono hLT_le | exact hf0.mono_left inf_le_left |
      exact hg0.mono_left inf_le_left | exact hlim.mono_left hLT_le
  have hset : ({0} : Set ℝ)ᶜ = Set.Iio 0 ∪ Set.Ioi 0 := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union,
      Set.mem_Iio, Set.mem_Ioi]
    constructor
    · exact lt_or_gt_of_ne
    · intro hx
      rcases hx with hx | hx
      · exact ne_of_lt hx
      · exact ne_of_gt hx
  have hratio : Tendsto (fun x : ℝ => logRemainder x / x ^ 2)
      punctured (𝓝 0) := by
    unfold punctured
    rw [hset, nhdsWithin_union]
    exact hratioLT.sup hratioGT
  refine (Asymptotics.isLittleO_iff_tendsto ?_).2 hratio
  intro x hx
  have hx0 : x = 0 := by
    nlinarith [sq_nonneg x]
  subst x
  norm_num [logRemainder]
theorem gap3 :
    Asymptotics.IsLittleO punctured exponentRemainder (fun x => x ^ 3) := by
  have h := gap2.mul_isBigO
    (Asymptotics.isBigO_refl (fun x : ℝ => x) punctured)
  convert h using 1 <;> ext x <;>
    simp only [logRemainder, exponentRemainder] <;> ring
theorem gap4 :
    ∀ᶠ x in punctured, y x = exponentialForm x := by
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  have hnear : ∀ᶠ x : ℝ in punctured, -1 < x :=
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0)).filter_mono hp_le
  filter_upwards [hnear] with x hx
  exact gap1 x hx
theorem gap5 :
    Asymptotics.IsLittleO punctured
      (fun x => y x - (x ^ 2 - x ^ 3 / 2)) (fun x => x ^ 3) := by
  let z : ℝ → ℝ := fun x => x * Real.log (1 + x)
  let p : ℝ → ℝ := fun x => x ^ 2 - x ^ 3 / 2
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  have h32 : (fun x : ℝ => x ^ 3) =o[punctured] (fun x => x ^ 2) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 2 < 3)).mono hp_le
  have h43 : (fun x : ℝ => x ^ 4) =o[punctured] (fun x => x ^ 3) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 3 < 4)).mono hp_le
  have hp : p =O[punctured] (fun x : ℝ => x ^ 2) := by
    have h := (Asymptotics.isBigO_refl (fun x : ℝ => x ^ 2) punctured).sub
      (h32.const_mul_left (1 / 2 : ℝ)).isBigO
    convert h using 1 <;> ext x <;> simp [p] <;> ring
  have hzerr : (fun x => z x - p x) =o[punctured] (fun x : ℝ => x ^ 3) := by
    simpa [z, p, exponentRemainder] using gap3
  have hz : z =O[punctured] (fun x : ℝ => x ^ 2) := by
    have h := (hzerr.trans h32).isBigO.add hp
    convert h using 1 <;> ext x <;> ring
  have hid : Tendsto (fun x : ℝ => x) punctured (𝓝 0) :=
    tendsto_id.mono_left hp_le
  have hlogAt : Tendsto Real.log (𝓝 (1 : ℝ)) (𝓝 0) := by
    have hc := (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt
    change Tendsto Real.log (𝓝 1) (𝓝 (Real.log 1)) at hc
    simpa using hc
  have hinner : Tendsto (fun x : ℝ => 1 + x) punctured (𝓝 1) := by
    simpa using
      ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) punctured (𝓝 1)).add hid)
  have hlog0 : Tendsto (fun x : ℝ => Real.log (1 + x)) punctured (𝓝 0) :=
    hlogAt.comp hinner
  have hz0 : Tendsto z punctured (𝓝 0) := by
    simpa [z] using hid.mul hlog0
  have hnear : ∀ᶠ x : ℝ in punctured, -1 < x :=
    (eventually_gt_nhds (by norm_num : (-1 : ℝ) < 0)).filter_mono hp_le
  have hz_nonneg : ∀ᶠ x : ℝ in punctured, 0 ≤ z x := by
    filter_upwards [hnear] with x hx
    dsimp [z]
    by_cases hx0 : 0 ≤ x
    · exact mul_nonneg hx0 (Real.log_nonneg (by linarith))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx0)
        (Real.log_nonpos (by linarith) (by linarith))
  have hz_small : ∀ᶠ x : ℝ in punctured, z x < 1 / 2 :=
    hz0.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hexpO :
      (fun x => Real.exp (z x) - 1 - z x) =O[punctured]
        (fun x => z x ^ 2) := by
    apply Asymptotics.IsBigO.of_bound 2
    filter_upwards [hz_nonneg, hz_small] with x hzx hzxlt
    have hzx1 : z x < 1 := by linarith
    have he := Real.exp_bound_div_one_sub_of_interval hzx hzx1
    have hlower : 0 ≤ Real.exp (z x) - 1 - z x := by
      linarith [Real.add_one_le_exp (z x)]
    have hden : 0 < 1 - z x := by linarith
    have hupper : Real.exp (z x) - 1 - z x ≤ 2 * z x ^ 2 := by
      calc
        Real.exp (z x) - 1 - z x ≤ 1 / (1 - z x) - 1 - z x := by linarith
        _ = z x ^ 2 / (1 - z x) := by field_simp; ring
        _ ≤ 2 * z x ^ 2 := by
          apply (div_le_iff₀ hden).2
          nlinarith [sq_nonneg (z x)]
    simpa [Real.norm_eq_abs, abs_of_nonneg hlower, abs_of_nonneg (sq_nonneg (z x))]
      using hupper
  have hzsq : (fun x => z x ^ 2) =O[punctured] (fun x : ℝ => x ^ 4) := by
    have h := hz.mul hz
    convert h using 1 <;> ext x <;> ring
  have hexp :
      (fun x => Real.exp (z x) - 1 - z x) =o[punctured]
        (fun x : ℝ => x ^ 3) :=
    (hexpO.trans hzsq).trans_isLittleO h43
  have hsum := hexp.add hzerr
  refine hsum.congr' ?_ (Eventually.of_forall fun _ => rfl)
  filter_upwards [gap4] with x hx
  simp only [z, p]
  rw [hx]
  unfold exponentialForm
  ring
theorem gap6 :
    Asymptotics.IsLittleO punctured
      (fun x => (x ^ 2 - x ^ 3 / 2) - x ^ 2) (fun x => x ^ 2) := by
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  have h : (fun x : ℝ => x ^ 3) =o[punctured] (fun x => x ^ 2) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 2 < 3)).mono hp_le
  convert h.const_mul_left (-1 / 2 : ℝ) using 1 <;> ext x <;> ring
theorem gap7 :
    Asymptotics.IsLittleO punctured
      (fun x => y x - x ^ 2) (fun x => x ^ 2) := by
  have hp_le : punctured ≤ 𝓝 (0 : ℝ) := by
    unfold punctured
    exact inf_le_left
  have h32 : (fun x : ℝ => x ^ 3) =o[punctured] (fun x => x ^ 2) :=
    (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (by omega : 2 < 3)).mono hp_le
  have h := (gap5.trans h32).add gap6
  convert h using 1 <;> ext x <;> ring
theorem gap8 :
    Asymptotics.IsEquivalent punctured y (fun x => x ^ 2) := by
  change (fun x => y x - x ^ 2) =o[punctured] (fun x => x ^ 2)
  exact gap7

end
end ProofGap.Exercise1408
