import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1411_1

noncomputable section
open Filter
open scoped Topology

def punctured := nhdsWithin (0 : ℝ) ({0} : Set ℝ)ᶜ
def target (R x : ℝ) := 1 / R ^ 2 - 1 / (R + x) ^ 2
def linearModel (R x : ℝ) := 2 * x / R ^ 3

theorem gap1 (R x : ℝ) (hR : 0 < R) (hx : R + x ≠ 0) :
    target R x = (1 / R ^ 2) * (1 - (1 + x / R) ^ (-2 : ℤ)) := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hbase : 1 + x / R ≠ 0 := by
    intro hb
    apply hx
    have hid : R + x = R * (1 + x / R) := by
      field_simp [hR0]
      <;> ring
    rw [hid, hb, mul_zero]
  have hz : (1 + x / R) ^ (-2 : ℤ) = ((1 + x / R) ^ 2)⁻¹ := by
    norm_num [zpow_neg]
    rfl
  rw [hz]
  unfold target
  field_simp [hR0, hx, hbase]
  <;> ring
theorem gap2 (R : ℝ) (hR : 0 < R) :
    Asymptotics.IsEquivalent punctured (target R) (linearModel R) := by
  have hR0 : R ≠ 0 := ne_of_gt hR
  have hxlim : Tendsto (fun x : ℝ => x) punctured (𝓝 0) := by
    apply tendsto_id.mono_left
    unfold punctured
    exact inf_le_left
  have hpunc : ∀ᶠ x : ℝ in punctured, x ∈ ({0} : Set ℝ)ᶜ := by
    simpa [punctured] using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ,
          x ∈ ({0} : Set ℝ)ᶜ)
  have hxne : ∀ᶠ x : ℝ in punctured, x ≠ 0 := by
    simpa using hpunc
  have hconstR : Tendsto (fun _ : ℝ => R) punctured (𝓝 R) :=
    tendsto_const_nhds
  have hconstTwo : Tendsto (fun _ : ℝ => (2 : ℝ)) punctured (𝓝 2) :=
    tendsto_const_nhds
  have hsumlim : Tendsto (fun x : ℝ => R + x) punctured (𝓝 R) := by
    simpa using hconstR.add hxlim
  have hsumne : ∀ᶠ x : ℝ in punctured, R + x ≠ 0 :=
    hsumlim.eventually (eventually_ne_nhds hR0)
  have hlinne : ∀ᶠ x : ℝ in punctured, linearModel R x ≠ 0 := by
    filter_upwards [hxne] with x hx
    unfold linearModel
    exact div_ne_zero (mul_ne_zero (by norm_num) hx) (pow_ne_zero 3 hR0)
  have htwoR : Tendsto (fun _ : ℝ => 2 * R) punctured (𝓝 (2 * R)) :=
    hconstTwo.mul hconstR
  have hbase :
      Tendsto (fun x : ℝ => 2 * R + x) punctured (𝓝 (2 * R)) := by
    simpa using htwoR.add hxlim
  have hnum :
      Tendsto (fun x : ℝ => R * (2 * R + x)) punctured
        (𝓝 (R * (2 * R))) :=
    hconstR.mul hbase
  have hden :
      Tendsto (fun x : ℝ => 2 * (R + x) ^ 2) punctured
        (𝓝 (2 * R ^ 2)) :=
    hconstTwo.mul (hsumlim.pow 2)
  have hden0 : (2 : ℝ) * R ^ 2 ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero 2 hR0)
  have hqraw :
      Tendsto
        (fun x : ℝ => R * (2 * R + x) / (2 * (R + x) ^ 2))
        punctured (𝓝 (R * (2 * R) / (2 * R ^ 2))) :=
    hnum.div hden hden0
  have hval : R * (2 * R) / (2 * R ^ 2) = (1 : ℝ) := by
    field_simp [hR0]
    <;> ring
  rw [hval] at hqraw
  have hquot :
      ∀ᶠ x : ℝ in punctured,
        target R x / linearModel R x =
          R * (2 * R + x) / (2 * (R + x) ^ 2) := by
    filter_upwards [hxne, hsumne] with x hx hs
    unfold target linearModel
    field_simp [hR0, hx, hs]
    <;> ring
  apply (Asymptotics.isEquivalent_iff_tendsto_one hlinne).2
  exact (tendsto_congr' hquot).2 hqraw
theorem gap3 (R x : ℝ) (hR : R ≠ 0) :
    (1 / R ^ 2) * (2 * x / R) = linearModel R x := by
  unfold linearModel
  field_simp [hR]
  <;> ring
theorem gap4 (R : ℝ) (hR : 0 < R) :
    Asymptotics.IsEquivalent punctured (target R) (linearModel R) := by
  exact gap2 R hR

end
end ProofGap.Exercise1411_1
