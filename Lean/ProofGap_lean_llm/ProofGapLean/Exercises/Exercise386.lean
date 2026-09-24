import ProofGapLean.Prelude.Sequences
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise386

noncomputable section

def f (x : ℝ) : ℝ := x / (1 + x)
def rangeOnNonnegative : Set ℝ :=
  {y | ∃ x ∈ Set.Ici (0 : ℝ), y = f x}

/-- Exercise 386, gap 1; restore the nonnegative domain. -/
theorem gap1 : ∀ x : ℝ, 0 ≤ x → 0 ≤ f x := by
  intro x hx
  unfold f
  apply div_nonneg hx
  linarith

/-- Exercise 386, gap 2; restore the nonnegative domain. -/
theorem gap2 : ∀ x : ℝ, 0 ≤ x → f x < 1 := by
  intro x hx
  unfold f
  have hden : 0 < 1 + x := by linarith
  apply (div_lt_iff₀ hden).2
  linarith

/-- Exercise 386, gap 3. -/
theorem gap3 : (0 : ℝ) < 1 := by
  exact zero_lt_one

/-- Exercise 386, gap 4. -/
theorem gap4 : StrictMonoOn f (Set.Ici 0) := by
  intro x hx y hy hxy
  have hx0 : 0 ≤ x := Set.mem_Ici.mp hx
  have hy0 : 0 ≤ y := Set.mem_Ici.mp hy
  have hxd : 0 < 1 + x := by linarith
  have hyd : 0 < 1 + y := by linarith
  unfold f
  apply (div_lt_div_iff₀ hxd hyd).2
  nlinarith

/-- Exercise 386, gap 5. -/
theorem gap5 :
    Filter.Tendsto f Filter.atTop (nhds 1) := by
  have hshift :
      Filter.Tendsto (fun x : ℝ => 1 + x) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_ge_atTop (b - 1)] with x hx
    linarith
  have hinv0 :
      Filter.Tendsto (fun x : ℝ => x⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  have hinv :
      Filter.Tendsto (fun x : ℝ => (1 + x)⁻¹) Filter.atTop (nhds 0) :=
    hinv0.comp hshift
  have hlim :
      Filter.Tendsto (fun x : ℝ => 1 - (1 + x)⁻¹)
        Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds.sub hinv)
  apply hlim.congr'
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  have hne : 1 + x ≠ 0 := by linarith
  simp only [f]
  field_simp [hne]
  ring

/-- Exercise 386, gap 6. -/
theorem gap6 : sInf rangeOnNonnegative = 0 := by
  have hzero : (0 : ℝ) ∈ rangeOnNonnegative := by
    refine ⟨0, Set.mem_Ici.mpr le_rfl, ?_⟩
    simp [f]
  have hbelow : BddBelow rangeOnNonnegative := by
    refine ⟨0, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact gap1 x (Set.mem_Ici.mp hx)
  apply le_antisymm
  · exact csInf_le hbelow hzero
  · refine le_csInf ⟨0, hzero⟩ ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact gap1 x (Set.mem_Ici.mp hx)

/-- Exercise 386, gap 7. -/
theorem gap7 : sSup rangeOnNonnegative = 1 := by
  have hzero : (0 : ℝ) ∈ rangeOnNonnegative := by
    refine ⟨0, Set.mem_Ici.mpr le_rfl, ?_⟩
    simp [f]
  have hnonempty : rangeOnNonnegative.Nonempty := ⟨0, hzero⟩
  have hupper : BddAbove rangeOnNonnegative := by
    refine ⟨1, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (gap2 x (Set.mem_Ici.mp hx)).le
  apply le_antisymm
  · refine csSup_le hnonempty ?_
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    exact (gap2 x (Set.mem_Ici.mp hx)).le
  · by_contra hcontra
    let a : ℝ := sSup rangeOnNonnegative
    have ha : a < 1 := by
      dsimp [a]
      exact lt_of_not_ge hcontra
    let x : ℝ := 1 / (1 - a)
    have hden : 0 < 1 - a := by linarith
    have hx : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg zero_le_one hden.le
    have hxmul : x * (1 - a) = 1 := by
      dsimp [x]
      field_simp [ne_of_gt hden]
    have hmem : f x ∈ rangeOnNonnegative :=
      ⟨x, Set.mem_Ici.mpr hx, rfl⟩
    have hle : f x ≤ a := by
      dsimp [a]
      exact le_csSup hupper hmem
    have hxd : 0 < 1 + x := by linarith
    have hgt : a < f x := by
      unfold f
      apply (lt_div_iff₀ hxd).2
      nlinarith [hxmul]
    exact (not_lt_of_ge hle) hgt

/-- Exercise 386, gap 8. -/
theorem gap8 :
    sInf rangeOnNonnegative = 0 ∧ sSup rangeOnNonnegative = 1 := by
  exact ⟨gap6, gap7⟩

end

end ProofGap.Exercise386
