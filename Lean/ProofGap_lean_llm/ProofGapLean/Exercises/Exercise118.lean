import ProofGapLean.Prelude.Sequences
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.Real.Lemmas

open Filter Topology

namespace ProofGap.Exercise118

def unitRationals : Set ℝ :=
  {v | ∃ q : ℚ, 0 < q ∧ q < 1 ∧ v = (q : ℝ)}

def EnumeratesUnitRationals (x : ℕ → ℝ) : Prop :=
  Set.range x = unitRationals

private theorem exists_unit_rat_seq (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    ∃ r : ℕ → ℚ,
      Function.Injective r ∧
      (∀ n, 0 < r n ∧ r n < 1) ∧
      Tendsto (fun n : ℕ => (r n : ℝ)) atTop (𝓝 y) := by
  by_cases hy0 : y = 0
  · subst y
    rcases Real.exists_seq_rat_strictAnti_tendsto 0 with
      ⟨u, hu, hu0, hlim⟩
    have hev : ∀ᶠ n : ℕ in atTop, (u n : ℝ) < 1 :=
      hlim.eventually (Iio_mem_nhds zero_lt_one)
    rcases eventually_atTop.1 hev with ⟨N, hN⟩
    let r : ℕ → ℚ := fun n => u (N + n)
    refine ⟨r, ?_, ?_, ?_⟩
    · exact hu.injective.comp (fun _ _ h => by omega)
    · intro n
      constructor
      · exact_mod_cast hu0 (N + n)
      · exact_mod_cast hN (N + n) (by omega)
    · have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop := by
        apply tendsto_atTop.2
        intro b
        filter_upwards [eventually_ge_atTop b] with n hn
        omega
      exact hlim.comp hshift
  · have hypos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    rcases Real.exists_seq_rat_strictMono_tendsto y with
      ⟨u, hu, huy, hlim⟩
    have hev : ∀ᶠ n : ℕ in atTop, 0 < (u n : ℝ) :=
      hlim.eventually (Ioi_mem_nhds hypos)
    rcases eventually_atTop.1 hev with ⟨N, hN⟩
    let r : ℕ → ℚ := fun n => u (N + n)
    refine ⟨r, ?_, ?_, ?_⟩
    · exact hu.injective.comp (fun _ _ h => by omega)
    · intro n
      constructor
      · exact_mod_cast hN (N + n) (by omega)
      · have : (u (N + n) : ℝ) < 1 :=
          lt_of_lt_of_le (huy (N + n)) hy.2
        exact_mod_cast this
    · have hshift : Tendsto (fun n : ℕ => N + n) atTop atTop := by
        apply tendsto_atTop.2
        intro b
        filter_upwards [eventually_ge_atTop b] with n hn
        omega
      exact hlim.comp hshift

/-- Exercise 118, gap 1; the enumerating ellipsis becomes a range equality. -/
theorem gap1
    (x : ℕ → ℝ)
    (henum : EnumeratesUnitRationals x) :
    Set.range x = unitRationals := by
  exact henum

/-- Exercise 118, gap 2. -/
theorem gap2
    (x : ℕ → ℝ)
    (henum : EnumeratesUnitRationals x) :
    ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 →
      ∃ p : ℕ → ℕ, StrictMono p ∧ Tendsto (x ∘ p) atTop (𝓝 y) := by
  intro y hy
  rcases exists_unit_rat_seq y hy with ⟨r, hrinj, hrmem, hrlim⟩
  have hpre : ∀ n : ℕ, ∃ k : ℕ, x k = (r n : ℝ) := by
    intro n
    have hmem : (r n : ℝ) ∈ unitRationals :=
      ⟨r n, hrmem n |>.1, hrmem n |>.2, rfl⟩
    rw [← henum] at hmem
    exact hmem
  let f : ℕ → ℕ := fun n => Classical.choose (hpre n)
  have hxf (n : ℕ) : x (f n) = (r n : ℝ) :=
    Classical.choose_spec (hpre n)
  have hfinj : Function.Injective f := by
    intro a b hab
    apply hrinj
    exact_mod_cast (hxf a).symm.trans ((congrArg x hab).trans (hxf b))
  have hftop : Tendsto f atTop atTop := hfinj.nat_tendsto_atTop
  have hxlim : Tendsto (x ∘ f) atTop (𝓝 y) := by
    apply hrlim.congr'
    filter_upwards with n
    exact (hxf n).symm
  have hcluster_comp : MapClusterPt y atTop (x ∘ f) :=
    hxlim.mapClusterPt
  have hcluster : MapClusterPt y atTop x :=
    hcluster_comp.of_comp hftop
  exact TopologicalSpace.FirstCountableTopology.tendsto_subseq hcluster

/-- Exercise 118, gap 3. -/
theorem gap3
    (x : ℕ → ℝ)
    (henum : EnumeratesUnitRationals x) :
    ∀ y : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → y ∈ ProofGap.ClusterSet x := by
  exact gap2 x henum

/-- Exercise 118, gap 4. -/
theorem gap4
    (x : ℕ → ℝ)
    (henum : EnumeratesUnitRationals x) :
    ProofGap.ClusterSet x = Set.Icc (0 : ℝ) 1 := by
  ext y
  constructor
  · intro hy
    rcases hy with ⟨p, hp, hlim⟩
    apply isClosed_Icc.mem_of_tendsto hlim
    filter_upwards with n
    have hxmem : x (p n) ∈ unitRationals := by
      rw [← henum]
      exact ⟨p n, rfl⟩
    rcases hxmem with ⟨q, hq0, hq1, hqx⟩
    rw [Function.comp_apply, hqx]
    constructor
    · exact_mod_cast le_of_lt hq0
    · exact_mod_cast le_of_lt hq1
  · exact gap3 x henum y

end ProofGap.Exercise118
