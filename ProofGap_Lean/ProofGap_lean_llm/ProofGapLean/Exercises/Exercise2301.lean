import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Neighborhoods

open Filter
open scoped Interval

namespace ProofGap.Exercise2301

noncomputable section

def OrderedPartition (c : ℕ → ℝ) (p : ℕ) (a b : ℝ) : Prop :=
  c 0 = a ∧ c (p + 1) = b ∧ ∀ i ≤ p, c i < c (i + 1)

def cutIntegralSum (f : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (η : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1),
    ∫ x in c i + η..c (i + 1) - η, f x

def incrementSum (F : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (η : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1),
    (F (c (i + 1) - η) - F (c i + η))

def sideIncrementSum (L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (p + 1), (L (c (i + 1)) - R (c i))

def jumpSum (L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 p, (R (c i) - L (c i))

def PiecewiseAntiderivative
    (f F : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) : Prop :=
  ∀ i ≤ p, ∀ x ∈ Set.Ioo (c i) (c (i + 1)), HasDerivAt F (f x) x

def HasSideValues
    (F L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) : Prop :=
  (∀ i ≤ p + 1,
      Tendsto F (nhdsWithin (c i) (Set.Iio (c i))) (nhds (L (c i)))) ∧
    (∀ i ≤ p + 1,
      Tendsto F (nhdsWithin (c i) (Set.Ioi (c i))) (nhds (R (c i))))

private theorem orderedPartition_mono
    {c : ℕ → ℝ} {p : ℕ} {a b : ℝ}
    (hc : OrderedPartition c p a b) {i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ p + 1) : c i ≤ c j := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      by_cases hi : i = j + 1
      · subst i
        exact le_rfl
      · have hij' : i ≤ j := by omega
        have hjp : j ≤ p := by omega
        exact (ih hij' (by omega)).trans (hc.2.2 j hjp).le

private theorem orderedPartition_bounds
    {c : ℕ → ℝ} {p : ℕ} {a b : ℝ}
    (hc : OrderedPartition c p a b) {i : ℕ} (hi : i ≤ p + 1) :
    a ≤ c i ∧ c i ≤ b := by
  constructor
  · rw [← hc.1]
    exact orderedPartition_mono hc (Nat.zero_le i) hi
  · rw [← hc.2.1]
    exact orderedPartition_mono hc hi le_rfl

private theorem sum_adjacent_sub (G : ℕ → ℝ) (p : ℕ) :
    (∑ i ∈ Finset.range (p + 1), (G (i + 1) - G i)) =
      G (p + 1) - G 0 := by
  induction p with
  | zero => simp
  | succ p ih =>
      rw [Finset.sum_range_succ, ih]
      ring

private theorem partition_integral_sum
    (f : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hc : OrderedPartition c p a b) :
    (∑ i ∈ Finset.range (p + 1), ∫ x in c i..c (i + 1), f x) =
      ∫ x in a..b, f x := by
  calc
    (∑ i ∈ Finset.range (p + 1), ∫ x in c i..c (i + 1), f x) =
        ∑ i ∈ Finset.range (p + 1),
          ((∫ x in a..c (i + 1), f x) - ∫ x in a..c i, f x) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hip : i ≤ p := by
        simp only [Finset.mem_range] at hi
        omega
      have hib := orderedPartition_bounds hc (by omega : i ≤ p + 1)
      have hi1b := orderedPartition_bounds hc (by omega : i + 1 ≤ p + 1)
      have hseg_order : c i ≤ c (i + 1) := (hc.2.2 i hip).le
      have hacont : ContinuousOn f (Set.Icc a (c i)) := by
        apply hf.mono
        intro x hx
        exact ⟨hx.1, hx.2.trans hib.2⟩
      have hsegcont : ContinuousOn f (Set.Icc (c i) (c (i + 1))) := by
        apply hf.mono
        intro x hx
        exact ⟨hib.1.trans hx.1, hx.2.trans hi1b.2⟩
      have hai : IntervalIntegrable f MeasureTheory.volume a (c i) := by
        have hu : ContinuousOn f (Set.uIcc a (c i)) := by
          simpa [Set.uIcc_of_le hib.1] using hacont
        exact hu.intervalIntegrable
      have hseg : IntervalIntegrable f MeasureTheory.volume (c i) (c (i + 1)) := by
        have hu : ContinuousOn f (Set.uIcc (c i) (c (i + 1))) := by
          simpa [Set.uIcc_of_le hseg_order] using hsegcont
        exact hu.intervalIntegrable
      have hadd := intervalIntegral.integral_add_adjacent_intervals hai hseg
      linarith
    _ = (∫ x in a..c (p + 1), f x) - ∫ x in a..c 0, f x := by
      exact sum_adjacent_sub (fun j : ℕ => ∫ x in a..c j, f x) p
    _ = ∫ x in a..b, f x := by
      simp [hc.1, hc.2.1]

private theorem tendsto_cut_interval
    (f : ℝ → ℝ) {u v : ℝ}
    (hf : ContinuousOn f (Set.Icc u v)) (huv : u < v) :
    Tendsto (fun η : ℝ => ∫ x in u + η..v - η, f x)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in u..v, f x)) := by
  let l : Filter ℝ := nhdsWithin 0 (Set.Ioi 0)
  have hIntegrable : MeasureTheory.IntegrableOn f (Set.Icc u v) :=
    hf.integrableOn_Icc
  have hP0 : ContinuousOn
      (fun y => ∫ x in Set.Ioc u y, f x ∂MeasureTheory.volume)
      (Set.Icc u v) :=
    intervalIntegral.continuousOn_primitive (f := f) hIntegrable
  have hP : ContinuousOn (fun y => ∫ x in u..y, f x) (Set.Icc u v) := by
    refine hP0.congr ?_
    intro y hy
    exact intervalIntegral.integral_of_le (f := f) hy.1
  have hzero : Tendsto (fun η : ℝ => η) l (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  have hleft0 : Tendsto (fun η : ℝ => u + η) l (nhds u) := by
    simpa using (tendsto_const_nhds.add hzero)
  have hright0 : Tendsto (fun η : ℝ => v - η) l (nhds v) := by
    simpa using (tendsto_const_nhds.sub hzero)
  have hδ : 0 < (v - u) / 2 := by linarith
  have hpos : ∀ᶠ η : ℝ in l, 0 < η := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hη
  have hlt0 : ∀ᶠ η : ℝ in nhds 0, η < (v - u) / 2 := Iio_mem_nhds hδ
  have hlt : ∀ᶠ η : ℝ in l, η < (v - u) / 2 :=
    hlt0.filter_mono inf_le_left
  have hleft : Tendsto (fun η : ℝ => u + η) l
      (nhdsWithin u (Set.Icc u v)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hleft0, ?_⟩
    filter_upwards [hpos, hlt] with η hη hηlt
    exact ⟨by linarith, by linarith⟩
  have hright : Tendsto (fun η : ℝ => v - η) l
      (nhdsWithin v (Set.Icc u v)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hright0, ?_⟩
    filter_upwards [hpos, hlt] with η hη hηlt
    exact ⟨by linarith, by linarith⟩
  have hu_mem : u ∈ Set.Icc u v := ⟨le_rfl, huv.le⟩
  have hv_mem : v ∈ Set.Icc u v := ⟨huv.le, le_rfl⟩
  have hPu : Tendsto (fun y => ∫ x in u..y, f x)
      (nhdsWithin u (Set.Icc u v))
      (nhds (∫ x in u..u, f x)) :=
    hP u hu_mem
  have hPv : Tendsto (fun y => ∫ x in u..y, f x)
      (nhdsWithin v (Set.Icc u v))
      (nhds (∫ x in u..v, f x)) :=
    hP v hv_mem
  have hleftP : Tendsto (fun η : ℝ => ∫ x in u..u + η, f x) l
      (nhds (∫ x in u..u, f x)) := hPu.comp hleft
  have hrightP : Tendsto (fun η : ℝ => ∫ x in u..v - η, f x) l
      (nhds (∫ x in u..v, f x)) := hPv.comp hright
  have hdiff := hrightP.sub hleftP
  have hcut : Tendsto (fun η : ℝ => ∫ x in u + η..v - η, f x) l
      (nhds ((∫ x in u..v, f x) - ∫ x in u..u, f x)) := by
    refine hdiff.congr' ?_
    filter_upwards [hpos, hlt] with η hη hηlt
    have hins : u + η < v - η := by linarith
    have hf1 : ContinuousOn f (Set.Icc u (u + η)) := by
      apply hf.mono
      intro x hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    have hf2 : ContinuousOn f (Set.Icc (u + η) (v - η)) := by
      apply hf.mono
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hule : u ≤ u + η := by linarith
    have hf1u : ContinuousOn f (Set.uIcc u (u + η)) := by
      simpa [Set.uIcc_of_le hule] using hf1
    have hf2u : ContinuousOn f (Set.uIcc (u + η) (v - η)) := by
      simpa [Set.uIcc_of_le hins.le] using hf2
    have hInt1 : IntervalIntegrable f MeasureTheory.volume u (u + η) :=
      hf1u.intervalIntegrable
    have hInt2 : IntervalIntegrable f MeasureTheory.volume (u + η) (v - η) :=
      hf2u.intervalIntegrable
    have hadd := intervalIntegral.integral_add_adjacent_intervals hInt1 hInt2
    linarith
  simpa using hcut

private theorem side_sum_telescope
    (L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) :
    sideIncrementSum L R c p =
      L (c (p + 1)) - R (c 0) - jumpSum L R c p := by
  induction p with
  | zero =>
      simp [sideIncrementSum, jumpSum]
  | succ p ih =>
      rw [sideIncrementSum, jumpSum] at ih ⊢
      have hIcc : Finset.Icc 1 (p + 1) =
          insert (p + 1) (Finset.Icc 1 p) := by
        ext i
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnot : p + 1 ∉ Finset.Icc 1 p := by
        simp
      rw [Finset.sum_range_succ]
      rw [hIcc, Finset.sum_insert hnot, ih]
      ring

theorem gap1 (f : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hc : OrderedPartition c p a b) :
    Tendsto (cutIntegralSum f c p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in a..b, f x)) := by
  unfold cutIntegralSum
  have hsum :
      Tendsto
        (fun η : ℝ => ∑ i ∈ Finset.range (p + 1),
          ∫ x in c i + η..c (i + 1) - η, f x)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i ∈ Finset.range (p + 1),
          ∫ x in c i..c (i + 1), f x)) := by
    apply tendsto_finset_sum
    intro i hi
    have hip : i ≤ p := by
      simp only [Finset.mem_range] at hi
      omega
    have hci : ContinuousOn f (Set.Icc (c i) (c (i + 1))) := by
      apply hf.mono
      intro x hx
      have hib := orderedPartition_bounds hc (by omega : i ≤ p + 1)
      have hi1b := orderedPartition_bounds hc (by omega : i + 1 ≤ p + 1)
      exact ⟨hib.1.trans hx.1, hx.2.trans hi1b.2⟩
    exact tendsto_cut_interval f hci (hc.2.2 i hip)
  have hpartition := partition_integral_sum f c p a b hf hc
  rw [hpartition] at hsum
  exact hsum

theorem gap2 (f F : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ)
    (hF : PiecewiseAntiderivative f F c p) :
    ∀ i ≤ p, ∀ x ∈ Set.Ioo (c i) (c (i + 1)),
      HasDerivAt F (f x) x := by
  exact hF

theorem gap3 (f F : ℝ → ℝ) (c : ℕ → ℝ) (p i : ℕ) (η : ℝ)
    (hi : i ≤ p) (hη : 0 < η)
    (hinside : c i + η < c (i + 1) - η)
    (hf : ContinuousOn f (Set.Icc (c i + η) (c (i + 1) - η)))
    (hF : ∀ x ∈ Set.Icc (c i + η) (c (i + 1) - η),
      HasDerivAt F (f x) x) :
    (∫ x in c i + η..c (i + 1) - η, f x) =
      F (c (i + 1) - η) - F (c i + η) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    apply hF x
    simpa [Set.uIcc_of_le hinside.le] using hx
  · have hfu : ContinuousOn f
        (Set.uIcc (c i + η) (c (i + 1) - η)) := by
      simpa [Set.uIcc_of_le hinside.le] using hf
    exact hfu.intervalIntegrable

theorem gap4 (f F : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hc : OrderedPartition c p a b)
    (hF : PiecewiseAntiderivative f F c p) :
    Tendsto (incrementSum F c p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (∫ x in a..b, f x)) := by
  unfold incrementSum
  have hsum :
      Tendsto
        (fun η : ℝ => ∑ i ∈ Finset.range (p + 1),
          (F (c (i + 1) - η) - F (c i + η)))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i ∈ Finset.range (p + 1),
          ∫ x in c i..c (i + 1), f x)) := by
    apply tendsto_finset_sum
    intro i hi
    have hip : i ≤ p := by
      simp only [Finset.mem_range] at hi
      omega
    have huv : c i < c (i + 1) := hc.2.2 i hip
    have hci : ContinuousOn f (Set.Icc (c i) (c (i + 1))) := by
      apply hf.mono
      intro x hx
      have hib := orderedPartition_bounds hc (by omega : i ≤ p + 1)
      have hi1b := orderedPartition_bounds hc (by omega : i + 1 ≤ p + 1)
      exact ⟨hib.1.trans hx.1, hx.2.trans hi1b.2⟩
    have hbase := tendsto_cut_interval f hci huv
    refine hbase.congr' ?_
    have hδ : 0 < (c (i + 1) - c i) / 2 := by linarith
    have hpos : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < η := by
      filter_upwards [self_mem_nhdsWithin] with η hη
      exact hη
    have hlt0 : ∀ᶠ η : ℝ in nhds 0,
        η < (c (i + 1) - c i) / 2 := Iio_mem_nhds hδ
    have hlt : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0),
        η < (c (i + 1) - c i) / 2 := hlt0.filter_mono inf_le_left
    filter_upwards [hpos, hlt] with η hη hηlt
    have hins : c i + η < c (i + 1) - η := by linarith
    have hfη : ContinuousOn f
        (Set.Icc (c i + η) (c (i + 1) - η)) := by
      apply hci.mono
      intro x hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hFη : ∀ x ∈ Set.Icc (c i + η) (c (i + 1) - η),
        HasDerivAt F (f x) x := by
      intro x hx
      apply hF i hip x
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    exact gap3 f F c p i η hip hη hins hfη hFη
  have hpartition := partition_integral_sum f c p a b hf hc
  rw [hpartition] at hsum
  exact hsum

theorem gap5 (F L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ)
    (hsides : HasSideValues F L R c p) :
    Tendsto (incrementSum F c p)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sideIncrementSum L R c p)) := by
  unfold incrementSum sideIncrementSum
  have hzero : Tendsto (fun η : ℝ => η)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left inf_le_left
  apply tendsto_finset_sum
  intro i hi
  have hip : i ≤ p := by
    simp only [Finset.mem_range] at hi
    omega
  have hpos : ∀ᶠ η : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < η := by
    filter_upwards [self_mem_nhdsWithin] with η hη
    exact hη
  have hleft0 : Tendsto (fun η : ℝ => c (i + 1) - η)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c (i + 1))) := by
    simpa using (tendsto_const_nhds.sub hzero)
  have hleft : Tendsto (fun η : ℝ => c (i + 1) - η)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (c (i + 1)) (Set.Iio (c (i + 1)))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hleft0, ?_⟩
    filter_upwards [hpos] with η hη
    exact sub_lt_self _ hη
  have hright0 : Tendsto (fun η : ℝ => c i + η)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (c i)) := by
    simpa using (tendsto_const_nhds.add hzero)
  have hright : Tendsto (fun η : ℝ => c i + η)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (c i) (Set.Ioi (c i))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hright0, ?_⟩
    filter_upwards [hpos] with η hη
    exact lt_add_of_pos_right _ hη
  exact ((hsides.1 (i + 1) (by omega)).comp hleft).sub
    ((hsides.2 i (by omega)).comp hright)

theorem gap6 (f F L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hc : OrderedPartition c p a b)
    (hF : PiecewiseAntiderivative f F c p)
    (hsides : HasSideValues F L R c p) :
    (∫ x in a..b, f x) = sideIncrementSum L R c p := by
  exact tendsto_nhds_unique
    (gap4 f F c p a b hf hc hF)
    (gap5 F L R c p hsides)

theorem gap7 (L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (a b : ℝ)
    (hc : OrderedPartition c p a b) :
    sideIncrementSum L R c p =
      L b - R a - jumpSum L R c p := by
  rw [side_sum_telescope]
  rw [hc.1, hc.2.1]

theorem gap8 (f F L R : ℝ → ℝ) (c : ℕ → ℝ) (p : ℕ) (a b : ℝ)
    (hf : ContinuousOn f (Set.Icc a b))
    (hc : OrderedPartition c p a b)
    (hF : PiecewiseAntiderivative f F c p)
    (hsides : HasSideValues F L R c p) :
    (∫ x in a..b, f x) =
      L b - R a - jumpSum L R c p := by
  calc
    (∫ x in a..b, f x) = sideIncrementSum L R c p :=
      gap6 f F L R c p a b hf hc hF hsides
    _ = L b - R a - jumpSum L R c p := gap7 L R c p a b hc

end

end ProofGap.Exercise2301
