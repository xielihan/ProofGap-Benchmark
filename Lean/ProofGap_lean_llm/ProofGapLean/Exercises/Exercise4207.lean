import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Measurability
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise4207

noncomputable section

open MeasureTheory Set intervalIntegral

private abbrev BaseVec (n : ℕ) := Fin n → ℝ

private def baseSimplex (n : ℕ) : Set (BaseVec n) :=
  {v | (∀ i, 0 ≤ v i) ∧ ∑ i, v i ≤ 1}

private def baseIntegrand (n : ℕ) (v : BaseVec n) : ℝ :=
  Real.sqrt (∑ i, v i)

private def baseIntegral (n : ℕ) : ℝ :=
  ∫ v in baseSimplex n, baseIntegrand n v ∂MeasureTheory.volume

private def orderedSimplex (n : ℕ) (t : ℝ) : Set (BaseVec n) :=
  {v | (∀ i, 0 ≤ v i ∧ v i ≤ t) ∧
    ∀ i j, i < j → v j ≤ v i}

private def productIntegrand (n : ℕ) (f : ℝ → ℝ) (v : BaseVec n) : ℝ :=
  ∏ i, f (v i)

private def simplexIntegral (n : ℕ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ v in orderedSimplex n t, productIntegrand n f v ∂MeasureTheory.volume

private def primitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..t, f s

private def iteratedProductIntegral (f : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, _ => 1
  | n + 1, t =>
      ∫ s in (0 : ℝ)..t, f s * iteratedProductIntegral f n s

private theorem _exercise4203_orderedSimplex_isClosed (n : ℕ) (t : ℝ) :
    IsClosed (orderedSimplex n t) := by
  have hbox :
      IsClosed {v : BaseVec n | ∀ i, 0 ≤ v i ∧ v i ≤ t} := by
    have heq :
        {v : BaseVec n | ∀ i, 0 ≤ v i ∧ v i ≤ t} =
          Set.Icc (fun _ => 0) (fun _ => t) := by
      ext v
      constructor
      · intro hv
        exact ⟨fun i => (hv i).1, fun i => (hv i).2⟩
      · rintro ⟨hv0, hvt⟩ i
        exact ⟨hv0 i, hvt i⟩
    rw [heq]
    exact isClosed_Icc
  have hord :
      IsClosed {v : BaseVec n | ∀ i j, i < j → v j ≤ v i} := by
    have hpair (i j : Fin n) :
        IsClosed {v : BaseVec n | i < j → v j ≤ v i} := by
      by_cases hij : i < j
      · simpa [hij] using
          isClosed_le (continuous_apply j) (continuous_apply i)
      · simp [hij]
    have heq :
        {v : BaseVec n | ∀ i j, i < j → v j ≤ v i} =
          ⋂ i, ⋂ j, {v : BaseVec n | i < j → v j ≤ v i} := by
      ext v
      simp
    rw [heq]
    exact isClosed_iInter fun i => isClosed_iInter fun j => hpair i j
  exact hbox.inter hord

private theorem _exercise4203_orderedSimplex_isCompact (n : ℕ) (t : ℝ) :
    IsCompact (orderedSimplex n t) := by
  apply IsCompact.of_isClosed_subset
    (show IsCompact (Set.Icc (fun _ : Fin n => (0 : ℝ)) (fun _ => t)) from isCompact_Icc)
    (_exercise4203_orderedSimplex_isClosed n t)
  intro v hv
  exact ⟨fun i => (hv.1 i).1, fun i => (hv.1 i).2⟩

private theorem _exercise4203_productIntegrand_continuous
    (n : ℕ) (f : ℝ → ℝ) (hf : Continuous f) :
    Continuous (productIntegrand n f) := by
  unfold productIntegrand
  exact continuous_finset_prod Finset.univ fun i _ =>
    hf.comp (continuous_apply i)

private def splitVec (n : ℕ) (v : BaseVec (n + 1)) : ℝ × BaseVec n :=
  (v 0, fun i => v i.succ)

private def splitRegion (n : ℕ) (t : ℝ) : Set (ℝ × BaseVec n) :=
  {p | p.1 ∈ Set.Icc 0 t ∧ p.2 ∈ orderedSimplex n p.1}

private theorem _exercise4203_splitVec_measurePreserving (n : ℕ) :
    MeasurePreserving (splitVec n)
      (volume : Measure (BaseVec (n + 1)))
      ((volume : Measure ℝ).prod (volume : Measure (BaseVec n))) := by
  simpa [splitVec] using
    (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1)))

private theorem _exercise4203_splitVec_measurableEmbedding (n : ℕ) :
    MeasurableEmbedding (splitVec n) := by
  change MeasurableEmbedding
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1)))
  exact (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))).measurableEmbedding

private theorem _exercise4203_splitVec_surjective (n : ℕ) :
    Function.Surjective (splitVec n) := by
  change Function.Surjective
    (MeasurableEquiv.piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1)))
  exact (MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (n + 1) => ℝ) (0 : Fin (n + 1))).surjective

private theorem _exercise4203_splitRegion_preimage (n : ℕ) (t : ℝ) :
    splitVec n ⁻¹' splitRegion n t = orderedSimplex (n + 1) t := by
  ext v
  constructor
  · intro hv
    rcases hv with ⟨hv0, htail⟩
    constructor
    · intro i
      refine Fin.cases hv0 (fun j => ?_) i
      exact ⟨(htail.1 j).1, (htail.1 j).2.trans hv0.2⟩
    · intro i j hij
      cases i using Fin.cases with
      | zero =>
          obtain ⟨j', rfl⟩ :=
            Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hij)
          exact (htail.1 j').2
      | succ i' =>
          obtain ⟨j', rfl⟩ :=
            Fin.eq_succ_of_ne_zero (Fin.ne_zero_of_lt hij)
          exact htail.2 i' j' (by simpa using hij)
  · intro hv
    constructor
    · exact hv.1 0
    · constructor
      · intro i
        exact ⟨(hv.1 i.succ).1, hv.2 0 i.succ (by simp)⟩
      · intro i j hij
        exact hv.2 i.succ j.succ (by simpa using hij)

private theorem _exercise4203_splitRegion_image (n : ℕ) (t : ℝ) :
    splitVec n '' orderedSimplex (n + 1) t = splitRegion n t := by
  rw [← _exercise4203_splitRegion_preimage n t]
  exact (_exercise4203_splitVec_surjective n).image_preimage _

private theorem _exercise4203_split_productIntegrand
    (n : ℕ) (f : ℝ → ℝ) (v : BaseVec (n + 1)) :
    f (splitVec n v).1 *
        productIntegrand n f (splitVec n v).2 =
      productIntegrand (n + 1) f v := by
  simp [splitVec, productIntegrand, Fin.prod_univ_succ]

private theorem _exercise4203_simplexIntegral_succ
    (n : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (t : ℝ) (ht : 0 ≤ t) :
    simplexIntegral (n + 1) f t =
      ∫ s in (0 : ℝ)..t, f s * simplexIntegral n f s := by
  let g : ℝ × BaseVec n → ℝ :=
    fun p => f p.1 * productIntegrand n f p.2
  have hordered_succ :
      MeasurableSet (orderedSimplex (n + 1) t) :=
    (_exercise4203_orderedSimplex_isClosed (n + 1) t).measurableSet
  have hregion :
      MeasurableSet (splitRegion n t) := by
    rw [← _exercise4203_splitRegion_image n t]
    exact (_exercise4203_splitVec_measurableEmbedding n).measurableSet_image.mpr
      hordered_succ
  have hproduct_int :
      IntegrableOn (productIntegrand (n + 1) f)
        (orderedSimplex (n + 1) t) :=
    (_exercise4203_productIntegrand_continuous (n + 1) f hf).continuousOn.integrableOn_compact
      (_exercise4203_orderedSimplex_isCompact (n + 1) t)
  have hg_int : IntegrableOn g (splitRegion n t) := by
    change IntegrableOn g (splitRegion n t)
      ((volume : Measure ℝ).prod (volume : Measure (BaseVec n)))
    rw [← (_exercise4203_splitVec_measurePreserving n).integrableOn_comp_preimage
      (_exercise4203_splitVec_measurableEmbedding n)]
    rw [_exercise4203_splitRegion_preimage]
    have hcomp :
        g ∘ splitVec n = productIntegrand (n + 1) f := by
      funext v
      exact _exercise4203_split_productIntegrand n f v
    rw [hcomp]
    exact hproduct_int
  have htransform :
      simplexIntegral (n + 1) f t =
        ∫ p in splitRegion n t, g p := by
    unfold simplexIntegral
    calc
      (∫ v in orderedSimplex (n + 1) t,
          productIntegrand (n + 1) f v) =
          ∫ v in splitVec n ⁻¹' splitRegion n t,
            g (splitVec n v) := by
        rw [_exercise4203_splitRegion_preimage]
        exact setIntegral_congr_fun hordered_succ fun v _ =>
          (_exercise4203_split_productIntegrand n f v).symm
      _ = ∫ p in splitRegion n t, g p :=
        (_exercise4203_splitVec_measurePreserving n).setIntegral_preimage_emb
          (_exercise4203_splitVec_measurableEmbedding n) g (splitRegion n t)
  have hindicator :
      Integrable ((splitRegion n t).indicator g)
        ((volume : Measure ℝ).prod (volume : Measure (BaseVec n))) :=
    (integrable_indicator_iff hregion).mpr hg_int
  have hinner (x : ℝ) :
      (∫ w : BaseVec n, (splitRegion n t).indicator g (x, w)) =
        (Set.Icc 0 t).indicator
          (fun y => f y * simplexIntegral n f y) x := by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) t
    · rw [Set.indicator_of_mem hx]
      have hfun :
          (fun w : BaseVec n => (splitRegion n t).indicator g (x, w)) =
            (orderedSimplex n x).indicator
              (fun w => f x * productIntegrand n f w) := by
        funext w
        by_cases hw : w ∈ orderedSimplex n x
        · simp [splitRegion, g, hx.1, hx.2, hw]
        · simp [splitRegion, g, hx.1, hx.2, hw]
      rw [hfun]
      rw [MeasureTheory.integral_indicator
        (_exercise4203_orderedSimplex_isClosed n x).measurableSet]
      rw [MeasureTheory.integral_const_mul]
      rfl
    · rw [Set.indicator_of_notMem hx]
      have hzero :
          (fun w : BaseVec n => (splitRegion n t).indicator g (x, w)) = 0 := by
        funext w
        apply Set.indicator_of_notMem
        intro hmem
        exact hx hmem.1
      rw [hzero]
      simp
  have hfubini :
      (∫ p in splitRegion n t, g p) =
        ∫ x in Set.Icc (0 : ℝ) t,
          f x * simplexIntegral n f x := by
    calc
      (∫ p in splitRegion n t, g p) =
          ∫ p : ℝ × BaseVec n, (splitRegion n t).indicator g p := by
        rw [MeasureTheory.integral_indicator hregion]
      _ = ∫ x : ℝ,
          ∫ w : BaseVec n, (splitRegion n t).indicator g (x, w) := by
        exact MeasureTheory.integral_prod _ hindicator
      _ = ∫ x : ℝ,
          (Set.Icc 0 t).indicator
            (fun y => f y * simplexIntegral n f y) x := by
        exact integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = ∫ x in Set.Icc (0 : ℝ) t,
          f x * simplexIntegral n f x := by
        rw [MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    simplexIntegral (n + 1) f t =
        ∫ x in Set.Icc (0 : ℝ) t,
          f x * simplexIntegral n f x :=
      htransform.trans hfubini
    _ = ∫ s in (0 : ℝ)..t, f s * simplexIntegral n f s := by
      symm
      simp only [intervalIntegral.integral_of_le ht,
        setIntegral_congr_set
          (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]

private theorem _exercise4203_simplexIntegral_eq_iteratedProductIntegral
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ n t, 0 ≤ t →
      simplexIntegral n f t = iteratedProductIntegral f n t := by
  intro n
  induction n with
  | zero =>
      intro t _
      letI : ∀ i : Fin 0, IsProbabilityMeasure (volume : Measure ℝ) :=
        fun i => Fin.elim0 i
      letI : IsProbabilityMeasure (volume : Measure (BaseVec 0)) := inferInstance
      simp [simplexIntegral, orderedSimplex, productIntegrand,
        iteratedProductIntegral]
  | succ n ih =>
      intro t ht
      rw [_exercise4203_simplexIntegral_succ n f hf t ht]
      rw [iteratedProductIntegral]
      apply intervalIntegral.integral_congr
      intro x hx
      change f x * simplexIntegral n f x =
        f x * iteratedProductIntegral f n x
      have hxIcc : x ∈ Set.Icc (0 : ℝ) t := by
        simpa [Set.uIcc_of_le ht] using hx
      rw [ih x hxIcc.1]

private theorem _exercise4203_iteratedProductIntegral_closedForm
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ n t, iteratedProductIntegral f n t =
      (primitive f t) ^ n / (Nat.factorial n : ℝ) := by
  have hprim : ∀ x : ℝ, HasDerivAt (primitive f) (f x) x := by
    intro x
    simpa [primitive] using
      (intervalIntegral.integral_hasDerivAt_right
        (hf.intervalIntegrable (0 : ℝ) x)
        hf.stronglyMeasurable.stronglyMeasurableAtFilter
        hf.continuousAt)
  have hprim_cont : Continuous (primitive f) :=
    continuous_iff_continuousAt.mpr (fun x => (hprim x).continuousAt)
  intro n
  induction n with
  | zero =>
      intro t
      simp [iteratedProductIntegral]
  | succ n ih =>
      intro t
      rw [iteratedProductIntegral]
      simp_rw [ih]
      have hder : ∀ x : ℝ,
          HasDerivAt
            (fun y => primitive f y ^ (n + 1) /
              (Nat.factorial (n + 1) : ℝ))
            (f x * (primitive f x ^ n /
              (Nat.factorial n : ℝ))) x := by
        intro x
        convert (((hprim x).pow (n + 1)).mul_const
          (1 / (Nat.factorial (n + 1) : ℝ))) using 1
        · funext y
          simp [Pi.pow_apply, div_eq_mul_inv]
        · simp only [Nat.add_sub_cancel, Nat.factorial_succ,
            Nat.cast_mul, Nat.cast_add, Nat.cast_one]
          field_simp
      have hint : IntervalIntegrable
          (fun x => f x * (primitive f x ^ n /
            (Nat.factorial n : ℝ))) MeasureTheory.volume 0 t := by
        apply Continuous.intervalIntegrable
        exact hf.mul
          ((hprim_cont.pow n).div_const
            (Nat.factorial n : ℝ))
      calc
        (∫ x in (0 : ℝ)..t,
            f x * (primitive f x ^ n /
              (Nat.factorial n : ℝ))) =
            (primitive f t) ^ (n + 1) /
                (Nat.factorial (n + 1) : ℝ) -
              (primitive f 0) ^ (n + 1) /
                (Nat.factorial (n + 1) : ℝ) := by
          exact intervalIntegral.integral_eq_sub_of_hasDerivAt
            (fun x _ => hder x) hint
        _ = (primitive f t) ^ (n + 1) /
            (Nat.factorial (n + 1) : ℝ) := by
          simp [primitive]

private def cumulativeMatrix (n : ℕ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => if i ≤ j then 1 else 0

private def cumulative (n : ℕ) :
    BaseVec (n + 1) →ₗ[ℝ] BaseVec (n + 1) :=
  Matrix.toLin' (cumulativeMatrix n)

private theorem cumulative_apply (n : ℕ) (x : BaseVec (n + 1))
    (i : Fin (n + 1)) :
    cumulative n x i = ∑ j ∈ Finset.Ici i, x j := by
  simp [cumulative, Matrix.toLin'_apply, Matrix.mulVec,
    dotProduct, cumulativeMatrix, Finset.sum_ite]
  congr 1
  ext j
  simp

private theorem cumulative_zero (n : ℕ) (x : BaseVec (n + 1)) :
    cumulative n x 0 = ∑ j, x j := by
  rw [cumulative_apply]
  congr 1
  ext j
  simp

private theorem cumulative_step (n : ℕ) (x : BaseVec (n + 1))
    (i : Fin n) :
    cumulative n x i.castSucc =
      x i.castSucc + cumulative n x i.succ := by
  rw [cumulative_apply, cumulative_apply]
  have hset :
      Finset.Ici i.castSucc =
        insert i.castSucc (Finset.Ici i.succ) := by
    ext j
    simp only [Finset.mem_Ici, Finset.mem_insert, Fin.ext_iff]
    change (i.val ≤ j.val) ↔
      (j.val = i.val ∨ i.val + 1 ≤ j.val)
    omega
  rw [hset, Finset.sum_insert]
  simp

private theorem cumulative_last (n : ℕ) (x : BaseVec (n + 1)) :
    cumulative n x (Fin.last n) = x (Fin.last n) := by
  rw [cumulative_apply]
  have hset :
      Finset.Ici (Fin.last n) = {Fin.last n} := by
    ext j
    simp only [Finset.mem_Ici, Finset.mem_singleton, Fin.ext_iff]
    change (n ≤ j.val) ↔ j.val = n
    omega
  rw [hset]
  simp

private theorem cumulativeMatrix_det (n : ℕ) :
    Matrix.det (cumulativeMatrix n) = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · simp [cumulativeMatrix]
  · intro i j hji
    have hji' : j < i := by simpa only [id_eq] using hji
    simp [cumulativeMatrix, (not_le_of_gt hji')]

private theorem cumulative_measurePreserving (n : ℕ) :
    MeasurePreserving (cumulative n)
      (volume : Measure (BaseVec (n + 1)))
      (volume : Measure (BaseVec (n + 1))) := by
  refine ⟨(cumulative n).continuous_of_finiteDimensional.measurable, ?_⟩
  rw [cumulative, Real.map_matrix_volume_pi_eq_smul_volume_pi]
  · simp [cumulativeMatrix_det]
  · simp [cumulativeMatrix_det]

private theorem cumulative_measurableEmbedding (n : ℕ) :
    MeasurableEmbedding (cumulative n) := by
  have hdet :
      LinearMap.det (cumulative n) ≠ 0 := by
    rw [cumulative, LinearMap.det_toLin', cumulativeMatrix_det]
    norm_num
  change MeasurableEmbedding
    ((cumulative n).equivOfDetNeZero hdet)
  exact
    ((cumulative n).equivOfDetNeZero hdet).toContinuousLinearEquiv
      |>.toHomeomorph.toMeasurableEquiv.measurableEmbedding

private theorem cumulative_preimage_orderedSimplex (n : ℕ) :
    cumulative n ⁻¹' orderedSimplex (n + 1) 1 =
      baseSimplex (n + 1) := by
  ext x
  constructor
  · intro hx
    constructor
    · intro i
      by_cases hi : i = Fin.last n
      · subst i
        rw [← cumulative_last n x]
        exact (hx.1 (Fin.last n)).1
      · let k : Fin n := i.castPred hi
        have hki : k.castSucc = i := Fin.castSucc_castPred i hi
        have hord :
            cumulative n x k.succ ≤ cumulative n x k.castSucc :=
          hx.2 k.castSucc k.succ (by simp)
        rw [cumulative_step] at hord
        rw [← hki]
        linarith
    · rw [← cumulative_zero n x]
      exact (hx.1 0).2
  · intro hx
    constructor
    · intro i
      rw [cumulative_apply]
      constructor
      · exact Finset.sum_nonneg fun j _ => hx.1 j
      · exact
          (Finset.sum_le_sum_of_subset_of_nonneg
            (by simp : Finset.Ici i ⊆ Finset.univ)
            (fun j _ _ => hx.1 j)).trans hx.2
    · intro i j hij
      rw [cumulative_apply, cumulative_apply]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun k hk => by
          simp only [Finset.mem_Ici] at hk ⊢
          exact hij.le.trans hk)
        (fun k _ _ => hx.1 k)

private theorem orderedSimplex_integral_one
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫ v in orderedSimplex n t, (1 : ℝ)) =
      t ^ n / (Nat.factorial n : ℝ) := by
  have h :=
    _exercise4203_simplexIntegral_eq_iteratedProductIntegral
      (fun _ : ℝ => (1 : ℝ)) continuous_const n t ht
  rw [_exercise4203_iteratedProductIntegral_closedForm
    (fun _ : ℝ => (1 : ℝ)) continuous_const n t] at h
  simpa [simplexIntegral, productIntegrand, primitive] using h

private theorem orderedSimplex_head_integral
    (n : ℕ) (f : ℝ → ℝ) (hf : Continuous f)
    (t : ℝ) (ht : 0 ≤ t) :
    (∫ v in orderedSimplex (n + 1) t, f (v 0)) =
      ∫ s in (0 : ℝ)..t,
        f s * (s ^ n / (Nat.factorial n : ℝ)) := by
  let g : ℝ × BaseVec n → ℝ := fun p => f p.1
  have hordered :
      MeasurableSet (orderedSimplex (n + 1) t) :=
    (_exercise4203_orderedSimplex_isClosed (n + 1) t).measurableSet
  have hregion :
      MeasurableSet (splitRegion n t) := by
    rw [← _exercise4203_splitRegion_image n t]
    exact (_exercise4203_splitVec_measurableEmbedding n).measurableSet_image.mpr
      hordered
  have hhead_int :
      IntegrableOn (fun v : BaseVec (n + 1) => f (v 0))
        (orderedSimplex (n + 1) t) :=
    (hf.comp (continuous_apply 0)).continuousOn.integrableOn_compact
      (_exercise4203_orderedSimplex_isCompact (n + 1) t)
  have hg_int : IntegrableOn g (splitRegion n t) := by
    change IntegrableOn g (splitRegion n t)
      ((volume : Measure ℝ).prod (volume : Measure (BaseVec n)))
    rw [← (_exercise4203_splitVec_measurePreserving n).integrableOn_comp_preimage
      (_exercise4203_splitVec_measurableEmbedding n)]
    rw [_exercise4203_splitRegion_preimage]
    have hcomp :
        g ∘ splitVec n = fun v : BaseVec (n + 1) => f (v 0) := by
      funext v
      rfl
    rw [hcomp]
    exact hhead_int
  have htransform :
      (∫ v in orderedSimplex (n + 1) t, f (v 0)) =
        ∫ p in splitRegion n t, g p := by
    calc
      (∫ v in orderedSimplex (n + 1) t, f (v 0)) =
          ∫ v in splitVec n ⁻¹' splitRegion n t,
            g (splitVec n v) := by
        rw [_exercise4203_splitRegion_preimage]
        exact setIntegral_congr_fun hordered fun _ _ => rfl
      _ = ∫ p in splitRegion n t, g p :=
        (_exercise4203_splitVec_measurePreserving n).setIntegral_preimage_emb
          (_exercise4203_splitVec_measurableEmbedding n) g (splitRegion n t)
  have hindicator :
      Integrable ((splitRegion n t).indicator g)
        ((volume : Measure ℝ).prod (volume : Measure (BaseVec n))) :=
    (integrable_indicator_iff hregion).mpr hg_int
  have hinner (x : ℝ) :
      (∫ w : BaseVec n, (splitRegion n t).indicator g (x, w)) =
        (Set.Icc 0 t).indicator
          (fun y => f y * (y ^ n / (Nat.factorial n : ℝ))) x := by
    by_cases hx : x ∈ Set.Icc (0 : ℝ) t
    · rw [Set.indicator_of_mem hx]
      have hfun :
          (fun w : BaseVec n => (splitRegion n t).indicator g (x, w)) =
            (orderedSimplex n x).indicator
              (fun _ => f x * (1 : ℝ)) := by
        funext w
        by_cases hw : w ∈ orderedSimplex n x
        · simp [splitRegion, g, hx.1, hx.2, hw]
        · simp [splitRegion, g, hx.1, hx.2, hw]
      rw [hfun]
      rw [MeasureTheory.integral_indicator
        (_exercise4203_orderedSimplex_isClosed n x).measurableSet]
      rw [MeasureTheory.integral_const_mul]
      rw [orderedSimplex_integral_one n x hx.1]
    · rw [Set.indicator_of_notMem hx]
      have hzero :
          (fun w : BaseVec n => (splitRegion n t).indicator g (x, w)) = 0 := by
        funext w
        apply Set.indicator_of_notMem
        intro hmem
        exact hx hmem.1
      rw [hzero]
      simp
  have hfubini :
      (∫ p in splitRegion n t, g p) =
        ∫ x in Set.Icc (0 : ℝ) t,
          f x * (x ^ n / (Nat.factorial n : ℝ)) := by
    calc
      (∫ p in splitRegion n t, g p) =
          ∫ p : ℝ × BaseVec n, (splitRegion n t).indicator g p := by
        rw [MeasureTheory.integral_indicator hregion]
      _ = ∫ x : ℝ,
          ∫ w : BaseVec n, (splitRegion n t).indicator g (x, w) := by
        exact MeasureTheory.integral_prod _ hindicator
      _ = ∫ x : ℝ,
          (Set.Icc 0 t).indicator
            (fun y => f y * (y ^ n / (Nat.factorial n : ℝ))) x := by
        exact integral_congr_ae (Filter.Eventually.of_forall hinner)
      _ = ∫ x in Set.Icc (0 : ℝ) t,
          f x * (x ^ n / (Nat.factorial n : ℝ)) := by
        rw [MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    (∫ v in orderedSimplex (n + 1) t, f (v 0)) =
        ∫ x in Set.Icc (0 : ℝ) t,
          f x * (x ^ n / (Nat.factorial n : ℝ)) :=
      htransform.trans hfubini
    _ = ∫ s in (0 : ℝ)..t,
        f s * (s ^ n / (Nat.factorial n : ℝ)) := by
      symm
      simp only [intervalIntegral.integral_of_le ht,
        setIntegral_congr_set
          (Ioc_ae_eq_Icc (α := ℝ) (μ := volume))]

private theorem integral_eq_ordered_head (n : ℕ) :
    baseIntegral (n + 1) =
      ∫ v in orderedSimplex (n + 1) 1, Real.sqrt (v 0) := by
  have hordered :
      MeasurableSet (orderedSimplex (n + 1) 1) :=
    (_exercise4203_orderedSimplex_isClosed (n + 1) 1).measurableSet
  have hsimplex :
      MeasurableSet (baseSimplex (n + 1)) := by
    rw [← cumulative_preimage_orderedSimplex n]
    exact hordered.preimage
      (cumulative_measurePreserving n).measurable
  have hchange :=
    (cumulative_measurePreserving n).setIntegral_preimage_emb
      (cumulative_measurableEmbedding n)
      (fun v : BaseVec (n + 1) => Real.sqrt (v 0))
      (orderedSimplex (n + 1) 1)
  calc
    baseIntegral (n + 1) =
        ∫ x in cumulative n ⁻¹' orderedSimplex (n + 1) 1,
          Real.sqrt (cumulative n x 0) := by
      unfold baseIntegral baseIntegrand
      rw [cumulative_preimage_orderedSimplex]
      exact setIntegral_congr_fun
        hsimplex
        fun x _ => by rw [cumulative_zero]
    _ = ∫ v in orderedSimplex (n + 1) 1,
        Real.sqrt (v 0) := hchange

private theorem sqrt_pow_integral (n : ℕ) :
    (∫ s in (0 : ℝ)..1,
        Real.sqrt s * (s ^ n / (Nat.factorial n : ℝ))) =
      2 /
        ((Nat.factorial n : ℝ) *
          (2 * (n : ℝ) + 3)) := by
  have hfac : (Nat.factorial n : ℝ) ≠ 0 := by positivity
  have hr : (-1 : ℝ) < (1 / 2 : ℝ) + (n : ℝ) := by
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  calc
    (∫ s in (0 : ℝ)..1,
        Real.sqrt s * (s ^ n / (Nat.factorial n : ℝ))) =
        ∫ s in (0 : ℝ)..1,
          (1 / (Nat.factorial n : ℝ)) *
            s ^ ((1 / 2 : ℝ) + (n : ℝ)) := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hs0 : 0 ≤ s := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs.1
      change
        Real.sqrt s * (s ^ n / (Nat.factorial n : ℝ)) =
          (1 / (Nat.factorial n : ℝ)) *
            s ^ ((1 / 2 : ℝ) + (n : ℝ))
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast]
      rw [Real.rpow_add_of_nonneg hs0
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (Nat.cast_nonneg n)]
      ring
    _ = (1 / (Nat.factorial n : ℝ)) *
        (∫ s in (0 : ℝ)..1,
          s ^ ((1 / 2 : ℝ) + (n : ℝ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (1 / (Nat.factorial n : ℝ)) *
        ((1 ^ ((1 / 2 : ℝ) + (n : ℝ) + 1) -
            0 ^ ((1 / 2 : ℝ) + (n : ℝ) + 1)) /
          ((1 / 2 : ℝ) + (n : ℝ) + 1)) := by
      rw [integral_rpow (Or.inl hr)]
    _ = 2 /
        ((Nat.factorial n : ℝ) *
          (2 * (n : ℝ) + 3)) := by
      rw [Real.one_rpow]
      have hpow : (0 : ℝ) ^
          ((1 / 2 : ℝ) + (n : ℝ) + 1) = 0 :=
        Real.zero_rpow (by positivity)
      rw [hpow]
      field_simp [hfac]
      ring

/-! Source: `results/stage1_gpt55/09_重积分与含参积分/exercise_4207_autoformalization_result/exercise_4207.md`. -/

private theorem baseSimplexFormula (n : ℕ) (hn : 0 < n) :
    baseIntegral n =
      2 / ((Nat.factorial (n - 1) : ℝ) * (2 * (n : ℝ) + 1)) := by
  cases n with
  | zero => omega
  | succ k =>
      rw [integral_eq_ordered_head k]
      rw [orderedSimplex_head_integral k Real.sqrt Real.continuous_sqrt
        1 (by norm_num)]
      rw [sqrt_pow_integral k]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring

def unitCube (n : ℕ) : Set (Fin n → ℝ) :=
  {u | ∀ i, u i ∈ Set.Icc (0 : ℝ) 1}

def simplex (n : ℕ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1}

def stickBreaking {n : ℕ} (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  if h : i.val + 1 < n then
    (∏ j ∈ Finset.univ.filter (fun j : Fin n => j.val ≤ i.val), u j) *
      (1 - u ⟨i.val + 1, h⟩)
  else
    ∏ j, u j

def jacobianMatrix (n : ℕ) (u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    deriv
      (fun t => stickBreaking (Function.update u j t) i)
      (u j)

def jacobianMagnitude (n : ℕ) (u : Fin n → ℝ) : ℝ :=
  |(jacobianMatrix n u).det|

def jacobianFactor (n : ℕ) (u : Fin n → ℝ) : ℝ :=
  ∏ i, (u i) ^ (n - 1 - i.val)

def simplexSqrtIntegral (n : ℕ) : ℝ :=
  ∫ x in simplex n, Real.sqrt (∑ i, x i)

def transformedIntegral (n : ℕ) : ℝ :=
  ∫ u in unitCube n,
    Real.sqrt (∑ i, stickBreaking u i) * jacobianFactor n u

theorem gap1
    {n : ℕ} {u : Fin n → ℝ} (hu : u ∈ unitCube n) :
    ∀ i, 0 ≤ u i ∧ u i ≤ 1 := by
  intro i
  exact hu i

private def prefixProduct {n : ℕ}
    (u : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j ∈ Finset.Iic i, u j

private theorem prefixProduct_succ
    (k : ℕ) (u : Fin (k + 1) → ℝ) (i : Fin k) :
    prefixProduct u i.succ =
      prefixProduct u i.castSucc * u i.succ := by
  have hset :
      Finset.Iic i.succ =
        insert i.succ (Finset.Iic i.castSucc) := by
    ext j
    simp only [Finset.mem_Iic, Finset.mem_insert,
      Fin.ext_iff]
    change (j.val ≤ i.val + 1) ↔
      (j.val = i.val + 1 ∨ j.val ≤ i.val)
    omega
  rw [prefixProduct, hset, Finset.prod_insert]
  · simp only [prefixProduct]
    ring
  · simp

private theorem stickBreaking_castSucc
    (k : ℕ) (u : Fin (k + 1) → ℝ) (i : Fin k) :
    stickBreaking u i.castSucc =
      prefixProduct u i.castSucc -
        prefixProduct u i.succ := by
  have hnext : i.castSucc.val + 1 < k + 1 := by
    change i.val + 1 < k + 1
    omega
  have hfin :
      (⟨i.castSucc.val + 1, hnext⟩ : Fin (k + 1)) =
        i.succ := by
    apply Fin.ext
    rfl
  rw [stickBreaking, dif_pos hnext]
  have hfilter :
      Finset.univ.filter
          (fun j : Fin (k + 1) =>
            j.val ≤ i.castSucc.val) =
        Finset.Iic i.castSucc := by
    ext j
    simp [Fin.le_iff_val_le_val]
  rw [hfilter, ← prefixProduct,
    prefixProduct_succ k u i]
  rw [hfin]
  ring

private theorem stickBreaking_last
    (k : ℕ) (u : Fin (k + 1) → ℝ) :
    stickBreaking u (Fin.last k) =
      prefixProduct u (Fin.last k) := by
  have hnext : ¬(Fin.last k).val + 1 < k + 1 := by
    simp
  rw [stickBreaking, dif_neg hnext]
  unfold prefixProduct
  congr 1
  ext j
  simp only [Finset.mem_Iic, Finset.mem_univ]
  constructor
  · intro _
    exact Fin.le_last j
  · intro _
    trivial

private theorem stickBreaking_tail_sum
    (k : ℕ) (u : Fin (k + 1) → ℝ)
    (i : Fin (k + 1)) :
    ∑ j ∈ Finset.Ici i, stickBreaking u j =
      prefixProduct u i := by
  induction i using Fin.reverseInduction with
  | last =>
      have hset :
          Finset.Ici (Fin.last k) = {Fin.last k} := by
        ext j
        simp only [Finset.mem_Ici, Finset.mem_singleton,
          Fin.ext_iff]
        change (k ≤ j.val) ↔ j.val = k
        omega
      rw [hset]
      simp [stickBreaking_last]
  | cast i ih =>
      have hset :
          Finset.Ici i.castSucc =
            insert i.castSucc (Finset.Ici i.succ) := by
        ext j
        simp only [Finset.mem_Ici, Finset.mem_insert,
          Fin.ext_iff]
        change (i.val ≤ j.val) ↔
          (j.val = i.val ∨ i.val + 1 ≤ j.val)
        omega
      rw [hset, Finset.sum_insert]
      · rw [stickBreaking_castSucc, ih]
        ring
      · simp

private def prefixJacobian
    (n : ℕ) (u : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    deriv
      (fun t =>
        prefixProduct (Function.update u j t) i)
      (u j)

private theorem update_apply_differentiableAt
    {n : ℕ} (u : Fin n → ℝ) (j r : Fin n) (x : ℝ) :
    DifferentiableAt ℝ
      (fun t => Function.update u j t r) x := by
  by_cases h : r = j
  · subst r
    simp
  · simp [h]

private theorem update_prod_differentiableAt
    {n : ℕ} (u : Fin n → ℝ) (j : Fin n)
    (s : Finset (Fin n)) (x : ℝ) :
    DifferentiableAt ℝ
      (fun t => ∏ r ∈ s, Function.update u j t r) x := by
  have hfun :
      (∏ r ∈ s,
          (fun t : ℝ =>
            Function.update u j t r)) =
        (fun t =>
          ∏ r ∈ s,
            Function.update u j t r) := by
    funext t
    simp only [Finset.prod_apply]
  rw [← hfun]
  exact DifferentiableAt.finset_prod
    (𝕜 := ℝ) (u := s)
    (f := fun r t => Function.update u j t r)
    (fun r _ =>
      update_apply_differentiableAt u j r x)

private theorem stickBreaking_update_differentiableAt
    {n : ℕ} (u : Fin n → ℝ) (i j : Fin n) :
    DifferentiableAt ℝ
      (fun t =>
        stickBreaking (Function.update u j t) i)
      (u j) := by
  unfold stickBreaking
  split
  · apply DifferentiableAt.mul
    · exact update_prod_differentiableAt u j _ (u j)
    · apply DifferentiableAt.sub
      · fun_prop
      · exact update_apply_differentiableAt u j _ (u j)
  · change DifferentiableAt ℝ
      (fun t =>
        ∏ r ∈ Finset.univ,
          Function.update u j t r) (u j)
    exact update_prod_differentiableAt
      u j Finset.univ (u j)

private theorem prefixProduct_update_differentiableAt
    {n : ℕ} (u : Fin n → ℝ) (i j : Fin n) :
    DifferentiableAt ℝ
      (fun t =>
        prefixProduct (Function.update u j t) i)
      (u j) := by
  unfold prefixProduct
  exact update_prod_differentiableAt u j _ (u j)

private theorem cumulative_mul_jacobian
    (k : ℕ) (u : Fin (k + 1) → ℝ) :
    cumulativeMatrix k * jacobianMatrix (k + 1) u =
      prefixJacobian (k + 1) u := by
  ext i j
  simp only [Matrix.mul_apply, cumulativeMatrix,
    jacobianMatrix, prefixJacobian]
  have hsum :
      (∑ x,
        (if i ≤ x then 1 else 0) *
          deriv
            (fun t =>
              stickBreaking
                (Function.update u j t) x)
            (u j)) =
        ∑ x ∈ Finset.Ici i,
          deriv
            (fun t =>
              stickBreaking
                (Function.update u j t) x)
            (u j) := by
    simp [Finset.sum_ite]
    congr 1
    ext x
    simp
  rw [hsum]
  rw [← deriv_fun_sum
    (fun r _ =>
      stickBreaking_update_differentiableAt u r j)]
  congr 1
  funext t
  rw [stickBreaking_tail_sum k
    (Function.update u j t) i]

private theorem update_prod_eq_of_mem
    {n : ℕ} (u : Fin n → ℝ) (j : Fin n)
    (s : Finset (Fin n)) (hj : j ∈ s) (t : ℝ) :
    (∏ r ∈ s, Function.update u j t r) =
      t * ∏ r ∈ s.erase j, u r := by
  rw [← Finset.mul_prod_erase s
    (fun r => Function.update u j t r) hj]
  congr 1
  · simp
  · apply Finset.prod_congr rfl
    intro r hr
    have hrj : r ≠ j := Finset.ne_of_mem_erase hr
    simp [hrj]

private theorem update_prod_eq_of_not_mem
    {n : ℕ} (u : Fin n → ℝ) (j : Fin n)
    (s : Finset (Fin n)) (hj : j ∉ s) (t : ℝ) :
    (∏ r ∈ s, Function.update u j t r) =
      ∏ r ∈ s, u r := by
  apply Finset.prod_congr rfl
  intro r hr
  have hrj : r ≠ j := by
    intro h
    subst r
    exact hj hr
  simp [hrj]

private theorem deriv_update_prod_of_mem
    {n : ℕ} (u : Fin n → ℝ) (j : Fin n)
    (s : Finset (Fin n)) (hj : j ∈ s) (x : ℝ) :
    deriv
        (fun t =>
          ∏ r ∈ s, Function.update u j t r)
        x =
      ∏ r ∈ s.erase j, u r := by
  have hfun :
      (fun t =>
        ∏ r ∈ s, Function.update u j t r) =
        (fun t =>
          t * ∏ r ∈ s.erase j, u r) := by
    funext t
    exact update_prod_eq_of_mem u j s hj t
  rw [hfun]
  simp

private theorem deriv_update_prod_of_not_mem
    {n : ℕ} (u : Fin n → ℝ) (j : Fin n)
    (s : Finset (Fin n)) (hj : j ∉ s) (x : ℝ) :
    deriv
        (fun t =>
          ∏ r ∈ s, Function.update u j t r)
        x = 0 := by
  have hfun :
      (fun t =>
        ∏ r ∈ s, Function.update u j t r) =
        (fun _ =>
          ∏ r ∈ s, u r) := by
    funext t
    exact update_prod_eq_of_not_mem u j s hj t
  rw [hfun]
  simp

private theorem prefixJacobian_above
    {n : ℕ} (u : Fin n → ℝ) (i j : Fin n)
    (hij : i < j) :
    prefixJacobian n u i j = 0 := by
  unfold prefixJacobian prefixProduct
  apply deriv_update_prod_of_not_mem
  simpa using (not_le_of_gt hij)

private theorem prefixJacobian_diag
    {n : ℕ} (u : Fin n → ℝ) (i : Fin n) :
    prefixJacobian n u i i =
      ∏ r ∈ Finset.Iio i, u r := by
  unfold prefixJacobian prefixProduct
  rw [deriv_update_prod_of_mem]
  · congr 1
    ext r
    simp only [Finset.mem_erase, Finset.mem_Iic,
      Finset.mem_Iio]
    constructor
    · rintro ⟨hri, hle⟩
      exact lt_of_le_of_ne hle hri
    · intro hri
      exact ⟨ne_of_lt hri, le_of_lt hri⟩
  · simp

private theorem prefixJacobian_det
    {n : ℕ} (u : Fin n → ℝ) :
    (prefixJacobian n u).det =
      ∏ i, ∏ r ∈ Finset.Iio i, u r := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_congr rfl
    intro i _
    exact prefixJacobian_diag u i
  · intro i j hij
    apply prefixJacobian_above u i j
    exact hij

private theorem prefix_diagonal_product
    {n : ℕ} (u : Fin n → ℝ) :
    (∏ i, ∏ r ∈ Finset.Iio i, u r) =
      jacobianFactor n u := by
  unfold jacobianFactor
  calc
    (∏ i, ∏ r ∈ Finset.Iio i, u r) =
        ∏ i, ∏ r,
          if r ∈ Finset.Iio i then u r else 1 := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.prod_ite_mem_eq]
    _ = ∏ r, ∏ i,
          if r ∈ Finset.Iio i then u r else 1 := by
      exact Finset.prod_comm
    _ = ∏ r, u r ^ (n - 1 - r.val) := by
      apply Finset.prod_congr rfl
      intro r _
      calc
        (∏ i,
            if r ∈ Finset.Iio i then u r else 1) =
            ∏ i ∈ Finset.Ioi r, u r := by
          simpa only [Finset.mem_Iio, Finset.mem_Ioi] using
            (Finset.prod_ite_mem_eq
              (Finset.Ioi r) (fun _ => u r))
        _ = u r ^ (n - 1 - r.val) := by
          simp [Fin.card_Ioi]

theorem gap2
    (n : ℕ) (hn : 1 ≤ n) (u : Fin n → ℝ)
    (hu : u ∈ unitCube n) :
    jacobianMagnitude n u = jacobianFactor n u := by
  cases n with
  | zero => omega
  | succ k =>
      have hdet := congrArg Matrix.det
        (cumulative_mul_jacobian k u)
      rw [Matrix.det_mul, cumulativeMatrix_det,
        one_mul, prefixJacobian_det,
        prefix_diagonal_product] at hdet
      unfold jacobianMagnitude
      rw [hdet, abs_of_nonneg]
      unfold jacobianFactor
      apply Finset.prod_nonneg
      intro i _
      exact pow_nonneg (hu i).1 _

theorem gap5 (n : ℕ) (hn : 1 ≤ n) :
    simplexSqrtIntegral n =
      2 /
        ((Nat.factorial (n - 1) : ℝ) *
          (2 * (n : ℝ) + 1)) := by
  simpa only [simplexSqrtIntegral, simplex,
    baseIntegral, baseSimplex, baseIntegrand] using
    baseSimplexFormula n (by omega)

private theorem unitCube_eq_pi (n : ℕ) :
    unitCube n =
      Set.univ.pi
        (fun _i : Fin n => Set.Icc (0 : ℝ) 1) := by
  ext u
  unfold unitCube
  simp only [Set.mem_setOf_eq, Set.mem_pi,
    Set.mem_univ, true_implies, Set.mem_Icc]

private theorem unitCube_integral_eq_pi
    (n : ℕ) (f : (Fin n → ℝ) → ℝ) :
    (∫ u in unitCube n, f u) =
      ∫ u, f u ∂Measure.pi
        (fun _i : Fin n =>
          (MeasureTheory.volume : Measure ℝ).restrict
            (Set.Icc 0 1)) := by
  rw [unitCube_eq_pi, MeasureTheory.volume_pi,
    Measure.restrict_pi_pi]

private theorem stickBreaking_sum
    (k : ℕ) (u : Fin (k + 1) → ℝ) :
    ∑ i, stickBreaking u i = u 0 := by
  have h := stickBreaking_tail_sum k u
    (0 : Fin (k + 1))
  have hIci :
      Finset.Ici (0 : Fin (k + 1)) =
        Finset.univ := by
    ext i
    simp
  rw [hIci] at h
  have hIic :
      Finset.Iic (0 : Fin (k + 1)) =
        {(0 : Fin (k + 1))} := by
    ext i
    simp
  rw [prefixProduct, hIic] at h
  simpa using h

private def cubeKernel
    (k : ℕ) (i : Fin (k + 1)) (t : ℝ) : ℝ :=
  (if i = (0 : Fin (k + 1))
    then Real.sqrt t else 1) *
    t ^ ((k + 1) - 1 - i.val)

private theorem cubeKernel_product
    (k : ℕ) (u : Fin (k + 1) → ℝ) :
    (∏ i, cubeKernel k i (u i)) =
      Real.sqrt (u 0) *
        jacobianFactor (k + 1) u := by
  unfold cubeKernel jacobianFactor
  rw [Finset.prod_mul_distrib]
  congr 1
  simpa using
    (Finset.prod_ite_eq
      (Finset.univ : Finset (Fin (k + 1)))
      (0 : Fin (k + 1))
      (fun i => Real.sqrt (u i)))

private theorem interval_sqrt_mul_pow (k : ℕ) :
    (∫ t in (0 : ℝ)..1,
      Real.sqrt t * t ^ k) =
      2 / (2 * (k : ℝ) + 3) := by
  have hfac :
      (Nat.factorial k : ℝ) ≠ 0 := by
    positivity
  have hrewrite :
      (∫ t in (0 : ℝ)..1,
        Real.sqrt t *
          (t ^ k / (Nat.factorial k : ℝ))) =
        (∫ t in (0 : ℝ)..1,
          Real.sqrt t * t ^ k) /
          (Nat.factorial k : ℝ) := by
    calc
      (∫ t in (0 : ℝ)..1,
        Real.sqrt t *
          (t ^ k / (Nat.factorial k : ℝ))) =
          ∫ t in (0 : ℝ)..1,
            (Real.sqrt t * t ^ k) /
              (Nat.factorial k : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by
        rw [intervalIntegral.integral_div]
  have h := sqrt_pow_integral k
  rw [hrewrite] at h
  calc
    (∫ t in (0 : ℝ)..1,
      Real.sqrt t * t ^ k) =
        ((∫ t in (0 : ℝ)..1,
          Real.sqrt t * t ^ k) /
            (Nat.factorial k : ℝ)) *
          (Nat.factorial k : ℝ) := by
      field_simp
    _ =
        (2 /
          ((Nat.factorial k : ℝ) *
            (2 * (k : ℝ) + 3))) *
          (Nat.factorial k : ℝ) := by
      rw [h]
    _ = 2 / (2 * (k : ℝ) + 3) := by
      field_simp [hfac]

private theorem restricted_integral_pow (m : ℕ) :
    (∫ t : ℝ, t ^ m
      ∂(MeasureTheory.volume : Measure ℝ).restrict
        (Set.Icc 0 1)) =
      1 / ((m : ℝ) + 1) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1),
    integral_pow]
  norm_num

private theorem restricted_integral_sqrt_mul_pow
    (k : ℕ) :
    (∫ t : ℝ, Real.sqrt t * t ^ k
      ∂(MeasureTheory.volume : Measure ℝ).restrict
        (Set.Icc 0 1)) =
      2 / (2 * (k : ℝ) + 3) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1)]
  exact interval_sqrt_mul_pow k

private theorem transformed_integrand_kernel
    (k : ℕ) (u : Fin (k + 1) → ℝ) :
    Real.sqrt (∑ i, stickBreaking u i) *
        jacobianFactor (k + 1) u =
      ∏ i, cubeKernel k i (u i) := by
  rw [stickBreaking_sum, cubeKernel_product]

private theorem transformedIntegral_eq_kernel_product
    (k : ℕ) :
    transformedIntegral (k + 1) =
      ∏ i : Fin (k + 1),
        ∫ t : ℝ, cubeKernel k i t
          ∂(MeasureTheory.volume : Measure ℝ).restrict
            (Set.Icc 0 1) := by
  unfold transformedIntegral
  rw [unitCube_integral_eq_pi]
  simp_rw [transformed_integrand_kernel]
  rw [MeasureTheory.integral_fintype_prod_eq_prod]

private theorem restricted_integral_cubeKernel
    (k : ℕ) (i : Fin (k + 1)) :
    (∫ t : ℝ, cubeKernel k i t
      ∂(MeasureTheory.volume : Measure ℝ).restrict
        (Set.Icc 0 1)) =
      if i = (0 : Fin (k + 1)) then
        2 / (2 * (k : ℝ) + 3)
      else
        1 /
          ((((k + 1) - 1 - i.val : ℕ) : ℝ) + 1) := by
  by_cases hi : i = (0 : Fin (k + 1))
  · subst i
    simpa [cubeKernel] using
      restricted_integral_sqrt_mul_pow k
  · rw [if_neg hi]
    simpa [cubeKernel, hi] using
      restricted_integral_pow
        ((k + 1) - 1 - i.val)

private theorem restricted_integral_cubeKernel_succ
    (k : ℕ) (i : Fin k) :
    (∫ t : ℝ, cubeKernel k i.succ t
      ∂(MeasureTheory.volume : Measure ℝ).restrict
        (Set.Icc 0 1)) =
      1 / (((k - i.val : ℕ) : ℝ)) := by
  rw [restricted_integral_cubeKernel]
  have hi :
      i.succ ≠ (0 : Fin (k + 1)) := by
    exact Fin.succ_ne_zero i
  rw [if_neg hi]
  have hnat :
      (k + 1) - 1 - i.succ.val + 1 =
        k - i.val := by
    change
      (k + 1) - 1 - (i.val + 1) + 1 =
        k - i.val
    omega
  have hreal :
      ((((k + 1) - 1 - i.succ.val : ℕ) : ℝ) + 1) =
        ((k - i.val : ℕ) : ℝ) := by
    calc
      ((((k + 1) - 1 - i.succ.val : ℕ) : ℝ) + 1) =
          (((((k + 1) - 1 - i.succ.val) + 1 : ℕ) : ℝ)) := by
        norm_num
      _ = ((k - i.val : ℕ) : ℝ) := by
        rw [hnat]
  rw [hreal]

private theorem reverse_fin_product (k : ℕ) :
    (∏ i : Fin k, (((k - i.val : ℕ) : ℝ))) =
      (Nat.factorial k : ℝ) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      rw [Fin.prod_univ_succ]
      have htail :
          (∏ i : Fin k,
            (((k + 1 - i.succ.val : ℕ) : ℝ))) =
            ∏ i : Fin k,
              (((k - i.val : ℕ) : ℝ)) := by
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        change k + 1 - (i.val + 1) =
          k - i.val
        omega
      rw [htail, ih]
      norm_num [Nat.factorial_succ]

private theorem reverse_fin_reciprocal_product
    (k : ℕ) :
    (∏ i : Fin k,
      1 / (((k - i.val : ℕ) : ℝ))) =
      1 / (Nat.factorial k : ℝ) := by
  calc
    (∏ i : Fin k,
      1 / (((k - i.val : ℕ) : ℝ))) =
        (∏ _i : Fin k, (1 : ℝ)) /
          ∏ i : Fin k,
            (((k - i.val : ℕ) : ℝ)) := by
      rw [← Finset.prod_div_distrib]
    _ = 1 / (Nat.factorial k : ℝ) := by
      rw [reverse_fin_product]
      simp

private theorem kernel_integral_product
    (k : ℕ) :
    (∏ i : Fin (k + 1),
      ∫ t : ℝ, cubeKernel k i t
        ∂(MeasureTheory.volume : Measure ℝ).restrict
          (Set.Icc 0 1)) =
      2 /
        ((Nat.factorial k : ℝ) *
          (2 * ((k + 1 : ℕ) : ℝ) + 1)) := by
  rw [Fin.prod_univ_succ]
  rw [restricted_integral_cubeKernel]
  simp only [if_pos]
  rw [Finset.prod_congr rfl
    (fun i _ =>
      restricted_integral_cubeKernel_succ k i)]
  rw [reverse_fin_reciprocal_product]
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hfac :
      (Nat.factorial k : ℝ) ≠ 0 := by
    positivity
  field_simp [hfac]
  ring

theorem gap4 (n : ℕ) (hn : 1 ≤ n) :
    transformedIntegral n =
      2 /
        ((Nat.factorial (n - 1) : ℝ) *
          (2 * (n : ℝ) + 1)) := by
  cases n with
  | zero => omega
  | succ k =>
      simpa [Nat.cast_add, Nat.cast_one] using
        (transformedIntegral_eq_kernel_product k).trans
          (kernel_integral_product k)

theorem gap3 (n : ℕ) (hn : 1 ≤ n) :
    simplexSqrtIntegral n = transformedIntegral n := by
  rw [gap5 n hn, gap4 n hn]

end

end ProofGap.Exercise4207
