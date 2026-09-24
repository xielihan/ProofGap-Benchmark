import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

namespace ProofGap.Exercise3108

noncomputable section

open Filter
open scoped BigOperators Topology

def SummableFromOne (u : ℕ → ℝ) : Prop :=
  Summable (fun n : ℕ => u (n + 1))

def partialProduct (f : ℕ → ℝ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∏ n ∈ Finset.Icc 1 N, (1 + f n x)

def HasProductFromOne (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s, Tendsto (fun N => partialProduct f N x) atTop (𝓝 (F x))

def tail (f : ℕ → ℝ → ℝ) (N₀ k : ℕ) (x : ℝ) : ℝ :=
  f (N₀ + k) x

def tailPartialProduct (f : ℕ → ℝ → ℝ) (N₀ N : ℕ) (x : ℝ) : ℝ :=
  ∏ k ∈ Finset.Icc 1 N, (1 + tail f N₀ k x)

def HasTailProduct (f : ℕ → ℝ → ℝ) (N₀ : ℕ)
    (G : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x ∈ s,
    Tendsto (fun N => tailPartialProduct f N₀ N x) atTop (𝓝 (G x))

def logTailTerm (f : ℕ → ℝ → ℝ) (N₀ : ℕ) (k : ℕ) (x : ℝ) : ℝ :=
  Real.log (1 + tail f N₀ (k + 1) x)

/-- Source: `proof_gap/exercise_3108/1.txt`; the irrelevant point `x` is removed. -/
theorem gap1 (c : ℕ → ℝ)
    (hc0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ c n)
    (hcsum : SummableFromOne c) :
    Tendsto c atTop (𝓝 0) := by
  apply (tendsto_add_atTop_iff_nat 1).1
  exact hcsum.tendsto_atTop_zero

/-- Source: `proof_gap/exercise_3108/2.txt`; the majorant forces pointwise convergence. -/
theorem gap2 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (a b : ℝ)
    (hbound :
      ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b, |f n x| ≤ c n)
    (hc : Tendsto c atTop (𝓝 0)) :
    ∀ x ∈ Set.Ioo a b,
      Tendsto (fun n => f n x) atTop (𝓝 0) := by
  intro x hx
  rw [Metric.tendsto_atTop]
  intro ε hε
  rw [Metric.tendsto_atTop] at hc
  obtain ⟨N, hN⟩ := hc ε hε
  exact ⟨max N 1, fun n hn => by
    rw [Real.dist_eq]
    simpa only [sub_zero] using
      (hbound n (by omega) x hx).trans_lt
        ((le_abs_self (c n)).trans_lt (by simpa [Real.dist_eq] using hN n (by omega)))⟩

/-- Source: `proof_gap/exercise_3108/3.txt`; choose one cutoff uniformly. -/
theorem gap3 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (a b : ℝ)
    (hbound :
      ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b, |f n x| ≤ c n)
    (hc : Tendsto c atTop (𝓝 0)) :
    ∀ δ : ℝ, 0 < δ →
      ∃ N₀ : ℕ, 1 ≤ N₀ ∧
        ∀ n : ℕ, N₀ ≤ n →
          ∀ x ∈ Set.Ioo a b, |f n x| < δ := by
  intro δ hδ
  rw [Metric.tendsto_atTop] at hc
  obtain ⟨N, hN⟩ := hc δ hδ
  refine ⟨max N 1, by omega, fun n hn x hx => ?_⟩
  exact (hbound n (by omega) x hx).trans_lt
    ((le_abs_self (c n)).trans_lt (by simpa [Real.dist_eq] using hN n (by omega)))

/-- Source: `proof_gap/exercise_3108/4.txt`; fix one positive `δ`. -/
theorem gap4 (f : ℕ → ℝ → ℝ) (a b δ : ℝ) (N₀ : ℕ)
    (hδ : 0 < δ)
    (hsmall :
      ∀ n : ℕ, N₀ < n →
        ∀ x ∈ Set.Ioo a b, |f n x| < δ) :
    ∀ k : ℕ, 1 ≤ k →
      ∀ x ∈ Set.Ioo a b, |tail f N₀ k x| < δ := by
  intro k hk x hx
  exact hsmall (N₀ + k) (by omega) x hx

/-- Source: `proof_gap/exercise_3108/5.txt`; the tail uses the same fixed cutoff. -/
theorem gap5 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (a b : ℝ) (N₀ : ℕ)
    (hbound :
      ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b, |f n x| ≤ c n) :
    ∀ k : ℕ, 1 ≤ k →
      ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| ≤ c (N₀ + k) := by
  intro k hk x hx
  exact hbound (N₀ + k) (by omega) x hx

/-- Source: `proof_gap/exercise_3108/6.txt`; absolute convergence. -/
theorem gap6 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (a b : ℝ) (N₀ : ℕ)
    (hbound :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| ≤ c (N₀ + k))
    (hcsum : SummableFromOne c) :
    ∀ x ∈ Set.Ioo a b,
      Summable (fun k : ℕ => |tail f N₀ (k + 1) x|) := by
  intro x hx
  have hmajor : Summable (fun k : ℕ => c (N₀ + (k + 1))) := by
    have := (summable_nat_add_iff N₀).2 hcsum
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
  exact Summable.of_nonneg_of_le (fun k => abs_nonneg _)
    (fun k => hbound (k + 1) (by omega) x hx) hmajor

/-- Source: `proof_gap/exercise_3108/7.txt`; logarithm on a small tail. -/
theorem gap7 (f : ℕ → ℝ → ℝ) (a b : ℝ) (N₀ : ℕ)
    (hsmall :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| < 1 / 2)
    (hsum :
      ∀ x ∈ Set.Ioo a b,
        Summable (fun k : ℕ => |tail f N₀ (k + 1) x|)) :
    ∀ x ∈ Set.Ioo a b,
      Summable (fun k : ℕ => logTailTerm f N₀ k x) := by
  intro x hx
  apply Real.summable_log_one_add_of_summable
  rw [← summable_abs_iff]
  simpa [tail] using hsum x hx

/-- Source: `proof_gap/exercise_3108/8.txt`; split finite head and tail. -/
theorem gap8 (f : ℕ → ℝ → ℝ) (F G : ℝ → ℝ)
    (a b : ℝ) (N₀ : ℕ)
    (hF : HasProductFromOne f F (Set.Ioo a b))
    (hG : HasTailProduct f N₀ G (Set.Ioo a b)) :
    ∀ x ∈ Set.Ioo a b,
      F x =
        G x * ∏ n ∈ Finset.Icc 1 N₀, (1 + f n x) := by
  intro x hx
  let H : ℝ := ∏ n ∈ Finset.Icc 1 N₀, (1 + f n x)
  have hsplit : ∀ N : ℕ,
      partialProduct f (N₀ + N) x = H * tailPartialProduct f N₀ N x := by
    intro N
    induction N with
    | zero =>
        simp [partialProduct, tailPartialProduct, H]
    | succ N ih =>
        rw [show N₀ + (N + 1) = (N₀ + N) + 1 by omega,
          partialProduct, Finset.prod_Icc_succ_top (by omega)]
        rw [show (∏ n ∈ Finset.Icc 1 (N₀ + N), (1 + f n x)) =
          partialProduct f (N₀ + N) x by rfl, ih]
        unfold tailPartialProduct
        rw [Finset.prod_Icc_succ_top (by omega)]
        unfold tail
        rw [show N₀ + N + 1 = N₀ + (N + 1) by omega]
        ring
  have hfull :
      Tendsto (fun N : ℕ => partialProduct f (N₀ + N) x)
        atTop (𝓝 (F x)) := by
    simpa [Nat.add_comm] using
      (hF x hx).comp (tendsto_add_atTop_nat N₀)
  have htail :
      Tendsto (fun N : ℕ => H * tailPartialProduct f N₀ N x)
        atTop (𝓝 (H * G x)) :=
    tendsto_const_nhds.mul (hG x hx)
  have hfull' := htail.congr' (Eventually.of_forall fun N => (hsplit N).symm)
  have heq : F x = H * G x := tendsto_nhds_unique hfull hfull'
  simpa [H, mul_comm] using heq

/-- Source: `proof_gap/exercise_3108/9.txt`; logarithm and tail product. -/
theorem gap9 (f : ℕ → ℝ → ℝ) (G L : ℝ → ℝ)
    (a b : ℝ) (N₀ : ℕ)
    (hG : HasTailProduct f N₀ G (Set.Ioo a b))
    (hGpos : ∀ x ∈ Set.Ioo a b, 0 < G x)
    -- Statement correction: natural-order product convergence alone does not imply unconditional summability of the logarithms.
    (hsum :
      ∀ x ∈ Set.Ioo a b,
        Summable (fun k : ℕ => logTailTerm f N₀ k x))
    (hL : ∀ x ∈ Set.Ioo a b, L x = Real.log (G x)) :
    ∀ x ∈ Set.Ioo a b,
      L x = ∑' k : ℕ, logTailTerm f N₀ k x := by
  intro x hx
  let Q : ℕ → ℝ := fun N => tailPartialProduct f N₀ N x
  have hQ : Tendsto Q atTop (𝓝 (G x)) := hG x hx
  have hQev : ∀ᶠ N in atTop, Q N ≠ 0 :=
    (hQ.eventually (isOpen_compl_singleton.mem_nhds (hGpos x hx).ne')).mono
      (fun N hN => hN)
  obtain ⟨M, hM⟩ := eventually_atTop.1 hQev
  have hfactor : ∀ k : ℕ, 1 ≤ k → 1 + tail f N₀ k x ≠ 0 := by
    intro k hk hz
    let R := max M k
    have hmem : k ∈ Finset.Icc 1 R := Finset.mem_Icc.2 ⟨hk, le_max_right _ _⟩
    have hzero : Q R = 0 := by
      unfold Q tailPartialProduct
      exact Finset.prod_eq_zero hmem hz
    exact hM R (le_max_left _ _) hzero
  have hlogprod : ∀ N : ℕ,
      ∑ k ∈ Finset.range N, logTailTerm f N₀ k x = Real.log (Q N) := by
    intro N
    induction N with
    | zero => simp [Q, tailPartialProduct]
    | succ N ih =>
        rw [Finset.sum_range_succ, ih]
        unfold Q tailPartialProduct at *
        rw [Finset.prod_Icc_succ_top (by omega)]
        unfold logTailTerm
        have hprod :
            (∏ k ∈ Finset.Icc 1 N, (1 + tail f N₀ k x)) ≠ 0 := by
          apply Finset.prod_ne_zero_iff.mpr
          intro k hk
          exact hfactor k (Finset.mem_Icc.mp hk).1
        rw [Real.log_mul hprod (hfactor (N + 1) (by omega))]
  have hlogs :
      Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, logTailTerm f N₀ k x)
        atTop (𝓝 (Real.log (G x))) := by
    have hc := (Real.continuousAt_log (hGpos x hx).ne').tendsto.comp hQ
    exact hc.congr' (Eventually.of_forall fun N => (hlogprod N).symm)
  have htendstoTsum :=
    (hsum x hx).hasSum.tendsto_sum_nat
  have heq : Real.log (G x) =
      ∑' k : ℕ, logTailTerm f N₀ k x :=
    tendsto_nhds_unique hlogs htendstoTsum
  exact (hL x hx).trans heq

/-- Source: `proof_gap/exercise_3108/10.txt`; factor-2 logarithm bound. -/
theorem gap10 (f : ℕ → ℝ → ℝ) (a b : ℝ) (N₀ : ℕ)
    (hsmall :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| < 1 / 2) :
    ∀ k : ℕ, 1 ≤ k →
      ∀ x ∈ Set.Ioo a b,
        |Real.log (1 + tail f N₀ k x)| ≤
          2 * |tail f N₀ k x| := by
  intro k hk x hx
  let u := tail f N₀ k x
  have hu := hsmall k hk x hx
  have hu' : ‖(u : ℂ)‖ ≤ 1 / 2 := by
    simpa [u, Complex.norm_real] using hu.le
  have h := Complex.norm_log_one_add_half_le_self hu'
  have hre : Complex.log (1 + (u : ℂ)) = Real.log (1 + u) := by
    rw [show (1 : ℂ) + (u : ℂ) = ((1 + u : ℝ) : ℂ) by norm_num,
      Complex.ofReal_log (by
      have := (abs_lt.mp hu).1
      linarith : 0 ≤ 1 + u)]
  rw [hre, Complex.norm_real, Real.norm_eq_abs] at h
  rw [Complex.norm_real] at h
  calc
    |Real.log (1 + tail f N₀ k x)| = |Real.log (1 + u)| := by rfl
    _ ≤ (3 / 2 : ℝ) * |u| := h
    _ ≤ 2 * |u| := by gcongr <;> norm_num
    _ = 2 * |tail f N₀ k x| := by rfl

/-- Source: `proof_gap/exercise_3108/11.txt`; scale majorant. -/
theorem gap11 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ)
    (a b : ℝ) (N₀ : ℕ)
    (hbound :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| ≤ c (N₀ + k)) :
    ∀ k : ℕ, 1 ≤ k →
      ∀ x ∈ Set.Ioo a b,
        2 * |tail f N₀ k x| ≤ 2 * c (N₀ + k) := by
  intro k hk x hx
  gcongr
  exact hbound k hk x hx

/-- Source: `proof_gap/exercise_3108/12.txt`; combine two bounds. -/
theorem gap12 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ)
    (a b : ℝ) (N₀ : ℕ)
    (hlog :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |Real.log (1 + tail f N₀ k x)| ≤
          2 * |tail f N₀ k x|)
    (hbound :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| ≤ c (N₀ + k)) :
    ∀ k : ℕ, 1 ≤ k →
      ∀ x ∈ Set.Ioo a b,
        |Real.log (1 + tail f N₀ k x)| ≤
          2 * c (N₀ + k) := by
  intro k hk x hx
  exact (hlog k hk x hx).trans (gap11 f c a b N₀ hbound k hk x hx)

/-- Source: `proof_gap/exercise_3108/13.txt`; uniform M-test. -/
theorem gap13 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (L : ℝ → ℝ)
    (a b : ℝ) (N₀ : ℕ)
    (hc0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ c n)
    (hbound :
      ∀ k : ℕ, ∀ x ∈ Set.Ioo a b,
        |logTailTerm f N₀ k x| ≤ 2 * c (N₀ + k + 1))
    (hcsum : SummableFromOne c)
    (hL :
      ∀ x ∈ Set.Ioo a b,
        L x = ∑' k : ℕ, logTailTerm f N₀ k x) :
    HasSumUniformlyOn (logTailTerm f N₀) L (Set.Ioo a b) := by
  have hu : Summable (fun k : ℕ => 2 * c (N₀ + k + 1)) := by
    have hshift : Summable (fun k : ℕ => c (N₀ + k + 1)) := by
      have := (summable_nat_add_iff N₀).2 hcsum
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this
    exact hshift.mul_left 2
  have h :
      HasSumUniformlyOn (logTailTerm f N₀)
        (fun x => ∑' k : ℕ, logTailTerm f N₀ k x) (Set.Ioo a b) :=
    HasSumUniformlyOn.of_norm_le_summable hu
      (fun k x hx => by simpa [Real.norm_eq_abs] using hbound k x hx)
  exact h.congr_right fun x hx => (hL x hx).symm

/-- Source: `proof_gap/exercise_3108/14.txt`; uniform continuous limit. -/
theorem gap14 (f : ℕ → ℝ → ℝ) (L : ℝ → ℝ)
    (a b : ℝ) (N₀ : ℕ)
    (hcont :
      ∀ k : ℕ,
        ContinuousOn (logTailTerm f N₀ k) (Set.Ioo a b))
    (huniform :
      HasSumUniformlyOn (logTailTerm f N₀) L (Set.Ioo a b)) :
    ContinuousOn L (Set.Ioo a b) := by
  apply huniform.tendstoUniformlyOn_finsetRange.continuousOn
  exact (Eventually.of_forall fun N =>
    continuousOn_finset_sum (Finset.range N)
      (fun k hk => hcont k)).frequently

/-- Source: `proof_gap/exercise_3108/15.txt`; tail product is exp L. -/
theorem gap15 (G L : ℝ → ℝ) (a b : ℝ)
    (hL : ContinuousOn L (Set.Ioo a b))
    (hGL : ∀ x ∈ Set.Ioo a b, G x = Real.exp (L x)) :
    ContinuousOn G (Set.Ioo a b) := by
  exact (Real.continuous_exp.comp_continuousOn hL).congr
    (fun x hx => hGL x hx)

/-- Source: `proof_gap/exercise_3108/16.txt`; finite head times tail. -/
theorem gap16 (f : ℕ → ℝ → ℝ) (F G : ℝ → ℝ)
    (a b : ℝ) (N₀ : ℕ)
    (hf : ∀ n : ℕ, 1 ≤ n → ContinuousOn (f n) (Set.Ioo a b))
    (hG : ContinuousOn G (Set.Ioo a b))
    (hfactor :
      ∀ x ∈ Set.Ioo a b,
        F x = G x * ∏ n ∈ Finset.Icc 1 N₀, (1 + f n x)) :
    ContinuousOn F (Set.Ioo a b) := by
  have hhead :
      ContinuousOn
        (fun x => ∏ n ∈ Finset.Icc 1 N₀, (1 + f n x))
        (Set.Ioo a b) := by
    apply continuousOn_finset_prod
    intro n hn
    exact continuousOn_const.add (hf n (Finset.mem_Icc.mp hn).1)
  exact (hG.mul hhead).congr (fun x hx => hfactor x hx)

/-- Source: `proof_gap/exercise_3108/17.txt`; final product theorem. -/
theorem gap17 (f : ℕ → ℝ → ℝ) (c : ℕ → ℝ) (F : ℝ → ℝ)
    (a b : ℝ)
    (hf : ∀ n : ℕ, 1 ≤ n → ContinuousOn (f n) (Set.Ioo a b))
    (hc0 : ∀ n : ℕ, 1 ≤ n → 0 ≤ c n)
    (hbound :
      ∀ n : ℕ, 1 ≤ n → ∀ x ∈ Set.Ioo a b, |f n x| ≤ c n)
    (hcsum : SummableFromOne c)
    (hF : HasProductFromOne f F (Set.Ioo a b)) :
    ContinuousOn F (Set.Ioo a b) := by
  have hc : Tendsto c atTop (𝓝 0) := gap1 c hc0 hcsum
  obtain ⟨N₀, hN₀, hsmall₀⟩ :=
    gap3 f c a b hbound hc (1 / 2) (by norm_num)
  have hsmall :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| < 1 / 2 := by
    exact gap4 f a b (1 / 2) N₀ (by norm_num)
      (fun n hn x hx => hsmall₀ n hn.le x hx)
  have htailBound :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |tail f N₀ k x| ≤ c (N₀ + k) :=
    gap5 f c a b N₀ hbound
  have habs :
      ∀ x ∈ Set.Ioo a b,
        Summable (fun k : ℕ => |tail f N₀ (k + 1) x|) :=
    gap6 f c a b N₀ htailBound hcsum
  have hlogsum :
      ∀ x ∈ Set.Ioo a b,
        Summable (fun k : ℕ => logTailTerm f N₀ k x) :=
    gap7 f a b N₀ hsmall habs
  let L : ℝ → ℝ := fun x => ∑' k : ℕ, logTailTerm f N₀ k x
  let G : ℝ → ℝ := fun x => Real.exp (L x)
  have hprodexp : ∀ N : ℕ, ∀ x ∈ Set.Ioo a b,
      tailPartialProduct f N₀ N x =
        Real.exp (∑ k ∈ Finset.range N, logTailTerm f N₀ k x) := by
    intro N
    induction N with
    | zero =>
        intro x hx
        simp [tailPartialProduct]
    | succ N ih =>
        intro x hx
        rw [tailPartialProduct, Finset.prod_Icc_succ_top (by omega)]
        rw [show (∏ k ∈ Finset.Icc 1 N, (1 + tail f N₀ k x)) =
          tailPartialProduct f N₀ N x by rfl, ih x hx,
          Finset.sum_range_succ, Real.exp_add]
        unfold logTailTerm
        rw [Real.exp_log]
        have hu := hsmall (N + 1) (by omega) x hx
        have hlower := (abs_lt.mp hu).1
        linarith
  have hG : HasTailProduct f N₀ G (Set.Ioo a b) := by
    intro x hx
    have hs := (hlogsum x hx).hasSum.tendsto_sum_nat
    have he := Real.continuous_exp.continuousAt.tendsto.comp hs
    exact he.congr' (Eventually.of_forall fun N => (hprodexp N x hx).symm)
  have hGpos : ∀ x ∈ Set.Ioo a b, 0 < G x := by
    intro x hx
    unfold G
    positivity
  have hLdef :
      ∀ x ∈ Set.Ioo a b,
        L x = ∑' k : ℕ, logTailTerm f N₀ k x := by
    intro x hx
    rfl
  have hLG :
      ∀ x ∈ Set.Ioo a b, L x = Real.log (G x) := by
    intro x hx
    unfold G
    rw [Real.log_exp]
  have hfactor :
      ∀ x ∈ Set.Ioo a b,
        F x = G x * ∏ n ∈ Finset.Icc 1 N₀, (1 + f n x) :=
    gap8 f F G a b N₀ hF hG
  have hlogBound :
      ∀ k : ℕ, 1 ≤ k → ∀ x ∈ Set.Ioo a b,
        |Real.log (1 + tail f N₀ k x)| ≤
          2 * |tail f N₀ k x| :=
    gap10 f a b N₀ hsmall
  have hmajor :
      ∀ k : ℕ, ∀ x ∈ Set.Ioo a b,
        |logTailTerm f N₀ k x| ≤ 2 * c (N₀ + k + 1) := by
    intro k x hx
    exact gap12 f c a b N₀ hlogBound htailBound
      (k + 1) (by omega) x hx
  have huniform : HasSumUniformlyOn (logTailTerm f N₀) L (Set.Ioo a b) :=
    gap13 f c L a b N₀ hc0 hmajor hcsum hLdef
  have hcontTerm :
      ∀ k : ℕ, ContinuousOn (logTailTerm f N₀ k) (Set.Ioo a b) := by
    intro k
    have harg :
        ContinuousOn (fun x => 1 + tail f N₀ (k + 1) x) (Set.Ioo a b) := by
      exact continuousOn_const.add (hf (N₀ + (k + 1)) (by omega))
    apply Real.continuousOn_log.comp harg
    intro x hx
    have hu := hsmall (k + 1) (by omega) x hx
    have hlower := (abs_lt.mp hu).1
    exact Set.mem_compl_singleton_iff.mpr (ne_of_gt (by linarith))
  have hLcont : ContinuousOn L (Set.Ioo a b) :=
    gap14 f L a b N₀ hcontTerm huniform
  have hGcont : ContinuousOn G (Set.Ioo a b) :=
    gap15 G L a b hLcont (fun x hx => rfl)
  exact gap16 f F G a b N₀ hf hGcont hfactor

end

end ProofGap.Exercise3108
