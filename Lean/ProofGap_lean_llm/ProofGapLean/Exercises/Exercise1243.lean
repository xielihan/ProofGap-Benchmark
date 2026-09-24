import ProofGapLean.Prelude.Analysis
import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Data.Finset.Sort

namespace ProofGap.Exercise1243

noncomputable section

open scoped BigOperators

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def Q (x : ℝ) : ℝ := Real.exp (-x ^ 2)
def H (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n * Real.exp (x ^ 2) * iterDeriv n Q x
def zeros (u : ℝ → ℝ) : Set ℝ := {x | u x = 0}
def rootList (α : ℕ → ℝ) (k : ℕ) : Set ℝ := α '' (Finset.range k : Set ℕ)
def StrictList (α : ℕ → ℝ) (k : ℕ) : Prop :=
  ∀ i, i + 1 < k → α i < α (i + 1)

private def gaussPoly : ℕ → Polynomial ℝ
  | 0 => 1
  | n + 1 =>
      (gaussPoly n).derivative -
        (Polynomial.C 2 * Polynomial.X) * gaussPoly n

private theorem gaussPoly_degree (n : ℕ) :
    (gaussPoly n).natDegree = n ∧ gaussPoly n ≠ 0 := by
  induction n with
  | zero =>
      simp [gaussPoly]
  | succ n ih =>
      have hlin :
          (Polynomial.C (2 : ℝ) * Polynomial.X) ≠ 0 := by
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
          Polynomial.X_ne_zero
      have hmul :
          ((Polynomial.C (2 : ℝ) * Polynomial.X) *
              gaussPoly n).natDegree = n + 1 := by
        rw [Polynomial.natDegree_mul hlin ih.2]
        simp [ih.1]
        omega
      have hderiv :
          (gaussPoly n).derivative.natDegree < n + 1 := by
        exact lt_of_le_of_lt (Polynomial.natDegree_derivative_le _)
          (by omega)
      have hdeg :
          (gaussPoly (n + 1)).natDegree = n + 1 := by
        rw [gaussPoly,
          Polynomial.natDegree_sub_eq_right_of_natDegree_lt]
        · exact hmul
        · simpa [hmul] using hderiv
      exact ⟨hdeg, fun hzero => by simpa [hzero] using hdeg⟩

private theorem gaussPoly_leadingCoeff (n : ℕ) :
    (gaussPoly n).leadingCoeff = (-2 : ℝ) ^ n := by
  induction n with
  | zero =>
      simp [gaussPoly]
  | succ n ih =>
      have hlin :
          (Polynomial.C (2 : ℝ) * Polynomial.X) ≠ 0 := by
        exact mul_ne_zero (Polynomial.C_ne_zero.mpr (by norm_num))
          Polynomial.X_ne_zero
      have hmul :
          ((Polynomial.C (2 : ℝ) * Polynomial.X) *
              gaussPoly n).natDegree = n + 1 := by
        rw [Polynomial.natDegree_mul hlin (gaussPoly_degree n).2]
        simp [(gaussPoly_degree n).1]
        omega
      have hderiv :
          (gaussPoly n).derivative.natDegree <
            ((Polynomial.C (2 : ℝ) * Polynomial.X) *
              gaussPoly n).natDegree := by
        rw [hmul]
        calc
          (gaussPoly n).derivative.natDegree ≤
              (gaussPoly n).natDegree - 1 :=
            Polynomial.natDegree_derivative_le _
          _ ≤ n := by
            rw [(gaussPoly_degree n).1]
            exact Nat.sub_le _ _
          _ < n + 1 := by omega
      rw [gaussPoly, show
          (gaussPoly n).derivative -
              (Polynomial.C (2 : ℝ) * Polynomial.X) * gaussPoly n =
            -(((Polynomial.C (2 : ℝ) * Polynomial.X) * gaussPoly n) -
              (gaussPoly n).derivative) by ring,
        Polynomial.leadingCoeff_neg,
        Polynomial.leadingCoeff_sub_of_degree_lt
          (Polynomial.degree_lt_degree hderiv),
        Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
        Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X, ih]
      ring

private theorem iterDeriv_eq_gaussPoly (n : ℕ) (x : ℝ) :
    iterDeriv n Q x =
      (gaussPoly n).eval x * Real.exp (-x ^ 2) := by
  induction n generalizing x with
  | zero =>
      simp [iterDeriv, Q, gaussPoly]
  | succ n ih =>
      have hfun :
          iterDeriv n Q =
            fun t => (gaussPoly n).eval t * Real.exp (-t ^ 2) := by
        funext t
        exact ih t
      rw [show iterDeriv (n + 1) Q x = deriv (iterDeriv n Q) x by
        simp [iterDeriv, Function.iterate_succ_apply']]
      rw [hfun]
      have hpoly := (gaussPoly n).hasDerivAt x
      have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * x) x := by
        convert ((hasDerivAt_id x).pow 2).neg using 1 <;>
          simp only [id_eq] <;> ring
      have hexp := (Real.hasDerivAt_exp (-x ^ 2)).comp x hsq
      convert (hpoly.mul hexp).deriv using 1 <;>
        simp [gaussPoly, Polynomial.eval_sub, Polynomial.eval_mul] <;>
        ring

private theorem zeros_iterDeriv_eq_rootSet (n : ℕ) :
    zeros (iterDeriv n Q) = (gaussPoly n).rootSet ℝ := by
  ext x
  rw [Polynomial.mem_rootSet_of_ne (gaussPoly_degree n).2]
  simp only [zeros, Set.mem_setOf_eq]
  rw [iterDeriv_eq_gaussPoly]
  exact mul_eq_zero_iff_right (Real.exp_ne_zero _)

private theorem ncard_zeros_iterDeriv_le (n : ℕ) :
    (zeros (iterDeriv n Q)).ncard ≤ n := by
  rw [zeros_iterDeriv_eq_rootSet]
  simpa [(gaussPoly_degree n).1] using
    Polynomial.ncard_rootSet_le (gaussPoly n) ℝ

private theorem strictMonoOn_of_StrictList {α : ℕ → ℝ} {k : ℕ}
    (hsort : StrictList α k) :
    StrictMonoOn α (Set.Iio k) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Iio
  intro i _hiMax _hi hi1
  exact hsort i hi1

private theorem ncard_rootList {α : ℕ → ℝ} {k : ℕ}
    (hsort : StrictList α k) :
    (rootList α k).ncard = k := by
  have hinj :
      Set.InjOn α (↑(Finset.range k) : Set ℕ) := by
    apply (strictMonoOn_of_StrictList hsort).injOn.mono
    intro i hi
    exact Set.mem_Iio.mpr (Finset.mem_range.mp hi)
  calc
    (rootList α k).ncard =
        (α '' (↑(Finset.range k) : Set ℕ)).ncard := rfl
    _ = (↑(Finset.range k) : Set ℕ).ncard := hinj.ncard_image
    _ = k := by rw [Set.ncard_coe_finset, Finset.card_range]

private theorem gaussPoly_factor_of_zeros
    (k : ℕ) (α : ℕ → ℝ)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    gaussPoly k =
      Polynomial.C ((-2 : ℝ) ^ k) *
        ∏ i ∈ Finset.range k,
          (Polynomial.X - Polynomial.C (α i)) := by
  let r : Finset ℝ := (Finset.range k).image α
  let s : Multiset ℝ := r.1
  have hinj :
      Set.InjOn α (↑(Finset.range k) : Set ℕ) := by
    apply (strictMonoOn_of_StrictList hsort).injOn.mono
    intro i hi
    exact Set.mem_Iio.mpr (Finset.mem_range.mp hi)
  have hcardr : r.card = k := by
    rw [show r = (Finset.range k).image α by rfl,
      Finset.card_image_iff.mpr hinj]
    simp
  have hsle : s ≤ (gaussPoly k).roots := by
    rw [Multiset.le_iff_count]
    intro a
    by_cases ha : a ∈ s
    · have hcounts : s.count a = 1 := by
        exact Multiset.count_eq_one_of_mem r.2 ha
      have har : a ∈ r := ha
      rw [show r = (Finset.range k).image α by rfl] at har
      rcases Finset.mem_image.mp har with ⟨i, hi, rfl⟩
      have hmem : α i ∈ zeros (iterDeriv k Q) := by
        rw [hzero]
        exact ⟨i, by simpa [rootList] using hi, rfl⟩
      rw [zeros_iterDeriv_eq_rootSet,
        Polynomial.mem_rootSet_of_ne (gaussPoly_degree k).2] at hmem
      have hroot : α i ∈ (gaussPoly k).roots :=
        Polynomial.mem_roots (gaussPoly_degree k).2 |>.mpr hmem
      rw [hcounts]
      exact Multiset.count_pos.mpr hroot
    · simp [Multiset.count_eq_zero.mpr ha]
  have hrootsCard : (gaussPoly k).roots.card = k := by
    have hlower : k ≤ (gaussPoly k).roots.card := by
      calc
        k = s.card := by simpa [s] using hcardr.symm
        _ ≤ (gaussPoly k).roots.card :=
          Multiset.card_le_card hsle
    have hupper :
        (gaussPoly k).roots.card ≤ k := by
      simpa [(gaussPoly_degree k).1] using
        Polynomial.card_roots' (gaussPoly k)
    omega
  have hseq : s = (gaussPoly k).roots := by
    apply Multiset.eq_of_le_of_card_le hsle
    simpa [s, hcardr] using hrootsCard.le
  have hrootsDegree :
      (gaussPoly k).roots.card = (gaussPoly k).natDegree := by
    rw [hrootsCard, (gaussPoly_degree k).1]
  have hpoly :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hrootsDegree
  rw [← hseq, gaussPoly_leadingCoeff] at hpoly
  rw [← hpoly]
  congr 1
  change
    (s.map (fun a => Polynomial.X - Polynomial.C a)).prod =
      ∏ i ∈ Finset.range k,
        (Polynomial.X - Polynomial.C (α i))
  change
    ∏ a ∈ r, (Polynomial.X - Polynomial.C a) =
      ∏ i ∈ Finset.range k,
        (Polynomial.X - Polynomial.C (α i))
  exact Finset.prod_image hinj

private theorem continuous_iterDeriv (n : ℕ) :
    Continuous (iterDeriv n Q) := by
  rw [show iterDeriv n Q =
      fun x => (gaussPoly n).eval x * Real.exp (-x ^ 2) by
    funext x
    exact iterDeriv_eq_gaussPoly n x]
  fun_prop

private theorem tendsto_eval_mul_gaussian_cocompact
    (p : Polynomial ℝ) :
    Filter.Tendsto (fun x => p.eval x * Real.exp (-x ^ 2))
      (Filter.cocompact ℝ) (nhds 0) := by
  induction p using Polynomial.induction_on' with
  | monomial n c =>
      have habs :
          Filter.Tendsto
            (fun x : ℝ =>
              |x| ^ (n : ℝ) * Real.exp (-(1 : ℝ) * x ^ 2))
            (Filter.cocompact ℝ) (nhds 0) :=
        tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact
          (by norm_num) n
      have hpow :
          Filter.Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2))
            (Filter.cocompact ℝ) (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        convert habs using 1 <;>
          simp [Real.norm_eq_abs, abs_mul, abs_pow,
            abs_of_pos (Real.exp_pos _), Real.rpow_natCast]
      simpa [Polynomial.eval_monomial, mul_assoc] using
        tendsto_const_nhds.mul hpow
  | add p q hp hq =>
      simpa [Polynomial.eval_add, add_mul] using hp.add hq

private theorem tendsto_iterDeriv_atBot (n : ℕ) :
    Filter.Tendsto (iterDeriv n Q) Filter.atBot (nhds 0) := by
  have h :=
    tendsto_eval_mul_gaussian_cocompact (gaussPoly n)
  rw [cocompact_eq_atBot_atTop] at h
  have h' := h.mono_left le_sup_left
  exact h'.congr' (Filter.Eventually.of_forall fun x =>
    (iterDeriv_eq_gaussPoly n x).symm)

private theorem tendsto_iterDeriv_atTop (n : ℕ) :
    Filter.Tendsto (iterDeriv n Q) Filter.atTop (nhds 0) := by
  have h :=
    tendsto_eval_mul_gaussian_cocompact (gaussPoly n)
  rw [cocompact_eq_atBot_atTop] at h
  have h' := h.mono_left le_sup_right
  exact h'.congr' (Filter.Eventually.of_forall fun x =>
    (iterDeriv_eq_gaussPoly n x).symm)

private theorem alpha_zero_le {k : ℕ} {α : ℕ → ℝ}
    (hk : 1 ≤ k) (hsort : StrictList α k) {i : ℕ} (hi : i < k) :
    α 0 ≤ α i := by
  exact (strictMonoOn_of_StrictList hsort).monotoneOn
    (Set.mem_Iio.mpr hk) (Set.mem_Iio.mpr hi) (Nat.zero_le i)

private theorem alpha_le_last {k : ℕ} {α : ℕ → ℝ}
    (hk : 1 ≤ k) (hsort : StrictList α k) {i : ℕ} (hi : i < k) :
    α i ≤ α (k - 1) := by
  exact (strictMonoOn_of_StrictList hsort).monotoneOn
    (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr (by omega))
    (by omega)

private theorem iterDeriv_ne_zero_lt_first
    {k : ℕ} {α : ℕ → ℝ} (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) {x : ℝ} (hx : x < α 0) :
    iterDeriv k Q x ≠ 0 := by
  intro hfx
  have hm : x ∈ zeros (iterDeriv k Q) := hfx
  rw [hzero] at hm
  rcases hm with ⟨i, hi, rfl⟩
  have hik : i < k := by simpa [rootList] using hi
  exact (not_lt_of_ge (alpha_zero_le hk hsort hik)) hx

private theorem iterDeriv_ne_zero_gt_last
    {k : ℕ} {α : ℕ → ℝ} (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) {x : ℝ} (hx : α (k - 1) < x) :
    iterDeriv k Q x ≠ 0 := by
  intro hfx
  have hm : x ∈ zeros (iterDeriv k Q) := hfx
  rw [hzero] at hm
  rcases hm with ⟨i, hi, rfl⟩
  have hik : i < k := by simpa [rootList] using hi
  exact (not_lt_of_ge (alpha_le_last hk hsort hik)) hx

private theorem exists_deriv_zero_lt_first
    {k : ℕ} {α : ℕ → ℝ} (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    ∃ β < α 0, deriv (iterDeriv k Q) β = 0 := by
  let f := iterDeriv k Q
  let c := α 0 - 1
  have hc : c < α 0 := by simp [c]
  have hfc : f c ≠ 0 :=
    iterDeriv_ne_zero_lt_first hk hzero hsort hc
  have habsfc : 0 < |f c| := abs_pos.mpr hfc
  have hsmall : ∀ᶠ x in Filter.atBot, |f x| < |f c| := by
    have hball := (tendsto_iterDeriv_atBot k).eventually
      (Metric.ball_mem_nhds 0 habsfc)
    filter_upwards [hball] with x hx
    simpa [f, Real.dist_eq] using hx
  rcases (hsmall.and (Filter.eventually_lt_atBot c)).exists with
    ⟨b, habs, hbc⟩
  have hbfirst : b < α 0 := hbc.trans hc
  have hfb : f b ≠ 0 :=
    iterDeriv_ne_zero_lt_first hk hzero hsort hbfirst
  have hsame : 0 < f b * f c := by
    by_contra hnpos
    have hnonpos : f b * f c ≤ 0 := le_of_not_gt hnpos
    have hzmem : 0 ∈ Set.uIcc (f b) (f c) := by
      rcases le_total (f b) (f c) with hle | hle
      · rw [Set.uIcc_of_le hle]
        constructor <;> nlinarith
      · rw [Set.uIcc_of_ge hle]
        constructor <;> nlinarith
    rcases (intermediate_value_uIcc
        (continuous_iterDeriv k).continuousOn) hzmem with
      ⟨d, hd, hfd⟩
    rw [Set.uIcc_of_le hbc.le] at hd
    have hdfirst : d < α 0 := hd.2.trans_lt hc
    exact iterDeriv_ne_zero_lt_first hk hzero hsort hdfirst hfd
  have hbetween : f b ∈ Set.uIcc (f c) 0 := by
    rcases (mul_pos_iff.mp hsame) with hpos | hneg
    · rw [Set.uIcc_of_ge hpos.2.le]
      constructor
      · exact hpos.1.le
      · rw [abs_of_pos hpos.1, abs_of_pos hpos.2] at habs
        exact habs.le
    · rw [Set.uIcc_of_le hneg.2.le]
      constructor
      · rw [abs_of_neg hneg.1, abs_of_neg hneg.2] at habs
        linarith
      · exact hneg.1.le
  have hfa : f (α 0) = 0 := by
    have hm : α 0 ∈ zeros (iterDeriv k Q) := by
      rw [hzero]
      exact ⟨0, by simpa [rootList] using hk, rfl⟩
    exact hm
  have hbetween' : f b ∈ Set.uIcc (f c) (f (α 0)) := by
    simpa [hfa] using hbetween
  rcases (intermediate_value_uIcc
      (continuous_iterDeriv k).continuousOn) hbetween' with
    ⟨d, hd, hfd⟩
  rw [Set.uIcc_of_le hc.le] at hd
  have hdc : c < d := by
    apply lt_of_le_of_ne hd.1
    intro hcd
    subst d
    apply (ne_of_lt habs)
    simpa [f] using congrArg abs hfd.symm
  have hda : d < α 0 := by
    apply lt_of_le_of_ne hd.2
    intro hda
    subst d
    exact hfb (hfd.symm.trans hfa)
  rcases exists_deriv_eq_zero (hbc.trans hdc)
      (continuous_iterDeriv k).continuousOn hfd.symm with
    ⟨β, hβ, hβzero⟩
  exact ⟨β, hβ.2.trans hda, hβzero⟩

private theorem exists_deriv_zero_gt_last
    {k : ℕ} {α : ℕ → ℝ} (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    ∃ β > α (k - 1), deriv (iterDeriv k Q) β = 0 := by
  let f := iterDeriv k Q
  let c := α (k - 1) + 1
  have hc : α (k - 1) < c := by simp [c]
  have hfc : f c ≠ 0 :=
    iterDeriv_ne_zero_gt_last hk hzero hsort hc
  have habsfc : 0 < |f c| := abs_pos.mpr hfc
  have hsmall : ∀ᶠ x in Filter.atTop, |f x| < |f c| := by
    have hball := (tendsto_iterDeriv_atTop k).eventually
      (Metric.ball_mem_nhds 0 habsfc)
    filter_upwards [hball] with x hx
    simpa [f, Real.dist_eq] using hx
  rcases (hsmall.and (Filter.eventually_gt_atTop c)).exists with
    ⟨b, habs, hcb⟩
  have hblast : α (k - 1) < b := hc.trans hcb
  have hfb : f b ≠ 0 :=
    iterDeriv_ne_zero_gt_last hk hzero hsort hblast
  have hsame : 0 < f b * f c := by
    by_contra hnpos
    have hnonpos : f b * f c ≤ 0 := le_of_not_gt hnpos
    have hzmem : 0 ∈ Set.uIcc (f c) (f b) := by
      rcases le_total (f c) (f b) with hle | hle
      · rw [Set.uIcc_of_le hle]
        constructor <;> nlinarith
      · rw [Set.uIcc_of_ge hle]
        constructor <;> nlinarith
    rcases (intermediate_value_uIcc
        (continuous_iterDeriv k).continuousOn) hzmem with
      ⟨d, hd, hfd⟩
    rw [Set.uIcc_of_le hcb.le] at hd
    have hdlast : α (k - 1) < d := hc.trans_le hd.1
    exact iterDeriv_ne_zero_gt_last hk hzero hsort hdlast hfd
  have hbetween : f b ∈ Set.uIcc (f c) 0 := by
    rcases (mul_pos_iff.mp hsame) with hpos | hneg
    · rw [Set.uIcc_of_ge hpos.2.le]
      constructor
      · exact hpos.1.le
      · rw [abs_of_pos hpos.1, abs_of_pos hpos.2] at habs
        exact habs.le
    · rw [Set.uIcc_of_le hneg.2.le]
      constructor
      · rw [abs_of_neg hneg.1, abs_of_neg hneg.2] at habs
        linarith
      · exact hneg.1.le
  have hfa : f (α (k - 1)) = 0 := by
    have hm : α (k - 1) ∈ zeros (iterDeriv k Q) := by
      rw [hzero]
      exact ⟨k - 1, by
        simpa [rootList] using (show k - 1 < k by omega), rfl⟩
    exact hm
  have hbetween' :
      f b ∈ Set.uIcc (f (α (k - 1))) (f c) := by
    simpa [hfa, Set.uIcc_comm] using hbetween
  rcases (intermediate_value_uIcc
      (continuous_iterDeriv k).continuousOn) hbetween' with
    ⟨d, hd, hfd⟩
  rw [Set.uIcc_of_le hc.le] at hd
  have had : α (k - 1) < d := by
    apply lt_of_le_of_ne hd.1
    intro had
    subst d
    exact hfb (hfd.symm.trans hfa)
  have hdc : d < c := by
    apply lt_of_le_of_ne hd.2
    intro hdc
    subst d
    apply (ne_of_lt habs)
    simpa [f] using congrArg abs hfd.symm
  rcases exists_deriv_eq_zero (hdc.trans hcb)
      (continuous_iterDeriv k).continuousOn hfd with
    ⟨β, hβ, hβzero⟩
  exact ⟨β, had.trans hβ.1, hβzero⟩

private theorem exists_strict_enumeration
    (s : Set ℝ) (hs : s.Finite) :
    ∃ α : ℕ → ℝ,
      s = rootList α s.ncard ∧ StrictList α s.ncard := by
  let t : Finset ℝ := hs.toFinset
  let l : ℕ := s.ncard
  have htcard : t.card = l := by
    simp [t, l, Set.ncard_eq_toFinset_card s hs]
  let e : Fin l ≃o t := t.orderIsoOfFin htcard
  let α : ℕ → ℝ := fun i =>
    if hi : i < l then (e ⟨i, hi⟩ : ℝ) else 0
  have hset : s = rootList α l := by
    ext x
    constructor
    · intro hx
      let z : t := ⟨x, hs.mem_toFinset.mpr hx⟩
      let j : Fin l := e.symm z
      rw [rootList]
      refine ⟨j.val, Finset.mem_range.mpr j.isLt, ?_⟩
      simp only [α, dif_pos j.isLt]
      exact congrArg Subtype.val (e.apply_symm_apply z)
    · intro hx
      rw [rootList] at hx
      rcases hx with ⟨i, hi, rfl⟩
      have hil : i < l := Finset.mem_range.mp hi
      have helem : (e ⟨i, hil⟩ : ℝ) ∈ s :=
        hs.mem_toFinset.mp (e ⟨i, hil⟩).property
      simpa [α, hil] using helem
  have hstrict : StrictList α l := by
    intro i hi
    have hi0 : i < l := by omega
    have hi1 : i + 1 < l := hi
    simp only [α, dif_pos hi0, dif_pos hi1]
    exact e.strictMono (by simp)
  exact ⟨α, by simpa [l] using hset, by simpa [l] using hstrict⟩

theorem gap1 (x : ℝ) :
    deriv Q x = -2 * x * Real.exp (-x ^ 2) := by
  unfold Q
  have hsq : HasDerivAt (fun t : ℝ => -t ^ 2) (-2 * x) x := by
    convert ((hasDerivAt_id x).pow 2).neg using 1 <;>
      simp only [id_eq] <;> ring
  convert ((Real.hasDerivAt_exp (-x ^ 2)).comp x hsq).deriv using 1 <;>
    ring

theorem gap2 (x : ℝ) :
    iterDeriv 2 Q x =
      2 * Real.exp (-x ^ 2) *
        (Real.sqrt 2 * x + 1) * (Real.sqrt 2 * x - 1) := by
  rw [iterDeriv_eq_gaussPoly]
  have hs : Real.sqrt 2 ^ 2 = 2 := by norm_num
  simp [gaussPoly, Polynomial.eval_sub, Polynomial.eval_mul]
  have hfac :
      (Real.sqrt 2 * x + 1) * (Real.sqrt 2 * x - 1) =
        2 * x ^ 2 - 1 := by
    nlinarith
  calc
    (-2 + 2 * x * (2 * x)) * Real.exp (-x ^ 2) =
        2 * Real.exp (-x ^ 2) * (2 * x ^ 2 - 1) := by ring
    _ = 2 * Real.exp (-x ^ 2) *
        (Real.sqrt 2 * x + 1) * (Real.sqrt 2 * x - 1) := by
      rw [← hfac]
      ring

theorem gap3 :
    (zeros (deriv Q)).ncard = 1 := by
  have hz : zeros (deriv Q) = ({0} : Set ℝ) := by
    ext x
    simp only [zeros, Set.mem_setOf_eq, Set.mem_singleton_iff]
    rw [gap1]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · norm_num at h
        · linarith
      · exact False.elim (Real.exp_ne_zero _ h)
    · intro h
      subst x
      ring
  rw [hz]
  simp

theorem gap4 :
    zeros (deriv Q) ⊆ Set.univ := by
  exact Set.subset_univ _

theorem gap5 :
    (zeros (iterDeriv 2 Q)).ncard = 2 := by
  let s := Real.sqrt 2
  have hspos : 0 < s := by positivity
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hz :
      zeros (iterDeriv 2 Q) =
        ({-(1 / s), 1 / s} : Set ℝ) := by
    ext x
    simp only [zeros, Set.mem_setOf_eq, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    rw [gap2]
    change
      2 * Real.exp (-x ^ 2) * (s * x + 1) * (s * x - 1) = 0 ↔
        x = -(1 / s) ∨ x = 1 / s
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · norm_num at h
          · exact False.elim (Real.exp_ne_zero _ h)
        · left
          field_simp [hsne]
          linarith
      · right
        field_simp [hsne]
        linarith
    · intro h
      rcases h with h | h
      · subst x
        have : s * (-(1 / s)) + 1 = 0 := by
          field_simp [hsne]
          norm_num
        rw [this]
        ring
      · subst x
        have : s * (1 / s) - 1 = 0 := by
          field_simp [hsne]
          norm_num
        rw [this]
        ring
  rw [hz]
  have hne : -(1 / s) ≠ 1 / s := by
    intro h
    have hinv : 0 < 1 / s := one_div_pos.mpr hspos
    linarith
  exact Set.ncard_pair hne

theorem gap6 :
    zeros (iterDeriv 2 Q) ⊆ Set.univ := by
  exact Set.subset_univ _

theorem gap7 (k : ℕ) (α : ℕ → ℝ)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    ∃ A : ℝ, A ≠ 0 ∧ ∀ x,
      iterDeriv k Q x =
        A * Real.exp (-x ^ 2) * ∏ i ∈ Finset.range k, (x - α i) := by
  refine ⟨(-2 : ℝ) ^ k, pow_ne_zero _ (by norm_num), ?_⟩
  intro x
  rw [iterDeriv_eq_gaussPoly,
    gaussPoly_factor_of_zeros k α hzero hsort]
  simp only [Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X]
  ring

theorem gap8 (k : ℕ) (α : ℕ → ℝ) (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    ∀ i, i + 1 < k → ∃ β ∈ Set.Ioo (α i) (α (i + 1)),
      iterDeriv (k + 1) Q β = 0 := by
  intro i hi
  have hab : α i < α (i + 1) := hsort i hi
  have hzi : iterDeriv k Q (α i) = 0 := by
    have hm : α i ∈ zeros (iterDeriv k Q) := by
      rw [hzero]
      exact ⟨i, by simpa [rootList] using (show i < k by omega), rfl⟩
    exact hm
  have hzi1 : iterDeriv k Q (α (i + 1)) = 0 := by
    have hm : α (i + 1) ∈ zeros (iterDeriv k Q) := by
      rw [hzero]
      exact ⟨i + 1, by simpa [rootList] using hi, rfl⟩
    exact hm
  rcases exists_deriv_eq_zero hab
      (continuous_iterDeriv k).continuousOn
      (hzi.trans hzi1.symm) with
    ⟨β, hβ, hderiv⟩
  refine ⟨β, hβ, ?_⟩
  simpa [iterDeriv, Function.iterate_succ_apply'] using hderiv

theorem gap9 (k : ℕ) (α : ℕ → ℝ) (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    ∃ β < α 0, iterDeriv (k + 1) Q β = 0 := by
  rcases exists_deriv_zero_lt_first hk hzero hsort with
    ⟨β, hβ, hzeroβ⟩
  refine ⟨β, hβ, ?_⟩
  simpa [iterDeriv, Function.iterate_succ_apply'] using hzeroβ

theorem gap10 (k : ℕ) (α : ℕ → ℝ) (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    ∃ β > α (k - 1), iterDeriv (k + 1) Q β = 0 := by
  rcases exists_deriv_zero_gt_last hk hzero hsort with
    ⟨β, hβ, hzeroβ⟩
  refine ⟨β, hβ, ?_⟩
  simpa [iterDeriv, Function.iterate_succ_apply'] using hzeroβ

theorem gap11 (k : ℕ) (α : ℕ → ℝ) (hk : 1 ≤ k)
    (hzero : zeros (iterDeriv k Q) = rootList α k)
    (hsort : StrictList α k) :
    (zeros (iterDeriv (k + 1) Q)).ncard = k + 1 := by
  classical
  rcases gap9 k α hk hzero hsort with
    ⟨left, hleft, hleftzero⟩
  rcases gap10 k α hk hzero hsort with
    ⟨right, hright, hrightzero⟩
  let mid : ℕ → ℝ := fun i =>
    if hi : i + 1 < k then
      Classical.choose (gap8 k α hk hzero hsort i hi)
    else 0
  have hmid (i : ℕ) (hi : i + 1 < k) :
      mid i ∈ Set.Ioo (α i) (α (i + 1)) ∧
        iterDeriv (k + 1) Q (mid i) = 0 := by
    simp only [mid, dif_pos hi]
    exact Classical.choose_spec
      (gap8 k α hk hzero hsort i hi)
  let β : ℕ → ℝ := fun j =>
    if j = 0 then left else if j = k then right else mid (j - 1)
  have hβ0 : β 0 = left := by simp [β]
  have hβlast : β k = right := by simp [β, Nat.ne_of_gt hk]
  have hβmid (j : ℕ) (hj0 : 0 < j) (hjk : j < k) :
      β j = mid (j - 1) := by
    simp [β, Nat.ne_of_gt hj0, ne_of_lt hjk]
  have hβzero (j : ℕ) (hj : j < k + 1) :
      iterDeriv (k + 1) Q (β j) = 0 := by
    by_cases hj0 : j = 0
    · subst j
      rwa [hβ0]
    by_cases hjk : j = k
    · subst j
      rwa [hβlast]
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjlt : j < k := by omega
    rw [hβmid j hjpos hjlt]
    exact (hmid (j - 1) (by omega)).2
  have hβadj (i : ℕ) (hi : i + 1 < k + 1) :
      β i < β (i + 1) := by
    have hik : i < k := by omega
    by_cases hi0 : i = 0
    · subst i
      by_cases hk1 : k = 1
      · subst k
        rw [hβ0, hβlast]
        linarith
      · rw [hβ0, hβmid 1 (by omega) (by omega)]
        exact hleft.trans (hmid 0 (by omega)).1.1
    · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
      by_cases hilast : i + 1 = k
      · rw [hβmid i hipos hik, hilast, hβlast]
        have hm := (hmid (i - 1) (by omega)).1.2
        have hai : α i = α (k - 1) := by
          congr 1
          omega
        have hprev : i - 1 + 1 = i := by omega
        rw [hprev, hai] at hm
        exact hm.trans hright
      · have hi1lt : i + 1 < k := by omega
        rw [hβmid i hipos hik,
          hβmid (i + 1) (by omega) hi1lt]
        have hm1 := (hmid (i - 1) (by omega)).1.2
        have hm2 := (hmid i hi1lt).1.1
        have hai : α ((i - 1) + 1) = α i := by
          congr 1
          omega
        rw [hai] at hm1
        exact hm1.trans hm2
  have hmono : StrictMonoOn β (Set.Iio (k + 1)) := by
    apply strictMonoOn_of_lt_add_one Set.ordConnected_Iio
    intro i _hiMax _hi hi1
    exact hβadj i hi1
  have hinj :
      Set.InjOn β (↑(Finset.range (k + 1)) : Set ℕ) := by
    apply hmono.injOn.mono
    intro i hi
    exact Set.mem_Iio.mpr (Finset.mem_range.mp hi)
  have hsubset :
      β '' (↑(Finset.range (k + 1)) : Set ℕ) ⊆
        zeros (iterDeriv (k + 1) Q) := by
    rintro x ⟨j, hj, rfl⟩
    exact hβzero j (Finset.mem_range.mp hj)
  have hfinite : (zeros (iterDeriv (k + 1) Q)).Finite := by
    rw [zeros_iterDeriv_eq_rootSet]
    exact Polynomial.rootSet_finite _ _
  have hlower :
      k + 1 ≤ (zeros (iterDeriv (k + 1) Q)).ncard := by
    calc
      k + 1 =
          (β '' (↑(Finset.range (k + 1)) : Set ℕ)).ncard := by
        rw [hinj.ncard_image, Set.ncard_coe_finset,
          Finset.card_range]
      _ ≤ (zeros (iterDeriv (k + 1) Q)).ncard :=
        Set.ncard_le_ncard hsubset hfinite
  have hupper :=
    ncard_zeros_iterDeriv_le (k + 1)
  omega

theorem gap12 (k : ℕ) :
    zeros (iterDeriv (k + 1) Q) ⊆ Set.univ := by
  exact Set.subset_univ _

theorem gap13 (n : ℕ) :
    (zeros (iterDeriv n Q)).ncard = n := by
  induction n with
  | zero =>
      have hupper := ncard_zeros_iterDeriv_le 0
      omega
  | succ n ih =>
      by_cases hn : n = 0
      · subst n
        simpa [iterDeriv, Function.iterate_succ_apply'] using gap3
      · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
        have hfinite : (zeros (iterDeriv n Q)).Finite := by
          rw [zeros_iterDeriv_eq_rootSet]
          exact Polynomial.rootSet_finite _ _
        rcases exists_strict_enumeration
            (zeros (iterDeriv n Q)) hfinite with
          ⟨α, henum, hsort⟩
        have hzero :
            zeros (iterDeriv n Q) = rootList α n := by
          simpa [ih] using henum
        have hsort' : StrictList α n := by
          simpa [ih] using hsort
        simpa [Nat.succ_eq_add_one] using
          gap11 n α hnpos hzero hsort'

theorem gap14 (n : ℕ) :
    zeros (iterDeriv n Q) ⊆ Set.univ := by
  exact Set.subset_univ _

theorem gap15 (n : ℕ) (x : ℝ) :
    H n x = (-1 : ℝ) ^ n * Real.exp (x ^ 2) * iterDeriv n Q x := by
  rfl

theorem gap16 (n : ℕ) :
    zeros (H n) = zeros (iterDeriv n Q) := by
  ext x
  simp only [zeros, Set.mem_setOf_eq, H]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with hsign | hexp
      · exact False.elim (pow_ne_zero n (by norm_num : (-1 : ℝ) ≠ 0) hsign)
      · exact False.elim (Real.exp_ne_zero _ hexp)
    · exact h
  · intro h
    simp [h]

theorem gap17 (n : ℕ) :
    zeros (H n) ⊆ Set.univ := by
  exact Set.subset_univ _

theorem gap18 (n : ℕ) :
    zeros (H n) ⊆ Set.univ := by
  exact Set.subset_univ _

end

end ProofGap.Exercise1243
