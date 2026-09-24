import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Data.Finset.Sort

namespace ProofGap.Exercise1240

noncomputable section

open scoped BigOperators

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def zeros (u : ℝ → ℝ) : Set ℝ := {x | u x = 0}
def rootList (α : ℕ → ℝ) (l : ℕ) : Set ℝ := α '' (Finset.range l : Set ℕ)
def RootMultiplicity (u : ℝ → ℝ) (x : ℝ) (k : ℕ) : Prop :=
  (∀ j < k, iterDeriv j u x = 0) ∧ iterDeriv k u x ≠ 0
def StrictList (α : ℕ → ℝ) (l : ℕ) : Prop :=
  ∀ i, i + 1 < l → α i < α (i + 1)
def TotalMultiplicity (k : ℕ → ℕ) (l : ℕ) : ℕ :=
  ∑ i ∈ Finset.range l, k i

def FactorData (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ) : Prop :=
  a₀ ≠ 0 ∧ ((n = 0 ∧ l = 0) ∨ 1 ≤ l) ∧ StrictList α l ∧
  (∀ i < l, 1 ≤ k i) ∧
  TotalMultiplicity k l = n ∧
  (∀ x, P x = a₀ * ∏ i ∈ Finset.range l, (x - α i) ^ k i)

def DerivativeRootCount (k : ℕ → ℕ) (l : ℕ) : ℕ :=
  (∑ i ∈ Finset.range l, (k i - 1)) + (l - 1)

def HasRealFactorization (P : ℝ → ℝ) (n : ℕ) : Prop :=
  ∃ l a₀ α k, FactorData P n l a₀ α k

private def factorPoly (l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ) : Polynomial ℝ :=
  Polynomial.C a₀ *
    ∏ i ∈ Finset.range l, (Polynomial.X - Polynomial.C (α i)) ^ k i

private lemma eval_factorPoly (l : ℕ) (a₀ x : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ) :
    (factorPoly l a₀ α k).eval x =
      a₀ * ∏ i ∈ Finset.range l, (x - α i) ^ k i := by
  rw [factorPoly, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp

private lemma eq_eval_factorPoly (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    P = fun x => (factorPoly l a₀ α k).eval x := by
  funext x
  rw [hfac.2.2.2.2.2 x, eval_factorPoly]

private lemma strictMonoOn_alpha (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    StrictMonoOn α (Set.Iio l) := by
  apply strictMonoOn_of_lt_add_one Set.ordConnected_Iio
  intro i hiMax hi hi1
  exact hfac.2.2.1 i hi1

private lemma factorPoly_ne_zero (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    factorPoly l a₀ α k ≠ 0 := by
  unfold factorPoly
  apply mul_ne_zero
  · exact Polynomial.C_ne_zero.mpr hfac.1
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (α i))

private lemma natDegree_factorPoly (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    (factorPoly l a₀ α k).natDegree = n := by
  unfold factorPoly
  rw [Polynomial.natDegree_C_mul hfac.1]
  rw [Polynomial.natDegree_prod]
  · simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C,
      mul_one]
    exact hfac.2.2.2.2.1
  · intro i hi
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (α i))

private lemma splits_factorPoly (l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ) :
    (factorPoly l a₀ α k).Splits := by
  unfold factorPoly
  exact (Polynomial.Splits.C a₀).mul (Polynomial.Splits.prod fun i hi =>
    (Polynomial.Splits.X_sub_C (α i)).pow (k i))

private lemma iterDeriv_eval (q : Polynomial ℝ) (j : ℕ) :
    iterDeriv j (fun x => q.eval x) =
      fun x => ((Polynomial.derivative^[j]) q).eval x := by
  induction j with
  | zero =>
      simp [iterDeriv]
  | succ j ih =>
      rw [show iterDeriv (j + 1) (fun x => q.eval x) =
          deriv (iterDeriv j (fun x => q.eval x)) by
        simp [iterDeriv, Function.iterate_succ_apply']]
      rw [Function.iterate_succ_apply']
      rw [ih]
      funext (x : ℝ)
      exact (((Polynomial.derivative^[j]) q).hasDerivAt x).deriv

private lemma rootMultiplicity_factorPoly (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) {i : ℕ} (hi : i < l) :
    (factorPoly l a₀ α k).rootMultiplicity (α i) = k i := by
  have hprod :
      (∏ j ∈ Finset.range l,
        (Polynomial.X - Polynomial.C (α j)) ^ k j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (α j))
  rw [← Polynomial.count_roots]
  rw [factorPoly, Polynomial.roots_C_mul _ hfac.1,
    Polynomial.roots_prod _ _ hprod]
  simp only [Multiset.count_bind, Polynomial.roots_pow,
    Polynomial.roots_X_sub_C, Multiset.count_nsmul,
    Multiset.count_singleton]
  change (∑ j ∈ Finset.range l,
    k j * if α i = α j then 1 else 0) = k i
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    have hne : α i ≠ α j := by
      intro heq
      exact hji ((strictMonoOn_alpha P n l a₀ α k hfac).injOn
        (Set.mem_Iio.mpr hi)
        (Set.mem_Iio.mpr (Finset.mem_range.mp hj)) heq).symm
    simp [hne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr hi))

private theorem exists_factorData_of_splits (q : Polynomial ℝ) (d : ℕ)
    (hq0 : q ≠ 0) (hdeg : q.natDegree = d) (hsplit : q.Splits) :
    ∃ l a₀ α k,
      FactorData (fun x => q.eval x) d l a₀ α k ∧
      TotalMultiplicity k l = d := by
  let s : Finset ℝ := q.roots.toFinset
  let l : ℕ := s.card
  let e : Fin l ≃o s := s.orderIsoOfFin rfl
  let α : ℕ → ℝ := fun i =>
    if hi : i < l then (e ⟨i, hi⟩ : ℝ) else 0
  let k : ℕ → ℕ := fun i => q.roots.count (α i)
  have hcard : q.roots.card = d := by
    exact hsplit.natDegree_eq_card_roots.symm.trans hdeg
  have htotal : TotalMultiplicity k l = d := by
    unfold TotalMultiplicity
    calc
      (∑ i ∈ Finset.range l, k i) =
          ∑ i : Fin l, k i := by
        exact (Fin.sum_univ_eq_sum_range k l).symm
      _ = ∑ i : Fin l, q.roots.count (e i : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [k, α]
      _ = ∑ z : s, q.roots.count (z : ℝ) := by
        exact Fintype.sum_equiv e.toEquiv _ _ (fun i => rfl)
      _ = ∑ z ∈ s, q.roots.count z := by
        exact Finset.sum_attach s (fun z => q.roots.count z)
      _ = q.roots.card := by
        exact Multiset.toFinset_sum_count_eq q.roots
      _ = d := hcard
  have hstrict : StrictList α l := by
    intro i hi
    have hi0 : i < l := by omega
    have hi1 : i + 1 < l := hi
    simp only [α, dif_pos hi0, dif_pos hi1]
    exact e.strictMono (by simp)
  have hkpos : ∀ i < l, 1 ≤ k i := by
    intro i hi
    have hemem : (e ⟨i, hi⟩ : ℝ) ∈ q.roots := by
      exact Multiset.mem_toFinset.mp (e ⟨i, hi⟩).property
    simp only [k, α, dif_pos hi]
    exact Multiset.count_pos.mpr hemem
  have hshape : (d = 0 ∧ l = 0) ∨ 1 ≤ l := by
    by_cases hd : d = 0
    · left
      refine ⟨hd, ?_⟩
      have hz : q.roots = 0 := Multiset.card_eq_zero.mp (hcard.trans hd)
      simp [l, s, hz]
    · right
      have hroots : q.roots ≠ 0 := by
        intro hz
        rw [hz, Multiset.card_zero] at hcard
        exact hd hcard.symm
      have hsne : s.Nonempty := by
        simpa [s, Multiset.toFinset_nonempty] using hroots
      exact Finset.one_le_card.mpr hsne
  have hprod (x : ℝ) :
      (q.roots.map (x - ·)).prod =
        ∏ i ∈ Finset.range l, (x - α i) ^ k i := by
    calc
      (q.roots.map (x - ·)).prod =
          ∏ z ∈ s, (x - (z : ℝ)) ^ q.roots.count (z : ℝ) := by
        exact Finset.prod_multiset_map_count q.roots (x - ·)
      _ = ∏ z : s, (x - (z : ℝ)) ^ q.roots.count (z : ℝ) := by
        exact (Finset.prod_attach s
          (fun z => (x - z) ^ q.roots.count z)).symm
      _ = ∏ i : Fin l,
          (x - (e i : ℝ)) ^ q.roots.count (e i : ℝ) := by
        exact (Fintype.prod_equiv e.toEquiv _ _
          (fun i => rfl)).symm
      _ = ∏ i : Fin l, (x - α i) ^ k i := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [α, k]
      _ = ∏ i ∈ Finset.range l, (x - α i) ^ k i := by
        exact Fin.prod_univ_eq_prod_range
          (fun i => (x - α i) ^ k i) l
  refine ⟨l, q.leadingCoeff, α, k, ?_, htotal⟩
  refine ⟨Polynomial.leadingCoeff_ne_zero.mpr hq0, hshape, hstrict,
    hkpos, htotal, ?_⟩
  intro x
  change q.eval x =
    q.leadingCoeff * ∏ i ∈ Finset.range l, (x - α i) ^ k i
  rw [hsplit.eval_eq_prod_roots x, hprod x]

theorem gap1 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    TotalMultiplicity k l = n := by
  exact hfac.2.2.2.2.1

theorem gap2 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    zeros P = rootList α l := by
  ext x
  constructor
  · intro hx
    have hx0 : P x = 0 := hx
    rw [hfac.2.2.2.2.2 x] at hx0
    have hp :
        (∏ i ∈ Finset.range l, (x - α i) ^ k i) = 0 :=
      (mul_eq_zero.mp hx0).resolve_left hfac.1
    rw [Finset.prod_eq_zero_iff] at hp
    rcases hp with ⟨i, hi, hzero⟩
    have hki : 1 ≤ k i := hfac.2.2.2.1 i (Finset.mem_range.mp hi)
    have hbase : x - α i = 0 := by
      exact eq_zero_of_pow_eq_zero hzero
    refine ⟨i, ?_, (sub_eq_zero.mp hbase).symm⟩
    simpa [rootList] using hi
  · rintro ⟨i, hi, rfl⟩
    have hil : i ∈ Finset.range l := by
      simpa [rootList] using hi
    show P (α i) = 0
    rw [hfac.2.2.2.2.2 (α i)]
    apply mul_eq_zero.mpr
    right
    rw [Finset.prod_eq_zero_iff]
    refine ⟨i, hil, ?_⟩
    simp [Nat.ne_of_gt (hfac.2.2.2.1 i (Finset.mem_range.mp hil))]

theorem gap3 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∀ i < l, RootMultiplicity P (α i) (k i) := by
  intro i hi
  let q := factorPoly l a₀ α k
  have hP : P = fun x => q.eval x := eq_eval_factorPoly P n l a₀ α k hfac
  have hq0 : q ≠ 0 := factorPoly_ne_zero P n l a₀ α k hfac
  have hrm : q.rootMultiplicity (α i) = k i :=
    rootMultiplicity_factorPoly P n l a₀ α k hfac hi
  have hiter (j : ℕ) :
      iterDeriv j P = fun x => ((Polynomial.derivative^[j]) q).eval x := by
    rw [hP]
    exact iterDeriv_eval q j
  constructor
  · intro j hj
    rw [hiter j]
    exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
      (hrm ▸ hj)
  · intro hkzero
    rw [hiter (k i)] at hkzero
    have hall :
        ∀ m ≤ k i, ((Polynomial.derivative^[m]) q).IsRoot (α i) := by
      intro m hm
      rcases hm.eq_or_lt with rfl | hmlt
      · exact hkzero
      · exact Polynomial.isRoot_iterate_derivative_of_lt_rootMultiplicity
          (hrm ▸ hmlt)
    have hlt :=
      Polynomial.lt_rootMultiplicity_of_isRoot_iterate_derivative hq0 hall
    rw [hrm] at hlt
    omega

theorem gap4 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∀ i < l, 1 ≤ k i := by
  exact hfac.2.2.2.1

theorem gap5 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∑ i ∈ Finset.range l, k i = n := by
  exact gap1 P n l a₀ α k hfac

theorem gap6 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∀ x, P x = a₀ * ∏ i ∈ Finset.range l, (x - α i) ^ k i := by
  exact hfac.2.2.2.2.2

theorem gap7 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∀ i < l, RootMultiplicity (deriv P) (α i) (k i - 1) := by
  intro i hi
  have hroot := gap3 P n l a₀ α k hfac i hi
  have hkpos := gap4 P n l a₀ α k hfac i hi
  constructor
  · intro j hj
    have hjs : j + 1 < k i := by omega
    have hz := hroot.1 (j + 1) hjs
    simpa [iterDeriv, Function.iterate_succ_apply] using hz
  · have hn : k i - 1 + 1 = k i := by omega
    have hnz := hroot.2
    change ((deriv^[k i - 1]) (deriv P)) (α i) ≠ 0
    rw [← Function.iterate_succ_apply]
    simpa [Nat.succ_eq_add_one, hn, iterDeriv] using hnz

theorem gap8 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∀ i, i + 1 < l → ∃ ξ ∈ Set.Ioo (α i) (α (i + 1)),
      deriv P ξ = 0 := by
  intro i hi
  have hab : α i < α (i + 1) := hfac.2.2.1 i hi
  have hzi : P (α i) = 0 := by
    have hm : α i ∈ rootList α l := by
      refine ⟨i, ?_, rfl⟩
      simpa [rootList] using (show i < l by omega)
    rw [← gap2 P n l a₀ α k hfac] at hm
    exact hm
  have hzis : P (α (i + 1)) = 0 := by
    have hm : α (i + 1) ∈ rootList α l := by
      refine ⟨i + 1, ?_, rfl⟩
      simpa [rootList] using hi
    rw [← gap2 P n l a₀ α k hfac] at hm
    exact hm
  have hcont : ContinuousOn P (Set.Icc (α i) (α (i + 1))) := by
    rw [eq_eval_factorPoly P n l a₀ α k hfac]
    exact (factorPoly l a₀ α k).continuous.continuousOn
  exact exists_deriv_eq_zero hab hcont (hzi.trans hzis.symm)

private lemma derivativeRootCount_eq (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    DerivativeRootCount k l = n - 1 := by
  have hpos := gap4 P n l a₀ α k hfac
  have hsum :
      (∑ i ∈ Finset.range l, k i) =
        (∑ i ∈ Finset.range l, (k i - 1)) + l := by
    calc
      (∑ i ∈ Finset.range l, k i) =
          ∑ i ∈ Finset.range l, ((k i - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hik : 1 ≤ k i := hpos i (Finset.mem_range.mp hi)
        omega
      _ = (∑ i ∈ Finset.range l, (k i - 1)) +
          ∑ _i ∈ Finset.range l, 1 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ Finset.range l, (k i - 1)) + l := by simp
  have htotal := gap5 P n l a₀ α k hfac
  unfold DerivativeRootCount
  by_cases hl : l = 0
  · subst l
    simp at htotal ⊢
    omega
  · have hlpos : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl
    omega

theorem gap9 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ) (hn : 1 ≤ n)
    (hfac : FactorData P n l a₀ α k) :
    ∃ l' a₀' α' k',
      FactorData (deriv P) (n - 1) l' a₀' α' k' ∧
      TotalMultiplicity k' l' = DerivativeRootCount k l := by
  let q := factorPoly l a₀ α k
  have hq0 : q ≠ 0 := factorPoly_ne_zero P n l a₀ α k hfac
  have hqdeg : q.natDegree = n :=
    natDegree_factorPoly P n l a₀ α k hfac
  have hqsplit : q.Splits := splits_factorPoly l a₀ α k
  have hqpos : 0 < q.natDegree := by
    rw [hqdeg]
    exact hn
  have hddegree :
      q.derivative.degree = (q.natDegree - 1 : ℕ) :=
    Polynomial.degree_derivative_eq q hqpos
  have hd0 : q.derivative ≠ 0 := by
    intro hz
    rw [hz] at hddegree
    simp at hddegree
  have hddeg : q.derivative.natDegree = n - 1 := by
    calc
      q.derivative.natDegree = q.natDegree - 1 :=
        Polynomial.natDegree_eq_of_degree_eq_some hddegree
      _ = n - 1 := by rw [hqdeg]
  have hqcard : q.roots.card = n :=
    hqsplit.natDegree_eq_card_roots.symm.trans hqdeg
  have hlower := Polynomial.card_roots_le_derivative q
  have hupper := Polynomial.card_roots' q.derivative
  have hdcard : q.derivative.roots.card = n - 1 := by
    rw [hqcard] at hlower
    rw [hddeg] at hupper
    omega
  have hdsplit : q.derivative.Splits := by
    rw [Polynomial.splits_iff_card_roots, hddeg]
    exact hdcard
  rcases exists_factorData_of_splits q.derivative (n - 1) hd0 hddeg hdsplit with
    ⟨l', a₀', α', k', hfac', htotal'⟩
  have hP : P = fun x => q.eval x :=
    eq_eval_factorPoly P n l a₀ α k hfac
  have hderivP : deriv P = fun x => q.derivative.eval x := by
    rw [hP]
    funext (x : ℝ)
    exact (q.hasDerivAt x).deriv
  have hfacDeriv :
      FactorData (deriv P) (n - 1) l' a₀' α' k' := by
    rw [hderivP]
    exact hfac'
  refine ⟨l', a₀', α', k', hfacDeriv, ?_⟩
  rw [htotal']
  exact (derivativeRootCount_eq P n l a₀ α k hfac).symm

theorem gap10 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    (∑ i ∈ Finset.range l, (k i - 1)) + (l - 1) =
      (∑ i ∈ Finset.range l, k i) - 1 := by
  have hpos := gap4 P n l a₀ α k hfac
  have hsum :
      (∑ i ∈ Finset.range l, k i) =
        (∑ i ∈ Finset.range l, (k i - 1)) + l := by
    calc
      (∑ i ∈ Finset.range l, k i) =
          ∑ i ∈ Finset.range l, ((k i - 1) + 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hik : 1 ≤ k i := hpos i (Finset.mem_range.mp hi)
        omega
      _ = (∑ i ∈ Finset.range l, (k i - 1)) +
          ∑ _i ∈ Finset.range l, 1 := by
        rw [Finset.sum_add_distrib]
      _ = (∑ i ∈ Finset.range l, (k i - 1)) + l := by simp
  by_cases hl : l = 0
  · subst l
    simp
  · have hlpos : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl
    omega

theorem gap11 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    (∑ i ∈ Finset.range l, k i) - 1 = n - 1 := by
  rw [gap5 P n l a₀ α k hfac]

theorem gap12 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ) (hn : 1 ≤ n)
    (hfac : FactorData P n l a₀ α k) :
    HasRealFactorization (deriv P) (n - 1) ∧
      ∃ l' a₀' α' k',
        FactorData (deriv P) (n - 1) l' a₀' α' k' ∧
        TotalMultiplicity k' l' = n - 1 := by
  rcases gap9 P n l a₀ α k hn hfac with
    ⟨l', a₀', α', k', hfac', htotal⟩
  have htotal' : TotalMultiplicity k' l' = n - 1 := by
    rw [htotal]
    exact derivativeRootCount_eq P n l a₀ α k hfac
  exact ⟨⟨l', a₀', α', k', hfac'⟩,
    ⟨l', a₀', α', k', hfac', htotal'⟩⟩

theorem gap13 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ) (hn : 1 ≤ n)
    (hfac : FactorData P n l a₀ α k) :
    HasRealFactorization (deriv P) (n - 1) := by
  exact (gap12 P n l a₀ α k hn hfac).1

theorem gap14 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∀ j, 1 ≤ j → j < n →
      HasRealFactorization (iterDeriv j P) (n - j) := by
  have hAll : ∀ j, j ≤ n →
      HasRealFactorization (iterDeriv j P) (n - j) := by
    intro j
    induction j with
    | zero =>
        intro hj
        exact ⟨l, a₀, α, k, by simpa [iterDeriv] using hfac⟩
    | succ j ih =>
        intro hj
        have hjle : j ≤ n := Nat.le_trans (Nat.le_succ j) hj
        rcases ih hjle with ⟨lj, aj, αj, kj, hfacj⟩
        have hpos : 1 ≤ n - j := by omega
        have hd :=
          gap13 (iterDeriv j P) (n - j) lj aj αj kj hpos hfacj
        simpa [iterDeriv, Function.iterate_succ_apply',
          Nat.sub_sub] using hd
  intro j hj1 hjn
  exact hAll j hjn.le

theorem gap15 (P : ℝ → ℝ) (n l : ℕ) (a₀ : ℝ)
    (α : ℕ → ℝ) (k : ℕ → ℕ)
    (hfac : FactorData P n l a₀ α k) :
    ∀ j, 1 ≤ j → j < n →
      ∃ l' a₀' α' k',
        FactorData (iterDeriv j P) (n - j) l' a₀' α' k' ∧
        TotalMultiplicity k' l' = n - j := by
  intro j hj1 hjn
  rcases gap14 P n l a₀ α k hfac j hj1 hjn with
    ⟨l', a₀', α', k', hfac'⟩
  exact ⟨l', a₀', α', k', hfac',
    gap1 (iterDeriv j P) (n - j) l' a₀' α' k' hfac'⟩

end

end ProofGap.Exercise1240
