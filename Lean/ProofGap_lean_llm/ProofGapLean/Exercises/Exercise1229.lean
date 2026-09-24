import ProofGapLean.Prelude.Core
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

namespace ProofGap.Exercise1229

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def y (f φ : ℝ → ℝ) (x : ℝ) : ℝ := f (φ x)

def expansion (f φ : ℝ → ℝ) (n : ℕ) (A : ℕ → ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, A k x * iterDeriv k f (φ x)

def RepresentsNear (f φ : ℝ → ℝ) (n : ℕ) (A : ℕ → ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ᶠ t in nhds x, iterDeriv n (y f φ) t = expansion f φ n A t

private lemma contDiffAt_iterDeriv (f : ℝ → ℝ) (x : ℝ) (n k : ℕ)
    (hf : ContDiffAt ℝ (n + k) f x) :
    ContDiffAt ℝ n (iterDeriv k f) x := by
  induction k generalizing f with
  | zero =>
      simpa [iterDeriv] using hf
  | succ k ih =>
      have hf' : ContDiffAt ℝ ((n + k) + 1) f x := by
        convert hf using 1 <;> omega
      have hderiv :
          ContDiffAt ℝ (n + k) (deriv f) x := by
        exact hf'.derivWithin (m := n + k) (le_refl _)
      simpa [iterDeriv, Function.iterate_succ_apply] using
        ih (f := deriv f) hderiv

theorem gap1 (f φ : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    deriv (y f φ) x = deriv f (φ x) * deriv φ x := by
  have hc :
      HasDerivAt (f ∘ φ) (deriv f (φ x) * deriv φ x) x :=
    HasDerivAt.comp x hf.hasDerivAt hφ.hasDerivAt
  unfold y
  simpa only [Function.comp_apply] using hc.deriv

theorem gap2 (f φ : ℝ → ℝ) (x : ℝ)
    (hf : DifferentiableAt ℝ f (φ x)) (hφ : DifferentiableAt ℝ φ x) :
    ∃ A : ℕ → ℝ → ℝ,
      deriv (y f φ) x = A 1 x * deriv f (φ x) := by
  refine ⟨fun _ _ => deriv φ x, ?_⟩
  rw [gap1 f φ x hf hφ]
  ring

theorem gap3 (f φ : ℝ → ℝ) (m : ℕ) (x : ℝ) (A : ℕ → ℝ → ℝ)
    (hrep : RepresentsNear f φ m A x) :
    iterDeriv (m + 1) (y f φ) x =
      deriv (fun t => expansion f φ m A t) x := by
  unfold RepresentsNear at hrep
  rw [iterDeriv, Function.iterate_succ_apply']
  exact Filter.EventuallyEq.deriv_eq hrep

theorem gap4 (f φ : ℝ → ℝ) (m : ℕ) (x : ℝ) (A : ℕ → ℝ → ℝ)
    (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1) f (φ x))
    (hφ : ContDiffAt ℝ (m + 1) φ x)
    (hA : ∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (A k) x)
    (hrep : RepresentsNear f φ m A x) :
    iterDeriv (m + 1) (y f φ) x =
      ∑ k ∈ Finset.Icc 1 m,
        (deriv (A k) x * iterDeriv k f (φ x) +
          A k x * iterDeriv (k + 1) f (φ x) * deriv φ x) := by
  have hφdiff : DifferentiableAt ℝ φ x :=
    hφ.differentiableAt (by
      change ((↑(m + 1) : ℕ∞) : WithTop ℕ∞) ≠ 0
      simp)
  have hsum :
      HasDerivAt (fun t => expansion f φ m A t)
        (∑ k ∈ Finset.Icc 1 m,
          (deriv (A k) x * iterDeriv k f (φ x) +
            A k x * iterDeriv (k + 1) f (φ x) * deriv φ x)) x := by
    unfold expansion
    apply HasDerivAt.fun_sum
    intro k hk
    have hk_le : k ≤ m := (Finset.mem_Icc.mp hk).2
    have hfkcd :
        ContDiffAt ℝ 1 (iterDeriv k f) (φ x) := by
      apply contDiffAt_iterDeriv f (φ x) 1 k
      apply hf.of_le
      have hn : 1 + k ≤ m + 1 := by omega
      change ((↑(1 + k) : ℕ∞) : WithTop ℕ∞) ≤
        ((↑(m + 1) : ℕ∞) : WithTop ℕ∞)
      rw [WithTop.coe_le_coe, ENat.coe_le_coe]
      exact hn
    have hfkd : DifferentiableAt ℝ (iterDeriv k f) (φ x) :=
      hfkcd.differentiableAt (by norm_num)
    have hcomp :
        HasDerivAt (fun t => iterDeriv k f (φ t))
          (iterDeriv (k + 1) f (φ x) * deriv φ x) x := by
      have hc := HasDerivAt.comp x hfkd.hasDerivAt hφdiff.hasDerivAt
      convert hc using 1 <;>
        simp only [Function.comp_apply, iterDeriv,
          Function.iterate_succ_apply'] <;> ring
    convert HasDerivAt.mul (hA k hk).hasDerivAt hcomp using 1 <;>
      ring
  rw [gap3 f φ m x A hrep]
  exact hsum.deriv

theorem gap5 (f φ : ℝ → ℝ) (m : ℕ) (x : ℝ) (A : ℕ → ℝ → ℝ)
    (hm : 1 ≤ m) (hf : ContDiffAt ℝ (m + 1) f (φ x))
    (hφ : ContDiffAt ℝ (m + 1) φ x)
    (hA : ∀ k ∈ Finset.Icc 1 m, DifferentiableAt ℝ (A k) x)
    (hrep : RepresentsNear f φ m A x) :
    ∃ B : ℕ → ℝ → ℝ,
      iterDeriv (m + 1) (y f φ) x = expansion f φ (m + 1) B x := by
  by_cases hex :
      ∃ k ∈ Finset.Icc 1 (m + 1), iterDeriv k f (φ x) ≠ 0
  · rcases hex with ⟨k, hk, hk0⟩
    let B : ℕ → ℝ → ℝ := fun j _ =>
      if j = k then
        iterDeriv (m + 1) (y f φ) x / iterDeriv k f (φ x)
      else 0
    refine ⟨B, ?_⟩
    unfold expansion
    rw [Finset.sum_eq_single k]
    · simp [B, hk0]
    · intro j hj hjk
      simp [B, hjk]
    · intro hknot
      exact (hknot hk).elim
  · push_neg at hex
    have hzero : iterDeriv (m + 1) (y f φ) x = 0 := by
      rw [gap4 f φ m x A hm hf hφ hA hrep]
      apply Finset.sum_eq_zero
      intro k hk
      have hkm : k ≤ m := (Finset.mem_Icc.mp hk).2
      have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
      have hdk : iterDeriv k f (φ x) = 0 :=
        hex k (Finset.mem_Icc.mpr ⟨hk1, by omega⟩)
      have hdk1 : iterDeriv (k + 1) f (φ x) = 0 :=
        hex (k + 1) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
      rw [hdk, hdk1]
      ring
    refine ⟨fun _ _ => 0, ?_⟩
    rw [hzero]
    simp [expansion]

theorem gap6 (φ : ℝ → ℝ) (m : ℕ) (x : ℝ) (A : ℕ → ℝ → ℝ) :
    ∃ B : ℕ → ℝ → ℝ, B 1 x = deriv (A 1) x := by
  exact ⟨fun _ _ => deriv (A 1) x, rfl⟩

theorem gap7 (φ : ℝ → ℝ) (m k : ℕ) (x : ℝ) (A : ℕ → ℝ → ℝ)
    (hk₁ : 2 ≤ k) (hk₂ : k ≤ m) :
    ∃ B : ℕ → ℝ → ℝ,
      B k x = deriv φ x * A (k - 1) x + deriv (A k) x := by
  exact
    ⟨fun _ _ => deriv φ x * A (k - 1) x + deriv (A k) x, rfl⟩

theorem gap8 (φ : ℝ → ℝ) (m : ℕ) (x : ℝ) (A : ℕ → ℝ → ℝ) :
    ∃ B : ℕ → ℝ → ℝ,
      B (m + 1) x = A m x * deriv φ x := by
  exact ⟨fun _ _ => A m x * deriv φ x, rfl⟩

theorem gap9 (f φ : ℝ → ℝ) (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hf : ContDiffAt ℝ n f (φ x)) (hφ : ContDiffAt ℝ n φ x) :
    ∃ A : ℕ → ℝ → ℝ,
      iterDeriv n (y f φ) x = expansion f φ n A x := by
  classical
  let P : OrderedFinpartition n → ℝ := fun c =>
    ∏ j, iteratedDeriv (c.partSize j) φ x
  let A : ℕ → ℝ → ℝ := fun k _ =>
    ∑ c : OrderedFinpartition n with c.length = k, P c
  refine ⟨A, ?_⟩
  have hlhs :
      iterDeriv n (y f φ) x = iteratedDeriv n (f ∘ φ) x := by
    unfold iterDeriv y
    rw [iteratedDeriv_eq_iterate]
    rfl
  have hFaa :
      iteratedDeriv n (f ∘ φ) x =
        ∑ c : OrderedFinpartition n,
          iteratedDeriv c.length f (φ x) * P c := by
    simpa only [P] using
      iteratedDeriv_comp_eq_sum_orderedFinpartition hf hφ
        (i := n) (le_refl _)
  have hmaps :
      ∀ c ∈ (Finset.univ : Finset (OrderedFinpartition n)),
        c.length ∈ Finset.Icc 1 n := by
    intro c hc
    exact Finset.mem_Icc.mpr
      ⟨c.length_pos (by omega), c.length_le⟩
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to hmaps
      (fun c : OrderedFinpartition n =>
        iteratedDeriv c.length f (φ x) * P c)
  have hexp :
      expansion f φ n A x =
        ∑ k ∈ Finset.Icc 1 n,
          ∑ c : OrderedFinpartition n with c.length = k,
            iteratedDeriv c.length f (φ x) * P c := by
    unfold expansion A
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro c hc
    have hck : c.length = k := (Finset.mem_filter.mp hc).2
    rw [hck]
    simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
    ring
  rw [hlhs, hFaa]
  exact (hexp.trans hfiber).symm

theorem gap10 (f φ : ℝ → ℝ) (n : ℕ) (x : ℝ) (hn : 1 ≤ n)
    (hf : ContDiffAt ℝ n f (φ x)) (hφ : ContDiffAt ℝ n φ x) :
    ∃ A : ℕ → ℝ → ℝ,
      iterDeriv n (y f φ) x = expansion f φ n A x := by
  exact gap9 f φ n x hn hf hφ

end

end ProofGap.Exercise1229
