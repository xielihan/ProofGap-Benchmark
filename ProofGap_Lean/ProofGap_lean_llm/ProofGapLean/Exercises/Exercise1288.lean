import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise1288

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def F (φ ψ : ℝ → ℝ) (x : ℝ) : ℝ := φ x - ψ x

def ComparisonData (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ) : Prop :=
  2 ≤ n ∧ ContDiff ℝ n φ ∧ ContDiff ℝ n ψ ∧
    (∀ k < n, nthDeriv k φ x₀ = nthDeriv k ψ x₀) ∧
    (∀ x, x₀ < x → nthDeriv n ψ x < nthDeriv n φ x)

private theorem nthDeriv_eq_iteratedDeriv (k : ℕ) (f : ℝ → ℝ) :
    nthDeriv k f = iteratedDeriv k f := by
  induction k with
  | zero => simp [nthDeriv]
  | succ k ih =>
      rw [nthDeriv, iteratedDeriv_succ, ih]

private theorem deriv_nthDeriv (k : ℕ) (f : ℝ → ℝ) :
    deriv (nthDeriv k f) = nthDeriv (k + 1) f := by
  rfl

private theorem nthDeriv_deriv (k : ℕ) (f : ℝ → ℝ) :
    nthDeriv k (deriv f) = nthDeriv (k + 1) f := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change deriv (nthDeriv k (deriv f)) = deriv (nthDeriv (k + 1) f)
      rw [ih]

private theorem contDiff_F (φ ψ : ℝ → ℝ) (n : ℕ)
    (hφ : ContDiff ℝ n φ) (hψ : ContDiff ℝ n ψ) :
    ContDiff ℝ n (F φ ψ) := by
  simpa only [F] using hφ.sub hψ

private theorem nthDeriv_sub_of_contDiff (φ ψ : ℝ → ℝ) (n k : ℕ) (x : ℝ)
    (hφ : ContDiff ℝ n φ) (hψ : ContDiff ℝ n ψ) (hk : k ≤ n) :
    nthDeriv k (F φ ψ) x = nthDeriv k φ x - nthDeriv k ψ x := by
  have hφx : ContDiffAt ℝ k φ x :=
    hφ.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hk))
  have hψx : ContDiffAt ℝ k ψ x :=
    hψ.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hk))
  rw [nthDeriv_eq_iteratedDeriv, nthDeriv_eq_iteratedDeriv,
    nthDeriv_eq_iteratedDeriv]
  simpa only [F] using iteratedDeriv_fun_sub hφx hψx

private theorem continuous_nthDeriv_of_contDiff (f : ℝ → ℝ) (n k : ℕ)
    (hf : ContDiff ℝ n f) (hk : k ≤ n) :
    Continuous (nthDeriv k f) := by
  rw [nthDeriv_eq_iteratedDeriv]
  exact hf.continuous_iteratedDeriv k
    (WithTop.coe_le_coe.mpr (ENat.coe_le_coe.mpr hk))

private theorem strictMonoOn_Ici_nthDeriv_of_pos_succ
    (f : ℝ → ℝ) (n k : ℕ) (x₀ : ℝ)
    (hf : ContDiff ℝ n f) (hk : k < n)
    (hpos : ∀ x, x₀ < x → 0 < nthDeriv (k + 1) f x) :
    StrictMonoOn (nthDeriv k f) (Set.Ici x₀) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici x₀)
    (continuous_nthDeriv_of_contDiff f n k hf hk.le).continuousOn
  intro x hx
  rw [deriv_nthDeriv]
  apply hpos x
  simpa only [interior_Ici] using hx

private theorem positive_of_positive_nthDeriv
    (f : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (hf : ContDiff ℝ n f)
    (hzero : ∀ k < n, nthDeriv k f x₀ = 0)
    (hpos : ∀ x, x₀ < x → 0 < nthDeriv n f x) :
    ∀ x, x₀ < x → 0 < f x := by
  induction n generalizing f with
  | zero =>
      intro x hx
      simpa [nthDeriv] using hpos x hx
  | succ n ih =>
      have hf' : ContDiff ℝ n (deriv f) := by
        simpa [Nat.succ_eq_add_one] using hf.deriv'
      have hzero' : ∀ k < n, nthDeriv k (deriv f) x₀ = 0 := by
        intro k hk
        rw [nthDeriv_deriv]
        exact hzero (k + 1) (by omega)
      have hpos' : ∀ x, x₀ < x → 0 < nthDeriv n (deriv f) x := by
        intro x hx
        rw [nthDeriv_deriv]
        exact hpos x hx
      have hderivpos : ∀ x, x₀ < x → 0 < deriv f x :=
        ih (deriv f) hf' hzero' hpos'
      intro x hx
      have hmono : StrictMonoOn f (Set.Ici x₀) :=
        strictMonoOn_of_deriv_pos (convex_Ici x₀) hf.continuous.continuousOn
          (by
            intro y hy
            apply hderivpos y
            simpa only [interior_Ici] using hy)
      have hlt := hmono (Set.self_mem_Ici) hx.le hx
      have hzero0 : f x₀ = 0 := by
        simpa [nthDeriv] using hzero 0 (Nat.zero_lt_succ n)
      rw [hzero0] at hlt
      exact hlt

theorem gap1 (φ ψ : ℝ → ℝ) (n : ℕ) (x : ℝ)
    (h : ComparisonData φ ψ n 0) :
    nthDeriv n (F φ ψ) x = nthDeriv n φ x - nthDeriv n ψ x := by
  exact nthDeriv_sub_of_contDiff φ ψ n n x h.2.1 h.2.2.1 le_rfl

theorem gap2 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ)
    (h : ComparisonData φ ψ n x₀) (hx : x₀ < x) :
    0 < nthDeriv n φ x - nthDeriv n ψ x := by
  exact sub_pos.mpr (h.2.2.2.2 x hx)

theorem gap3 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ)
    (h : ComparisonData φ ψ n x₀) (hx : x₀ < x) :
    0 < nthDeriv n (F φ ψ) x := by
  rw [nthDeriv_sub_of_contDiff φ ψ n n x h.2.1 h.2.2.1 le_rfl]
  exact gap2 φ ψ n x₀ x h hx

theorem gap4 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    StrictMonoOn (nthDeriv (n - 1) (F φ ψ)) (Set.Ioi x₀) := by
  have hn : 2 ≤ n := h.1
  have hk : n - 1 < n := by omega
  have hindex : n - 1 + 1 = n := by omega
  have hF : ContDiff ℝ n (F φ ψ) :=
    contDiff_F φ ψ n h.2.1 h.2.2.1
  have hpos : ∀ x, x₀ < x →
      0 < nthDeriv (n - 1 + 1) (F φ ψ) x := by
    intro x hx
    rw [hindex]
    exact gap3 φ ψ n x₀ x h hx
  exact (strictMonoOn_Ici_nthDeriv_of_pos_succ
    (F φ ψ) n (n - 1) x₀ hF hk hpos).mono Set.Ioi_subset_Ici_self

theorem gap5 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 1) (F φ ψ) x₀ =
      nthDeriv (n - 1) φ x₀ - nthDeriv (n - 1) ψ x₀ := by
  apply nthDeriv_sub_of_contDiff φ ψ n (n - 1) x₀ h.2.1 h.2.2.1
  omega

theorem gap6 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 1) φ x₀ - nthDeriv (n - 1) ψ x₀ = 0 := by
  have hn : 2 ≤ n := h.1
  apply sub_eq_zero.mpr
  exact h.2.2.2.1 (n - 1) (by omega)

theorem gap7 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 1) (F φ ψ) x₀ = 0 := by
  rw [gap5 φ ψ n x₀ h, gap6 φ ψ n x₀ h]

theorem gap8 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ)
    (h : ComparisonData φ ψ n x₀) (hx : x₀ < x) :
    nthDeriv (n - 1) (F φ ψ) x₀ <
      nthDeriv (n - 1) (F φ ψ) x := by
  have hn : 2 ≤ n := h.1
  have hk : n - 1 < n := by omega
  have hindex : n - 1 + 1 = n := by omega
  have hF : ContDiff ℝ n (F φ ψ) :=
    contDiff_F φ ψ n h.2.1 h.2.2.1
  have hpos : ∀ y, x₀ < y →
      0 < nthDeriv (n - 1 + 1) (F φ ψ) y := by
    intro y hy
    rw [hindex]
    exact gap3 φ ψ n x₀ y h hy
  exact strictMonoOn_Ici_nthDeriv_of_pos_succ
    (F φ ψ) n (n - 1) x₀ hF hk hpos Set.self_mem_Ici hx.le hx

theorem gap9 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 1) (F φ ψ) x₀ = 0 := by
  exact gap7 φ ψ n x₀ h

theorem gap10 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ)
    (h : ComparisonData φ ψ n x₀) (hx : x₀ < x) :
    0 < nthDeriv (n - 1) (F φ ψ) x := by
  rw [← gap9 φ ψ n x₀ h]
  exact gap8 φ ψ n x₀ x h hx

theorem gap11 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    StrictMonoOn (nthDeriv (n - 2) (F φ ψ)) (Set.Ioi x₀) := by
  have hn : 2 ≤ n := h.1
  have hk : n - 2 < n := by omega
  have hindex : n - 2 + 1 = n - 1 := by omega
  have hF : ContDiff ℝ n (F φ ψ) :=
    contDiff_F φ ψ n h.2.1 h.2.2.1
  have hpos : ∀ x, x₀ < x →
      0 < nthDeriv (n - 2 + 1) (F φ ψ) x := by
    intro x hx
    rw [hindex]
    exact gap10 φ ψ n x₀ x h hx
  exact (strictMonoOn_Ici_nthDeriv_of_pos_succ
    (F φ ψ) n (n - 2) x₀ hF hk hpos).mono Set.Ioi_subset_Ici_self

theorem gap12 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 2) (F φ ψ) x₀ =
      nthDeriv (n - 2) φ x₀ - nthDeriv (n - 2) ψ x₀ := by
  apply nthDeriv_sub_of_contDiff φ ψ n (n - 2) x₀ h.2.1 h.2.2.1
  omega

theorem gap13 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 2) φ x₀ - nthDeriv (n - 2) ψ x₀ = 0 := by
  have hn : 2 ≤ n := h.1
  apply sub_eq_zero.mpr
  exact h.2.2.2.1 (n - 2) (by omega)

theorem gap14 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 2) (F φ ψ) x₀ = 0 := by
  rw [gap12 φ ψ n x₀ h, gap13 φ ψ n x₀ h]

theorem gap15 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ)
    (h : ComparisonData φ ψ n x₀) (hx : x₀ < x) :
    nthDeriv (n - 2) (F φ ψ) x₀ <
      nthDeriv (n - 2) (F φ ψ) x := by
  have hn : 2 ≤ n := h.1
  have hk : n - 2 < n := by omega
  have hindex : n - 2 + 1 = n - 1 := by omega
  have hF : ContDiff ℝ n (F φ ψ) :=
    contDiff_F φ ψ n h.2.1 h.2.2.1
  have hpos : ∀ y, x₀ < y →
      0 < nthDeriv (n - 2 + 1) (F φ ψ) y := by
    intro y hy
    rw [hindex]
    exact gap10 φ ψ n x₀ y h hy
  exact strictMonoOn_Ici_nthDeriv_of_pos_succ
    (F φ ψ) n (n - 2) x₀ hF hk hpos Set.self_mem_Ici hx.le hx

theorem gap16 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    nthDeriv (n - 2) (F φ ψ) x₀ = 0 := by
  exact gap14 φ ψ n x₀ h

theorem gap17 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ x : ℝ)
    (h : ComparisonData φ ψ n x₀) (hx : x₀ < x) :
    0 < nthDeriv (n - 2) (F φ ψ) x := by
  rw [← gap16 φ ψ n x₀ h]
  exact gap15 φ ψ n x₀ x h hx

theorem gap18 (φ ψ : ℝ → ℝ) (x₀ x : ℝ)
    (hmono : StrictMonoOn (F φ ψ) (Set.Ici x₀))
    (hx : x₀ < x) :
    F φ ψ x₀ < F φ ψ x := by
  exact hmono Set.self_mem_Ici hx.le hx

theorem gap19 (φ ψ : ℝ → ℝ) (x₀ : ℝ)
    (h0 : φ x₀ = ψ x₀) :
    F φ ψ x₀ = 0 := by
  simp [F, h0]

theorem gap20 (φ ψ : ℝ → ℝ) (x₀ x : ℝ)
    (hmono : StrictMonoOn (F φ ψ) (Set.Ici x₀))
    (h0 : φ x₀ = ψ x₀) (hx : x₀ < x) :
    0 < F φ ψ x := by
  rw [← gap19 φ ψ x₀ h0]
  exact gap18 φ ψ x₀ x hmono hx

theorem gap21 (φ ψ : ℝ → ℝ) (x₀ x : ℝ)
    (hmono : StrictMonoOn (F φ ψ) (Set.Ici x₀))
    (h0 : φ x₀ = ψ x₀) (hx : x₀ < x) :
    ψ x < φ x := by
  have := gap20 φ ψ x₀ x hmono h0 hx
  simpa [F, sub_pos] using this

theorem gap22 (φ ψ : ℝ → ℝ) (n : ℕ) (x₀ : ℝ)
    (h : ComparisonData φ ψ n x₀) :
    ∀ x, x₀ < x → ψ x < φ x := by
  have hF : ContDiff ℝ n (F φ ψ) :=
    contDiff_F φ ψ n h.2.1 h.2.2.1
  have hzero : ∀ k < n, nthDeriv k (F φ ψ) x₀ = 0 := by
    intro k hk
    rw [nthDeriv_sub_of_contDiff φ ψ n k x₀ h.2.1 h.2.2.1 hk.le]
    exact sub_eq_zero.mpr (h.2.2.2.1 k hk)
  have hpos : ∀ x, x₀ < x → 0 < nthDeriv n (F φ ψ) x := by
    intro x hx
    exact gap3 φ ψ n x₀ x h hx
  intro x hx
  have hFx := positive_of_positive_nthDeriv (F φ ψ) n x₀ hF hzero hpos x hx
  simpa [F, sub_pos] using hFx

end

end ProofGap.Exercise1288
