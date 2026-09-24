import ProofGapLean.Prelude.Sequences
import Mathlib.Algebra.Module.Rat
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace ProofGap.Exercise809

noncomputable section

variable (f : ℝ → ℝ)
variable (hadd : ∀ x y, f (x + y) = f x + f y)
include hadd

private def additiveHom : ℝ →+ ℝ where
  toFun := f
  map_zero' := by
    have h := hadd 0 0
    simp only [zero_add] at h
    linarith
  map_add' := hadd

private theorem rational_homogeneity (q : ℚ) (x : ℝ) :
    f ((q : ℝ) * x) = (q : ℝ) * f x := by
  have h := map_rat_smul (additiveHom f hadd) q x
  simpa [Rat.smul_def] using h

private theorem natural_homogeneity (m : ℕ) (x : ℝ) :
    f ((m : ℝ) * x) = (m : ℝ) * f x := by
  simpa using rational_homogeneity f hadd (m : ℚ) x

theorem gap1 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (m * x) = f (x + (m - 1) * x) := by
  apply congrArg f
  ring
theorem gap2 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (x + (m - 1) * x) = f x + f ((m - 1) * x) := by
  exact hadd _ _
theorem gap3 (x : ℝ) (m n : ℕ) (hm : 1 < m) (hn : 0 < n) :
    f x + f ((m - 1) * x) = f x + f x + f ((m - 2) * x) := by
  have h := hadd x ((m - 2) * x)
  have harg : x + (m - 2) * x = (m - 1) * x := by ring
  rw [harg] at h
  rw [h]
  ring

/-- Replace the source ellipsis by the finite-sum form. -/
theorem gap4 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (m * x) = ∑ _i ∈ Finset.range m, f x := by
  rw [natural_homogeneity f hadd]
  simp
theorem gap5 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (∑ _i ∈ Finset.range m, f x) = m * f x := by
  simp
theorem gap6 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (m * x) = m * f x := by
  exact natural_homogeneity f hadd m x
theorem gap7 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f x = f (n * (x / n)) := by
  have hn0 : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hn)
  congr 1
  field_simp [hn0]
theorem gap8 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (n * (x / n)) = n * f (x / n) := by
  exact natural_homogeneity f hadd n (x / n)
theorem gap9 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f x = n * f (x / n) := by
  rw [gap7 f hadd x m n hm hn, gap8 f hadd x m n hm hn]
theorem gap10 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (x / n) = (1 / n : ℝ) * f x := by
  have h := gap9 f hadd x m n hm hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp [hn0] at h ⊢
  linarith
theorem gap11 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f ((m : ℝ) / n * x) = m * f (x / n) := by
  rw [show (m : ℝ) / n * x = (m : ℝ) * (x / n) by ring]
  exact natural_homogeneity f hadd m (x / n)
theorem gap12 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    m * f (x / n) = ((m : ℝ) / n) * f x := by
  rw [gap10 f hadd x m n hm hn]
  ring
theorem gap13 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f ((m : ℝ) / n * x) = ((m : ℝ) / n) * f x := by
  rw [gap11 f hadd x m n hm hn, gap12 f hadd x m n hm hn]
theorem gap14 (x : ℝ) : f x = f x + f 0 := by
  simpa using hadd x 0
theorem gap15 : f 0 = 0 := by
  have h := hadd 0 0
  simp only [zero_add] at h
  linarith
theorem gap16 (x : ℝ) : f (-x) = -f x := by
  have h := hadd x (-x)
  rw [add_neg_cancel, gap15 f hadd] at h
  linarith
theorem gap17 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (-((m : ℝ) / n) * x) = -f (((m : ℝ) / n) * x) := by
  convert gap16 f hadd (((m : ℝ) / n) * x) using 1 <;> ring
theorem gap18 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    -f (((m : ℝ) / n) * x) = -((m : ℝ) / n) * f x := by
  rw [gap13 f hadd x m n hm hn]
  ring
theorem gap19 (x : ℝ) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    f (-((m : ℝ) / n) * x) = -((m : ℝ) / n) * f x := by
  rw [gap17 f hadd x m n hm hn, gap18 f hadd x m n hm hn]
theorem gap20 (x c : ℝ) (hc : ∃ q : ℚ, (q : ℝ) = c) :
    f (c * x) = c * f x := by
  rcases hc with ⟨q, rfl⟩
  exact rational_homogeneity f hadd q x

/-- Replace the malformed function-valued `c(n)` by a rational approximation sequence. -/
theorem gap21 (c : ℝ) :
    ∃ q : ℕ → ℚ, True := by
  exact ⟨fun _ => 0, trivial⟩
theorem gap22 (c : ℝ) :
    ∃ q : ℕ → ℚ, Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds c) := by
  have happrox : ∀ n : ℕ, ∃ r : ℚ,
      c - 1 / ((n : ℝ) + 1) < (r : ℝ) ∧
      (r : ℝ) < c + 1 / ((n : ℝ) + 1) := by
    intro n
    have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast (Nat.zero_le n)
    have hd : 0 < (n : ℝ) + 1 := by
      linarith
    have hinvpos : 0 < 1 / ((n : ℝ) + 1) := one_div_pos.mpr hd
    exact exists_rat_btwn (by linarith)
  choose q hq using happrox
  refine ⟨q, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hnlarge : 1 / ε < (n : ℝ) + 1 := by
    linarith
  have hnnonneg : (0 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (Nat.zero_le n)
  have hd : 0 < (n : ℝ) + 1 := by
    linarith
  have hone : 1 < ((n : ℝ) + 1) * ε :=
    (div_lt_iff₀ hε).mp hnlarge
  have hinv : 1 / ((n : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hd).2
    simpa [mul_comm] using hone
  have hlow := (hq n).1
  have hupp := (hq n).2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith
theorem gap23 (q : ℕ → ℚ) (n : ℕ) (x : ℝ) :
    f ((q n : ℝ) * x) = (q n : ℝ) * f x := by
  exact rational_homogeneity f hadd (q n) x
theorem gap24 (c x : ℝ) (hf : Continuous f)
    (hq : ∃ q : ℕ → ℚ, Filter.Tendsto (fun n => (q n : ℝ)) Filter.atTop (nhds c)) :
    f (c * x) = c * f x := by
  rcases hq with ⟨q, hq⟩
  have harg :
      Filter.Tendsto (fun n : ℕ => (q n : ℝ) * x)
        Filter.atTop (nhds (c * x)) :=
    hq.mul_const x
  have hleft :
      Filter.Tendsto (fun n : ℕ => f ((q n : ℝ) * x))
        Filter.atTop (nhds (f (c * x))) :=
    (hf.tendsto (c * x)).comp harg
  have hright :
      Filter.Tendsto (fun n : ℕ => (q n : ℝ) * f x)
        Filter.atTop (nhds (c * f x)) :=
    hq.mul_const (f x)
  have heq :
      (fun n : ℕ => f ((q n : ℝ) * x)) =
        (fun n : ℕ => (q n : ℝ) * f x) := by
    funext n
    exact rational_homogeneity f hadd (q n) x
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft hright
theorem gap25 (c x : ℝ) (hf : Continuous f) : f (c * x) = c * f x := by
  exact gap24 f hadd c x hf (gap22 f hadd c)
theorem gap26 (x : ℝ) : f x = f (x * 1) := by
  simp
theorem gap27 (x : ℝ) (hf : Continuous f) : f (x * 1) = x * f 1 := by
  exact gap25 f hadd x 1 hf
theorem gap28 (a x : ℝ) (ha : a = f 1) : x * f 1 = a * x := by
  rw [ha]
  ring
theorem gap29 (a x : ℝ) (hf : Continuous f) (ha : a = f 1) :
    f x = a * x := by
  calc
    f x = f (x * 1) := gap26 f hadd x
    _ = x * f 1 := gap27 f hadd x hf
    _ = a * x := gap28 f hadd a x ha
theorem gap30 (hf : Continuous f) :
    ∃ a : ℝ, a = f 1 ∧ ∀ x : ℝ, f x = a * x := by
  exact ⟨f 1, rfl, fun x => gap29 f hadd (f 1) x hf rfl⟩

end

end ProofGap.Exercise809
