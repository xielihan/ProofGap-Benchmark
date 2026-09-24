import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace ProofGap.Exercise456

noncomputable section

def root (k : ℕ) (x : ℝ) : ℝ := Real.rpow x (1 / (k : ℝ))
def numerator (n : ℕ) (x : ℝ) : ℝ :=
  (Finset.Icc 2 n).prod (fun k => 1 - root k x)
def f (n : ℕ) (x : ℝ) : ℝ := numerator n x / (1 - x) ^ (n - 1)
def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 456, gap 1; replace products and exponent ellipses by `Finset` products. -/
private theorem exercise456_main (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => root n x) (nhds 1) (nhds 1) ∧
      HasLimitAt (f n) 1 (1 / (n.factorial : ℝ)) ∧
      ((Finset.Icc 2 n).prod (fun k => (n.factorial : ℝ) / k)) /
          (n.factorial : ℝ) ^ (n - 1) =
        1 / (n.factorial : ℝ) := by
  have hone_rpow (a : ℝ) : Real.rpow (1 : ℝ) a = 1 := by
    simpa only using (Real.one_rpow a)
  have hroot_deriv (k : ℕ) :
      HasDerivAt (root k) (1 / (k : ℝ)) 1 := by
    have h :
        HasDerivAt
          (fun x : ℝ => Real.rpow x (1 / (k : ℝ)))
          ((1 / (k : ℝ)) *
            Real.rpow (1 : ℝ) (1 / (k : ℝ) - 1)) 1 :=
      Real.hasDerivAt_rpow_const (by norm_num)
    change
      HasDerivAt
        (fun x : ℝ => Real.rpow x (1 / (k : ℝ)))
        (1 / (k : ℝ)) 1
    rw [hone_rpow] at h
    simpa only [mul_one] using h
  have hroot_tendsto (k : ℕ) :
      Filter.Tendsto (fun x : ℝ => root k x) (nhds 1) (nhds 1) := by
    have hone : root k 1 = 1 := by
      unfold root
      exact hone_rpow _
    simpa only [ContinuousAt, hone] using
      (hroot_deriv k).continuousAt
  have hratio (k : ℕ) :
      Filter.Tendsto
        (fun x : ℝ => (1 - root k x) / (1 - x))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds (1 / (k : ℝ))) := by
    have hs :
        Filter.Tendsto (slope (root k) 1)
          (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
          (nhds (1 / (k : ℝ))) :=
      (hroot_deriv k).tendsto_slope
    refine hs.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx1 : x ≠ 1 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hxm : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
    have homx : 1 - x ≠ 0 := sub_ne_zero.mpr hx1.symm
    simp only [slope, root, smul_eq_mul, vsub_eq_sub]
    rw [hone_rpow]
    field_simp [hxm, homx] <;> ring
  have hprod_general : ∀ s : Finset ℕ,
      Filter.Tendsto
        (fun x : ℝ => s.prod (fun k => (1 - root k x) / (1 - x)))
        (nhdsWithin 1 ({1} : Set ℝ)ᶜ)
        (nhds (s.prod (fun k => 1 / (k : ℝ)))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
        simpa only [Finset.prod_insert ha] using (hratio a).mul ih
  have hnatprod : ∀ m : ℕ,
      (Finset.Icc 2 m).prod (fun k => (k : ℝ)) =
        (m.factorial : ℝ) := by
    intro m
    induction m with
    | zero => norm_num
    | succ m ih =>
        by_cases hm : m = 0
        · subst m
          norm_num
        · have hset :
              Finset.Icc 2 (Nat.succ m) =
                insert (Nat.succ m) (Finset.Icc 2 m) := by
            ext k
            simp only [Finset.mem_Icc, Finset.mem_insert]
            omega
          have hnot : Nat.succ m ∉ Finset.Icc 2 m := by
            simp
          rw [hset, Finset.prod_insert hnot, ih, Nat.factorial_succ]
          norm_num
  have hcard : (Finset.Icc 2 n).card = n - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hrecip :
      (Finset.Icc 2 n).prod (fun k => 1 / (k : ℝ)) =
        1 / (n.factorial : ℝ) := by
    calc
      (Finset.Icc 2 n).prod (fun k => 1 / (k : ℝ)) =
          (Finset.Icc 2 n).prod (fun _ => (1 : ℝ)) /
            (Finset.Icc 2 n).prod (fun k => (k : ℝ)) := by
        simpa using
          (Finset.prod_div_distrib
            (s := Finset.Icc 2 n)
            (fun _ : ℕ => (1 : ℝ))
            (fun k : ℕ => (k : ℝ)))
      _ = 1 / (n.factorial : ℝ) := by
        rw [hnatprod n]
        simp
  have hfactor :
      f n =
        fun x : ℝ =>
          (Finset.Icc 2 n).prod
            (fun k => (1 - root k x) / (1 - x)) := by
    funext x
    unfold f numerator
    rw [Finset.prod_div_distrib, Finset.prod_const, hcard]
  have hlim : HasLimitAt (f n) 1 (1 / (n.factorial : ℝ)) := by
    unfold HasLimitAt
    rw [hfactor]
    simpa only [hrecip] using hprod_general (Finset.Icc 2 n)
  have hF : (n.factorial : ℝ) ≠ 0 := by
    positivity
  have halgebra :
      ((Finset.Icc 2 n).prod (fun k => (n.factorial : ℝ) / k)) /
          (n.factorial : ℝ) ^ (n - 1) =
        1 / (n.factorial : ℝ) := by
    rw [Finset.prod_div_distrib, Finset.prod_const, hcard, hnatprod n]
    field_simp [hF]
    <;> ring
  exact ⟨hroot_tendsto n, hlim, halgebra⟩

theorem gap1 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (f n) 1 (1 / (n.factorial : ℝ)) := by
  exact (exercise456_main n).2.1

/-- Exercise 456, gap 2; encode the geometric products by their closed limit. -/
theorem gap2 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (f n) 1 (1 / (n.factorial : ℝ)) := by
  exact gap1 n hn

/-- Exercise 456, gap 3. -/
theorem gap3 (n : ℕ) :
    Filter.Tendsto (fun x : ℝ => root n x) (nhds 1) (nhds 1) := by
  exact (exercise456_main n).1

/-- Exercise 456, gap 4. -/
theorem gap4 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (f n) 1
      (((Finset.Icc 2 n).prod (fun k => (n.factorial : ℝ) / k)) /
        (n.factorial : ℝ) ^ (n - 1)) := by
  have hvalue := (exercise456_main n).2.2
  rw [hvalue]
  exact (exercise456_main n).2.1

/-- Exercise 456, gap 5. -/
theorem gap5 (n : ℕ) (hn : 0 < n) :
    ((Finset.Icc 2 n).prod (fun k => (n.factorial : ℝ) / k)) /
        (n.factorial : ℝ) ^ (n - 1) =
      1 / (n.factorial : ℝ) := by
  exact (exercise456_main n).2.2

/-- Exercise 456, gap 6. -/
theorem gap6 (n : ℕ) (hn : 0 < n) :
    HasLimitAt (f n) 1 (1 / (n.factorial : ℝ)) := by
  exact gap1 n hn

end

end ProofGap.Exercise456
