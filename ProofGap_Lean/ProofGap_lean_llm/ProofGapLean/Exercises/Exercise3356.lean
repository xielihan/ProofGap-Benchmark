import ProofGapLean.Prelude.Finite
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

namespace ProofGap.Exercise3356

noncomputable section

def partialYOrder (n : ℕ) (z : ℝ → ℝ → ℝ) (x y : ℝ) : ℝ :=
  (deriv^[n]) (fun s => z x s) y

def VerticallyCn (n : ℕ) (z : ℝ → ℝ → ℝ) : Prop :=
  ∀ x, ContDiff ℝ n (fun y => z x y)

def polynomialFamily (n : ℕ) (φ : Fin n → ℝ → ℝ) (x y : ℝ) : ℝ :=
  ∑ i : Fin n, y ^ (i : ℕ) * φ i x

private lemma partialYOrder_eq_iterated3356
    (n : ℕ) (z : ℝ → ℝ → ℝ) (x y : ℝ) :
    partialYOrder n z x y =
      iteratedDeriv n (fun s => z x s) y := by
  rw [partialYOrder, iteratedDeriv_eq_iterate]

private lemma second_deriv_zero_iff_affine3356 (g : ℝ → ℝ)
    (hg : Differentiable ℝ g) (hdg : Differentiable ℝ (deriv g)) :
    (∀ y, deriv (deriv g) y = 0) ↔
      ∃ c d : ℝ, ∀ y, g y = y * c + d := by
  constructor
  · intro hzero
    have hconst : ∀ y, deriv g y = deriv g 0 :=
      fun y => is_const_of_deriv_eq_zero hdg hzero y 0
    refine ⟨deriv g 0, g 0, ?_⟩
    intro y
    let q : ℝ → ℝ := fun s => g s - s * deriv g 0
    have hqdiff : Differentiable ℝ q := by
      dsimp [q]
      fun_prop
    have hqzero : ∀ s, deriv q s = 0 := by
      intro s
      have hs := hg s |>.hasDerivAt.sub
        ((hasDerivAt_id s).mul_const (deriv g 0))
      dsimp [q]
      convert hs.deriv using 1
      rw [hconst s]
      ring
    have hc := is_const_of_deriv_eq_zero hqdiff hqzero y 0
    dsimp [q] at hc
    linarith
  · rintro ⟨c, d, h⟩
    have heq : g = fun y => y * c + d := funext h
    have hderiv : deriv g = fun _ => c := by
      rw [heq]
      funext y
      convert (((hasDerivAt_id y).mul_const c).add_const d).deriv using 1 <;>
        ring
    rw [hderiv]
    simp

theorem gap1 (n : ℕ) (hn : 1 ≤ n) (z : ℝ → ℝ → ℝ)
    (hz : VerticallyCn n z) :
    (∀ x y, partialYOrder n z x y = 0) ↔
      ∃ φ : ℝ → ℝ, ∀ x y, partialYOrder (n - 1) z x y = φ x := by
  let k := n - 1
  have hkn : k + 1 = n := by
    dsimp [k]
    omega
  constructor
  · intro hzero
    refine ⟨fun x => partialYOrder k z x 0, ?_⟩
    intro x y
    let g : ℝ → ℝ := fun s => z x s
    have hg : ContDiff ℝ n g := hz x
    have hdiff : Differentiable ℝ (iteratedDeriv k g) := by
      exact (contDiff_nat_iff_iteratedDeriv.mp hg).2 k (by omega)
    have hsucc :
        iteratedDeriv n g = deriv (iteratedDeriv k g) := by
      rw [← hkn]
      exact iteratedDeriv_succ
    have hderivzero : ∀ s, deriv (iteratedDeriv k g) s = 0 := by
      intro s
      rw [← congrFun hsucc s]
      simpa [g, partialYOrder_eq_iterated3356] using hzero x s
    have hc :=
      is_const_of_deriv_eq_zero hdiff hderivzero y 0
    simpa [g, partialYOrder_eq_iterated3356] using hc
  · rintro ⟨φ, hφ⟩ x y
    let g : ℝ → ℝ := fun s => z x s
    have hsucc :
        iteratedDeriv n g = deriv (iteratedDeriv k g) := by
      rw [← hkn]
      exact iteratedDeriv_succ
    have heq : iteratedDeriv k g = fun _ => φ x := by
      funext s
      simpa [g, partialYOrder_eq_iterated3356] using hφ x s
    rw [partialYOrder_eq_iterated3356, show (fun s => z x s) = g by rfl,
      hsucc, heq]
    simp

theorem gap2 (n : ℕ) (hn : 2 ≤ n) (z : ℝ → ℝ → ℝ)
    (hz : VerticallyCn n z) :
    (∀ x y, partialYOrder n z x y = 0) ↔
      ∃ φ₁ φ₀ : ℝ → ℝ, ∀ x y,
        partialYOrder (n - 2) z x y = y * φ₁ x + φ₀ x := by
  let k := n - 2
  have hkn : k + 2 = n := by
    dsimp [k]
    omega
  have hdata : ∀ x : ℝ,
      let g : ℝ → ℝ := fun s => z x s
      let G : ℝ → ℝ := iteratedDeriv k g
      Differentiable ℝ G ∧
        Differentiable ℝ (deriv G) ∧
        iteratedDeriv n g = deriv (deriv G) := by
    intro x
    dsimp only
    let g : ℝ → ℝ := fun s => z x s
    have hg : ContDiff ℝ n g := hz x
    have hG : Differentiable ℝ (iteratedDeriv k g) :=
      (contDiff_nat_iff_iteratedDeriv.mp hg).2 k (by omega)
    have hDGbase : Differentiable ℝ (iteratedDeriv (k + 1) g) :=
      (contDiff_nat_iff_iteratedDeriv.mp hg).2 (k + 1) (by omega)
    have hDG : Differentiable ℝ (deriv (iteratedDeriv k g)) := by
      rw [← iteratedDeriv_succ]
      exact hDGbase
    have htwo :
        iteratedDeriv n g =
          deriv (deriv (iteratedDeriv k g)) := by
      calc
        iteratedDeriv n g = iteratedDeriv (k + 2) g := by rw [hkn]
        _ = deriv (iteratedDeriv (k + 1) g) := by
          simpa [Nat.add_assoc] using
            (iteratedDeriv_succ (n := k + 1) (f := g))
        _ = deriv (deriv (iteratedDeriv k g)) := by
          rw [iteratedDeriv_succ]
    exact ⟨hG, hDG, htwo⟩
  constructor
  · intro hzero
    have hex : ∀ x : ℝ, ∃ c d : ℝ, ∀ y,
        partialYOrder k z x y = y * c + d := by
      intro x
      let g : ℝ → ℝ := fun s => z x s
      let G : ℝ → ℝ := iteratedDeriv k g
      rcases hdata x with ⟨hG, hDG, htwo⟩
      have hsecond : ∀ y, deriv (deriv G) y = 0 := by
        intro y
        rw [← congrFun htwo y]
        simpa [g, partialYOrder_eq_iterated3356] using hzero x y
      rcases (second_deriv_zero_iff_affine3356 G hG hDG).mp hsecond with
        ⟨c, d, hcd⟩
      exact ⟨c, d, fun y => by
        simpa [G, g, partialYOrder_eq_iterated3356] using hcd y⟩
    choose c d hcd using hex
    exact ⟨c, d, hcd⟩
  · rintro ⟨c, d, hcd⟩ x y
    let g : ℝ → ℝ := fun s => z x s
    let G : ℝ → ℝ := iteratedDeriv k g
    rcases hdata x with ⟨hG, hDG, htwo⟩
    have haff : ∀ s, G s = s * c x + d x := by
      intro s
      simpa [G, g, partialYOrder_eq_iterated3356] using hcd x s
    have hsecond : ∀ s, deriv (deriv G) s = 0 :=
      (second_deriv_zero_iff_affine3356 G hG hDG).mpr
        ⟨c x, d x, haff⟩
    rw [partialYOrder_eq_iterated3356,
      show (fun s => z x s) = g by rfl, htwo]
    exact hsecond y

private theorem exists_fin_poly_of_iteratedDeriv_zero3356
    (n : ℕ) (hn : 1 ≤ n) (g : ℝ → ℝ) (hg : ContDiff ℝ n g)
    (hzero : ∀ y, iteratedDeriv n g y = 0) :
    ∃ c : Fin n → ℝ, ∀ y, g y = ∑ i : Fin n, y ^ (i : ℕ) * c i := by
  induction n generalizing g with
  | zero => omega
  | succ n ih =>
      by_cases hn0 : n = 0
      · subst n
        refine ⟨fun _ => g 0, ?_⟩
        intro y
        rw [Fin.sum_univ_one]
        simp only [Fin.val_zero, pow_zero, one_mul]
        have hgdiff : Differentiable ℝ g := hg.differentiable (by norm_num)
        have hderiv : ∀ s, deriv g s = 0 := by
          intro s
          simpa [iteratedDeriv_one] using hzero s
        exact is_const_of_deriv_eq_zero hgdiff hderiv y 0
      · have hnpos : 1 ≤ n := by omega
        have hdg : ContDiff ℝ n (deriv g) := hg.deriv'
        have hzeroD : ∀ y, iteratedDeriv n (deriv g) y = 0 := by
          intro y
          rw [← congrFun (iteratedDeriv_succ' (n := n) (f := g)) y]
          exact hzero y
        rcases ih hnpos (deriv g) hdg hzeroD with ⟨c, hc⟩
        let C : Fin (n + 1) → ℝ :=
          Fin.cases (g 0) (fun i : Fin n => c i / ((i : ℕ) + 1))
        let P : ℝ → ℝ :=
          fun y => ∑ j : Fin (n + 1), y ^ (j : ℕ) * C j
        have hPderiv (y : ℝ) :
            deriv P y =
              ∑ j : Fin (n + 1),
                (j : ℕ) * y ^ ((j : ℕ) - 1) * C j := by
          have hs :
              HasDerivAt
                (∑ j : Fin (n + 1), fun s : ℝ => s ^ (j : ℕ) * C j)
                (∑ j : Fin (n + 1),
                  (j : ℕ) * y ^ ((j : ℕ) - 1) * C j) y := by
            apply HasDerivAt.sum
            intro j hj
            simpa [mul_assoc] using
              ((hasDerivAt_id y).pow (j : ℕ)).mul_const (C j)
          have hfun :
              P = ∑ j : Fin (n + 1),
                fun s : ℝ => s ^ (j : ℕ) * C j := by
            funext s
            simp [P]
          rw [hfun]
          exact hs.deriv
        have hPderiv_eq (y : ℝ) : deriv P y = deriv g y := by
          rw [hPderiv, Fin.sum_univ_succ]
          simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_add,
            Fin.val_succ, Nat.succ_sub_one]
          calc
            (∑ i : Fin n,
                ((i : ℕ) + 1 : ℕ) * y ^ (i : ℕ) * C i.succ) =
                ∑ i : Fin n, y ^ (i : ℕ) * c i := by
              apply Finset.sum_congr rfl
              intro i hi
              simp only [C, Fin.cases_succ]
              have hi1 : ((i : ℝ) + 1) ≠ 0 := by positivity
              push_cast
              field_simp
            _ = deriv g y := (hc y).symm
        have hPdiff : Differentiable ℝ P := by
          intro y
          have hs :
              HasDerivAt
                (∑ j : Fin (n + 1), fun s : ℝ => s ^ (j : ℕ) * C j)
                (∑ j : Fin (n + 1),
                  (j : ℕ) * y ^ ((j : ℕ) - 1) * C j) y := by
            apply HasDerivAt.sum
            intro j hj
            simpa [mul_assoc] using
              ((hasDerivAt_id y).pow (j : ℕ)).mul_const (C j)
          have hfun :
              P = ∑ j : Fin (n + 1),
                fun s : ℝ => s ^ (j : ℕ) * C j := by
            funext s
            simp [P]
          rw [hfun]
          exact hs.differentiableAt
        have hgdiff : Differentiable ℝ g := hg.differentiable (by simp)
        have hqdiff : Differentiable ℝ (fun y => g y - P y) :=
          hgdiff.sub hPdiff
        have hqzero : ∀ y, deriv (fun s => g s - P s) y = 0 := by
          intro y
          convert (hgdiff y |>.hasDerivAt.sub
            (hPdiff y).hasDerivAt).deriv using 1
          rw [hPderiv_eq]
          ring
        have hPzero : P 0 = g 0 := by
          simp [P, C, Fin.sum_univ_succ]
        refine ⟨C, ?_⟩
        intro y
        have hcst :=
          is_const_of_deriv_eq_zero hqdiff hqzero y 0
        rw [hPzero] at hcst
        linarith

private lemma partialYOrder_polynomialFamily_zero3356
    (n : ℕ) (φ : Fin n → ℝ → ℝ) (x y : ℝ) :
    partialYOrder n (polynomialFamily n φ) x y = 0 := by
  rw [partialYOrder, ← iteratedDeriv_eq_iterate]
  change iteratedDeriv n
    (fun s : ℝ => ∑ i : Fin n, s ^ (i : ℕ) * φ i x) y = 0
  rw [iteratedDeriv_fun_sum]
  · apply Finset.sum_eq_zero
    intro i hi
    rw [iteratedDeriv_mul_const_field, iteratedDeriv_pow]
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr i.isLt]
    simp
  · intro i hi
    fun_prop

theorem gap3 (n : ℕ) (hn : 1 ≤ n) (z : ℝ → ℝ → ℝ)
    (hz : VerticallyCn n z) :
    (∀ x y, partialYOrder n z x y = 0) ↔
      ∃ φ : Fin n → ℝ → ℝ, ∀ x y, z x y = polynomialFamily n φ x y := by
  constructor
  · intro hzero
    have hex : ∀ x : ℝ, ∃ c : Fin n → ℝ, ∀ y,
        z x y = ∑ i : Fin n, y ^ (i : ℕ) * c i := by
      intro x
      let g : ℝ → ℝ := fun y => z x y
      have hg : ContDiff ℝ n g := hz x
      have hnzero : ∀ y, iteratedDeriv n g y = 0 := by
        intro y
        simpa [g, partialYOrder_eq_iterated3356] using hzero x y
      simpa [g] using
        exists_fin_poly_of_iteratedDeriv_zero3356 n hn g hg hnzero
    choose c hc using hex
    refine ⟨fun i x => c x i, ?_⟩
    intro x y
    simpa [polynomialFamily] using hc x y
  · rintro ⟨φ, hφ⟩ x y
    have heq : z = polynomialFamily n φ := by
      funext s t
      exact hφ s t
    rw [heq]
    exact partialYOrder_polynomialFamily_zero3356 n φ x y

theorem gap4 (n : ℕ) (φ : Fin n → ℝ → ℝ) :
    ∀ x y, partialYOrder n (polynomialFamily n φ) x y = 0 := by
  intro x y
  exact partialYOrder_polynomialFamily_zero3356 n φ x y

end

end ProofGap.Exercise3356
