import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1232

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def g (n : ℕ) (x : ℝ) : ℝ := x ^ (n - 1) * Real.exp (1 / x)
def closedForm (n : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ n / x ^ (n + 1) * Real.exp (1 / x)

theorem gap1 (x : ℝ) (hx : x ≠ 0) :
    deriv (fun t : ℝ => Real.exp (1 / t)) x =
      -1 / x ^ 2 * Real.exp (1 / x) := by
  have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> ring
  simpa only [Function.comp_apply, mul_comm] using
    ((Real.hasDerivAt_exp (1 / x)).comp x hi).deriv

theorem gap2 (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : x ≠ 0)
    (hind : iterDeriv k (g k) x = closedForm k x) :
    iterDeriv (k + 1) (g (k + 1)) x =
      deriv (fun t => iterDeriv k (fun s : ℝ => s * g k s) t) x := by
  have hg : g (k + 1) = fun s : ℝ => s * g k s := by
    funext s
    have he₁ : k + 1 - 1 = k := by omega
    have hp : s ^ k = s * s ^ (k - 1) := by
      calc
        s ^ k = s ^ ((k - 1) + 1) := by congr 1 <;> omega
        _ = s * s ^ (k - 1) := by rw [pow_succ]; ring
    unfold g
    rw [he₁, hp]
    ring
  rw [hg]
  simp [iterDeriv, Function.iterate_succ_apply']

private theorem hasDerivAt_closedForm (k : ℕ) (x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (closedForm k)
      (((-1 : ℝ) ^ (k + 1) * (k + 1 : ℕ) / x ^ (k + 2) *
          Real.exp (1 / x)) +
        (-1 : ℝ) ^ (k + 1) / x ^ (k + 3) *
          Real.exp (1 / x)) x := by
  have hp := (hasDerivAt_id x).pow (k + 1)
  have hq := (hasDerivAt_const x ((-1 : ℝ) ^ k)).div hp
    (pow_ne_zero _ hx)
  have hi : HasDerivAt (fun t : ℝ => 1 / t) (-1 / x ^ 2) x := by
    convert (hasDerivAt_const x (1 : ℝ)).div (hasDerivAt_id x) hx using 1 <;>
      simp [id] <;> ring
  have he := (Real.hasDerivAt_exp (1 / x)).comp x hi
  unfold closedForm
  convert hq.mul he using 1 <;>
    simp [Function.comp_apply] <;>
    field_simp [hx] <;>
    ring

private theorem sum_linear (n : ℕ) (hn : 1 ≤ n)
    (x : ℝ) (G : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℝ) *
        (if i = 0 then x else if i = 1 then 1 else 0) *
        G (n - i)) =
      x * G n + (n : ℝ) * G (n - 1) := by
  have hsummand (i : ℕ) :
      (Nat.choose n i : ℝ) *
          (if i = 0 then x else if i = 1 then 1 else 0) *
          G (n - i) =
        (if i = 0 then x * G n else 0) +
        (if i = 1 then (n : ℝ) * G (n - 1) else 0) := by
    by_cases h0 : i = 0
    · subst i
      simp
    by_cases h1 : i = 1
    · subst i
      simp [h0, Nat.choose_one_right]
    simp [h0, h1]
  simp_rw [hsummand]
  simp only [Finset.sum_add_distrib]
  simp [Finset.mem_range]
  omega

private theorem iterDeriv_id_mul (n : ℕ) (hn : 1 ≤ n)
    (h : ℝ → ℝ) (x : ℝ) (hh : ContDiffAt ℝ n h x) :
    iterDeriv n (fun t => t * h t) x =
      x * iterDeriv n h x + (n : ℝ) * iterDeriv (n - 1) h x := by
  simp only [iterDeriv, ← iteratedDeriv_eq_iterate]
  rw [iteratedDeriv_fun_mul (n := n) (by fun_prop) hh]
  rw [show
      (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          iteratedDeriv i (fun t : ℝ => t) x *
          iteratedDeriv (n - i) h x) =
        ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) *
            (if i = 0 then x else if i = 1 then 1 else 0) *
            iteratedDeriv (n - i) h x by
        apply Finset.sum_congr rfl
        intro i hi
        rw [iteratedDeriv_fun_id]]
  exact sum_linear n hn x (fun j => iteratedDeriv j h x)

private theorem master (n : ℕ) (hn : 1 ≤ n) (x : ℝ) (hx : x ≠ 0) :
    iterDeriv n (g n) x = closedForm n x := by
  induction n, hn using Nat.le_induction generalizing x with
  | base =>
      rw [show g 1 = fun t : ℝ => Real.exp (1 / t) by
        funext t
        simp [g]]
      change deriv (fun t : ℝ => Real.exp (1 / t)) x = closedForm 1 x
      rw [gap1 x hx]
      simp [closedForm]
  | succ k hk ih =>
      have hgfun : g (k + 1) = fun t : ℝ => t * g k t := by
        funext t
        have hp : t ^ k = t * t ^ (k - 1) := by
          calc
            t ^ k = t ^ ((k - 1) + 1) := by congr 1 <;> omega
            _ = t * t ^ (k - 1) := by rw [pow_succ]; ring
        unfold g
        rw [show k + 1 - 1 = k by omega, hp]
        ring
      have hgcd : ContDiffAt ℝ (k + 1) (g k) x := by
        unfold g
        apply ContDiffAt.mul (by fun_prop)
        exact Real.contDiff_exp.contDiffAt.comp x
          (contDiffAt_const.div contDiffAt_id hx)
      rw [hgfun, iterDeriv_id_mul (k + 1) (by omega) (g k) x hgcd]
      have hev : iterDeriv k (g k) =ᶠ[nhds x] closedForm k := by
        filter_upwards [eventually_ne_nhds hx] with t ht
        exact ih t ht
      have hder :
          iterDeriv (k + 1) (g k) x = deriv (closedForm k) x := by
        rw [show iterDeriv (k + 1) (g k) x =
            deriv (iterDeriv k (g k)) x by
          simp [iterDeriv, Function.iterate_succ_apply']]
        exact Filter.EventuallyEq.deriv_eq hev
      rw [hder, show k + 1 - 1 = k by omega, ih x hx,
        (hasDerivAt_closedForm k x hx).deriv]
      unfold closedForm
      rw [show (-1 : ℝ) ^ (k + 1) = -((-1 : ℝ) ^ k) by
        rw [pow_succ]
        ring]
      field_simp [hx]
      ring

private lemma contDiffAt_iterDeriv (f : ℝ → ℝ) (x : ℝ) (n k : ℕ)
    (hf : ContDiffAt ℝ (n + k) f x) :
    ContDiffAt ℝ n (iterDeriv k f) x := by
  induction k generalizing f with
  | zero =>
      simpa [iterDeriv] using hf
  | succ k ih =>
      have hf' : ContDiffAt ℝ ((n + k) + 1) f x := by
        convert hf using 1 <;> omega
      have hderiv : ContDiffAt ℝ (n + k) (deriv f) x :=
        hf'.derivWithin (m := n + k) (le_refl _)
      simpa [iterDeriv, Function.iterate_succ_apply] using
        ih (f := deriv f) hderiv

theorem gap3 (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : x ≠ 0)
    (hind : iterDeriv k (g k) x = closedForm k x) :
    iterDeriv (k + 1) (g (k + 1)) x =
      deriv (fun t => t * iterDeriv k (g k) t +
        (k : ℝ) * iterDeriv (k - 1) (g k) t) x := by
  rw [gap2 k x hk hx hind]
  have hev : iterDeriv k (fun s : ℝ => s * g k s) =ᶠ[nhds x]
      fun t => t * iterDeriv k (g k) t +
        (k : ℝ) * iterDeriv (k - 1) (g k) t := by
    filter_upwards [eventually_ne_nhds hx] with t ht
    apply iterDeriv_id_mul k hk (g k) t
    unfold g
    apply ContDiffAt.mul (by fun_prop)
    exact Real.contDiff_exp.contDiffAt.comp t
      (contDiffAt_const.div contDiffAt_id ht)
  exact Filter.EventuallyEq.deriv_eq hev

theorem gap4 (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : x ≠ 0)
    (hind : iterDeriv k (g k) x = closedForm k x) :
    iterDeriv (k + 1) (g (k + 1)) x =
      x * deriv (closedForm k) x + (k + 1 : ℕ) * closedForm k x := by
  rw [show iterDeriv (k + 1) (g (k + 1)) x =
      deriv (fun t => t * iterDeriv k (g k) t +
        (k : ℝ) * iterDeriv (k - 1) (g k) t) x by
    exact gap3 k x hk hx hind]
  have hgcd : ContDiffAt ℝ (k + 1) (g k) x := by
    unfold g
    apply ContDiffAt.mul (by fun_prop)
    exact Real.contDiff_exp.contDiffAt.comp x
      (contDiffAt_const.div contDiffAt_id hx)
  have hdk : DifferentiableAt ℝ (iterDeriv k (g k)) x :=
    (contDiffAt_iterDeriv (g k) x 1 k (by
      simpa [add_comm] using hgcd)).differentiableAt (by norm_num)
  have hprev : DifferentiableAt ℝ (iterDeriv (k - 1) (g k)) x :=
    (contDiffAt_iterDeriv (g k) x 1 (k - 1) (by
      apply hgcd.of_le
      have hn : 1 + (k - 1) ≤ k + 1 := by omega
      have hen : ((1 + (k - 1) : ℕ) : ℕ∞) ≤ (k + 1 : ℕ) :=
        ENat.coe_le_coe.mpr hn
      exact WithTop.coe_le_coe.mpr hen)).differentiableAt (by norm_num)
  have hev : iterDeriv k (g k) =ᶠ[nhds x] closedForm k := by
    filter_upwards [eventually_ne_nhds hx] with t ht
    exact master k hk t ht
  have hder :
      deriv (iterDeriv k (g k)) x = deriv (closedForm k) x :=
    Filter.EventuallyEq.deriv_eq hev
  have hprevder :
      deriv (iterDeriv (k - 1) (g k)) x = iterDeriv k (g k) x := by
    rw [show k = (k - 1) + 1 by omega]
    simp [iterDeriv, Function.iterate_succ_apply']
  have hF := ((hasDerivAt_id x).mul hdk.hasDerivAt).add
    (hprev.hasDerivAt.const_mul (k : ℝ))
  have hFder :
      deriv (fun t => t * iterDeriv k (g k) t +
        (k : ℝ) * iterDeriv (k - 1) (g k) t) x =
        iterDeriv k (g k) x +
          x * deriv (iterDeriv k (g k)) x +
          (k : ℝ) * deriv (iterDeriv (k - 1) (g k)) x := by
    convert hF.deriv using 1 <;> simp [id] <;> ring
  rw [hFder, hder, hprevder, master k hk x hx]
  push_cast
  ring

theorem gap5 (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : x ≠ 0)
    (hind : iterDeriv k (g k) x = closedForm k x) :
    iterDeriv (k + 1) (g (k + 1)) x =
      (-1 : ℝ) ^ (k + 1) * (k + 1 : ℕ) / x ^ (k + 1) * Real.exp (1 / x) +
      (-1 : ℝ) ^ (k + 1) / x ^ (k + 2) * Real.exp (1 / x) +
      (-1 : ℝ) ^ k * (k + 1 : ℕ) / x ^ (k + 1) * Real.exp (1 / x) := by
  rw [show iterDeriv (k + 1) (g (k + 1)) x =
      x * deriv (closedForm k) x + (k + 1 : ℕ) * closedForm k x by
    exact gap4 k x hk hx hind]
  rw [(hasDerivAt_closedForm k x hx).deriv]
  unfold closedForm
  field_simp [hx]
  ring

theorem gap6 (k : ℕ) (x : ℝ) (hk : 1 ≤ k) (hx : x ≠ 0)
    (hind : iterDeriv k (g k) x = closedForm k x) :
    iterDeriv (k + 1) (g (k + 1)) x = closedForm (k + 1) x := by
  exact master (k + 1) (by omega) x hx

theorem gap7 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : x ≠ 0) :
    iterDeriv n (g n) x = closedForm n x := by
  exact master n hn x hx

theorem gap8 (n : ℕ) (x : ℝ) (hn : 1 ≤ n) (hx : x ≠ 0) :
    iterDeriv n (g n) x = closedForm n x := by
  exact gap7 n x hn hx

end

end ProofGap.Exercise1232
