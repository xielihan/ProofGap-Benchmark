import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

namespace ProofGap.Exercise1234

noncomputable section

def iterDeriv (n : ℕ) (f : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) f
def xCoord (t : ℝ) : ℝ := Real.exp t
def pullback (y : ℝ → ℝ) (t : ℝ) : ℝ := y (xCoord t)
def D (v : ℝ → ℝ) (t : ℝ) : ℝ := deriv v t
def delta (y : ℝ → ℝ) (t : ℝ) : ℝ := deriv y (xCoord t)

def fallingD : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, v => v
  | k + 1, v => fun t => deriv (fallingD k v) t - (k : ℝ) * fallingD k v t

def eulerSum (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1),
    a k * xCoord t ^ k * iterDeriv k y (xCoord t)

def transformedSum (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), a k * fallingD k (pullback y) t

theorem gap1 (y : ℝ → ℝ) (t : ℝ)
    (hy : DifferentiableAt ℝ y (xCoord t)) :
    D (pullback y) t = deriv y (xCoord t) * deriv xCoord t := by
  unfold D pullback xCoord at *
  rw [Real.hasDerivAt_exp t |>.deriv]
  simpa only [Function.comp_apply] using
    (HasDerivAt.comp t hy.hasDerivAt (Real.hasDerivAt_exp t)).deriv

theorem gap2 (y : ℝ → ℝ) (t : ℝ)
    (hy : DifferentiableAt ℝ y (xCoord t)) :
    deriv y (xCoord t) * deriv xCoord t =
      Real.exp t * delta y t := by
  unfold xCoord delta at *
  rw [Real.hasDerivAt_exp t |>.deriv]
  simp only [xCoord]
  ring

theorem gap3 (y : ℝ → ℝ) (t : ℝ)
    (hy : DifferentiableAt ℝ y (xCoord t)) :
    D (pullback y) t = Real.exp t * delta y t := by
  rw [gap1 y t hy, gap2 y t hy]

theorem gap4 (y : ℝ → ℝ) (t : ℝ)
    (hy : DifferentiableAt ℝ y (xCoord t)) :
    delta y t = Real.exp (-t) * D (pullback y) t := by
  rw [gap3 y t hy]
  rw [show Real.exp (-t) * (Real.exp t * delta y t) =
      (Real.exp (-t) * Real.exp t) * delta y t by ring,
    ← Real.exp_add]
  simp

theorem gap5 (y : ℝ → ℝ) (t : ℝ)
    (hy : DifferentiableAt ℝ y (xCoord t)) :
    delta y t = Real.exp (-t) * D (pullback y) t := by
  exact gap4 y t hy

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

theorem gap6 (y : ℝ → ℝ) (t : ℝ) (hy : ContDiffAt ℝ 2 y (xCoord t)) :
    iterDeriv 2 y (xCoord t) =
      Real.exp (-t) * D (fun s => Real.exp (-s) * D (pullback y) s) t := by
  have hy1 : DifferentiableAt ℝ (iterDeriv 1 y) (xCoord t) := by
    exact (contDiffAt_iterDeriv y (xCoord t) 1 1 (by
      simpa using hy)).differentiableAt (by norm_num)
  rw [show iterDeriv 2 y (xCoord t) =
      delta (iterDeriv 1 y) t by
    simp [delta, iterDeriv, Function.iterate_succ_apply']]
  rw [gap5 (iterDeriv 1 y) t hy1]
  have hevent_at :
      ∀ᶠ u in nhds (xCoord t), ContDiffAt ℝ 2 y u :=
    hy.eventually (by simp)
  have htend : Filter.Tendsto xCoord (nhds t) (nhds (xCoord t)) := by
    unfold xCoord
    exact Real.continuous_exp.continuousAt
  have hevent := htend.eventually hevent_at
  have hev :
      (fun s => Real.exp (-s) * D (pullback y) s) =ᶠ[nhds t]
        pullback (iterDeriv 1 y) := by
    filter_upwards [hevent] with s hys
    have hdiff : DifferentiableAt ℝ y (xCoord s) :=
      hys.differentiableAt two_ne_zero
    have h := gap5 y s hdiff
    simpa [delta, iterDeriv, pullback,
      Function.iterate_succ_apply'] using h.symm
  have hd := Filter.EventuallyEq.deriv_eq hev
  exact congrArg (fun z : ℝ => Real.exp (-t) * z) hd.symm

theorem gap7 (y : ℝ → ℝ) (t : ℝ) (hy : ContDiffAt ℝ 2 y (xCoord t)) :
    Real.exp (-t) * D (fun s => Real.exp (-s) * D (pullback y) s) t =
      Real.exp (-t) *
        (-Real.exp (-t) * D (pullback y) t +
          Real.exp (-t) * iterDeriv 2 (pullback y) t) := by
  have hpb : ContDiffAt ℝ 2 (pullback y) t := by
    unfold pullback xCoord
    exact hy.comp t Real.contDiff_exp.contDiffAt
  have hdp : DifferentiableAt ℝ (D (pullback y)) t := by
    unfold D
    exact (contDiffAt_iterDeriv (pullback y) t 1 1 (by
      simpa using hpb)).differentiableAt (by norm_num)
  have hn : HasDerivAt (fun s : ℝ => Real.exp (-s))
      (-Real.exp (-t)) t := by
    convert (Real.hasDerivAt_exp (-t)).comp t (hasDerivAt_id t).neg using 1 <;>
      simp [Function.comp_apply, id]
  have hp := hn.mul hdp.hasDerivAt
  unfold D
  convert congrArg (fun z : ℝ => Real.exp (-t) * z) hp.deriv using 1 <;>
    simp [iterDeriv, Function.iterate_succ_apply'] <;> ring

theorem gap8 (y : ℝ → ℝ) (t : ℝ) (hy : ContDiffAt ℝ 2 y (xCoord t)) :
    Real.exp (-t) *
        (-Real.exp (-t) * D (pullback y) t +
          Real.exp (-t) * iterDeriv 2 (pullback y) t) =
      Real.exp (-2 * t) * fallingD 2 (pullback y) t := by
  have he : Real.exp (-t) * Real.exp (-t) = Real.exp (-2 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [fallingD, D, Nat.cast_zero, zero_mul, sub_zero, Nat.cast_one,
    one_mul]
  simp only [iterDeriv, Function.iterate_succ_apply']
  calc
    Real.exp (-t) *
        (-Real.exp (-t) * deriv (pullback y) t +
          Real.exp (-t) * deriv (deriv (pullback y)) t) =
      (Real.exp (-t) * Real.exp (-t)) *
        (deriv (deriv (pullback y)) t - deriv (pullback y) t) := by ring
    _ = Real.exp (-2 * t) *
        (deriv (deriv (pullback y)) t - deriv (pullback y) t) := by rw [he]

theorem gap9 (y : ℝ → ℝ) (t : ℝ) (hy : ContDiffAt ℝ 2 y (xCoord t)) :
    iterDeriv 2 y (xCoord t) =
      Real.exp (-2 * t) * fallingD 2 (pullback y) t := by
  rw [gap6 y t hy, gap7 y t hy, gap8 y t hy]

private lemma contDiffAt_fallingD (v : ℝ → ℝ) (t : ℝ) (n k : ℕ)
    (hv : ContDiffAt ℝ (n + k) v t) :
    ContDiffAt ℝ n (fallingD k v) t := by
  induction k generalizing n v with
  | zero =>
      simpa [fallingD] using hv
  | succ k ih =>
      have hprev : ContDiffAt ℝ (n + 1) (fallingD k v) t := by
        apply ih
        convert hv using 1 <;> push_cast <;> ac_rfl
      have hd : ContDiffAt ℝ n (deriv (fallingD k v)) t :=
        hprev.derivWithin (m := n) (le_refl _)
      have hc : ContDiffAt ℝ n
          (fun s => (k : ℝ) * fallingD k v s) t :=
        contDiffAt_const.mul (hprev.of_le (by
          have hn : (n : ℕ∞) ≤ (n + 1 : ℕ) :=
            ENat.coe_le_coe.mpr (Nat.le_succ n)
          exact WithTop.coe_le_coe.mpr hn))
      simpa [fallingD] using hd.sub hc

private theorem master (y : ℝ → ℝ) (k : ℕ) (t : ℝ)
    (hy : ContDiffAt ℝ k y (xCoord t)) :
    iterDeriv k y (xCoord t) =
      Real.exp (-(k : ℝ) * t) * fallingD k (pullback y) t := by
  induction k generalizing t with
  | zero =>
      simp [iterDeriv, fallingD, pullback, xCoord]
  | succ m ih =>
      have hdm : DifferentiableAt ℝ (iterDeriv m y) (xCoord t) :=
        (contDiffAt_iterDeriv y (xCoord t) 1 m (by
          simpa [add_comm] using hy)).differentiableAt (by norm_num)
      rw [show iterDeriv (m + 1) y (xCoord t) =
          delta (iterDeriv m y) t by
        simp [delta, iterDeriv, Function.iterate_succ_apply']]
      rw [gap5 (iterDeriv m y) t hdm]
      have hpb : ContDiffAt ℝ (m + 1) (pullback y) t := by
        unfold pullback xCoord
        exact hy.comp t Real.contDiff_exp.contDiffAt
      have hfd : DifferentiableAt ℝ (fallingD m (pullback y)) t :=
        (contDiffAt_fallingD (pullback y) t 1 m (by
          simpa [add_comm] using hpb)).differentiableAt (by norm_num)
      have he : HasDerivAt
          (fun s : ℝ => Real.exp (-(m : ℝ) * s))
          (-(m : ℝ) * Real.exp (-(m : ℝ) * t)) t := by
        have hlin : HasDerivAt (fun s : ℝ => -(m : ℝ) * s)
            (-(m : ℝ)) t := by
          convert (hasDerivAt_id t).const_mul (-(m : ℝ)) using 1 <;>
            simp [id]
        convert (Real.hasDerivAt_exp (-(m : ℝ) * t)).comp t hlin using 1 <;>
          simp [Function.comp_apply] <;> ring
      have hp := he.mul hfd.hasDerivAt
      have hevent_at :
          ∀ᶠ u in nhds (xCoord t), ContDiffAt ℝ (m + 1) y u :=
        hy.eventually (by simp)
      have htend : Filter.Tendsto xCoord (nhds t) (nhds (xCoord t)) := by
        unfold xCoord
        exact Real.continuous_exp.continuousAt
      have hevent := htend.eventually hevent_at
      have hev :
          (fun s => Real.exp (-(m : ℝ) * s) *
            fallingD m (pullback y) s) =ᶠ[nhds t]
            pullback (iterDeriv m y) := by
        filter_upwards [hevent] with s hys
        have hysm : ContDiffAt ℝ m y (xCoord s) := by
          apply hys.of_le
          have hn : (m : ℕ∞) ≤ (m + 1 : ℕ) :=
            ENat.coe_le_coe.mpr (Nat.le_succ m)
          exact WithTop.coe_le_coe.mpr hn
        exact (ih s hysm).symm
      have hd := Filter.EventuallyEq.deriv_eq hev
      unfold D
      rw [← hd]
      have hpderiv :
          deriv (fun s => Real.exp (-(m : ℝ) * s) *
            fallingD m (pullback y) s) t =
            (-(m : ℝ) * Real.exp (-(m : ℝ) * t)) *
                fallingD m (pullback y) t +
              Real.exp (-(m : ℝ) * t) *
                deriv (fallingD m (pullback y)) t := by
        simpa only [Pi.mul_apply] using hp.deriv
      rw [hpderiv]
      simp only [fallingD]
      have hexp :
          Real.exp (-t) * Real.exp (-(m : ℝ) * t) =
            Real.exp (-(m + 1 : ℕ) * t) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [show Real.exp (-t) *
          (-(m : ℝ) * Real.exp (-(m : ℝ) * t) *
              fallingD m (pullback y) t +
            Real.exp (-(m : ℝ) * t) *
              deriv (fallingD m (pullback y)) t) =
          (Real.exp (-t) * Real.exp (-(m : ℝ) * t)) *
            (deriv (fallingD m (pullback y)) t -
              (m : ℝ) * fallingD m (pullback y) t) by ring,
        hexp]

theorem gap10 (y : ℝ → ℝ) (k : ℕ) (t : ℝ)
    (hy : ContDiffAt ℝ k y (xCoord t)) :
    iterDeriv k y (xCoord t) =
      Real.exp (-(k : ℝ) * t) * fallingD k (pullback y) t := by
  exact master y k t hy

theorem gap11 (y : ℝ → ℝ) (m : ℕ) (t : ℝ)
    (hy : ContDiffAt ℝ (m + 1) y (xCoord t))
    (hind : iterDeriv m y (xCoord t) =
      Real.exp (-(m : ℝ) * t) * fallingD m (pullback y) t) :
    iterDeriv (m + 1) y (xCoord t) =
      delta (iterDeriv m y) t := by
  simp [delta, iterDeriv, Function.iterate_succ_apply']

theorem gap12 (y : ℝ → ℝ) (m : ℕ) (t : ℝ)
    (hy : ContDiffAt ℝ (m + 1) y (xCoord t))
    (hind : iterDeriv m y (xCoord t) =
      Real.exp (-(m : ℝ) * t) * fallingD m (pullback y) t) :
    iterDeriv (m + 1) y (xCoord t) =
      Real.exp (-t) *
        D (fun s => Real.exp (-(m : ℝ) * s) * fallingD m (pullback y) s) t := by
  rw [gap11 y m t hy hind]
  have hdm : DifferentiableAt ℝ (iterDeriv m y) (xCoord t) :=
    (contDiffAt_iterDeriv y (xCoord t) 1 m (by
      simpa [add_comm] using hy)).differentiableAt (by norm_num)
  rw [gap5 (iterDeriv m y) t hdm]
  have hevent_at :
      ∀ᶠ u in nhds (xCoord t), ContDiffAt ℝ (m + 1) y u :=
    hy.eventually (by simp)
  have htend : Filter.Tendsto xCoord (nhds t) (nhds (xCoord t)) := by
    unfold xCoord
    exact Real.continuous_exp.continuousAt
  have hevent := htend.eventually hevent_at
  have hev :
      (fun s => Real.exp (-(m : ℝ) * s) *
        fallingD m (pullback y) s) =ᶠ[nhds t]
        pullback (iterDeriv m y) := by
    filter_upwards [hevent] with s hys
    have hysm : ContDiffAt ℝ m y (xCoord s) := by
      apply hys.of_le
      have hn : (m : ℕ∞) ≤ (m + 1 : ℕ) :=
        ENat.coe_le_coe.mpr (Nat.le_succ m)
      exact WithTop.coe_le_coe.mpr hn
    exact (master y m s hysm).symm
  have hd := Filter.EventuallyEq.deriv_eq hev
  unfold D
  rw [← hd]

theorem gap13 (y : ℝ → ℝ) (m : ℕ) (t : ℝ)
    (hy : ContDiffAt ℝ (m + 1) y (xCoord t)) :
    iterDeriv (m + 1) y (xCoord t) =
      Real.exp (-(m + 1 : ℕ) * t) * fallingD (m + 1) (pullback y) t := by
  exact master y (m + 1) t hy

theorem gap14 (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ) :
    eulerSum a n y t =
      ∑ k ∈ Finset.range (n + 1),
        a k * xCoord t ^ k * iterDeriv k y (xCoord t) := by
  rfl

theorem gap15 (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ)
    (hy : ContDiffAt ℝ n y (xCoord t)) :
    eulerSum a n y t =
      ∑ k ∈ Finset.range (n + 1),
        a k * Real.exp ((k : ℝ) * t) * Real.exp (-(k : ℝ) * t) *
          fallingD k (pullback y) t := by
  unfold eulerSum
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hyk : ContDiffAt ℝ k y (xCoord t) := by
    apply hy.of_le
    have hcoe : (k : ℕ∞) ≤ (n : ℕ∞) := ENat.coe_le_coe.mpr hkn
    exact WithTop.coe_le_coe.mpr hcoe
  rw [master y k t hyk]
  have hexp : xCoord t ^ k = Real.exp ((k : ℝ) * t) := by
    unfold xCoord
    rw [← Real.exp_nat_mul]
  rw [hexp]
  ring

theorem gap16 (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ)
    (hEq : eulerSum a n y t = 0) (hy : ContDiffAt ℝ n y (xCoord t)) :
    (∑ k ∈ Finset.range (n + 1),
      a k * Real.exp ((k : ℝ) * t) * Real.exp (-(k : ℝ) * t) *
        fallingD k (pullback y) t) = 0 := by
  rw [← gap15 a n y t hy]
  exact hEq

theorem gap17 (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ)
    (hEq : eulerSum a n y t = 0) (hy : ContDiffAt ℝ n y (xCoord t)) :
    eulerSum a n y t = 0 := by
  exact hEq

theorem gap18 (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ)
    (hEq : eulerSum a n y t = 0) (hy : ContDiffAt ℝ n y (xCoord t)) :
    transformedSum a n y t = 0 := by
  unfold transformedSum
  calc
    (∑ k ∈ Finset.range (n + 1),
        a k * fallingD k (pullback y) t) =
        ∑ k ∈ Finset.range (n + 1),
          a k * Real.exp ((k : ℝ) * t) * Real.exp (-(k : ℝ) * t) *
            fallingD k (pullback y) t := by
      apply Finset.sum_congr rfl
      intro k hk
      have he :
          Real.exp ((k : ℝ) * t) * Real.exp (-(k : ℝ) * t) = 1 := by
        rw [← Real.exp_add]
        ring_nf
        simp
      calc
        a k * fallingD k (pullback y) t =
            a k * (Real.exp ((k : ℝ) * t) *
              Real.exp (-(k : ℝ) * t)) *
              fallingD k (pullback y) t := by rw [he]; ring
        _ = a k * Real.exp ((k : ℝ) * t) *
              Real.exp (-(k : ℝ) * t) *
              fallingD k (pullback y) t := by ring
    _ = 0 := gap16 a n y t hEq hy

theorem gap19 (a : ℕ → ℝ) (n : ℕ) (y : ℝ → ℝ) (t : ℝ)
    (hEq : eulerSum a n y t = 0) (hy : ContDiffAt ℝ n y (xCoord t)) :
    transformedSum a n y t = 0 := by
  exact gap18 a n y t hEq hy

end

end ProofGap.Exercise1234
