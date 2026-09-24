import ProofGapLean.Prelude.Analysis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter

namespace ProofGap.Exercise2517

noncomputable section

def representativeRadius (R h : ℝ) (n i : ℕ) : ℝ :=
  Real.sqrt ((h / n * (i - 1) + R) * (h / n * i + R))
def force (k m M R h : ℝ) (n i : ℕ) : ℝ :=
  k * m * M /
    ((h / n * (i - 1) + R) * (h / n * i + R))
def workApprox (k m M R h : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.Icc 1 n, force k m M R h n i * (h / n)
def telescopingApprox (k m M R h : ℝ) (n : ℕ) : ℝ :=
  k * m * M * n *
    ∑ i ∈ Finset.Icc 1 n,
      (1 / (h * (i - 1) + n * R) - 1 / (h * i + n * R))
def finiteHeightWork (k m M R h : ℝ) : ℝ :=
  k * m * M * h / ((R + h) * R)

theorem gap1 (R h : ℝ) (n i : ℕ) :
    representativeRadius R h n i =
      Real.sqrt ((h / n * (i - 1) + R) * (h / n * i + R)) := by
  rfl

theorem gap2 (k m M R h : ℝ) (n i : ℕ) :
    force k m M R h n i =
      k * m * M /
        ((h / n * (i - 1) + R) * (h / n * i + R)) := by
  rfl

theorem gap3 (k m M R h W : ℝ)
    (hW : Filter.Tendsto (workApprox k m M R h)
      Filter.atTop (nhds W)) :
    Filter.Tendsto (workApprox k m M R h) Filter.atTop (nhds W) := by
  exact hW

theorem gap4 (k m M R h : ℝ) (n : ℕ) (hn : 0 < n)
    (hR : 0 < R) (hh : 0 ≤ h) :
    workApprox k m M R h n =
      telescopingApprox k m M R h n := by
  unfold workApprox telescopingApprox force
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hn' : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hn'
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hi1' : (1 : ℝ) ≤ (i : ℝ) := by
    exact_mod_cast hi1
  have hii : 0 ≤ (i : ℝ) - 1 := by
    linarith
  have hhdiv : 0 ≤ h / (n : ℝ) :=
    div_nonneg hh (le_of_lt hn')
  have hfa : 0 < h / (n : ℝ) * ((i : ℝ) - 1) + R :=
    add_pos_of_nonneg_of_pos (mul_nonneg hhdiv hii) hR
  have hfb : 0 < h / (n : ℝ) * (i : ℝ) + R :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg hhdiv (Nat.cast_nonneg i)) hR
  have ha : 0 < h * ((i : ℝ) - 1) + (n : ℝ) * R :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg hh hii) (mul_pos hn' hR)
  have hb : 0 < h * (i : ℝ) + (n : ℝ) * R :=
    add_pos_of_nonneg_of_pos
      (mul_nonneg hh (Nat.cast_nonneg i)) (mul_pos hn' hR)
  field_simp [hn0, ne_of_gt hfa, ne_of_gt hfb,
    ne_of_gt ha, ne_of_gt hb] <;> ring_nf

theorem gap5 (k m M R h : ℝ) (n : ℕ) (hn : 0 < n)
    (hR : 0 < R) (hh : 0 ≤ h) :
    telescopingApprox k m M R h n =
      k * m * M * n *
        (1 / (n * R) - 1 / (n * (R + h))) := by
  let f : ℕ → ℝ := fun i => 1 / (h * i + n * R)
  have htel : ∀ j : ℕ,
      (∑ i ∈ Finset.Icc 1 j, (f (i - 1) - f i)) = f 0 - f j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hset : Finset.Icc 1 (Nat.succ j) =
            insert (Nat.succ j) (Finset.Icc 1 j) := by
          ext a
          simp only [Finset.mem_Icc, Finset.mem_insert]
          omega
        have hnot : Nat.succ j ∉ Finset.Icc 1 j := by
          simp
        rw [hset, Finset.sum_insert hnot, ih]
        have hs : Nat.succ j - 1 = j := by omega
        rw [hs]
        ring
  have hsum :
      (∑ i ∈ Finset.Icc 1 n,
        (1 / (h * ((i : ℝ) - 1) + n * R) -
          1 / (h * i + n * R))) = f 0 - f n := by
    calc
      (∑ i ∈ Finset.Icc 1 n,
        (1 / (h * ((i : ℝ) - 1) + n * R) -
          1 / (h * i + n * R))) =
          ∑ i ∈ Finset.Icc 1 n, (f (i - 1) - f i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
            simp [f, Nat.cast_sub hi1]
      _ = f 0 - f n := htel n
  unfold telescopingApprox
  rw [hsum]
  dsimp [f]
  simp only [Nat.cast_zero, mul_zero, zero_add]
  rw [show h * (n : ℝ) + (n : ℝ) * R =
      (n : ℝ) * (R + h) by ring]

theorem gap6 (k m M R h : ℝ) (hR : 0 < R) (hh : 0 ≤ h) :
    Filter.Tendsto
      (fun n : ℕ => k * m * M * n *
        (1 / (n * R) - 1 / (n * (R + h))))
      Filter.atTop (nhds (finiteHeightWork k m M R h)) := by
  have hRh : 0 < R + h := by linarith
  have heq :
      (fun n : ℕ => k * m * M * n *
        (1 / (n * R) - 1 / (n * (R + h)))) =ᶠ[Filter.atTop]
      (fun _ : ℕ => finiteHeightWork k m M R h) := by
    apply Filter.eventually_atTop.2
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hnpos)
    unfold finiteHeightWork
    field_simp [hn0, ne_of_gt hR, ne_of_gt hRh] <;> ring_nf
  have hc : Filter.Tendsto
      (fun _ : ℕ => finiteHeightWork k m M R h)
      Filter.atTop (nhds (finiteHeightWork k m M R h)) :=
    tendsto_const_nhds
  exact hc.congr' heq.symm

theorem gap7 (k m M R h W : ℝ) (hR : 0 < R) (hh : 0 ≤ h)
    (hW : Filter.Tendsto (workApprox k m M R h)
      Filter.atTop (nhds W)) :
    W = finiteHeightWork k m M R h := by
  have heq : workApprox k m M R h =ᶠ[Filter.atTop]
      (fun n : ℕ => k * m * M * n *
        (1 / (n * R) - 1 / (n * (R + h)))) := by
    apply Filter.eventually_atTop.2
    refine ⟨1, ?_⟩
    intro n hn
    have hnpos : 0 < n := hn
    rw [gap4 k m M R h n hnpos hR hh,
      gap5 k m M R h n hnpos hR hh]
  have hfinite : Filter.Tendsto (workApprox k m M R h)
      Filter.atTop (nhds (finiteHeightWork k m M R h)) :=
    (gap6 k m M R h hR hh).congr' heq.symm
  exact tendsto_nhds_unique hW hfinite

theorem gap8 (k m M R A : ℝ)
    (hA : Filter.Tendsto (finiteHeightWork k m M R)
      Filter.atTop (nhds A)) :
    Filter.Tendsto (finiteHeightWork k m M R)
      Filter.atTop (nhds A) := by
  exact hA

theorem gap9 (k m M R : ℝ) :
    Filter.Tendsto (finiteHeightWork k m M R)
      Filter.atTop
      (nhds (k * m * M / R)) := by
  rcases eq_or_ne R 0 with hR0 | hR0
  · subst R
    have hz : finiteHeightWork k m M 0 = fun _ : ℝ => 0 := by
      funext x
      simp [finiteHeightWork]
    simpa only [hz, div_zero] using
      (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
        Filter.atTop (nhds 0))
  · have hsum : Filter.Tendsto (fun x : ℝ => R + x)
        Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      exact Filter.eventually_atTop.2
        ⟨b - R, fun x hx => by
          linarith⟩
    have hinv : Filter.Tendsto (fun x : ℝ => (R + x)⁻¹)
        Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp hsum
    have hRinv : Filter.Tendsto (fun x : ℝ => R * (R + x)⁻¹)
        Filter.atTop (nhds (R * 0)) :=
      tendsto_const_nhds.mul hinv
    have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ))
        Filter.atTop (nhds 1) := tendsto_const_nhds
    have hcorr : Filter.Tendsto
        (fun x : ℝ => 1 - R * (R + x)⁻¹)
        Filter.atTop (nhds 1) := by
      simpa using hone.sub hRinv
    have hc : Filter.Tendsto (fun _ : ℝ => k * m * M / R)
        Filter.atTop (nhds (k * m * M / R)) := tendsto_const_nhds
    have hscaled : Filter.Tendsto
        (fun x : ℝ => (k * m * M / R) *
          (1 - R * (R + x)⁻¹))
        Filter.atTop (nhds (k * m * M / R)) := by
      simpa using hc.mul hcorr
    have heq : finiteHeightWork k m M R =ᶠ[Filter.atTop]
        (fun x : ℝ => (k * m * M / R) *
          (1 - R * (R + x)⁻¹)) := by
      apply Filter.eventually_atTop.2
      refine ⟨1 - R, ?_⟩
      intro x hx
      have hs : R + x ≠ 0 := by
        intro hs0
        have : (0 : ℝ) < R + x := by linarith
        linarith
      unfold finiteHeightWork
      field_simp [hR0, hs] <;> ring_nf
    exact hscaled.congr' heq.symm

theorem gap10 (k m M R g : ℝ) (hR : 0 < R) (hM : M ≠ 0)
    (hk : k = g * R ^ 2 / M) :
    k * m * M / R = m * g * R := by
  rw [hk]
  field_simp [hM, ne_of_gt hR] <;> ring

theorem gap11 (k m M R g A : ℝ) (hR : 0 < R) (hM : M ≠ 0)
    (hk : k = g * R ^ 2 / M)
    (hA : Filter.Tendsto (finiteHeightWork k m M R)
      Filter.atTop (nhds A)) :
    A = m * g * R := by
  have hlimit : A = k * m * M / R :=
    tendsto_nhds_unique hA (gap9 k m M R)
  calc
    A = k * m * M / R := hlimit
    _ = m * g * R := gap10 k m M R g hR hM hk

end

end ProofGap.Exercise2517
