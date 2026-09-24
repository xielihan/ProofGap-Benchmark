import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Stirling

namespace ProofGap.Exercise3103

noncomputable section

open Filter
open scoped BigOperators Topology

def wallisFactor (n : ℕ) : ℝ :=
  (2 * (n : ℝ) / (2 * (n : ℝ) - 1)) *
    (2 * (n : ℝ) / (2 * (n : ℝ) + 1))

def wallisPartialProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, wallisFactor i

def HasWallisProduct (L : ℝ) : Prop :=
  Tendsto wallisPartialProduct atTop (𝓝 L)

def evenProduct (n : ℕ) : ℝ :=
  ∏ i ∈ Finset.Icc 1 n, 2 * (i : ℝ)

def oddProduct (n : ℕ) : ℝ :=
  -- Statement correction: parenthesize the odd factor so subtraction is inside the product.
  ∏ i ∈ Finset.Icc 1 n, (2 * (i : ℝ) - 1)

def evenOddWallisTerm (n : ℕ) : ℝ :=
  (evenProduct n / oddProduct n) ^ 2 / (2 * (n : ℝ) + 1)

def oddEvenRatio (n : ℕ) : ℝ :=
  oddProduct n / evenProduct n

def squareModel (n : ℕ) : ℝ :=
  2 / (Real.pi * (2 * (n : ℝ) + 1))

def ratioModel (n : ℕ) : ℝ :=
  1 / Real.sqrt (Real.pi * n)

private theorem wallisPartialProduct_eq_W (n : ℕ) :
    wallisPartialProduct n = Real.Wallis.W n := by
  induction n with
  | zero =>
      simp [wallisPartialProduct, Real.Wallis.W]
  | succ n ih =>
      rw [wallisPartialProduct, Finset.prod_Icc_succ_top (by omega)]
      rw [show (∏ x ∈ Finset.Icc 1 n, wallisFactor x) =
        wallisPartialProduct n by rfl, ih, Real.Wallis.W_succ]
      congr 1
      unfold wallisFactor
      push_cast
      ring

private theorem evenProduct_succ (n : ℕ) :
    evenProduct (n + 1) = evenProduct n * (2 * ((n + 1 : ℕ) : ℝ)) := by
  rw [evenProduct, Finset.prod_Icc_succ_top (by omega)]
  rfl

private theorem oddProduct_succ (n : ℕ) :
    oddProduct (n + 1) = oddProduct n * (2 * ((n + 1 : ℕ) : ℝ) - 1) := by
  rw [oddProduct, Finset.prod_Icc_succ_top (by omega)]
  rfl

private theorem evenProduct_pos (n : ℕ) : 0 < evenProduct n := by
  unfold evenProduct
  apply Finset.prod_pos
  intro i hi
  simp only [Finset.mem_Icc] at hi
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
  linarith

private theorem oddProduct_pos (n : ℕ) : 0 < oddProduct n := by
  unfold oddProduct
  apply Finset.prod_pos
  intro i hi
  simp only [Finset.mem_Icc] at hi
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi.1
  linarith

private theorem evenOddWallisTerm_eq_W (n : ℕ) :
    evenOddWallisTerm n = Real.Wallis.W n := by
  induction n with
  | zero =>
      simp [evenOddWallisTerm, evenProduct, oddProduct, Real.Wallis.W]
  | succ n ih =>
      rw [Real.Wallis.W_succ, ← ih, evenOddWallisTerm,
        evenProduct_succ, oddProduct_succ]
      unfold evenOddWallisTerm
      have he := (evenProduct_pos n).ne'
      have ho := (oddProduct_pos n).ne'
      have hodd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
      have hnext : 2 * (n : ℝ) + 3 ≠ 0 := by positivity
      push_cast
      field_simp [he, ho, hodd, hnext]
      have hden : 2 * ((n : ℝ) + 1) - 1 ≠ 0 := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        linarith
      field_simp [hden]
      ring

/-- Source: `proof_gap/exercise_3103/1.txt`; use convergence of partial products. -/
theorem gap1 : HasWallisProduct (Real.pi / 2) := by
  unfold HasWallisProduct
  exact Real.Wallis.tendsto_W_nhds_pi_div_two.congr'
    (Eventually.of_forall fun n => (wallisPartialProduct_eq_W n).symm)

/-- Source: `proof_gap/exercise_3103/2.txt`. -/
theorem gap2 :
    Tendsto evenOddWallisTerm atTop (𝓝 (Real.pi / 2)) := by
  exact Real.Wallis.tendsto_W_nhds_pi_div_two.congr'
    (Eventually.of_forall fun n => (evenOddWallisTerm_eq_W n).symm)

/-- Source: `proof_gap/exercise_3103/3.txt`. -/
theorem gap3 :
    Asymptotics.IsEquivalent atTop
      (fun n : ℕ => (oddEvenRatio n) ^ 2) squareModel := by
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hWne : ∀ n, evenOddWallisTerm n ≠ 0 :=
    fun n => by rw [evenOddWallisTerm_eq_W]; exact (Real.Wallis.W_pos n).ne'
  have hlim :
      Tendsto (fun n : ℕ => (Real.pi / 2) / evenOddWallisTerm n)
        atTop (𝓝 1) := by
    have hc :
        Tendsto (fun _ : ℕ => Real.pi / 2) atTop (𝓝 (Real.pi / 2)) :=
      tendsto_const_nhds
    have h := hc.div gap2 (by positivity : Real.pi / 2 ≠ 0)
    convert h using 1
    field_simp [hpi]
  convert hlim using 1
  funext n
  unfold oddEvenRatio squareModel evenOddWallisTerm
  have he := (evenProduct_pos n).ne'
  have ho := (oddProduct_pos n).ne'
  have hd : 2 * (n : ℝ) + 1 ≠ 0 := by positivity
  simp only [Pi.div_apply]
  field_simp [he, ho, hd, hpi]

/-- Source: `proof_gap/exercise_3103/4.txt`; both sides are eventually positive. -/
theorem gap4 :
    Asymptotics.IsEquivalent atTop oddEvenRatio ratioModel := by
  have hsquare_ne : ∀ᶠ n : ℕ in atTop, squareModel n ≠ 0 :=
    Eventually.of_forall fun n => by
      unfold squareModel
      positivity
  have hsquares :
      Tendsto
        ((fun n : ℕ => (oddEvenRatio n) ^ 2) / squareModel)
        atTop (𝓝 1) :=
    (Asymptotics.isEquivalent_iff_tendsto_one hsquare_ne).mp gap3
  have hmodels :
      Tendsto (fun n : ℕ => squareModel n / (ratioModel n) ^ 2)
        atTop (𝓝 1) := by
    have hbase :=
      (Stirling.tendsto_self_div_two_mul_self_add_one.const_mul (2 : ℝ))
    have hbase' :
        Tendsto (fun n : ℕ => 2 * ((n : ℝ) / (2 * n + 1)))
          atTop (𝓝 1) := by
      norm_num at hbase ⊢
      exact hbase
    apply hbase'.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    unfold squareModel ratioModel
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hnpos : 0 < (n : ℝ) := by positivity
    have hs_sq :
        Real.sqrt (Real.pi * (n : ℝ)) ^ 2 = Real.pi * (n : ℝ) :=
      Real.sq_sqrt (by positivity)
    have hs_sq' :
        Real.sqrt ((n : ℝ) * Real.pi) ^ 2 = (n : ℝ) * Real.pi := by
      simpa [mul_comm] using hs_sq
    field_simp [hpi, hnpos.ne']
    nlinarith [hs_sq']
  have hsq :
      Tendsto
        (fun n : ℕ => (oddEvenRatio n / ratioModel n) ^ 2)
        atTop (𝓝 1) := by
    have h := hsquares.mul hmodels
    norm_num at h
    apply h.congr'
    filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
    unfold ratioModel squareModel
    have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
    have hnpos : 0 < (n : ℝ) := by positivity
    have hspos : 0 < Real.sqrt (Real.pi * (n : ℝ)) :=
      Real.sqrt_pos.2 (mul_pos Real.pi_pos hnpos)
    field_simp [hpi, hnpos.ne', hspos.ne']
  apply Asymptotics.isEquivalent_of_tendsto_one
  have hsqrt :
      Tendsto
        (fun n : ℕ => Real.sqrt ((oddEvenRatio n / ratioModel n) ^ 2))
        atTop (𝓝 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  apply hsqrt.congr'
  filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
  have hratio_nonneg : 0 ≤ oddEvenRatio n := by
    unfold oddEvenRatio
    exact div_nonneg (oddProduct_pos n).le (evenProduct_pos n).le
  have hmodel_pos : 0 < ratioModel n := by
    unfold ratioModel
    have hnpos : 0 < (n : ℝ) := by positivity
    exact one_div_pos.mpr (Real.sqrt_pos.2 (mul_pos Real.pi_pos hnpos))
  simp only [Pi.div_apply]
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (div_nonneg hratio_nonneg hmodel_pos.le)]

/-- Source: `proof_gap/exercise_3103/5.txt`. -/
theorem gap5 :
    Asymptotics.IsEquivalent atTop oddEvenRatio ratioModel := by
  exact gap4

end

end ProofGap.Exercise3103
