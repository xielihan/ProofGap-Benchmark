import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Polynomial

namespace ProofGap.Exercise2091
noncomputable section

def Family (U : Set ℝ) (f : ℝ → ℝ) :=
  {F : ℝ → ℝ | ∀ x ∈ U, HasDerivAt F (f x) x}
def Regular {l : ℕ} (U : Set ℝ) (pole : Fin l → ℝ) :=
  IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, ∀ i, x ≠ pole i
def Decomposes {l : ℕ} (R : ℝ → ℝ) (P : Polynomial ℝ)
    (pole : Fin l → ℝ) (mult : Fin l → ℕ)
    (A : (i : Fin l) → Fin (mult i) → ℝ) : Prop :=
  ∀ x, (∀ i, x ≠ pole i) →
    R x = P.eval x +
      ∑ i : Fin l, ∑ j : Fin (mult i),
        A i j / (x - pole i) ^ ((j : ℕ) + 1)
def mode (a c : ℝ) (j : ℕ) (x : ℝ) :=
  Real.exp (a * x) / (x - c) ^ j
def CombinedFamily {l : ℕ} (U : Set ℝ) (P : Polynomial ℝ) (a : ℝ)
    (pole : Fin l → ℝ) (mult : Fin l → ℕ)
    (A : (i : Fin l) → Fin (mult i) → ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U (fun x => P.eval x * Real.exp (a * x)),
    ∃ H : (i : Fin l) → (j : Fin (mult i)) → ℝ → ℝ,
    (∀ (i : Fin l) (j : Fin (mult i)),
      H i j ∈ Family U (mode a (pole i) ((j : ℕ) + 1))) ∧
      ∃ C, ∀ x ∈ U, F x = G x +
        ∑ i : Fin l, ∑ j : Fin (mult i), A i j * H i j x + C}
def shift (c t : ℝ) := c + t
def Pullback (φ : ℝ → ℝ) (V : Set ℝ) (A : Set (ℝ → ℝ)) :=
  {G : ℝ → ℝ | ∃ F ∈ A, ∀ t ∈ V, G t = F (φ t)}
def ShiftMode (a c : ℝ) (j : ℕ) (t : ℝ) :=
  Real.exp (a * (c + t)) / t ^ j
def ReductionFamily (V : Set ℝ) (a c : ℝ) (j : ℕ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family V (fun t => Real.exp (a * t) / t ^ (j - 1)),
    ∃ C, ∀ t ∈ V,
      F t = Real.exp (a * c) / (1 - (j : ℝ)) *
        Real.exp (a * t) / t ^ (j - 1) -
        a * Real.exp (a * c) / (1 - (j : ℝ)) * G t + C}
def PoleLiForm (U : Set ℝ) (a c : ℝ) (j : ℕ) :=
  {F : ℝ → ℝ |
    ∃ G ∈ Family U (mode a c 1), ∃ E : ℝ → ℝ,
    (∀ x ∈ U, F x = E x + G x) ∧
      ∀ x ∈ U, HasDerivAt E (mode a c j x - mode a c 1 x) x}
def FinalFamily {l : ℕ} (U : Set ℝ) (P : Polynomial ℝ) (a : ℝ)
    (pole : Fin l → ℝ) (mult : Fin l → ℕ)
    (A : (i : Fin l) → Fin (mult i) → ℝ) :=
  {F : ℝ → ℝ | ∃ G ∈ Family U (fun x => P.eval x * Real.exp (a * x)),
    ∃ H : (i : Fin l) → (j : Fin (mult i)) → ℝ → ℝ,
    (∀ (i : Fin l) (j : Fin (mult i)),
      H i j ∈ PoleLiForm U a (pole i) ((j : ℕ) + 1)) ∧
      ∃ C, ∀ x ∈ U, F x = G x +
        ∑ i : Fin l, ∑ j : Fin (mult i), A i j * H i j x + C}

private theorem family_nonempty_of_continuousOn (U : Set ℝ)
    (hU : IsOpen U) (hconn : IsPreconnected U) {f : ℝ → ℝ}
    (hf : ContinuousOn f U) : ∃ G, G ∈ Family U f := by
  by_cases hne : U.Nonempty
  · obtain ⟨x₀, hx₀⟩ := hne
    refine ⟨fun x => ∫ t in x₀..x, f t, ?_⟩
    intro x hx
    exact intervalIntegral.integral_hasDerivAt_right
      (hf.mono (hconn.ordConnected.uIcc_subset hx₀ hx)).intervalIntegrable
      (hf.stronglyMeasurableAtFilter hU x hx)
      (hf.continuousAt (hU.mem_nhds hx))
  · refine ⟨0, ?_⟩
    intro x hx
    exact (hne ⟨x, hx⟩).elim

private theorem exists_eq_add_on_of_same_deriv (U : Set ℝ)
    (hU : IsOpen U) (hconn : IsPreconnected U) {F G f : ℝ → ℝ}
    (hF : F ∈ Family U f) (hG : G ∈ Family U f) :
    ∃ C, ∀ x ∈ U, F x = G x + C := by
  apply hU.exists_eq_add_of_deriv_eq hconn
  · intro x hx
    exact (hF x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (hG x hx).differentiableAt.differentiableWithinAt
  · intro x hx
    exact (hF x hx).deriv.trans (hG x hx).deriv.symm

private theorem hasDerivAt_congr_on_open {U : Set ℝ} (hU : IsOpen U)
    {F G : ℝ → ℝ} {f x : ℝ} (hx : x ∈ U)
    (hFG : ∀ y ∈ U, F y = G y) (hG : HasDerivAt G f x) :
    HasDerivAt F f x := by
  apply hG.congr_of_eventuallyEq
  filter_upwards [hU.mem_nhds hx] with y hy
  exact hFG y hy

private theorem continuousOn_mode (U : Set ℝ) (a c : ℝ) (j : ℕ)
    (hc : ∀ x ∈ U, x ≠ c) : ContinuousOn (mode a c j) U := by
  intro x hx
  unfold mode
  simpa only [Function.comp_apply, id_eq] using ((Real.continuous_exp.continuousAt.comp
      (continuousAt_const.mul continuousAt_id)).div
    ((continuousAt_id.sub continuousAt_const).pow j)
    (pow_ne_zero j (sub_ne_zero.mpr (hc x hx)))).continuousWithinAt

private theorem hasDerivAt_one_div_pow (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 / s ^ n)
      (-(n : ℝ) / x ^ (n + 1)) x := by
  cases n with
  | zero => simpa using hasDerivAt_const x (1 : ℝ)
  | succ n =>
      have hd := (hasDerivAt_inv hx).pow (n + 1)
      convert hd using 1
      · funext y
        simp [Pi.pow_apply, ← inv_pow]
      · push_cast
        field_simp
        have hpow : x ^ n * x⁻¹ ^ n = 1 := by
          rw [← mul_pow, mul_inv_cancel₀ hx, one_pow]
        have hn : n + 1 + 1 = n + 2 := by omega
        rw [hn, pow_add]
        simp only [one_div]
        rw [show x ^ n * x ^ 2 * x⁻¹ ^ n = x ^ 2 by
          calc
            x ^ n * x ^ 2 * x⁻¹ ^ n = x ^ 2 * (x ^ n * x⁻¹ ^ n) := by ring
            _ = x ^ 2 := by rw [hpow, mul_one]]

private theorem hasDerivAt_one_div_pow_sub_one (j : ℕ) (hj : 1 ≤ j)
    {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun s : ℝ => 1 / s ^ (j - 1))
      ((1 - (j : ℝ)) / x ^ j) x := by
  convert hasDerivAt_one_div_pow (j - 1) hx using 1
  rw [Nat.sub_add_cancel hj, Nat.cast_sub hj]
  ring

private theorem family_eq_scaled_antiderivatives (U : Set ℝ)
    (hU : IsOpen U) (hconn : IsPreconnected U) {f g : ℝ → ℝ} (k : ℝ)
    (hkg : ∀ x ∈ U, k * g x = f x) (hg : ∃ G, G ∈ Family U g) :
    Family U f =
      {F : ℝ → ℝ | ∃ G ∈ Family U g,
        ∃ C, ∀ x ∈ U, F x = k * G x + C} := by
  ext F
  constructor
  · intro hF
    obtain ⟨G, hG⟩ := hg
    have hkG : (fun x => k * G x) ∈ Family U f := by
      intro x hx
      convert (hG x hx).const_mul k using 1
      exact (hkg x hx).symm
    obtain ⟨C, hC⟩ := exists_eq_add_on_of_same_deriv U hU hconn hF hkG
    exact ⟨G, hG, C, hC⟩
  · rintro ⟨G, hG, C, hC⟩
    intro x hx
    apply hasDerivAt_congr_on_open hU hx hC
    convert ((hG x hx).const_mul k).add_const C using 1
    exact (hkg x hx).symm

private theorem pullback_shift_family_of_isOpen (U : Set ℝ) (hU : IsOpen U)
    (a c : ℝ) (j : ℕ) :
    Pullback (shift c) {t | c + t ∈ U} (Family U (mode a c j)) =
      Family {t | c + t ∈ U} (ShiftMode a c j) := by
  have hV : IsOpen {t : ℝ | c + t ∈ U} :=
    hU.preimage (continuous_const.add continuous_id)
  ext G
  constructor
  · rintro ⟨F, hF, hEq⟩
    intro t ht
    have hshift : HasDerivAt (shift c) 1 t := by
      simpa [shift] using (hasDerivAt_const t c).add (hasDerivAt_id t)
    have hcomp : HasDerivAt (fun s => F (shift c s))
        (ShiftMode a c j t) t := by
      simpa [Function.comp_def, shift, mode, ShiftMode] using
        (hF (c + t) ht).comp t hshift
    exact hasDerivAt_congr_on_open hV ht hEq hcomp
  · intro hG
    refine ⟨fun x => G (x - c), ?_, ?_⟩
    · intro x hx
      have hxc : c + (x - c) ∈ U := by simpa using hx
      have hsub : HasDerivAt (fun y : ℝ => y - c) 1 x := by
        simpa using (hasDerivAt_id x).sub_const c
      simpa [Function.comp_def, mode, ShiftMode] using
        (hG (x - c) hxc).comp x hsub
    · intro t ht
      simp [shift]

theorem gap1 {l : ℕ} (R : ℝ → ℝ) (P : Polynomial ℝ)
    (pole : Fin l → ℝ) (mult : Fin l → ℕ)
    (A : (i : Fin l) → Fin (mult i) → ℝ)
    (h : Decomposes R P pole mult A) :
    ∀ x, (∀ i, x ≠ pole i) →
      R x = P.eval x + ∑ i : Fin l, ∑ j : Fin (mult i),
        A i j / (x - pole i) ^ ((j : ℕ) + 1) := by
  exact h
theorem gap2 {l : ℕ} (U : Set ℝ) (R : ℝ → ℝ) (P : Polynomial ℝ)
    (a : ℝ) (pole : Fin l → ℝ) (mult : Fin l → ℕ)
    (A : (i : Fin l) → Fin (mult i) → ℝ)
    (hR : Regular U pole) (h : Decomposes R P pole mult A) :
    Family U (fun x => R x * Real.exp (a * x)) =
      CombinedFamily U P a pole mult A := by
  obtain ⟨G, hG_univ⟩ := family_nonempty_of_continuousOn Set.univ isOpen_univ
    isPreconnected_univ
    ((P.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn)
  have hG : G ∈ Family U (fun x => P.eval x * Real.exp (a * x)) := by
    intro x hx
    exact hG_univ x (Set.mem_univ x)
  have hmodes : ∀ (i : Fin l) (j : Fin (mult i)),
      ∃ H, H ∈ Family U (mode a (pole i) ((j : ℕ) + 1)) := by
    intro i j
    exact family_nonempty_of_continuousOn U hR.1 hR.2.1
      (continuousOn_mode U a (pole i) ((j : ℕ) + 1)
        (fun x hx => hR.2.2 x hx i))
  choose H hH using hmodes
  have hderiv (G' : ℝ → ℝ)
      (H' : (i : Fin l) → (j : Fin (mult i)) → ℝ → ℝ)
      (hG' : G' ∈ Family U (fun x => P.eval x * Real.exp (a * x)))
      (hH' : ∀ (i : Fin l) (j : Fin (mult i)),
        H' i j ∈ Family U (mode a (pole i) ((j : ℕ) + 1))) :
      ∀ x ∈ U, HasDerivAt
        (fun y => G' y +
          ∑ i : Fin l, ∑ j : Fin (mult i), A i j * H' i j y)
        (R x * Real.exp (a * x)) x := by
    intro x hx
    have hs : HasDerivAt
        (fun y => ∑ i : Fin l, ∑ j : Fin (mult i), A i j * H' i j y)
        (∑ i : Fin l, ∑ j : Fin (mult i),
          A i j * mode a (pole i) ((j : ℕ) + 1) x) x := by
      apply HasDerivAt.fun_sum
      intro i hi
      apply HasDerivAt.fun_sum
      intro j hj
      exact (hH' i j x hx).const_mul (A i j)
    have hadd := (hG' x hx).add hs
    convert hadd using 1
    rw [h x (fun i => hR.2.2 x hx i)]
    simp only [add_mul, Finset.sum_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    unfold mode
    ring
  ext F
  constructor
  · intro hF
    obtain ⟨C, hC⟩ := exists_eq_add_on_of_same_deriv U hR.1 hR.2.1
      hF (hderiv G H hG hH)
    exact ⟨G, hG, H, hH, C, hC⟩
  · rintro ⟨G', hG', H', hH', C, hC⟩
    intro x hx
    exact hasDerivAt_congr_on_open hR.1 hx hC
      ((hderiv G' H' hG' hH' x hx).add_const C)
theorem gap3 (U : Set ℝ) (P : Polynomial ℝ) (a : ℝ) :
    ∃ G, G ∈ Family U (fun x => P.eval x * Real.exp (a * x)) := by
  obtain ⟨G, hG⟩ := family_nonempty_of_continuousOn Set.univ isOpen_univ
    isPreconnected_univ
    ((P.continuous.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn)
  refine ⟨G, ?_⟩
  intro x hx
  exact hG x (Set.mem_univ x)
theorem gap4 (U : Set ℝ) (a c : ℝ) (j : ℕ) (hU : IsOpen U) :
    Pullback (shift c) {t | c + t ∈ U} (Family U (mode a c j)) =
      Family {t | c + t ∈ U} (ShiftMode a c j) := by
  exact pullback_shift_family_of_isOpen U hU a c j
theorem gap5 (V : Set ℝ) (a c : ℝ) (j : ℕ) (hj : 2 ≤ j)
    (hV : IsOpen V ∧ IsPreconnected V ∧ ∀ t ∈ V, t ≠ 0) :
    Family V (ShiftMode a c j) =
      {F : ℝ → ℝ | ∃ G ∈ Family V
        (fun t => Real.exp (a * t) * deriv (fun s => 1 / s ^ (j - 1)) t),
        ∃ C, ∀ t ∈ V, F t = Real.exp (a * c) / (1 - (j : ℝ)) * G t + C} := by
  have hj1 : 1 ≤ j := by omega
  have hden : (1 - (j : ℝ)) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast (show (1 : ℕ) ≠ j by omega)
  have hderiv (t : ℝ) (ht : t ∈ V) :
      deriv (fun s : ℝ => 1 / s ^ (j - 1)) t =
        (1 - (j : ℝ)) / t ^ j :=
    (hasDerivAt_one_div_pow_sub_one j hj1 (hV.2.2 t ht)).deriv
  have hq0_cont : ContinuousOn
      (fun t : ℝ => (1 - (j : ℝ)) * Real.exp (a * t) / t ^ j) V := by
    intro t ht
    simpa only [Function.comp_apply, id_eq] using
      (((continuousAt_const.mul (Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul continuousAt_id))).div
        (continuousAt_id.pow j) (pow_ne_zero j (hV.2.2 t ht))).continuousWithinAt)
  obtain ⟨G, hG0⟩ := family_nonempty_of_continuousOn V hV.1 hV.2.1 hq0_cont
  have hG : G ∈ Family V
      (fun t => Real.exp (a * t) * deriv (fun s => 1 / s ^ (j - 1)) t) := by
    intro t ht
    convert hG0 t ht using 1
    change Real.exp (a * t) * deriv (fun s : ℝ => 1 / s ^ (j - 1)) t =
      (1 - (j : ℝ)) * Real.exp (a * t) / t ^ j
    rw [hderiv t ht]
    ring
  apply family_eq_scaled_antiderivatives V hV.1 hV.2.1
    (Real.exp (a * c) / (1 - (j : ℝ)))
  · intro t ht
    rw [hderiv t ht]
    unfold ShiftMode
    rw [show a * (c + t) = a * c + a * t by ring, Real.exp_add]
    field_simp [hden, hV.2.2 t ht]
    <;> ring
  · exact ⟨G, hG⟩
theorem gap6 (V : Set ℝ) (a c : ℝ) (j : ℕ) (hj : 2 ≤ j)
    (hV : IsOpen V ∧ IsPreconnected V ∧ ∀ t ∈ V, t ≠ 0) :
    Family V (ShiftMode a c j) = ReductionFamily V a c j := by
  rw [gap5 V a c j hj hV]
  have hj1 : 1 ≤ j := by omega
  have hr_cont : ContinuousOn
      (fun t : ℝ => Real.exp (a * t) / t ^ (j - 1)) V := by
    intro t ht
    simpa only [Function.comp_apply, id_eq] using
      ((Real.continuous_exp.continuousAt.comp
        (continuousAt_const.mul continuousAt_id)).div
        (continuousAt_id.pow (j - 1))
        (pow_ne_zero (j - 1) (hV.2.2 t ht))).continuousWithinAt
  obtain ⟨G₀, hG₀⟩ :=
    family_nonempty_of_continuousOn V hV.1 hV.2.1 hr_cont
  have hparts (G : ℝ → ℝ)
      (hG : G ∈ Family V (fun t => Real.exp (a * t) / t ^ (j - 1))) :
      (fun t => Real.exp (a * t) / t ^ (j - 1) - a * G t) ∈
        Family V
          (fun t => Real.exp (a * t) *
            deriv (fun s => 1 / s ^ (j - 1)) t) := by
    intro t ht
    have hinv := hasDerivAt_one_div_pow_sub_one j hj1 (hV.2.2 t ht)
    have hexp : HasDerivAt (fun s : ℝ => Real.exp (a * s))
        (Real.exp (a * t) * a) t := by
      simpa only [id_eq, mul_one] using ((hasDerivAt_id t).const_mul a).exp
    have hcalc := (hexp.mul hinv).sub ((hG t ht).const_mul a)
    convert hcalc using 1
    · funext s
      simp only [Pi.sub_apply, Pi.mul_apply]
      ring
    · change Real.exp (a * t) * deriv (fun s : ℝ => 1 / s ^ (j - 1)) t =
        Real.exp (a * t) * a * (1 / t ^ (j - 1)) +
          Real.exp (a * t) * ((1 - (j : ℝ)) / t ^ j) -
          a * (Real.exp (a * t) / t ^ (j - 1))
      rw [hinv.deriv]
      ring
  ext F
  constructor
  · rintro ⟨Q, hQ, C, hF⟩
    obtain ⟨D, hD⟩ := exists_eq_add_on_of_same_deriv V hV.1 hV.2.1
      hQ (hparts G₀ hG₀)
    refine ⟨G₀, hG₀,
      Real.exp (a * c) / (1 - (j : ℝ)) * D + C, ?_⟩
    intro t ht
    rw [hF t ht, hD t ht]
    ring
  · rintro ⟨G, hG, C, hF⟩
    refine ⟨fun t => Real.exp (a * t) / t ^ (j - 1) - a * G t,
      hparts G hG, C, ?_⟩
    intro t ht
    rw [hF t ht]
    ring
theorem gap7 (U : Set ℝ) (a c : ℝ) (j : ℕ) (hj : 2 ≤ j)
    (hU : IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, x ≠ c) :
    Pullback (shift c) {t | c + t ∈ U} (Family U (mode a c j)) =
      ReductionFamily {t | c + t ∈ U} a c j := by
  let V : Set ℝ := {t | c + t ∈ U}
  have hVopen : IsOpen V := by
    exact hU.1.preimage (continuous_const.add continuous_id)
  have hVconn : IsPreconnected V := by
    have hImage : V = (fun x : ℝ => x - c) '' U := by
      ext t
      constructor
      · intro ht
        exact ⟨c + t, ht, by ring⟩
      · rintro ⟨x, hx, rfl⟩
        change c + (x - c) ∈ U
        simpa using hx
    rw [hImage]
    exact hU.2.1.image (fun x : ℝ => x - c)
      (continuous_id.sub continuous_const).continuousOn
  have hVzero : ∀ t ∈ V, t ≠ 0 := by
    intro t ht ht0
    apply hU.2.2 (c + t) ht
    rw [ht0, add_zero]
  calc
    Pullback (shift c) {t | c + t ∈ U} (Family U (mode a c j)) =
        Family V (ShiftMode a c j) :=
      pullback_shift_family_of_isOpen U hU.1 a c j
    _ = ReductionFamily V a c j :=
      gap6 V a c j hj ⟨hVopen, hVconn, hVzero⟩
theorem gap8 (U : Set ℝ) (a c : ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hU : IsOpen U ∧ IsPreconnected U ∧ ∀ x ∈ U, x ≠ c) :
    Family U (mode a c j) = PoleLiForm U a c j := by
  ext F
  constructor
  · intro hF
    obtain ⟨G, hG⟩ := family_nonempty_of_continuousOn U hU.1 hU.2.1
      (continuousOn_mode U a c 1 hU.2.2)
    refine ⟨G, hG, fun x => F x - G x, ?_, ?_⟩
    · intro x hx
      ring
    · intro x hx
      exact (hF x hx).sub (hG x hx)
  · rintro ⟨G, hG, E, hEq, hE⟩
    intro x hx
    apply hasDerivAt_congr_on_open hU.1 hx hEq
    convert (hE x hx).add (hG x hx) using 1 <;> ring
theorem gap9 {l : ℕ} (U : Set ℝ) (R : ℝ → ℝ) (P : Polynomial ℝ)
    (a : ℝ) (pole : Fin l → ℝ) (mult : Fin l → ℕ)
    (A : (i : Fin l) → Fin (mult i) → ℝ)
    (hR : Regular U pole) (h : Decomposes R P pole mult A) :
    Family U (fun x => R x * Real.exp (a * x)) =
      FinalFamily U P a pole mult A := by
  rw [gap2 U R P a pole mult A hR h]
  ext F
  constructor
  · rintro ⟨G, hG, H, hH, C, hC⟩
    refine ⟨G, hG, H, ?_, C, hC⟩
    intro i j
    rw [← gap8 U a (pole i) ((j : ℕ) + 1)
      (Nat.succ_le_succ (Nat.zero_le _))
      ⟨hR.1, hR.2.1, fun x hx => hR.2.2 x hx i⟩]
    exact hH i j
  · rintro ⟨G, hG, H, hH, C, hC⟩
    refine ⟨G, hG, H, ?_, C, hC⟩
    intro i j
    rw [gap8 U a (pole i) ((j : ℕ) + 1)
      (Nat.succ_le_succ (Nat.zero_le _))
      ⟨hR.1, hR.2.1, fun x hx => hR.2.2 x hx i⟩]
    exact hH i j
theorem gap10 {l : ℕ} (U : Set ℝ) (R : ℝ → ℝ) (P : Polynomial ℝ)
    (a : ℝ) (pole : Fin l → ℝ) (mult : Fin l → ℕ)
    (A : (i : Fin l) → Fin (mult i) → ℝ)
    (hR : Regular U pole) (h : Decomposes R P pole mult A) :
    Family U (fun x => R x * Real.exp (a * x)) =
      FinalFamily U P a pole mult A := by
  exact gap9 U R P a pole mult A hR h

end
end ProofGap.Exercise2091
