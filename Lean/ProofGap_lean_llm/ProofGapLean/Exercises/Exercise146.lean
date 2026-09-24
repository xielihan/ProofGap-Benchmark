import ProofGapLean.Prelude.Analysis
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Filter Topology

namespace ProofGap.Exercise146

noncomputable section

def harmonic (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n, (1 : ℝ) / i
def eulerSeq (n : ℕ) : ℝ := harmonic n - Real.log n

private theorem harmonic_succ_local (n : ℕ) :
    harmonic (n + 1) = harmonic n + 1 / (n + 1 : ℝ) := by
  unfold harmonic
  rw [show Finset.Icc 1 (n + 1) =
    insert (n + 1) (Finset.Icc 1 n) by
      ext i
      simp
      omega]
  simp [add_comm]

private theorem harmonic_eq_mathlib (n : ℕ) :
    harmonic n = (↑(_root_.harmonic n) : ℝ) := by
  induction n with
  | zero => simp [harmonic]
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl, _root_.harmonic_succ]
      rw [show Nat.succ n = n + 1 by omega, harmonic_succ_local, ih]
      push_cast
      norm_num [Rat.cast_inv, Rat.cast_natCast]

/-- Source: `proof_gap/exercise_146/1.txt`; n must be positive. -/
theorem gap1 : ∀ n : ℕ, 0 < n →
    Real.log (1 + 1 / (n : ℝ)) < 1 / (n : ℝ) := by
  intro n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have h := Real.log_lt_sub_one_of_pos
    (show 0 < (1 + 1 / (n : ℝ)) by positivity)
    (show (1 + 1 / (n : ℝ)) ≠ 1 by
      exact ne_of_gt (lt_add_of_pos_right 1 (by positivity)))
  convert h using 1 <;> ring

/-- Source: `proof_gap/exercise_146/2.txt`; n must be positive. -/
theorem gap2 : ∀ n : ℕ, 0 < n →
    Real.log (n + 1) - Real.log n < 1 / (n : ℝ) := by
  intro n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [← Real.log_div (by positivity) (by positivity)]
  convert gap1 n hn using 1
  field_simp

/-- Source: `proof_gap/exercise_146/3.txt`. -/
theorem gap3 : ∀ k : ℕ, 0 < k →
    Real.log (k + 1) - Real.log k < 1 / (k : ℝ) := by
  exact gap2

/-- Source: `proof_gap/exercise_146/4.txt`; n must be positive. -/
theorem gap4 : ∀ n : ℕ, 0 < n → Real.log (n + 1) < harmonic n := by
  intro n hn
  induction n using Nat.case_strong_induction_on with
  | hz => omega
  | hi n ih =>
      by_cases hn0 : n = 0
      · subst n
        norm_num [harmonic]
        have h := gap1 1 (by omega)
        norm_num at h
        exact h
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
        have hprev := ih n (by omega) hnpos
        have hstep := gap3 (n + 1) (by omega)
        rw [harmonic_succ_local]
        norm_num [Nat.cast_add, Nat.cast_one] at hstep ⊢
        linarith

/-- Source: `proof_gap/exercise_146/5.txt`. -/
theorem gap5 : ∀ n : ℕ, 0 < n →
    eulerSeq (n + 1) = harmonic n + 1 / (n + 1 : ℝ) - Real.log (n + 1) := by
  intro n _
  rw [eulerSeq, harmonic_succ_local]
  norm_num [Nat.cast_add, Nat.cast_one]

/-- Source: `proof_gap/exercise_146/6.txt`. -/
theorem gap6 : ∀ n : ℕ, 0 < n →
    harmonic n + 1 / (n + 1 : ℝ) - Real.log (n + 1) > 1 / (n + 1 : ℝ) := by
  intro n hn
  linarith [gap4 n hn]

/-- Source: `proof_gap/exercise_146/7.txt`. -/
theorem gap7 : ∀ n : ℕ, 0 < 1 / (n + 1 : ℝ) := by
  intro n
  positivity

/-- Source: `proof_gap/exercise_146/8.txt`. -/
theorem gap8 : ∀ n : ℕ, 0 < n → 0 < eulerSeq (n + 1) := by
  intro n hn
  rw [gap5 n hn]
  exact lt_trans (gap7 n) (gap6 n hn)

/-- Source: `proof_gap/exercise_146/9.txt`. -/
theorem gap9 : BddBelow (Set.range eulerSeq) := by
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  cases n with
  | zero => simp [eulerSeq, harmonic]
  | succ n =>
      cases n with
      | zero => norm_num [eulerSeq, harmonic]
      | succ n => exact (gap8 (n + 1) (by omega)).le

/-- Source: `proof_gap/exercise_146/10.txt`; n must be positive. -/
theorem gap10 : ∀ n : ℕ, 0 < n →
    eulerSeq n - eulerSeq (n + 1) =
      -1 / (n + 1 : ℝ) + Real.log (n + 1) - Real.log n := by
  intro n _
  rw [eulerSeq, eulerSeq, harmonic_succ_local]
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

/-- Source: `proof_gap/exercise_146/11.txt`; n must be positive. -/
theorem gap11 : ∀ n : ℕ, 0 < n →
    -1 / (n + 1 : ℝ) + Real.log (n + 1) - Real.log n =
      Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
  intro n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  rw [show -1 / (n + 1 : ℝ) + Real.log (n + 1) - Real.log n =
    (Real.log (n + 1) - Real.log n) - 1 / (n + 1 : ℝ) by ring]
  rw [← Real.log_div (by positivity) (by positivity)]
  congr 1
  field_simp

/-- Source: `proof_gap/exercise_146/12.txt`. -/
theorem gap12 : ∀ n : ℕ, 0 < n →
    eulerSeq n - eulerSeq (n + 1) =
      Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
  intro n hn
  rw [gap10 n hn, gap11 n hn]

/-- Source: `proof_gap/exercise_146/13.txt`; n must be positive. -/
theorem gap13 : ∀ n : ℕ, 0 < n →
    1 / (n + 1 : ℝ) < Real.log (1 + 1 / (n : ℝ)) := by
  intro n hn
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hratio_pos : 0 < (n : ℝ) / (n + 1 : ℝ) := by positivity
  have hratio_ne : (n : ℝ) / (n + 1 : ℝ) ≠ 1 := by
    apply ne_of_lt
    apply (div_lt_one (by positivity)).2
    norm_num
  have h := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
  have hlog :
      Real.log ((n : ℝ) / (n + 1 : ℝ)) =
        -Real.log (1 + 1 / (n : ℝ)) := by
    rw [show (n : ℝ) / (n + 1 : ℝ) =
      (1 + 1 / (n : ℝ))⁻¹ by
        field_simp
        ]
    exact Real.log_inv _
  rw [hlog] at h
  have halg :
      (n : ℝ) / (n + 1 : ℝ) - 1 = -1 / (n + 1 : ℝ) := by
    field_simp
    ring
  rw [halg] at h
  have h' :
      -Real.log (1 + 1 / (n : ℝ)) < -(1 / (n + 1 : ℝ)) := by
    simpa only [neg_div] using h
  exact neg_lt_neg_iff.mp h'

/-- Source: `proof_gap/exercise_146/14.txt`. -/
theorem gap14 : ∀ n : ℕ, 0 < n → 0 < eulerSeq n - eulerSeq (n + 1) := by
  intro n hn
  rw [gap12 n hn]
  linarith [gap13 n hn]

/-- Source: `proof_gap/exercise_146/15.txt`; monotonicity holds on the positive-index tail. -/
theorem gap15 : Antitone (fun n => eulerSeq (n + 1)) := by
  apply antitone_nat_of_succ_le
  intro n
  have h := gap14 (n + 1) (by omega)
  norm_num [Nat.add_assoc] at h ⊢
  linarith

/-- Source: `proof_gap/exercise_146/16.txt`. -/
theorem gap16 : ProofGap.ConvergentSeq eulerSeq := by
  refine ⟨Real.eulerMascheroniConstant, ?_⟩
  apply Real.tendsto_harmonic_sub_log.congr'
  filter_upwards with n
  simp only [eulerSeq, harmonic_eq_mathlib]

/-- Source: `proof_gap/exercise_146/17.txt`. -/
theorem gap17 :
    ∃ C : ℝ, Tendsto eulerSeq atTop (𝓝 C) := by
  exact gap16

private theorem expDecimalLower :
    Real.exp (2.3025848 : ℝ) < 10 := by
  rw [show (2.3025848 : ℝ) = 1 + 1 + 0.3025848 by norm_num,
    Real.exp_add, Real.exp_add]
  have he := Real.exp_one_lt_d9
  have hb := Real.exp_bound (x := (0.3025848 : ℝ)) (n := 12)
    (by norm_num) (by norm_num)
  have hu := (abs_sub_le_iff.mp hb).1
  norm_num [Finset.sum_range_succ, Nat.factorial] at hu
  have hu' : Real.exp (0.3025848 : ℝ) ≤
      (22183175078422573772205245580823096914261708154524521027962359522174855961471331 /
        16391277313232421875000000000000000000000000000000000000000000000000000000000000 : ℝ) := by
    convert hu using 1 <;> norm_num
  calc
    Real.exp 1 * Real.exp 1 * Real.exp 0.3025848
        < 2.7182818286 * 2.7182818286 * Real.exp 0.3025848 := by
          gcongr
    _ ≤ 2.7182818286 * 2.7182818286 *
        (22183175078422573772205245580823096914261708154524521027962359522174855961471331 /
          16391277313232421875000000000000000000000000000000000000000000000000000000000000) := by
          gcongr
    _ < 10 := by norm_num

private theorem expDecimalUpper :
    10 < Real.exp (2.3025852 : ℝ) := by
  rw [show (2.3025852 : ℝ) = 1 + 1 + 0.3025852 by norm_num,
    Real.exp_add, Real.exp_add]
  have he := Real.exp_one_gt_d9
  have hl := Real.sum_le_exp_of_nonneg (x := (0.3025852 : ℝ)) (by norm_num) 12
  norm_num [Finset.sum_range_succ, Nat.factorial] at hl
  have hl' :
      (1287973406782535778506548490048802757912532431943043982917960709993343394743087 /
        951690673828125000000000000000000000000000000000000000000000000000000000000000 : ℝ) ≤
          Real.exp (0.3025852 : ℝ) := by
    convert hl using 1 <;> norm_num
  calc
    10 < 2.7182818283 * 2.7182818283 *
        (1287973406782535778506548490048802757912532431943043982917960709993343394743087 /
          951690673828125000000000000000000000000000000000000000000000000000000000000000) := by
            norm_num
    _ ≤ Real.exp 1 * Real.exp 1 *
        (1287973406782535778506548490048802757912532431943043982917960709993343394743087 /
          951690673828125000000000000000000000000000000000000000000000000000000000000000) := by
            gcongr
    _ ≤ Real.exp 1 * Real.exp 1 * Real.exp 0.3025852 := by
            gcongr

private theorem logPadeUpper {x : ℝ} (hx : 1 < x) :
    Real.log x < (x - x⁻¹) / 2 := by
  let f : ℝ → ℝ := fun y => (y - y⁻¹) / 2 - Real.log y
  have hf : StrictMonoOn f (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · dsimp [f]
      exact ((continuousOn_id.sub
        (continuousOn_id.inv₀ (fun y hy hy0 => by
          have hy' : 1 ≤ y := hy
          simp only [id_eq] at hy0
          linarith))).div_const 2).sub
          (Real.continuousOn_log.mono (by
            intro y hy
            have hy' : 1 ≤ y := hy
            simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
            linarith))
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : 1 < y := hy
      have hy0 : y ≠ 0 := by linarith
      have hd : HasDerivAt f (((1 + y⁻¹ ^ 2) / 2) - y⁻¹) y := by
        dsimp [f]
        convert (((hasDerivAt_id y).sub (hasDerivAt_inv hy0)).div_const 2).sub
          (Real.hasDerivAt_log hy0) using 1 <;> ring
      rw [hd.deriv]
      field_simp [hy0]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hy')]
  have h := hf (by simp) (by simp [hx.le]) hx
  simpa [f] using h

private theorem logPadeLower {x : ℝ} (hx : 1 < x) :
    2 * (x - 1) / (x + 1) < Real.log x := by
  let f : ℝ → ℝ := fun y => Real.log y - (y - 1) / (y + 1) * 2
  have hf : StrictMonoOn f (Set.Ici 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 1)
    · dsimp [f]
      have hlog := Real.continuousOn_log.mono (by
        intro y hy
        have hy' : 1 ≤ y := hy
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        linarith : Set.Ici (1 : ℝ) ⊆ {0}ᶜ)
      have hid : ContinuousOn (fun y : ℝ => y) (Set.Ici 1) := continuousOn_id
      have hone : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Set.Ici 1) :=
        continuousOn_const
      have hquot := (hid.sub hone).div (hid.add hone) (fun y hy => by
        have hy' : 1 ≤ y := hy
        simp only [Pi.add_apply]
        linarith)
      exact hlog.sub (hquot.mul_const 2)
    · intro y hy
      rw [interior_Ici] at hy
      have hy' : 1 < y := hy
      have hy0 : y ≠ 0 := by linarith
      have hy1 : y + 1 ≠ 0 := by linarith
      have hd : HasDerivAt f
          (y⁻¹ - (((y + 1) - (y - 1)) / (y + 1) ^ 2) * 2) y := by
        dsimp [f]
        convert (Real.hasDerivAt_log hy0).sub
          (((hasDerivAt_id y).sub_const 1).div
            ((hasDerivAt_id y).add_const 1) hy1 |>.mul_const 2) using 1 <;>
              simp [id] <;> ring
      rw [hd.deriv]
      field_simp [hy0, hy1]
      nlinarith [sq_pos_of_pos (sub_pos.mpr hy')]
  have h := hf (by simp) (by simp [hx.le]) hx
  dsimp [f] at h
  norm_num at h
  rw [show 2 * (x - 1) / (x + 1) = (x - 1) / (x + 1) * 2 by ring]
  linarith

private theorem eulerDifferenceUpper (n : ℕ) (hn : 0 < n) :
    Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) <
      1 / (2 * (n : ℝ) * (n + 1 : ℝ)) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) / n := by
    rw [one_lt_div hn']
    norm_num
  have h := logPadeUpper hx
  rw [show (((n + 1 : ℕ) : ℝ) / n) =
    1 + 1 / (n : ℝ) by
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp] at h
  have hinv :
      (1 + 1 / (n : ℝ))⁻¹ = (n : ℝ) / (n + 1 : ℝ) := by
    field_simp
  rw [hinv] at h
  field_simp at h ⊢
  nlinarith

private theorem eulerDifferenceLower (n : ℕ) (hn : 0 < n) :
    1 / (2 * (n + 1 : ℝ) * (n + 2 : ℝ)) <
      Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
  have hn' : 0 < (n : ℝ) := by exact_mod_cast hn
  have hx : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) / n := by
    rw [one_lt_div hn']
    norm_num
  have h := logPadeLower hx
  rw [show (((n + 1 : ℕ) : ℝ) / n) =
    1 + 1 / (n : ℝ) by
      norm_num [Nat.cast_add, Nat.cast_one]
      field_simp] at h
  field_simp at h ⊢
  have hm := mul_lt_mul_of_pos_left h
    (show 0 < 2 * ((n : ℝ) + 2) * ((n : ℝ) + 1) by positivity)
  nlinarith

private noncomputable def mathlibEulerSeq (n : ℕ) : ℝ :=
  (↑(_root_.harmonic n) : ℝ) - Real.log n

private theorem mathlibEulerDiff (n : ℕ) (hn : 0 < n) :
    mathlibEulerSeq n - mathlibEulerSeq (n + 1) =
      Real.log (1 + 1 / (n : ℝ)) - 1 / (n + 1 : ℝ) := by
  rw [mathlibEulerSeq, mathlibEulerSeq, _root_.harmonic_succ]
  push_cast
  norm_num [Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one]
  rw [show
    (↑(_root_.harmonic n) : ℝ) - Real.log n -
      ((↑(_root_.harmonic n) : ℝ) + ((n : ℝ) + 1)⁻¹ -
        Real.log ((n : ℝ) + 1)) =
      (Real.log ((n : ℝ) + 1) - Real.log n) - ((n : ℝ) + 1)⁻¹ by ring]
  rw [show Real.log ((n : ℝ) + 1) - Real.log n =
    Real.log (1 + 1 / (n : ℝ)) by
      rw [← Real.log_div (by positivity) (by positivity)]
      congr 1
      field_simp]
  ring

private noncomputable def lowerCorrected (n : ℕ) : ℝ :=
  mathlibEulerSeq (n + 1) - 1 / (2 * ((n + 1 : ℕ) : ℝ))

private noncomputable def upperCorrected (n : ℕ) : ℝ :=
  mathlibEulerSeq (n + 1) - 1 / (2 * ((n + 2 : ℕ) : ℝ))

private theorem strictMonoLowerCorrected : StrictMono lowerCorrected := by
  apply strictMono_nat_of_lt_succ
  intro n
  have hd := eulerDifferenceUpper (n + 1) (by omega)
  rw [← mathlibEulerDiff (n + 1) (by omega)] at hd
  dsimp [lowerCorrected]
  norm_num [Nat.cast_add, Nat.cast_one] at hd ⊢
  field_simp at hd ⊢
  nlinarith

private theorem strictAntiUpperCorrected : StrictAnti upperCorrected := by
  apply strictAnti_nat_of_succ_lt
  intro n
  have hd := eulerDifferenceLower (n + 1) (by omega)
  rw [← mathlibEulerDiff (n + 1) (by omega)] at hd
  dsimp [upperCorrected]
  norm_num [Nat.cast_add, Nat.cast_one] at hd ⊢
  field_simp at hd ⊢
  nlinarith

private theorem tendstoLowerCorrected :
    Tendsto lowerCorrected atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hE : Tendsto (fun n : ℕ => mathlibEulerSeq (n + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    exact Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hi0 : Tendsto (fun n : ℕ => 1 / (2 * ((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 1)
    have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    convert hc.mul h using 1
    · funext n
      norm_num [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    · norm_num
  have hs := hE.sub hi0
  rw [sub_zero] at hs
  apply hs.congr'
  filter_upwards with n
  dsimp [lowerCorrected]

private theorem tendstoUpperCorrected :
    Tendsto upperCorrected atTop (𝓝 Real.eulerMascheroniConstant) := by
  have hE : Tendsto (fun n : ℕ => mathlibEulerSeq (n + 1)) atTop
      (𝓝 Real.eulerMascheroniConstant) := by
    exact Real.tendsto_harmonic_sub_log.comp (tendsto_add_atTop_nat 1)
  have hi0 : Tendsto (fun n : ℕ => 1 / (2 * ((n + 2 : ℕ) : ℝ)))
      atTop (𝓝 0) := by
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (tendsto_add_atTop_nat 2)
    have hc : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2 : ℝ)) :=
      tendsto_const_nhds
    convert hc.mul h using 1
    · funext n
      norm_num [Function.comp_apply, Nat.cast_add, Nat.cast_one]
      ring
    · norm_num
  have hs := hE.sub hi0
  rw [sub_zero] at hs
  apply hs.congr'
  filter_upwards with n
  dsimp [upperCorrected]

private theorem lowerCorrected_lt_gamma (n : ℕ) :
    lowerCorrected n < Real.eulerMascheroniConstant := by
  exact (strictMonoLowerCorrected (Nat.lt_succ_self n)).trans_le
    (strictMonoLowerCorrected.monotone.ge_of_tendsto tendstoLowerCorrected (n + 1))

private theorem gamma_lt_upperCorrected (n : ℕ) :
    Real.eulerMascheroniConstant < upperCorrected n := by
  exact (strictAntiUpperCorrected.antitone.le_of_tendsto
    tendstoUpperCorrected (n + 1)).trans_lt
      (strictAntiUpperCorrected (Nat.lt_succ_self n))

private theorem logTenBounds :
    (2.3025848 : ℝ) < Real.log 10 ∧ Real.log 10 < (2.3025852 : ℝ) := by
  exact ⟨(Real.lt_log_iff_exp_lt (by norm_num)).2 expDecimalLower,
    (Real.log_lt_iff_lt_exp (by norm_num)).2 expDecimalUpper⟩

private theorem logThousandBounds :
    (6.9077544 : ℝ) < Real.log 1000 ∧
      Real.log 1000 < (6.9077556 : ℝ) := by
  have hlog : Real.log (1000 : ℝ) = 3 * Real.log 10 := by
    rw [show (1000 : ℝ) = 10 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog]
  constructor <;> nlinarith [logTenBounds.1, logTenBounds.2]

set_option maxRecDepth 100000 in
private theorem gammaDecimal :
    |Real.eulerMascheroniConstant - 0.577216| < (0.000001 : ℝ) := by
  rw [abs_lt]
  constructor
  · have hgamma := lowerCorrected_lt_gamma 999
    have hq : (74854706 / 10000000 : ℚ) < _root_.harmonic 1000 := by
      native_decide
    have hqR : (74854706 / 10000000 : ℝ) <
        (↑(_root_.harmonic 1000) : ℝ) := by
      convert (Rat.cast_lt (K := ℝ)).2 hq using 1 <;> norm_num
    have hrat :
        (0.577215 : ℝ) <
          (↑(_root_.harmonic 1000) : ℝ) - 6.9077556 - 1 / 2000 := by
      nlinarith [hqR]
    dsimp only [lowerCorrected, mathlibEulerSeq] at hgamma
    norm_num only [Nat.cast_ofNat] at hgamma
    nlinarith [logThousandBounds.2]
  · have hgamma := gamma_lt_upperCorrected 999
    have hq : _root_.harmonic 1000 <
        (577217 / 1000000 + 69077544 / 10000000 + 1 / 2002 : ℚ) := by
      native_decide
    have hqR : (↑(_root_.harmonic 1000) : ℝ) <
        (577217 / 1000000 + 69077544 / 10000000 + 1 / 2002 : ℝ) := by
      convert (Rat.cast_lt (K := ℝ)).2 hq using 1 <;> norm_num
    have hrat :
        (↑(_root_.harmonic 1000) : ℝ) - 6.9077544 - 1 / 2002 <
          (0.577217 : ℝ) := by
      nlinarith [hqR]
    dsimp only [upperCorrected, mathlibEulerSeq] at hgamma
    norm_num only [Nat.cast_ofNat] at hgamma
    nlinarith [logThousandBounds.1]

/-- Source: `proof_gap/exercise_146/18.txt`; formalize the displayed decimal approximation. -/
theorem gap18 (C : ℝ) (hC : Tendsto eulerSeq atTop (𝓝 C)) :
    |C - 0.577216| < 0.000001 := by
  have hgamma : Tendsto eulerSeq atTop (𝓝 Real.eulerMascheroniConstant) :=
    by
      apply Real.tendsto_harmonic_sub_log.congr'
      filter_upwards with n
      simp only [eulerSeq, harmonic_eq_mathlib]
  have hCeq : C = Real.eulerMascheroniConstant :=
    tendsto_nhds_unique hC hgamma
  rw [hCeq]
  exact gammaDecimal

/-- Source: `proof_gap/exercise_146/19.txt`; n=0 is excluded from log n. -/
theorem gap19 (C : ℝ) (hC : Tendsto eulerSeq atTop (𝓝 C)) :
    ∃ ε : ℕ → ℝ, ∀ n : ℕ, 0 < n →
      harmonic n = C + Real.log n + ε n := by
  refine ⟨fun n => eulerSeq n - C, ?_⟩
  intro n _
  simp only [eulerSeq]
  ring

/-- Source: `proof_gap/exercise_146/20.txt`; retain the same expansion witness. -/
theorem gap20 (C : ℝ) (hC : Tendsto eulerSeq atTop (𝓝 C)) :
    ∃ ε : ℕ → ℝ,
      (∀ n : ℕ, 0 < n → harmonic n = C + Real.log n + ε n) ∧
      Tendsto ε atTop (𝓝 0) := by
  refine ⟨fun n => eulerSeq n - C, ?_, ?_⟩
  · intro n _
    simp only [eulerSeq]
    ring
  · convert hC.sub tendsto_const_nhds using 1 <;> simp

/-- Source: `proof_gap/exercise_146/21.txt`. -/
theorem gap21 : ProofGap.ConvergentSeq eulerSeq := by
  exact gap16

end

end ProofGap.Exercise146
