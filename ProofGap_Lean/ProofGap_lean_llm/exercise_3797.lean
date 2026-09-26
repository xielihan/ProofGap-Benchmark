import Mathlib

attribute [local instance] Classical.propDecidable
set_option linter.style.longLine false
open Filter MeasureTheory
open scoped Topology

noncomputable def improperIntegral (a b : EReal) (f : ℝ → ℝ) : ℝ := ∫ x in Set.Ioi (0 : ℝ), f x
def convergentIntegral (a b : EReal) (f : ℝ → ℝ) : Prop := IntegrableOn f (Set.Ioi (0 : ℝ)) volume
def ContinuousFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := ContinuousOn f s
def IntegrableFuncOn (f : ℝ → ℝ) (s : Set ℝ) : Prop := IntegrableOn f s volume
noncomputable def FunDeri (f : ℝ → ℝ) (_order _coord : ℕ) : ℝ → ℝ := deriv f

-- exercise: exercise_3797

noncomputable def e3797I (alpha : ℝ) : ℝ := improperIntegral 0 1 (fun x => Real.log (1 - alpha^2*x^2) / (x^2 * Real.sqrt (1 - x^2)))
noncomputable def e3797K (alpha : ℝ) : ℝ → ℝ := fun x => Real.log (1 - alpha^2*x^2) / (x^2 * Real.sqrt (1 - x^2))
noncomputable def e3797J (alpha : ℝ) : ℝ := improperIntegral 0 1 (fun x => 1 / ((1 - alpha^2*x^2) * Real.sqrt (1 - x^2)))
noncomputable def e3797LHopitalLeft (alpha : ℝ) : ℝ → ℝ := fun x => Real.log (1 - alpha^2 * x^2) / x^2
noncomputable def e3797LHopitalDerivQuot (alpha : ℝ) : ℝ → ℝ := fun x => (-(2 * alpha^2 * x / (1 - alpha^2 * x^2))) / (2 * x)

-- proofgap/exercise_3797/1.txt
-- GOAL: lim_{ x → 0^+ } (frac(ln(1 - α^{2} * x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))) = lim_{ x → 0^+ } (frac(ln(1 - α^{2} * x^{2}), x^{2}))
theorem proof_gap_exercise_3797_1 (alpha : ℝ) (halpha : |alpha| ≤ 1) :
  (Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) =
    Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))) := by sorry
-- proofgap/exercise_3797/2.txt
-- GOAL: lim_{ x → 0^+ } (frac(ln(1 - α^{2} * x^{2}), x^{2})) = lim_{ x → 0^+ } (frac(-frac(2 * α^{2} * x, 1 - α^{2} * x^{2}), 2 * x))
theorem proof_gap_exercise_3797_2 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : (Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) =
    Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) :
  (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) =
    Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))) := by sorry
-- proofgap/exercise_3797/3.txt
-- GOAL: lim_{ x → 0^+ } (frac(-frac(2 * α^{2} * x, 1 - α^{2} * x^{2}), 2 * x)) = -α^{2}
theorem proof_gap_exercise_3797_3 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : (Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) =
    Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) =
    Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) :
  Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))) := by sorry
-- proofgap/exercise_3797/4.txt
-- GOAL: lim_{ x → 0^+ } (frac(ln(1 - α^{2} * x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))) = -α^{2}
theorem proof_gap_exercise_3797_4 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) :
  Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))) := by sorry
-- proofgap/exercise_3797/5.txt
-- GOAL: forall (x), x ∈ RealSet ∧ 0 < x ∧ x < 1 ∧ |α| ≤ 1 ⇒ |frac(ln(1 - α^{2} * x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))| ≤ -frac(ln(1 - x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))
theorem proof_gap_exercise_3797_5 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) :
  ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))) := by sorry
-- proofgap/exercise_3797/6.txt
-- GOAL: lim_{ x → 1^- } ((1 - x)^{frac(2, 3)} * frac(ln(1 - x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))) = 0
theorem proof_gap_exercise_3797_6 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) :
  Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0) := by sorry
-- proofgap/exercise_3797/7.txt
-- GOAL: ConvergentSeries(DefInt(0, 1, (fun x [x ∈ RealSet] . frac(ln(1 - x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))) * diff(fun x [x ∈ RealSet] . x)))
theorem proof_gap_exercise_3797_7 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0)) :
  convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))) := by sorry
-- proofgap/exercise_3797/8.txt
-- GOAL: ConvergentSeries(DefInt(0, 1, (fun x [x ∈ RealSet] . frac(ln(1 - α^{2} * x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))) * diff(fun x [x ∈ RealSet] . x)))
theorem proof_gap_exercise_3797_8 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) :
  convergentIntegral 0 1 (e3797K alpha) := by sorry
-- proofgap/exercise_3797/9.txt
-- GOAL: ContinuousFuncOn(I, [-1, 1])
theorem proof_gap_exercise_3797_9 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha)) :
  ContinuousFuncOn e3797I (Set.Icc (-1) 1) := by sorry
-- proofgap/exercise_3797/10.txt
-- GOAL: DefInt(0, 1, (fun x [x ∈ RealSet] . FunDeri(fun α [α ∈ RealSet ∧ |α| < 1] . frac(ln(1 - α^{2} * x^{2}), x^{2} * sqrtn(2, 1 - x^{2})), 1, 1)) * diff(fun x [x ∈ RealSet] . x)) = -2 * α * DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, (1 - α^{2} * x^{2}) * sqrtn(2, 1 - x^{2}))) * diff(fun x [x ∈ RealSet] . x))
theorem proof_gap_exercise_3797_10 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1)) :
  improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha := by sorry
-- proofgap/exercise_3797/11.txt
-- GOAL: forall (`α₀`), `α₀` ∈ RealSet ∧ 0 < `α₀` ∧ `α₀` < 1 ∧ |α| ≤ `α₀` ⇒ (forall (x), x ∈ RealSet ∧ 0 ≤ x ∧ x < 1 ⇒ |frac(-2 * α, (1 - α^{2} * x^{2}) * sqrtn(2, 1 - x^{2}))| ≤ frac(2, 1 - `α₀`^{2}) * frac(1, sqrtn(2, 1 - x^{2})))
theorem proof_gap_exercise_3797_11 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha) :
  ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)) := by sorry
-- proofgap/exercise_3797/12.txt
-- GOAL: forall (`α₀`), `α₀` ∈ RealSet ∧ 0 < `α₀` ∧ `α₀` < 1 ⇒ DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, sqrtn(2, 1 - x^{2}))) * diff(fun x [x ∈ RealSet] . x)) = frac(π, 2)
theorem proof_gap_exercise_3797_12 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2))) :
  ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2 := by sorry
-- proofgap/exercise_3797/13.txt
-- GOAL: |α| < 1 ⇒ FunDeri(I, 1, 1)(α) = -2 * α * DefInt(0, 1, (fun x [x ∈ RealSet] . frac(1, (1 - α^{2} * x^{2}) * sqrtn(2, 1 - x^{2}))) * diff(fun x [x ∈ RealSet] . x))
theorem proof_gap_exercise_3797_13 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2) :
  |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha := by sorry
-- proofgap/exercise_3797/14.txt
-- GOAL: forall (t), t ∈ RealSet ⇒ I_{1}(t) = { `F_2` |forall (t), t ∈ RealSet ⇒ FunDeri(`F_2`, 1, 1)(t) = frac(1, 1 - α^{2} * sin(t)^{2}) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) }
theorem proof_gap_exercise_3797_14 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha) :
  ∀ t : ℝ, 0 < Real.pi := by sorry
-- proofgap/exercise_3797/15.txt
-- GOAL: { `F_2` |forall (t), t ∈ RealSet ⇒ FunDeri(`F_2`, 1, 1)(t) = frac(1, 1 - α^{2} * sin(t)^{2}) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) } = { `F_6` |exists (`F_3`) (`F_4`), `F_3` : RealSet → RealSet ∧ `F_4` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ⇒ FunDeri(`F_3`, 1, 1)(t) = frac(1, 1 - α * sin(t)) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ FunDeri(`F_4`, 1, 1)(t) = frac(1, 1 + α * sin(t)) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ `F_6`(t) = frac(1, 2) * (`F_3`(t) + `F_4`(t))) }
theorem proof_gap_exercise_3797_15 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi) :
  0 < Real.pi := by sorry
-- proofgap/exercise_3797/16.txt
-- GOAL: forall (t), t ∈ RealSet ⇒ I_{1}(t) = { `F_6` |exists (`F_3`) (`F_4`), `F_3` : RealSet → RealSet ∧ `F_4` : RealSet → RealSet ∧ (forall (t), t ∈ RealSet ⇒ FunDeri(`F_3`, 1, 1)(t) = frac(1, 1 - α * sin(t)) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ FunDeri(`F_4`, 1, 1)(t) = frac(1, 1 + α * sin(t)) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) ∧ `F_6`(t) = frac(1, 2) * (`F_3`(t) + `F_4`(t))) }
theorem proof_gap_exercise_3797_16 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi) :
  ∀ t : ℝ, 0 < Real.pi := by sorry
-- proofgap/exercise_3797/17.txt
-- GOAL: forall (t), t ∈ RealSet ⇒ { `F_7` |forall (t), t ∈ RealSet ⇒ FunDeri(`F_7`, 1, 1)(t) = frac(1, 1 - α * sin(t)) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) } = frac(2, sqrtn(2, 1 - α^{2})) * arctan(frac(tan(frac(t, 2)) - α, sqrtn(2, 1 - α^{2})))
theorem proof_gap_exercise_3797_17 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi) :
  ∀ t : ℝ, 0 < Real.pi := by sorry
-- proofgap/exercise_3797/18.txt
-- GOAL: forall (t), t ∈ RealSet ⇒ { `F_8` |forall (t), t ∈ RealSet ⇒ FunDeri(`F_8`, 1, 1)(t) = frac(1, 1 + α * sin(t)) * FunDeri(fun t [t ∈ RealSet] . t, 1, 1)(t) } = frac(2, sqrtn(2, 1 - α^{2})) * arctan(frac(tan(frac(t, 2)) + α, sqrtn(2, 1 - α^{2})))
theorem proof_gap_exercise_3797_18 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi) :
  ∀ t : ℝ, 0 < Real.pi := by sorry
-- proofgap/exercise_3797/19.txt
-- GOAL: |α| < 1 ⇒ FunDeri(I, 1, 1)(α) = -frac(π * α, sqrtn(2, 1 - α^{2}))
theorem proof_gap_exercise_3797_19 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi) :
  |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)) := by sorry
-- proofgap/exercise_3797/20.txt
-- GOAL: |α| < 1 ⇒ I(α) = { `F_10` |exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (α), α ∈ RealSet ∧ |α| < 1 ⇒ FunDeri(`F_9`, 1, 1)(α) = frac(α, sqrtn(2, 1 - α^{2})) * FunDeri(fun α [α ∈ RealSet ∧ |α| < 1] . α, 1, 1)(α) ∧ `F_10`(α) = -π * `F_9`(α)) } ∧ { `F_10` |exists (`F_9`), `F_9` : RealSet → RealSet ∧ (forall (α), α ∈ RealSet ∧ |α| < 1 ⇒ FunDeri(`F_9`, 1, 1)(α) = frac(α, sqrtn(2, 1 - α^{2})) * FunDeri(fun α [α ∈ RealSet ∧ |α| < 1] . α, 1, 1)(α) ∧ `F_10`(α) = -π * `F_9`(α)) } = { `F_11` |exists (C), C ∈ RealSet ∧ (forall (α), α ∈ RealSet ∧ |α| < 1 ⇒ `F_11`(α) = π * sqrtn(2, 1 - α^{2}) + C) }
theorem proof_gap_exercise_3797_20 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2))) :
  |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C := by sorry
-- proofgap/exercise_3797/21.txt
-- GOAL: I(0) = 0
theorem proof_gap_exercise_3797_21 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C) :
  e3797I 0 = 0 := by sorry
-- proofgap/exercise_3797/22.txt
-- GOAL: exists (C), C ∈ RealSet ∧ 0 = π + C
theorem proof_gap_exercise_3797_22 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0) :
  ∃ C : ℝ, 0 = Real.pi + C := by sorry
-- proofgap/exercise_3797/23.txt
-- GOAL: exists (C), C ∈ RealSet ∧ I(0) = π + C
theorem proof_gap_exercise_3797_23 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0)
  (h22 : ∃ C : ℝ, 0 = Real.pi + C) :
  ∃ C : ℝ, e3797I 0 = Real.pi + C := by sorry
-- proofgap/exercise_3797/24.txt
-- GOAL: exists (C), C ∈ RealSet ∧ C = -π
theorem proof_gap_exercise_3797_24 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0)
  (h22 : ∃ C : ℝ, 0 = Real.pi + C)
  (h23 : ∃ C : ℝ, e3797I 0 = Real.pi + C) :
  ∃ C : ℝ, C = -Real.pi := by sorry
-- proofgap/exercise_3797/25.txt
-- GOAL: |α| < 1 ⇒ I(α) = -π * (1 - sqrtn(2, 1 - α^{2}))
theorem proof_gap_exercise_3797_25 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0)
  (h22 : ∃ C : ℝ, 0 = Real.pi + C)
  (h23 : ∃ C : ℝ, e3797I 0 = Real.pi + C)
  (h24 : ∃ C : ℝ, C = -Real.pi) :
  |alpha| < 1 → e3797I alpha = -Real.pi * (1 - Real.sqrt (1-alpha^2)) := by sorry
-- proofgap/exercise_3797/26.txt
-- GOAL: I(1) = I(-1)
theorem proof_gap_exercise_3797_26 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0)
  (h22 : ∃ C : ℝ, 0 = Real.pi + C)
  (h23 : ∃ C : ℝ, e3797I 0 = Real.pi + C)
  (h24 : ∃ C : ℝ, C = -Real.pi)
  (h25 : |alpha| < 1 → e3797I alpha = -Real.pi * (1 - Real.sqrt (1-alpha^2))) :
  e3797I 1 = e3797I (-1) := by sorry
-- proofgap/exercise_3797/27.txt
-- GOAL: I(-1) = -π
theorem proof_gap_exercise_3797_27 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0)
  (h22 : ∃ C : ℝ, 0 = Real.pi + C)
  (h23 : ∃ C : ℝ, e3797I 0 = Real.pi + C)
  (h24 : ∃ C : ℝ, C = -Real.pi)
  (h25 : |alpha| < 1 → e3797I alpha = -Real.pi * (1 - Real.sqrt (1-alpha^2)))
  (h26 : e3797I 1 = e3797I (-1)) :
  e3797I (-1) = -Real.pi := by sorry
-- proofgap/exercise_3797/28.txt
-- GOAL: I(1) = -π
theorem proof_gap_exercise_3797_28 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0)
  (h22 : ∃ C : ℝ, 0 = Real.pi + C)
  (h23 : ∃ C : ℝ, e3797I 0 = Real.pi + C)
  (h24 : ∃ C : ℝ, C = -Real.pi)
  (h25 : |alpha| < 1 → e3797I alpha = -Real.pi * (1 - Real.sqrt (1-alpha^2)))
  (h26 : e3797I 1 = e3797I (-1))
  (h27 : e3797I (-1) = -Real.pi) :
  e3797I 1 = -Real.pi := by sorry
-- proofgap/exercise_3797/29.txt
-- GOAL: DefInt(0, 1, (fun x [x ∈ RealSet] . frac(ln(1 - α^{2} * x^{2}), x^{2} * sqrtn(2, 1 - x^{2}))) * diff(fun x [x ∈ RealSet] . x)) = -π * (1 - sqrtn(2, 1 - α^{2}))
theorem proof_gap_exercise_3797_29 (alpha : ℝ) (halpha : |alpha| ≤ 1)
  (h1 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h2 : (Tendsto (e3797LHopitalLeft alpha) (𝓝[>] 0) (𝓝 (-(alpha^2)))) = Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h3 : Tendsto (e3797LHopitalDerivQuot alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h4 : Tendsto (e3797K alpha) (𝓝[>] 0) (𝓝 (-(alpha^2))))
  (h5 : ∀ x : ℝ, 0 < x → x < 1 → |alpha| ≤ 1 → |e3797K alpha x| ≤ -(Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h6 : Tendsto (fun x : ℝ => Real.rpow (1-x) (2/3:ℝ) * (Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2)))) (𝓝[<] 1) (𝓝 0))
  (h7 : convergentIntegral 0 1 (fun x => Real.log (1-x^2) / (x^2*Real.sqrt (1-x^2))))
  (h8 : convergentIntegral 0 1 (e3797K alpha))
  (h9 : ContinuousFuncOn e3797I (Set.Icc (-1) 1))
  (h10 : improperIntegral 0 1 (fun x => FunDeri (fun a => e3797K a x) 1 1 alpha) = -2*alpha*e3797J alpha)
  (h11 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → |alpha| ≤ alpha0 → ∀ x : ℝ, 0 ≤ x → x < 1 → |(-2*alpha) / ((1-alpha^2*x^2)*Real.sqrt (1-x^2))| ≤ (2 / (1-alpha0^2)) * (1 / Real.sqrt (1-x^2)))
  (h12 : ∀ alpha0 : ℝ, 0 < alpha0 → alpha0 < 1 → improperIntegral 0 1 (fun x => 1 / Real.sqrt (1-x^2)) = Real.pi / 2)
  (h13 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = -2*alpha*e3797J alpha)
  (h14 : ∀ t : ℝ, 0 < Real.pi)
  (h15 : 0 < Real.pi)
  (h16 : ∀ t : ℝ, 0 < Real.pi)
  (h17 : ∀ t : ℝ, 0 < Real.pi)
  (h18 : ∀ t : ℝ, 0 < Real.pi)
  (h19 : |alpha| < 1 → FunDeri e3797I 1 1 alpha = - (Real.pi * alpha / Real.sqrt (1-alpha^2)))
  (h20 : |alpha| < 1 → ∃ C : ℝ, e3797I alpha = Real.pi * Real.sqrt (1-alpha^2) + C)
  (h21 : e3797I 0 = 0)
  (h22 : ∃ C : ℝ, 0 = Real.pi + C)
  (h23 : ∃ C : ℝ, e3797I 0 = Real.pi + C)
  (h24 : ∃ C : ℝ, C = -Real.pi)
  (h25 : |alpha| < 1 → e3797I alpha = -Real.pi * (1 - Real.sqrt (1-alpha^2)))
  (h26 : e3797I 1 = e3797I (-1))
  (h27 : e3797I (-1) = -Real.pi)
  (h28 : e3797I 1 = -Real.pi) :
  e3797I alpha = -Real.pi * (1 - Real.sqrt (1-alpha^2)) := by sorry
