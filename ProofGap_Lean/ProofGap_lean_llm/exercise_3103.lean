import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology Asymptotics
open Filter

namespace Exercise3103

noncomputable def oddEvenRatio (n : ℕ) : ℝ :=
  ((Finset.range n).prod (fun i => (2 * (i + 1) - 1 : ℝ))) /
    ((Finset.range n).prod (fun i => (2 * (i + 1) : ℝ)))

noncomputable def wallisTerm (k : ℕ) : ℝ :=
  ((2 * (k + 1) : ℝ) / (2 * (k + 1) - 1 : ℝ)) *
    ((2 * (k + 1) : ℝ) / (2 * (k + 1) + 1 : ℝ))

-- exercise: exercise_3103

theorem proof_gap_exercise_3103_1 :
    HasProd wallisTerm (Real.pi / 2) := by
  sorry

theorem proof_gap_exercise_3103_2
    (h1 : HasProd wallisTerm (Real.pi / 2)) :
    Tendsto
      (fun n : ℕ =>
        (((Finset.range n).prod (fun i => (2 * (i + 1) : ℝ))) /
            ((Finset.range n).prod (fun i => (2 * (i + 1) - 1 : ℝ)))) ^ (2 : ℕ) *
          (1 / (2 * n + 1 : ℝ)))
      atTop (𝓝 (Real.pi / 2)) := by
  sorry

theorem proof_gap_exercise_3103_3
    (h1 : HasProd wallisTerm (Real.pi / 2))
    (h2 :
      Tendsto
        (fun n : ℕ =>
          (((Finset.range n).prod (fun i => (2 * (i + 1) : ℝ))) /
              ((Finset.range n).prod (fun i => (2 * (i + 1) - 1 : ℝ)))) ^ (2 : ℕ) *
            (1 / (2 * n + 1 : ℝ)))
        atTop (𝓝 (Real.pi / 2))) :
    (fun n : ℕ => (oddEvenRatio n) ^ (2 : ℕ)) ~[atTop]
      (fun n : ℕ => 2 / (Real.pi * (2 * n + 1 : ℝ))) := by
  sorry

theorem proof_gap_exercise_3103_4
    (h1 : HasProd wallisTerm (Real.pi / 2))
    (h2 :
      Tendsto
        (fun n : ℕ =>
          (((Finset.range n).prod (fun i => (2 * (i + 1) : ℝ))) /
              ((Finset.range n).prod (fun i => (2 * (i + 1) - 1 : ℝ)))) ^ (2 : ℕ) *
            (1 / (2 * n + 1 : ℝ)))
        atTop (𝓝 (Real.pi / 2)))
    (h3 : (fun n : ℕ => (oddEvenRatio n) ^ (2 : ℕ)) ~[atTop]
      (fun n : ℕ => 2 / (Real.pi * (2 * n + 1 : ℝ)))) :
    (fun n : ℕ => oddEvenRatio n) ~[atTop]
      (fun n : ℕ => Real.sqrt (2 / (Real.pi * (2 * n + 1 : ℝ)))) := by
  sorry

theorem proof_gap_exercise_3103_5
    (h1 : HasProd wallisTerm (Real.pi / 2))
    (h2 :
      Tendsto
        (fun n : ℕ =>
          (((Finset.range n).prod (fun i => (2 * (i + 1) : ℝ))) /
              ((Finset.range n).prod (fun i => (2 * (i + 1) - 1 : ℝ)))) ^ (2 : ℕ) *
            (1 / (2 * n + 1 : ℝ)))
        atTop (𝓝 (Real.pi / 2)))
    (h3 : (fun n : ℕ => (oddEvenRatio n) ^ (2 : ℕ)) ~[atTop]
      (fun n : ℕ => 2 / (Real.pi * (2 * n + 1 : ℝ))))
    (h4 : (fun n : ℕ => oddEvenRatio n) ~[atTop]
      (fun n : ℕ => Real.sqrt (2 / (Real.pi * (2 * n + 1 : ℝ))))) :
    (fun n : ℕ => Real.sqrt (2 / (Real.pi * (2 * n + 1 : ℝ)))) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (Real.pi * n)) := by
  sorry

theorem proof_gap_exercise_3103_6
    (h1 : HasProd wallisTerm (Real.pi / 2))
    (h2 :
      Tendsto
        (fun n : ℕ =>
          (((Finset.range n).prod (fun i => (2 * (i + 1) : ℝ))) /
              ((Finset.range n).prod (fun i => (2 * (i + 1) - 1 : ℝ)))) ^ (2 : ℕ) *
            (1 / (2 * n + 1 : ℝ)))
        atTop (𝓝 (Real.pi / 2)))
    (h3 : (fun n : ℕ => (oddEvenRatio n) ^ (2 : ℕ)) ~[atTop]
      (fun n : ℕ => 2 / (Real.pi * (2 * n + 1 : ℝ))))
    (h4 : (fun n : ℕ => oddEvenRatio n) ~[atTop]
      (fun n : ℕ => Real.sqrt (2 / (Real.pi * (2 * n + 1 : ℝ)))))
    (h5 : (fun n : ℕ => Real.sqrt (2 / (Real.pi * (2 * n + 1 : ℝ)))) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (Real.pi * n))) :
    (fun n : ℕ => oddEvenRatio n) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (Real.pi * n)) := by
  sorry

theorem proof_gap_exercise_3103_7
    (h1 : HasProd wallisTerm (Real.pi / 2))
    (h2 :
      Tendsto
        (fun n : ℕ =>
          (((Finset.range n).prod (fun i => (2 * (i + 1) : ℝ))) /
              ((Finset.range n).prod (fun i => (2 * (i + 1) - 1 : ℝ)))) ^ (2 : ℕ) *
            (1 / (2 * n + 1 : ℝ)))
        atTop (𝓝 (Real.pi / 2)))
    (h3 : (fun n : ℕ => (oddEvenRatio n) ^ (2 : ℕ)) ~[atTop]
      (fun n : ℕ => 2 / (Real.pi * (2 * n + 1 : ℝ))))
    (h4 : (fun n : ℕ => oddEvenRatio n) ~[atTop]
      (fun n : ℕ => Real.sqrt (2 / (Real.pi * (2 * n + 1 : ℝ)))))
    (h5 : (fun n : ℕ => Real.sqrt (2 / (Real.pi * (2 * n + 1 : ℝ)))) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (Real.pi * n)))
    (h6 : (fun n : ℕ => oddEvenRatio n) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (Real.pi * n))) :
    (fun n : ℕ => oddEvenRatio n) ~[atTop]
      (fun n : ℕ => 1 / Real.sqrt (Real.pi * n)) := by
  sorry

end Exercise3103
