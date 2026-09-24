import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Defs.Filter
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

namespace ProofGap.Exercise3225

noncomputable section

def radiusSq (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 + z ^ 2

def powThreeHalves (x y z : ℝ) : ℝ :=
  Real.rpow (radiusSq x y z) (3 / 2 : ℝ)

def powFiveHalves (x y z : ℝ) : ℝ :=
  Real.rpow (radiusSq x y z) (5 / 2 : ℝ)

def u (x y z : ℝ) : ℝ :=
  1 / Real.sqrt (radiusSq x y z)

def partialX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f t y z) x

def partialY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x t z) y

def partialZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => f x y t) z

def secondXX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f t y z) x

def secondYY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x t z) y

def secondZZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f x y t) z

def mixedXY (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialX f x t z) y

def mixedYZ (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialY f x y t) z

def mixedZX (f : ℝ → ℝ → ℝ → ℝ) (x y z : ℝ) : ℝ :=
  deriv (fun t => partialZ f t y z) x

private lemma exercise3225_hasDerivAt_square (a : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ 2) (2 * a) a := by
  simpa [id_eq, mul_comm] using ((hasDerivAt_id a).pow 2)

private lemma exercise3225_rpow_one_of_pos (a : ℝ) (ha : 0 < a) :
    Real.rpow a (1 : ℝ) = a := by
  calc
    Real.rpow a (1 : ℝ) =
        Real.exp (Real.log a * (1 : ℝ)) := by
      exact Real.rpow_def_of_pos ha (1 : ℝ)
    _ = a := by
      simpa using (Real.exp_log ha)

theorem gap1 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      partialX u x y z = -(x / powThreeHalves x y z) := by
  intro x y z h
  unfold partialX u
  have hq : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    simpa [radiusSq] using h
  have hs : 0 < Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := Real.sqrt_pos.2 hq
  have hd : HasDerivAt (fun t : ℝ => t ^ 2 + y ^ 2 + z ^ 2) (2 * x) x := by
    have hd' : HasDerivAt (fun t : ℝ => t ^ 2 + (y ^ 2 + z ^ 2))
        (2 * x) x :=
      (exercise3225_hasDerivAt_square x).add_const (y ^ 2 + z ^ 2)
    convert hd' using 1
    funext t
    ring
  have hr := (Real.hasDerivAt_sqrt (ne_of_gt hq)).comp x hd
  have hi := (hasDerivAt_const x (1 : ℝ)).div hr (ne_of_gt hs)
  change deriv ((fun _ : ℝ => (1 : ℝ)) /
      ((fun q : ℝ => Real.sqrt q) ∘
        (fun t : ℝ => t ^ 2 + y ^ 2 + z ^ 2))) x = _
  rw [hi.deriv]
  unfold powThreeHalves radiusSq
  have hpow : Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) (3 / 2 : ℝ) =
      (x ^ 2 + y ^ 2 + z ^ 2) * Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
    calc
      Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) (3 / 2 : ℝ) =
          Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) (1 + 1 / 2 : ℝ) := by
            congr 1 <;> norm_num
      _ = Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) (1 : ℝ) *
          Real.rpow (x ^ 2 + y ^ 2 + z ^ 2) (1 / 2 : ℝ) := by
            exact Real.rpow_add hq (1 : ℝ) (1 / 2 : ℝ)
      _ = (x ^ 2 + y ^ 2 + z ^ 2) *
          Real.sqrt (x ^ 2 + y ^ 2 + z ^ 2) := by
            rw [exercise3225_rpow_one_of_pos
              (x ^ 2 + y ^ 2 + z ^ 2) hq]
            congr 1
            exact (Real.sqrt_eq_rpow (x ^ 2 + y ^ 2 + z ^ 2)).symm
  rw [hpow]
  simp only [Function.comp_apply, zero_mul, one_mul]
  field_simp [ne_of_gt hq, ne_of_gt hs]
  rw [Real.sq_sqrt hq.le] <;> ring

theorem gap2 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      partialY u x y z = -(y / powThreeHalves x y z) := by
  intro x y z h
  have hsym : partialY u x y z = partialX u y x z := by
    unfold partialY partialX
    apply congrArg (fun f : ℝ → ℝ => deriv f y)
    funext t
    unfold u
    apply congrArg (fun q : ℝ => 1 / Real.sqrt q)
    unfold radiusSq
    ring
  have hpos : 0 < radiusSq y x z := by
    simpa [radiusSq, add_comm, add_left_comm, add_assoc] using h
  have hp : powThreeHalves y x z = powThreeHalves x y z := by
    unfold powThreeHalves
    apply congrArg (fun q : ℝ => Real.rpow q (3 / 2 : ℝ))
    unfold radiusSq
    ring
  rw [hsym, gap1 y x z hpos, hp]

theorem gap3 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      partialZ u x y z = -(z / powThreeHalves x y z) := by
  intro x y z h
  have hsym : partialZ u x y z = partialX u z y x := by
    unfold partialZ partialX
    apply congrArg (fun f : ℝ → ℝ => deriv f z)
    funext t
    unfold u
    apply congrArg (fun q : ℝ => 1 / Real.sqrt q)
    unfold radiusSq
    ring
  have hpos : 0 < radiusSq z y x := by
    simpa [radiusSq, add_comm, add_left_comm, add_assoc] using h
  have hp : powThreeHalves z y x = powThreeHalves x y z := by
    unfold powThreeHalves
    apply congrArg (fun q : ℝ => Real.rpow q (3 / 2 : ℝ))
    unfold radiusSq
    ring
  rw [hsym, gap1 z y x hpos, hp]

theorem gap4 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      secondXX u x y z =
        -(1 / powThreeHalves x y z) +
          3 * x ^ 2 / powFiveHalves x y z := by
  intro x y z h
  unfold secondXX
  have hlocal : ∀ᶠ t in nhds x, 0 < radiusSq t y z := by
    have hc : Continuous (fun t : ℝ => radiusSq t y z) := by
      unfold radiusSq
      fun_prop
    exact hc.continuousAt.eventually (isOpen_Ioi.mem_nhds h)
  have heq : (fun t => partialX u t y z) =ᶠ[nhds x]
      (fun t => (-t) / powThreeHalves t y z) :=
    hlocal.mono (fun t ht => by simpa [neg_div] using gap1 t y z ht)
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hdq : HasDerivAt (fun t : ℝ => radiusSq t y z) (2 * x) x := by
    have hd' : HasDerivAt (fun t : ℝ => t ^ 2 + (y ^ 2 + z ^ 2))
        (2 * x) x :=
      (exercise3225_hasDerivAt_square x).add_const (y ^ 2 + z ^ 2)
    convert hd' using 1
    funext t
    unfold radiusSq
    ring
  have hp : HasDerivAt (fun t : ℝ => powThreeHalves t y z)
      (3 * x * Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) x := by
    unfold powThreeHalves
    convert (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
      (Or.inl (ne_of_gt h))).comp x hdq using 1 <;> norm_num <;> ring
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) x := (hasDerivAt_id x).neg
  have hden : powThreeHalves x y z ≠ 0 := by
    unfold powThreeHalves
    exact ne_of_gt (Real.rpow_pos_of_pos h _)
  have hd := hn.div hp hden
  change deriv ((fun t : ℝ => -t) / (fun t : ℝ => powThreeHalves t y z)) x = _
  rw [hd.deriv]
  unfold powThreeHalves powFiveHalves
  have hr3 : Real.rpow (radiusSq x y z) (3 / 2 : ℝ) =
      radiusSq x y z * Real.rpow (radiusSq x y z) (1 / 2 : ℝ) := by
    calc
      Real.rpow (radiusSq x y z) (3 / 2 : ℝ) =
          Real.rpow (radiusSq x y z) (1 + 1 / 2 : ℝ) := by
            congr 1 <;> norm_num
      _ = Real.rpow (radiusSq x y z) (1 : ℝ) *
          Real.rpow (radiusSq x y z) (1 / 2 : ℝ) := by
            exact Real.rpow_add h (1 : ℝ) (1 / 2 : ℝ)
      _ = radiusSq x y z * Real.rpow (radiusSq x y z) (1 / 2 : ℝ) := by
            rw [exercise3225_rpow_one_of_pos (radiusSq x y z) h]
  have hr5 : Real.rpow (radiusSq x y z) (5 / 2 : ℝ) =
      radiusSq x y z * (radiusSq x y z *
        Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) := by
    calc
      Real.rpow (radiusSq x y z) (5 / 2 : ℝ) =
          Real.rpow (radiusSq x y z) (1 + 3 / 2 : ℝ) := by
            congr 1 <;> norm_num
      _ = Real.rpow (radiusSq x y z) (1 : ℝ) *
          Real.rpow (radiusSq x y z) (3 / 2 : ℝ) := by
            exact Real.rpow_add h (1 : ℝ) (3 / 2 : ℝ)
      _ = radiusSq x y z * (radiusSq x y z *
          Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) := by
            rw [exercise3225_rpow_one_of_pos (radiusSq x y z) h, hr3]
  have hs : (Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) ^ 2 =
      radiusSq x y z := by
    calc
      (Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) ^ 2 =
          (Real.sqrt (radiusSq x y z)) ^ 2 := by
            congr 1
            exact (Real.sqrt_eq_rpow (radiusSq x y z)).symm
      _ = radiusSq x y z := Real.sq_sqrt h.le
  rw [hr3, hr5]
  field_simp [ne_of_gt h, ne_of_gt (Real.rpow_pos_of_pos h (1 / 2 : ℝ))] <;>
    nlinarith [hs]

theorem gap5 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      -(1 / powThreeHalves x y z) +
          3 * x ^ 2 / powFiveHalves x y z =
        (2 * x ^ 2 - y ^ 2 - z ^ 2) / powFiveHalves x y z := by
  intro x y z h
  have h3 : powThreeHalves x y z ≠ 0 := by
    unfold powThreeHalves
    exact ne_of_gt (Real.rpow_pos_of_pos h _)
  have hr : powFiveHalves x y z = radiusSq x y z * powThreeHalves x y z := by
    unfold powFiveHalves powThreeHalves
    calc
      Real.rpow (radiusSq x y z) (5 / 2 : ℝ) =
          Real.rpow (radiusSq x y z) (1 + 3 / 2 : ℝ) := by
            congr 1 <;> norm_num
      _ = Real.rpow (radiusSq x y z) (1 : ℝ) *
          Real.rpow (radiusSq x y z) (3 / 2 : ℝ) := by
            exact Real.rpow_add h (1 : ℝ) (3 / 2 : ℝ)
      _ = radiusSq x y z * Real.rpow (radiusSq x y z) (3 / 2 : ℝ) := by
            rw [exercise3225_rpow_one_of_pos (radiusSq x y z) h]
  rw [hr]
  field_simp [h3, ne_of_gt h] <;>
    unfold radiusSq <;> ring

theorem gap6 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      secondXX u x y z =
        (2 * x ^ 2 - y ^ 2 - z ^ 2) / powFiveHalves x y z := by
  intro x y z h
  rw [gap4 x y z h]
  exact gap5 x y z h

theorem gap7 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      mixedXY u x y z =
        3 * x * y / powFiveHalves x y z := by
  intro x y z h
  unfold mixedXY
  have hlocal : ∀ᶠ t in nhds y, 0 < radiusSq x t z := by
    have hc : Continuous (fun t : ℝ => radiusSq x t z) := by
      unfold radiusSq
      fun_prop
    exact hc.continuousAt.eventually (isOpen_Ioi.mem_nhds h)
  have heq : (fun t => partialX u x t z) =ᶠ[nhds y]
      (fun t => (-x) / powThreeHalves x t z) :=
    hlocal.mono (fun t ht => by simpa [neg_div] using gap1 x t z ht)
  rw [Filter.EventuallyEq.deriv_eq heq]
  have hdq : HasDerivAt (fun t : ℝ => radiusSq x t z) (2 * y) y := by
    have hd' : HasDerivAt (fun t : ℝ => t ^ 2 + (x ^ 2 + z ^ 2))
        (2 * y) y :=
      (exercise3225_hasDerivAt_square y).add_const (x ^ 2 + z ^ 2)
    convert hd' using 1
    funext t
    unfold radiusSq
    ring
  have hp : HasDerivAt (fun t : ℝ => powThreeHalves x t z)
      (3 * y * Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) y := by
    unfold powThreeHalves
    convert (Real.hasDerivAt_rpow_const (p := (3 / 2 : ℝ))
      (Or.inl (ne_of_gt h))).comp y hdq using 1 <;> norm_num <;> ring
  have hn : HasDerivAt (fun _ : ℝ => -x) 0 y := hasDerivAt_const y (-x)
  have hden : powThreeHalves x y z ≠ 0 := by
    unfold powThreeHalves
    exact ne_of_gt (Real.rpow_pos_of_pos h _)
  have hd := hn.div hp hden
  change deriv ((fun _ : ℝ => -x) / (fun t : ℝ => powThreeHalves x t z)) y = _
  rw [hd.deriv]
  unfold powThreeHalves powFiveHalves
  have hr3 : Real.rpow (radiusSq x y z) (3 / 2 : ℝ) =
      radiusSq x y z * Real.rpow (radiusSq x y z) (1 / 2 : ℝ) := by
    calc
      Real.rpow (radiusSq x y z) (3 / 2 : ℝ) =
          Real.rpow (radiusSq x y z) (1 + 1 / 2 : ℝ) := by
            congr 1 <;> norm_num
      _ = Real.rpow (radiusSq x y z) (1 : ℝ) *
          Real.rpow (radiusSq x y z) (1 / 2 : ℝ) := by
            exact Real.rpow_add h (1 : ℝ) (1 / 2 : ℝ)
      _ = radiusSq x y z * Real.rpow (radiusSq x y z) (1 / 2 : ℝ) := by
            rw [exercise3225_rpow_one_of_pos (radiusSq x y z) h]
  have hr5 : Real.rpow (radiusSq x y z) (5 / 2 : ℝ) =
      radiusSq x y z * (radiusSq x y z *
        Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) := by
    calc
      Real.rpow (radiusSq x y z) (5 / 2 : ℝ) =
          Real.rpow (radiusSq x y z) (1 + 3 / 2 : ℝ) := by
            congr 1 <;> norm_num
      _ = Real.rpow (radiusSq x y z) (1 : ℝ) *
          Real.rpow (radiusSq x y z) (3 / 2 : ℝ) := by
            exact Real.rpow_add h (1 : ℝ) (3 / 2 : ℝ)
      _ = radiusSq x y z * (radiusSq x y z *
          Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) := by
            rw [exercise3225_rpow_one_of_pos (radiusSq x y z) h, hr3]
  have hs : (Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) ^ 2 =
      radiusSq x y z := by
    calc
      (Real.rpow (radiusSq x y z) (1 / 2 : ℝ)) ^ 2 =
          (Real.sqrt (radiusSq x y z)) ^ 2 := by
            congr 1
            exact (Real.sqrt_eq_rpow (radiusSq x y z)).symm
      _ = radiusSq x y z := Real.sq_sqrt h.le
  rw [hr3, hr5]
  field_simp [ne_of_gt h, ne_of_gt (Real.rpow_pos_of_pos h (1 / 2 : ℝ))] <;>
    nlinarith [hs]

theorem gap8 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      secondYY u x y z =
        (2 * y ^ 2 - x ^ 2 - z ^ 2) / powFiveHalves x y z := by
  intro x y z h
  have heq : (fun t => partialY u x t z) =
      (fun t => partialX u t x z) := by
    funext t
    unfold partialY partialX
    apply congrArg (fun f : ℝ → ℝ => deriv f t)
    funext s
    unfold u
    apply congrArg (fun q : ℝ => 1 / Real.sqrt q)
    unfold radiusSq
    ring
  have hpos : 0 < radiusSq y x z := by
    simpa [radiusSq, add_comm, add_left_comm, add_assoc] using h
  have hp : powFiveHalves y x z = powFiveHalves x y z := by
    unfold powFiveHalves
    apply congrArg (fun q : ℝ => Real.rpow q (5 / 2 : ℝ))
    unfold radiusSq
    ring
  calc
    secondYY u x y z = secondXX u y x z := by
      unfold secondYY secondXX
      rw [heq]
    _ = (2 * y ^ 2 - x ^ 2 - z ^ 2) / powFiveHalves y x z :=
      gap6 y x z hpos
    _ = (2 * y ^ 2 - x ^ 2 - z ^ 2) / powFiveHalves x y z := by
      rw [hp]

theorem gap9 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      secondZZ u x y z =
        (2 * z ^ 2 - x ^ 2 - y ^ 2) / powFiveHalves x y z := by
  intro x y z h
  have heq : (fun t => partialZ u x y t) =
      (fun t => partialX u t x y) := by
    funext t
    unfold partialZ partialX
    apply congrArg (fun f : ℝ → ℝ => deriv f t)
    funext s
    unfold u
    apply congrArg (fun q : ℝ => 1 / Real.sqrt q)
    unfold radiusSq
    ring
  have hpos : 0 < radiusSq z x y := by
    simpa [radiusSq, add_comm, add_left_comm, add_assoc] using h
  have hp : powFiveHalves z x y = powFiveHalves x y z := by
    unfold powFiveHalves
    apply congrArg (fun q : ℝ => Real.rpow q (5 / 2 : ℝ))
    unfold radiusSq
    ring
  calc
    secondZZ u x y z = secondXX u z x y := by
      unfold secondZZ secondXX
      rw [heq]
    _ = (2 * z ^ 2 - x ^ 2 - y ^ 2) / powFiveHalves z x y :=
      gap6 z x y hpos
    _ = (2 * z ^ 2 - x ^ 2 - y ^ 2) / powFiveHalves x y z := by
      rw [hp]

theorem gap10 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      mixedYZ u x y z =
        3 * y * z / powFiveHalves x y z := by
  intro x y z h
  have heq : (fun t => partialY u x y t) =
      (fun t => partialX u y t x) := by
    funext t
    unfold partialY partialX
    apply congrArg (fun f : ℝ → ℝ => deriv f y)
    funext s
    unfold u
    apply congrArg (fun q : ℝ => 1 / Real.sqrt q)
    unfold radiusSq
    ring
  have hpos : 0 < radiusSq y z x := by
    simpa [radiusSq, add_comm, add_left_comm, add_assoc] using h
  have hp : powFiveHalves y z x = powFiveHalves x y z := by
    unfold powFiveHalves
    apply congrArg (fun q : ℝ => Real.rpow q (5 / 2 : ℝ))
    unfold radiusSq
    ring
  calc
    mixedYZ u x y z = mixedXY u y z x := by
      unfold mixedYZ mixedXY
      rw [heq]
    _ = 3 * y * z / powFiveHalves y z x := gap7 y z x hpos
    _ = 3 * y * z / powFiveHalves x y z := by rw [hp]

theorem gap11 :
    ∀ x y z : ℝ, 0 < radiusSq x y z →
      mixedZX u x y z =
        3 * x * z / powFiveHalves x y z := by
  intro x y z h
  have heq : (fun t => partialZ u t y z) =
      (fun t => partialX u z t y) := by
    funext t
    unfold partialZ partialX
    apply congrArg (fun f : ℝ → ℝ => deriv f z)
    funext s
    unfold u
    apply congrArg (fun q : ℝ => 1 / Real.sqrt q)
    unfold radiusSq
    ring
  have hpos : 0 < radiusSq z x y := by
    simpa [radiusSq, add_comm, add_left_comm, add_assoc] using h
  have hp : powFiveHalves z x y = powFiveHalves x y z := by
    unfold powFiveHalves
    apply congrArg (fun q : ℝ => Real.rpow q (5 / 2 : ℝ))
    unfold radiusSq
    ring
  calc
    mixedZX u x y z = mixedXY u z x y := by
      unfold mixedZX mixedXY
      rw [heq]
    _ = 3 * z * x / powFiveHalves z x y := gap7 z x y hpos
    _ = 3 * x * z / powFiveHalves x y z := by
      rw [hp]
      ring

end

end ProofGap.Exercise3225
