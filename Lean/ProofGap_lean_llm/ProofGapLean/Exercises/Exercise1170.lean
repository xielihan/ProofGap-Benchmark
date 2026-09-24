import ProofGapLean.Prelude.Elementary
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Neighborhoods
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise1170

noncomputable section

def nthDeriv : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => deriv (nthDeriv n f)

def y (x : ℝ) : ℝ := Real.sin x ^ 2 * Real.log x
def logCos (x : ℝ) : ℝ := Real.cos (2 * x) * Real.log x

private theorem sin_sq_two (x : ℝ) :
    Real.sin x ^ 2 = (1 - Real.cos (2 * x)) / 2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq x]

private def invPow (n : ℕ) (x : ℝ) : ℝ := 1 / x ^ n

private def logD0 (x : ℝ) : ℝ := Real.log x
private def logD1 (x : ℝ) : ℝ := invPow 1 x
private def logD2 (x : ℝ) : ℝ := -invPow 2 x
private def logD3 (x : ℝ) : ℝ := 2 * invPow 3 x
private def logD4 (x : ℝ) : ℝ := -6 * invPow 4 x
private def logD5 (x : ℝ) : ℝ := 24 * invPow 5 x
private def logD6 (x : ℝ) : ℝ := -120 * invPow 6 x

private theorem hasDerivAt_invPow (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (invPow n)
      (-(n : ℝ) * invPow (n + 1) x) x := by
  cases n with
  | zero =>
      convert (hasDerivAt_const (x := x) (c := (1 : ℝ))) using 1 <;>
        (try funext z) <;>
        simp [invPow]
  | succ n =>
      have h := (((hasDerivAt_id x).pow (n + 1)).inv
        (pow_ne_zero (n + 1) hx.ne'))
      convert h using 1
      all_goals
        first
        | funext z
          simp [invPow]
        | simp [invPow, pow_succ]
          field_simp [hx.ne']
          ring

private theorem hasDerivAt_logD0 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logD0 (logD1 x) x := by
  simpa [logD0, logD1, invPow, one_div] using
    Real.hasDerivAt_log hx.ne'

private theorem hasDerivAt_logD1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logD1 (logD2 x) x := by
  change HasDerivAt (fun z : ℝ => invPow 1 z) (-invPow 2 x) x
  simpa using hasDerivAt_invPow 1 x hx

private theorem hasDerivAt_logD2 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logD2 (logD3 x) x := by
  change HasDerivAt (fun z : ℝ => -invPow 2 z) (2 * invPow 3 x) x
  convert (hasDerivAt_invPow 2 x hx).const_mul (-1) using 1 <;>
    (try funext z) <;>
    norm_num <;>
    ring

private theorem hasDerivAt_logD3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logD3 (logD4 x) x := by
  change HasDerivAt (fun z : ℝ => 2 * invPow 3 z) (-6 * invPow 4 x) x
  convert (hasDerivAt_invPow 3 x hx).const_mul 2 using 1 <;>
    (try funext z) <;>
    norm_num <;>
    ring

private theorem hasDerivAt_logD4 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logD4 (logD5 x) x := by
  change HasDerivAt (fun z : ℝ => -6 * invPow 4 z) (24 * invPow 5 x) x
  convert (hasDerivAt_invPow 4 x hx).const_mul (-6) using 1 <;>
    (try funext z) <;>
    norm_num <;>
    ring

private theorem hasDerivAt_logD5 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logD5 (logD6 x) x := by
  change HasDerivAt (fun z : ℝ => 24 * invPow 5 z) (-120 * invPow 6 x) x
  convert (hasDerivAt_invPow 5 x hx).const_mul 24 using 1 <;>
    (try funext z) <;>
    norm_num <;>
    ring

private def cosDiv (n : ℕ) (x : ℝ) : ℝ :=
  Real.cos (2 * x) * invPow n x

private def sinDiv (n : ℕ) (x : ℝ) : ℝ :=
  Real.sin (2 * x) * invPow n x

private theorem hasDerivAt_sinTwo (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.sin (2 * z))
      (2 * Real.cos (2 * x)) x := by
  convert (Real.hasDerivAt_sin (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;>
    ring

private theorem hasDerivAt_cosTwo (x : ℝ) :
    HasDerivAt (fun z : ℝ => Real.cos (2 * z))
      (-2 * Real.sin (2 * x)) x := by
  convert (Real.hasDerivAt_cos (2 * x)).comp x
    ((hasDerivAt_id x).const_mul 2) using 1 <;>
    ring

private theorem hasDerivAt_cosDiv (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (cosDiv n)
      (-2 * sinDiv n x - (n : ℝ) * cosDiv (n + 1) x) x := by
  convert (hasDerivAt_cosTwo x).mul (hasDerivAt_invPow n x hx) using 1 <;>
    simp [cosDiv, sinDiv] <;>
    ring

private theorem hasDerivAt_sinDiv (n : ℕ) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (sinDiv n)
      (2 * cosDiv n x - (n : ℝ) * sinDiv (n + 1) x) x := by
  convert (hasDerivAt_sinTwo x).mul (hasDerivAt_invPow n x hx) using 1 <;>
    simp [cosDiv, sinDiv] <;>
    ring

private def logCosD0 (x : ℝ) : ℝ := logCos x
private def logCosD1 (x : ℝ) : ℝ :=
  -2 * sinDiv 0 x * logD0 x + cosDiv 1 x
private def logCosD2 (x : ℝ) : ℝ :=
  -4 * cosDiv 0 x * logD0 x - 4 * sinDiv 1 x - cosDiv 2 x
private def logCosD3 (x : ℝ) : ℝ :=
  8 * sinDiv 0 x * logD0 x - 12 * cosDiv 1 x +
    6 * sinDiv 2 x + 2 * cosDiv 3 x
private def logCosD4 (x : ℝ) : ℝ :=
  16 * cosDiv 0 x * logD0 x + 32 * sinDiv 1 x +
    24 * cosDiv 2 x - 16 * sinDiv 3 x - 6 * cosDiv 4 x
private def logCosD5 (x : ℝ) : ℝ :=
  -32 * sinDiv 0 x * logD0 x + 80 * cosDiv 1 x -
    80 * sinDiv 2 x - 80 * cosDiv 3 x +
    60 * sinDiv 4 x + 24 * cosDiv 5 x
private def logCosD6 (x : ℝ) : ℝ :=
  -64 * cosDiv 0 x * logD0 x - 192 * sinDiv 1 x -
    240 * cosDiv 2 x + 320 * sinDiv 3 x +
    360 * cosDiv 4 x - 288 * sinDiv 5 x - 120 * cosDiv 6 x

private theorem hasDerivAt_logCosD0 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logCosD0 (logCosD1 x) x := by
  convert (hasDerivAt_cosDiv 0 x hx).mul (hasDerivAt_logD0 x hx) using 1 <;>
    (try funext z) <;>
    norm_num [logCosD0, logCosD1, logCos, logD0, logD1,
      cosDiv, sinDiv, invPow] <;>
    ring

private theorem hasDerivAt_logCosD1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logCosD1 (logCosD2 x) x := by
  convert (((hasDerivAt_sinDiv 0 x hx).const_mul (-2)).mul
      (hasDerivAt_logD0 x hx)).add (hasDerivAt_cosDiv 1 x hx) using 1 <;>
    (try funext z) <;>
    norm_num [logCosD1, logCosD2, logD0, logD1,
      cosDiv, sinDiv, invPow] <;>
    ring

private theorem hasDerivAt_logCosD2 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logCosD2 (logCosD3 x) x := by
  convert ((((hasDerivAt_cosDiv 0 x hx).const_mul (-4)).mul
      (hasDerivAt_logD0 x hx)).add
      ((hasDerivAt_sinDiv 1 x hx).const_mul (-4))).add
      ((hasDerivAt_cosDiv 2 x hx).const_mul (-1)) using 1 <;>
    (try funext z) <;>
    norm_num [logCosD2, logCosD3, logD0, logD1,
      cosDiv, sinDiv, invPow] <;>
    ring

private theorem hasDerivAt_logCosD3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logCosD3 (logCosD4 x) x := by
  convert (((((hasDerivAt_sinDiv 0 x hx).const_mul 8).mul
      (hasDerivAt_logD0 x hx)).add
      ((hasDerivAt_cosDiv 1 x hx).const_mul (-12))).add
      ((hasDerivAt_sinDiv 2 x hx).const_mul 6)).add
      ((hasDerivAt_cosDiv 3 x hx).const_mul 2) using 1 <;>
    (try funext z) <;>
    norm_num [logCosD3, logCosD4, logD0, logD1,
      cosDiv, sinDiv, invPow] <;>
    ring

private theorem hasDerivAt_logCosD4 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logCosD4 (logCosD5 x) x := by
  convert ((((((hasDerivAt_cosDiv 0 x hx).const_mul 16).mul
      (hasDerivAt_logD0 x hx)).add
      ((hasDerivAt_sinDiv 1 x hx).const_mul 32)).add
      ((hasDerivAt_cosDiv 2 x hx).const_mul 24)).add
      ((hasDerivAt_sinDiv 3 x hx).const_mul (-16))).add
      ((hasDerivAt_cosDiv 4 x hx).const_mul (-6)) using 1 <;>
    (try funext z) <;>
    norm_num [logCosD4, logCosD5, logD0, logD1,
      cosDiv, sinDiv, invPow] <;>
    ring

private theorem hasDerivAt_logCosD5 (x : ℝ) (hx : 0 < x) :
    HasDerivAt logCosD5 (logCosD6 x) x := by
  convert (((((((hasDerivAt_sinDiv 0 x hx).const_mul (-32)).mul
      (hasDerivAt_logD0 x hx)).add
      ((hasDerivAt_cosDiv 1 x hx).const_mul 80)).add
      ((hasDerivAt_sinDiv 2 x hx).const_mul (-80))).add
      ((hasDerivAt_cosDiv 3 x hx).const_mul (-80))).add
      ((hasDerivAt_sinDiv 4 x hx).const_mul 60)).add
      ((hasDerivAt_cosDiv 5 x hx).const_mul 24) using 1 <;>
    (try funext z) <;>
    norm_num [logCosD5, logCosD6, logD0, logD1,
      cosDiv, sinDiv, invPow] <;>
    ring

private def yD0 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logD0 x - (1 / 2 : ℝ) * logCosD0 x
private def yD1 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logD1 x - (1 / 2 : ℝ) * logCosD1 x
private def yD2 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logD2 x - (1 / 2 : ℝ) * logCosD2 x
private def yD3 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logD3 x - (1 / 2 : ℝ) * logCosD3 x
private def yD4 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logD4 x - (1 / 2 : ℝ) * logCosD4 x
private def yD5 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logD5 x - (1 / 2 : ℝ) * logCosD5 x
private def yD6 (x : ℝ) : ℝ :=
  (1 / 2 : ℝ) * logD6 x - (1 / 2 : ℝ) * logCosD6 x

private theorem hasDerivAt_yD0 (x : ℝ) (hx : 0 < x) :
    HasDerivAt yD0 (yD1 x) x := by
  change HasDerivAt
    (fun z : ℝ => (1 / 2 : ℝ) * logD0 z - (1 / 2 : ℝ) * logCosD0 z)
    ((1 / 2 : ℝ) * logD1 x - (1 / 2 : ℝ) * logCosD1 x) x
  simpa using
    ((hasDerivAt_logD0 x hx).const_mul (1 / 2 : ℝ)).sub
      ((hasDerivAt_logCosD0 x hx).const_mul (1 / 2 : ℝ))

private theorem hasDerivAt_yD1 (x : ℝ) (hx : 0 < x) :
    HasDerivAt yD1 (yD2 x) x := by
  change HasDerivAt
    (fun z : ℝ => (1 / 2 : ℝ) * logD1 z - (1 / 2 : ℝ) * logCosD1 z)
    ((1 / 2 : ℝ) * logD2 x - (1 / 2 : ℝ) * logCosD2 x) x
  simpa using
    ((hasDerivAt_logD1 x hx).const_mul (1 / 2 : ℝ)).sub
      ((hasDerivAt_logCosD1 x hx).const_mul (1 / 2 : ℝ))

private theorem hasDerivAt_yD2 (x : ℝ) (hx : 0 < x) :
    HasDerivAt yD2 (yD3 x) x := by
  change HasDerivAt
    (fun z : ℝ => (1 / 2 : ℝ) * logD2 z - (1 / 2 : ℝ) * logCosD2 z)
    ((1 / 2 : ℝ) * logD3 x - (1 / 2 : ℝ) * logCosD3 x) x
  simpa using
    ((hasDerivAt_logD2 x hx).const_mul (1 / 2 : ℝ)).sub
      ((hasDerivAt_logCosD2 x hx).const_mul (1 / 2 : ℝ))

private theorem hasDerivAt_yD3 (x : ℝ) (hx : 0 < x) :
    HasDerivAt yD3 (yD4 x) x := by
  change HasDerivAt
    (fun z : ℝ => (1 / 2 : ℝ) * logD3 z - (1 / 2 : ℝ) * logCosD3 z)
    ((1 / 2 : ℝ) * logD4 x - (1 / 2 : ℝ) * logCosD4 x) x
  simpa using
    ((hasDerivAt_logD3 x hx).const_mul (1 / 2 : ℝ)).sub
      ((hasDerivAt_logCosD3 x hx).const_mul (1 / 2 : ℝ))

private theorem hasDerivAt_yD4 (x : ℝ) (hx : 0 < x) :
    HasDerivAt yD4 (yD5 x) x := by
  change HasDerivAt
    (fun z : ℝ => (1 / 2 : ℝ) * logD4 z - (1 / 2 : ℝ) * logCosD4 z)
    ((1 / 2 : ℝ) * logD5 x - (1 / 2 : ℝ) * logCosD5 x) x
  simpa using
    ((hasDerivAt_logD4 x hx).const_mul (1 / 2 : ℝ)).sub
      ((hasDerivAt_logCosD4 x hx).const_mul (1 / 2 : ℝ))

private theorem hasDerivAt_yD5 (x : ℝ) (hx : 0 < x) :
    HasDerivAt yD5 (yD6 x) x := by
  change HasDerivAt
    (fun z : ℝ => (1 / 2 : ℝ) * logD5 z - (1 / 2 : ℝ) * logCosD5 z)
    ((1 / 2 : ℝ) * logD6 x - (1 / 2 : ℝ) * logCosD6 x) x
  simpa using
    ((hasDerivAt_logD5 x hx).const_mul (1 / 2 : ℝ)).sub
      ((hasDerivAt_logCosD5 x hx).const_mul (1 / 2 : ℝ))

private theorem nthDeriv_succ_pos
    (f d e : ℝ → ℝ) (n : ℕ)
    (hd : ∀ z, 0 < z → nthDeriv n f z = d z)
    (hde : ∀ z, 0 < z → HasDerivAt d (e z) z) :
    ∀ z, 0 < z → nthDeriv (n + 1) f z = e z := by
  intro x hx
  change deriv (nthDeriv n f) x = e x
  have hnear : Filter.EventuallyEq (nhds x) (nthDeriv n f) d := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact hd z hz
  calc
    deriv (nthDeriv n f) x = deriv d x := hnear.deriv_eq
    _ = e x := (hde x hx).deriv

private theorem nthDeriv_logCos_six (x : ℝ) (hx : 0 < x) :
    nthDeriv 6 logCos x = logCosD6 x := by
  have h0 : ∀ z, 0 < z → nthDeriv 0 logCos z = logCosD0 z := by
    intro z hz
    rfl
  have h1 : ∀ z, 0 < z → nthDeriv 1 logCos z = logCosD1 z := by
    simpa using nthDeriv_succ_pos logCos logCosD0 logCosD1 0 h0
      hasDerivAt_logCosD0
  have h2 : ∀ z, 0 < z → nthDeriv 2 logCos z = logCosD2 z := by
    simpa using nthDeriv_succ_pos logCos logCosD1 logCosD2 1 h1
      hasDerivAt_logCosD1
  have h3 : ∀ z, 0 < z → nthDeriv 3 logCos z = logCosD3 z := by
    simpa using nthDeriv_succ_pos logCos logCosD2 logCosD3 2 h2
      hasDerivAt_logCosD2
  have h4 : ∀ z, 0 < z → nthDeriv 4 logCos z = logCosD4 z := by
    simpa using nthDeriv_succ_pos logCos logCosD3 logCosD4 3 h3
      hasDerivAt_logCosD3
  have h5 : ∀ z, 0 < z → nthDeriv 5 logCos z = logCosD5 z := by
    simpa using nthDeriv_succ_pos logCos logCosD4 logCosD5 4 h4
      hasDerivAt_logCosD4
  have h6 : ∀ z, 0 < z → nthDeriv 6 logCos z = logCosD6 z := by
    simpa using nthDeriv_succ_pos logCos logCosD5 logCosD6 5 h5
      hasDerivAt_logCosD5
  exact h6 x hx

private theorem nthDeriv_y_six (x : ℝ) (hx : 0 < x) :
    nthDeriv 6 y x = yD6 x := by
  have h0 : ∀ z, 0 < z → nthDeriv 0 y z = yD0 z := by
    intro z hz
    simp only [nthDeriv]
    unfold yD0 logD0 logCosD0 y logCos
    rw [sin_sq_two]
    ring
  have h1 : ∀ z, 0 < z → nthDeriv 1 y z = yD1 z := by
    simpa using nthDeriv_succ_pos y yD0 yD1 0 h0 hasDerivAt_yD0
  have h2 : ∀ z, 0 < z → nthDeriv 2 y z = yD2 z := by
    simpa using nthDeriv_succ_pos y yD1 yD2 1 h1 hasDerivAt_yD1
  have h3 : ∀ z, 0 < z → nthDeriv 3 y z = yD3 z := by
    simpa using nthDeriv_succ_pos y yD2 yD3 2 h2 hasDerivAt_yD2
  have h4 : ∀ z, 0 < z → nthDeriv 4 y z = yD4 z := by
    simpa using nthDeriv_succ_pos y yD3 yD4 3 h3 hasDerivAt_yD3
  have h5 : ∀ z, 0 < z → nthDeriv 5 y z = yD5 z := by
    simpa using nthDeriv_succ_pos y yD4 yD5 4 h4 hasDerivAt_yD4
  have h6 : ∀ z, 0 < z → nthDeriv 6 y z = yD6 z := by
    simpa using nthDeriv_succ_pos y yD5 yD6 5 h5 hasDerivAt_yD5
  exact h6 x hx

theorem gap1 (x : ℝ) (hx : 0 < x) :
    y x = (1 - Real.cos (2 * x)) / 2 * Real.log x := by
  simp [y, sin_sq_two]

theorem gap2 (x : ℝ) (hx : 0 < x) :
    (1 - Real.cos (2 * x)) / 2 * Real.log x =
      (1 / 2 : ℝ) * Real.log x -
        (1 / 2 : ℝ) * Real.cos (2 * x) * Real.log x := by
  ring

theorem gap3 (x : ℝ) (hx : 0 < x) :
    y x =
      (1 / 2 : ℝ) * Real.log x -
        (1 / 2 : ℝ) * Real.cos (2 * x) * Real.log x := by
  rw [gap1 x hx, gap2 x hx]

theorem gap4 (x : ℝ) (hx : 0 < x) :
    nthDeriv 6 y x =
      ((-1 : ℝ) ^ 5 / 2) * (2 * 3 * 4 * 5 : ℝ) / x ^ 6 -
        (1 / 2 : ℝ) * nthDeriv 6 logCos x := by
  rw [nthDeriv_y_six x hx, nthDeriv_logCos_six x hx]
  norm_num [yD6, logD6, invPow]
  field_simp [hx.ne']
  ring

theorem gap5 (x : ℝ) (hx : 0 < x) :
    nthDeriv 6 y x =
      -60 / x ^ 6 +
        (144 / x ^ 5 - 160 / x ^ 3 + 96 / x) *
          Real.sin (2 * x) +
        (60 / x ^ 6 - 180 / x ^ 4 + 120 / x ^ 2 +
          32 * Real.log x) * Real.cos (2 * x) := by
  rw [nthDeriv_y_six x hx]
  norm_num [yD6, logD6, logCosD6, logD0, cosDiv, sinDiv, invPow]
  field_simp [hx.ne']
  ring

end

end ProofGap.Exercise1170
