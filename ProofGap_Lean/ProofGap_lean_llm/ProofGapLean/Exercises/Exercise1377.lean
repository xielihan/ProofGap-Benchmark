import ProofGapLean.Prelude.Analysis
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow

namespace ProofGap.Exercise1377

noncomputable section

open Filter

def f (x : ℝ) : ℝ := (1 + x + x ^ 2) / (1 - x + x ^ 2)
def rewritten (x : ℝ) : ℝ := (1 + x + x ^ 2) * ((1 + x) / (1 + x ^ 3))
def polynomial (x : ℝ) : ℝ := 1 + 2 * x + 2 * x ^ 2 - 2 * x ^ 4
def iterDeriv (n : ℕ) (g : ℝ → ℝ) : ℝ → ℝ := (deriv^[n]) g

def AgreesToOrderAt (g p : ℝ → ℝ) (a : ℝ) (n : ℕ) : Prop :=
  Asymptotics.IsLittleO (nhds a) (fun x => g x - p x)
    (fun x => (x - a) ^ n)

private def d1 (x : ℝ) : ℝ :=
  -2 * (x - 1) * (x + 1) / (1 - x + x ^ 2) ^ 2

private def d2 (x : ℝ) : ℝ :=
  4 * (x ^ 3 - 3 * x + 1) / (1 - x + x ^ 2) ^ 3

private def d3 (x : ℝ) : ℝ :=
  -12 * x * (x - 2) * (x ^ 2 + 2 * x - 2) /
    (1 - x + x ^ 2) ^ 4

private theorem quad_ne (x : ℝ) : 1 - x + x ^ 2 ≠ 0 := by
  nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]

private theorem hasDeriv_quad (x : ℝ) :
    HasDerivAt (fun y : ℝ => 1 - y + y ^ 2) (-1 + 2 * x) x := by
  have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x (1 : ℝ)
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hs : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hi.fun_pow 2
  simpa using (HasDerivAt.add (HasDerivAt.sub hc hi) hs)

private theorem deriv_f_eq (x : ℝ) : deriv f x = d1 x := by
  have hn : HasDerivAt (fun y : ℝ => 1 + y + y ^ 2) (1 + 2 * x) x := by
    have hc : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
      hasDerivAt_const x (1 : ℝ)
    have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have hs : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hi.fun_pow 2
    simpa using (HasDerivAt.add (HasDerivAt.add hc hi) hs)
  have hd := hasDeriv_quad x
  have hquot := (hn.div hd (quad_ne x)).deriv
  unfold f d1
  rw [show deriv (fun y : ℝ =>
    (1 + y + y ^ 2) / (1 - y + y ^ 2)) x =
      ((1 + 2 * x) * (1 - x + x ^ 2) -
        (1 + x + x ^ 2) * (-1 + 2 * x)) /
          (1 - x + x ^ 2) ^ 2 by simpa using hquot]
  field_simp [quad_ne x]
  ring

private theorem deriv_d1_eq (x : ℝ) : deriv d1 x = d2 x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x (1 : ℝ)
  have hcm2 : HasDerivAt (fun _ : ℝ => (-2 : ℝ)) 0 x :=
    hasDerivAt_const x (-2 : ℝ)
  have hxm : HasDerivAt (fun y : ℝ => y - 1) 1 x := by
    simpa only [Pi.sub_apply, sub_zero] using HasDerivAt.sub hi hc1
  have hxp : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa only [Pi.add_apply, add_zero] using HasDerivAt.add hi hc1
  have hn : HasDerivAt (fun y : ℝ => -2 * (y - 1) * (y + 1))
      (-4 * x) x := by
    convert HasDerivAt.mul (HasDerivAt.mul hcm2 hxm) hxp using 1 <;>
      simp [Pi.mul_apply] <;> ring
  have hd : HasDerivAt (fun y : ℝ => (1 - y + y ^ 2) ^ 2)
      (2 * (1 - x + x ^ 2) * (-1 + 2 * x)) x := by
    simpa using (hasDeriv_quad x).fun_pow 2
  have hq := (hn.div hd (pow_ne_zero 2 (quad_ne x))).deriv
  unfold d1 d2
  rw [show deriv (fun y : ℝ =>
    -2 * (y - 1) * (y + 1) / (1 - y + y ^ 2) ^ 2) x =
      ((-4 * x) * (1 - x + x ^ 2) ^ 2 -
        (-2 * (x - 1) * (x + 1)) *
          (2 * (1 - x + x ^ 2) * (-1 + 2 * x))) /
          ((1 - x + x ^ 2) ^ 2) ^ 2 by simpa using hq]
  field_simp [quad_ne x]
  ring

private theorem deriv_d2_eq (x : ℝ) : deriv d2 x = d3 x := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hc1 : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 x :=
    hasDerivAt_const x (1 : ℝ)
  have hc3 : HasDerivAt (fun _ : ℝ => (3 : ℝ)) 0 x :=
    hasDerivAt_const x (3 : ℝ)
  have hc4 : HasDerivAt (fun _ : ℝ => (4 : ℝ)) 0 x :=
    hasDerivAt_const x (4 : ℝ)
  have hx3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    convert hi.fun_pow 3 using 1 <;> norm_num
  have h3x : HasDerivAt (fun y : ℝ => 3 * y) 3 x := by
    simpa using HasDerivAt.mul hc3 hi
  have hn : HasDerivAt (fun y : ℝ => 4 * (y ^ 3 - 3 * y + 1))
      (4 * (3 * x ^ 2 - 3)) x := by
    have hinner := HasDerivAt.add (HasDerivAt.sub hx3 h3x) hc1
    convert HasDerivAt.mul hc4 hinner using 1 <;> ring
  have hd : HasDerivAt (fun y : ℝ => (1 - y + y ^ 2) ^ 3)
      (3 * (1 - x + x ^ 2) ^ 2 * (-1 + 2 * x)) x := by
    simpa using (hasDeriv_quad x).fun_pow 3
  have hq := (hn.div hd (pow_ne_zero 3 (quad_ne x))).deriv
  unfold d2 d3
  rw [show deriv (fun y : ℝ =>
    4 * (y ^ 3 - 3 * y + 1) / (1 - y + y ^ 2) ^ 3) x =
      ((4 * (3 * x ^ 2 - 3)) * (1 - x + x ^ 2) ^ 3 -
        (4 * (x ^ 3 - 3 * x + 1)) *
          (3 * (1 - x + x ^ 2) ^ 2 * (-1 + 2 * x))) /
          ((1 - x + x ^ 2) ^ 3) ^ 2 by simpa using hq]
  field_simp [quad_ne x]
  ring

private theorem deriv_d3_zero : deriv d3 0 = -48 := by
  have hi : HasDerivAt (fun y : ℝ => y) 1 0 := hasDerivAt_id 0
  have hc2 : HasDerivAt (fun _ : ℝ => (2 : ℝ)) 0 0 :=
    hasDerivAt_const 0 (2 : ℝ)
  have hcm2 : HasDerivAt (fun _ : ℝ => (-2 : ℝ)) 0 0 :=
    hasDerivAt_const 0 (-2 : ℝ)
  have hcm12 : HasDerivAt (fun _ : ℝ => (-12 : ℝ)) 0 0 :=
    hasDerivAt_const 0 (-12 : ℝ)
  have hx2 : HasDerivAt (fun y : ℝ => y ^ 2) 0 0 := by
    simpa using hi.fun_pow 2
  have h2x : HasDerivAt (fun y : ℝ => 2 * y) 2 0 := by
    simpa using HasDerivAt.mul hc2 hi
  have hn : HasDerivAt
      (fun y : ℝ => -12 * y * (y - 2) * (y ^ 2 + 2 * y - 2))
      (-48) 0 := by
    have ha := HasDerivAt.mul hcm12 hi
    have hb := HasDerivAt.sub hi hc2
    have hc := HasDerivAt.sub (HasDerivAt.add hx2 h2x) hc2
    convert HasDerivAt.mul (HasDerivAt.mul ha hb) hc using 1 <;> norm_num
  have hd : HasDerivAt (fun y : ℝ => (1 - y + y ^ 2) ^ 4) (-4) 0 := by
    convert (hasDeriv_quad 0).fun_pow 4 using 1 <;> norm_num
  have hq := (hn.div hd (by norm_num)).deriv
  unfold d3
  simpa using hq

private theorem fourth_deriv_value :
    iterDeriv 4 f 0 = -48 := by
  change deriv (deriv (deriv (deriv f))) 0 = -48
  rw [show deriv f = d1 from funext deriv_f_eq]
  rw [show deriv d1 = d2 from funext deriv_d1_eq]
  rw [show deriv d2 = d3 from funext deriv_d2_eq]
  exact deriv_d3_zero

private theorem rational_rewrite (x : ℝ) (hden : 1 + x ^ 3 ≠ 0) :
    f x = rewritten x := by
  have hquad : 1 - x + x ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg (x - (1 / 2 : ℝ))]
  have hx1 : 1 + x ≠ 0 := by
    intro hx
    have : x = -1 := by linarith
    subst x
    norm_num at hden
  unfold f rewritten
  field_simp [hquad, hx1, hden]
  ring

private theorem rewritten_agrees :
    AgreesToOrderAt rewritten polynomial 0 4 := by
  have hdenlim : Tendsto (fun x : ℝ => 1 + x ^ 3) (nhds 0) (nhds 1) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1)).add
        ((tendsto_id :
          Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).pow 3) using 1 <;>
      norm_num
  have hqlim : Tendsto
      (fun x : ℝ => 2 * (x - 1) * (x + 1) / (1 + x ^ 3))
      (nhds 0) (nhds (-2)) := by
    have hn : Tendsto (fun x : ℝ => 2 * (x - 1) * (x + 1))
        (nhds 0) (nhds (-2)) := by
      have hm : Tendsto (fun x : ℝ => x - 1) (nhds 0) (nhds (-1)) := by
        convert (tendsto_id :
          Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).sub
            (tendsto_const_nhds :
              Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1)) using 1 <;>
          norm_num
      have hp : Tendsto (fun x : ℝ => x + 1) (nhds 0) (nhds 1) := by
        convert (tendsto_id :
          Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).add
            (tendsto_const_nhds :
              Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1)) using 1 <;>
          norm_num
      convert (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (2 : ℝ)) (nhds 0) (nhds 2)).mul hm |>.mul hp
          using 1 <;> norm_num
    simpa using hn.div hdenlim (by norm_num)
  have hqo :
      (fun x : ℝ => 2 * (x - 1) * (x + 1) / (1 + x ^ 3)) =O[nhds 0]
        (fun _ : ℝ => (1 : ℝ)) :=
    hqlim.isBigO_one ℝ
  have hpow : (fun x : ℝ => x ^ 5) =o[nhds 0]
      (fun x : ℝ => x ^ 4) :=
    Asymptotics.isLittleO_pow_pow (by norm_num)
  have hmul := hpow.mul_isBigO hqo
  unfold AgreesToOrderAt
  refine hmul.congr' ?_ ?_
  · filter_upwards
      [hdenlim.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with x hx
    unfold rewritten polynomial
    field_simp [hx]
    ring
  · exact Eventually.of_forall (by intro x; simp)

theorem gap1 (x : ℝ) (hden : 1 + x ^ 3 ≠ 0) :
    f x = rewritten x := by
  exact rational_rewrite x hden

theorem gap2 :
    AgreesToOrderAt rewritten polynomial 0 4 := by
  exact rewritten_agrees

theorem gap3 :
    AgreesToOrderAt rewritten polynomial 0 4 := by
  exact rewritten_agrees

theorem gap4 :
    AgreesToOrderAt f polynomial 0 4 := by
  have hdenlim : Tendsto (fun x : ℝ => 1 + x ^ 3) (nhds 0) (nhds 1) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (1 : ℝ)) (nhds 0) (nhds 1)).add
        ((tendsto_id :
          Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0)).pow 3) using 1 <;>
      norm_num
  have hrew := rewritten_agrees
  unfold AgreesToOrderAt at hrew ⊢
  refine hrew.congr' ?_ (Eventually.of_forall (by intro x; rfl))
  filter_upwards
    [hdenlim.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with x hx
  rw [rational_rewrite x hx]

theorem gap5 :
    iterDeriv 4 f 0 = (Nat.factorial 4 : ℝ) * (-2) := by
  calc
    iterDeriv 4 f 0 = -48 := fourth_deriv_value
    _ = (Nat.factorial 4 : ℝ) * (-2) := by norm_num

theorem gap6 :
    (Nat.factorial 4 : ℝ) * (-2) = -48 := by
  norm_num

theorem gap7 :
    iterDeriv 4 f 0 = -48 := by
  exact fourth_deriv_value

end

end ProofGap.Exercise1377
