import ProofGapLean.Prelude.Analysis
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace ProofGap.Exercise451

noncomputable section

def fifthRoot (x : ℝ) : ℝ := Real.rpow x (1 / 5 : ℝ)
def f (x : ℝ) : ℝ := x ^ 2 / (fifthRoot (1 + 5 * x) - (1 + x))
def HasLimitAt (g : ℝ → ℝ) (a L : ℝ) : Prop :=
  Filter.Tendsto g (nhdsWithin a ({a} : Set ℝ)ᶜ) (nhds L)

/-- Exercise 451, gap 1; replace the fifth-power rationalization ellipsis by its limit statement. -/
theorem gap1 : HasLimitAt f 0 (-1 / 2) := by
  unfold HasLimitAt
  let F : Filter ℝ := nhdsWithin 0 ({0} : Set ℝ)ᶜ
  let r : ℝ → ℝ := fun x => fifthRoot (1 + 5 * x)
  let b : ℝ → ℝ := fun x => 1 + x
  let S : ℝ → ℝ := fun x =>
    r x ^ 4 + r x ^ 3 * b x + r x ^ 2 * b x ^ 2 +
      r x * b x ^ 3 + b x ^ 4
  let Q : ℝ → ℝ := fun x => 10 + 10 * x + 5 * x ^ 2 + x ^ 3
  let G : ℝ → ℝ := fun x => -(S x / Q x)
  change Filter.Tendsto f F (nhds (-1 / 2))
  have hle : F ≤ nhds (0 : ℝ) := by
    change nhds 0 ⊓ Filter.principal ({0} : Set ℝ)ᶜ ≤ nhds 0
    exact inf_le_left
  have hxlim : Filter.Tendsto (fun x : ℝ => x) F (nhds 0) := by
    simpa [Filter.Tendsto] using hle
  have hone : Filter.Tendsto (fun _ : ℝ => (1 : ℝ)) F (nhds 1) :=
    tendsto_const_nhds
  have hfive : Filter.Tendsto (fun _ : ℝ => (5 : ℝ)) F (nhds 5) :=
    tendsto_const_nhds
  have hten : Filter.Tendsto (fun _ : ℝ => (10 : ℝ)) F (nhds 10) :=
    tendsto_const_nhds
  have hlin : Filter.Tendsto (fun x : ℝ => 1 + 5 * x) F (nhds 1) := by
    simpa using hone.add (hfive.mul hxlim)
  have hb : Filter.Tendsto b F (nhds 1) := by
    simpa [b] using hone.add hxlim
  have hnear : ∀ᶠ x in F, -1 / 5 < x := by
    have hm : {x : ℝ | -1 / 5 < x} ∈ nhds (0 : ℝ) := by
      exact (isOpen_lt continuous_const continuous_id).mem_nhds (by norm_num)
    exact hle hm
  have hlog :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + 5 * x)) F (nhds 0) := by
    have h := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hlin
    simpa using h
  have hscaled :
      Filter.Tendsto (fun x : ℝ => Real.log (1 + 5 * x) * (1 / 5 : ℝ)) F
        (nhds 0) := by
    have hc : Filter.Tendsto (fun _ : ℝ => (1 / 5 : ℝ)) F (nhds (1 / 5 : ℝ)) :=
      tendsto_const_nhds
    simpa using hlog.mul hc
  have halt :
      Filter.Tendsto
        (fun x : ℝ => Real.exp (Real.log (1 + 5 * x) * (1 / 5 : ℝ))) F
        (nhds 1) := by
    have h := Real.continuous_exp.continuousAt.tendsto.comp hscaled
    simpa using h
  have heqroot :
      (fun x : ℝ => r x) =ᶠ[F]
        (fun x : ℝ => Real.exp (Real.log (1 + 5 * x) * (1 / 5 : ℝ))) := by
    filter_upwards [hnear] with x hx
    have hp : 0 < 1 + 5 * x := by linarith
    simp only [r, fifthRoot]
    exact Real.rpow_def_of_pos hp (1 / 5 : ℝ)
  have hroot : Filter.Tendsto r F (nhds 1) :=
    halt.congr' heqroot.symm
  have hS : Filter.Tendsto S F (nhds 5) := by
    have h :=
      (((((hroot.pow 4).add ((hroot.pow 3).mul hb)).add
          ((hroot.pow 2).mul (hb.pow 2))).add
          (hroot.mul (hb.pow 3))).add (hb.pow 4))
    norm_num at h
    simpa only [S] using h
  have hQ : Filter.Tendsto Q F (nhds 10) := by
    simpa [Q] using
      (((hten.add (hten.mul hxlim)).add (hfive.mul (hxlim.pow 2))).add
        (hxlim.pow 3))
  have hG : Filter.Tendsto G F (nhds (-1 / 2)) := by
    change Filter.Tendsto (fun x => -(S x / Q x)) F (nhds (-1 / 2))
    have hdiv :
        Filter.Tendsto (fun x => S x / Q x) F (nhds (5 / 10)) :=
      hS.div hQ (by norm_num : (10 : ℝ) ≠ 0)
    have hneg :
        Filter.Tendsto (fun x => -(S x / Q x)) F (nhds (-(5 / 10))) :=
      hdiv.neg
    have hnum : (-(5 / 10) : ℝ) = -1 / 2 := by
      norm_num
    rw [hnum] at hneg
    exact hneg
  have hnonzero : ∀ᶠ x in F, x ≠ 0 := by
    simpa [F] using
      (self_mem_nhdsWithin :
        ∀ᶠ x : ℝ in nhdsWithin 0 ({0} : Set ℝ)ᶜ, x ∈ ({0} : Set ℝ)ᶜ)
  have hexp_pow (a : ℝ) :
      Real.exp a ^ 5 = Real.exp ((5 : ℝ) * a) := by
    calc
      Real.exp a ^ 5 =
          Real.exp a * Real.exp a * Real.exp a * Real.exp a * Real.exp a := by
            ring
      _ = Real.exp (a + a + a + a + a) := by
            rw [Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_add]
      _ = Real.exp ((5 : ℝ) * a) := by
            congr 1
            ring
  have heq : G =ᶠ[F] f := by
    filter_upwards [hnear, hnonzero] with x hxnear hxne
    have hbase : 0 < 1 + 5 * x := by linarith
    have hrdef :
        r x = Real.exp (Real.log (1 + 5 * x) * (1 / 5 : ℝ)) := by
      simp only [r, fifthRoot]
      exact Real.rpow_def_of_pos hbase (1 / 5 : ℝ)
    have hpow : r x ^ 5 = 1 + 5 * x := by
      calc
        r x ^ 5 =
            Real.exp
              ((5 : ℝ) * (Real.log (1 + 5 * x) * (1 / 5 : ℝ))) := by
                rw [hrdef, hexp_pow]
        _ = Real.exp (Real.log (1 + 5 * x)) := by
              congr 1
              ring
        _ = 1 + 5 * x := Real.exp_log hbase
    have hfac : (r x - b x) * S x = -x ^ 2 * Q x := by
      calc
        (r x - b x) * S x = r x ^ 5 - b x ^ 5 := by
          simp only [S]
          ring
        _ = -x ^ 2 * Q x := by
          rw [hpow]
          simp only [b, Q]
          ring
    have hqpos : 0 < Q x := by
      simp only [Q]
      by_cases hx0 : 0 ≤ x
      · have hx3 : 0 ≤ x ^ 3 := by positivity
        nlinarith [sq_nonneg x]
      · have hxneg : x < 0 := lt_of_not_ge hx0
        have hunit : 0 < (x + 1) * (1 - x) :=
          mul_pos (by linarith) (by linarith)
        have hx2lt : x ^ 2 < 1 := by nlinarith [hunit]
        have hc0 : 0 ≤ x * (x ^ 2 - 1) :=
          mul_nonneg_of_nonpos_of_nonpos (le_of_lt hxneg) (le_of_lt (by linarith))
        have hc : 0 ≤ x ^ 3 - x := by nlinarith [hc0]
        nlinarith [sq_nonneg x]
    have hQne : Q x ≠ 0 := ne_of_gt hqpos
    have hx2ne : x ^ 2 ≠ 0 := pow_ne_zero 2 hxne
    have hprodne : -x ^ 2 * Q x ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr hx2ne) hQne
    have hden : r x - b x ≠ 0 := by
      intro hd
      apply hprodne
      rw [← hfac, hd, zero_mul]
    change -(S x / Q x) = f x
    symm
    unfold f
    change x ^ 2 / (r x - b x) = -(S x / Q x)
    field_simp [hden, hQne] <;> nlinarith [hfac]
  exact hG.congr' heq

/-- Exercise 451, gap 2. -/
theorem gap2 : HasLimitAt f 0 (-1 / 2) := by
  exact gap1

end

end ProofGap.Exercise451
