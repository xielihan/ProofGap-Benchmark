import Mathlib

set_option linter.style.longLine false

noncomputable section

local notation:70 x:71 " /. " y:71 => ((x : ℝ) / (y : ℝ))

abbrev Region3 := Set (ℝ × ℝ × ℝ)

noncomputable def DefInt (a b : ℝ) (f : ℝ → ℝ) : ℝ := ∫ x in a..b, f x
noncomputable def diff {α : Type*} (_x : α) : ℝ := 1
noncomputable def Jac3 {α β γ : Type*} (_a : α) (_b : β) (_c : γ) : ℝ := 0

-- exercise: exercise_4123
-- source: substitution u=x/a, v=x/a+y/b, w=x/a+y/b+z/c.

def Region4123xyz (a b c : ℝ) : Region3 :=
  {p | ((p.1 /. a + p.2.1 /. b) /. (p.1 /. a + p.2.1 /. b + p.2.2 /. c)) =
         (2 /. Real.pi) * Real.arcsin (p.1 /. a + p.2.1 /. b + p.2.2 /. c) ∧
       p.1 /. a + p.2.1 /. b = 1 ∧ (p.1 = 0 ∨ p.1 = a) ∧
       p.1 /. a + p.2.1 /. b + p.2.2 /. c ≠ 0 ∧
       -1 ≤ p.1 /. a + p.2.1 /. b + p.2.2 /. c ∧ p.1 /. a + p.2.1 /. b + p.2.2 /. c ≤ 1}

def Region4123uvw : Region3 :=
  {p | 0 ≤ p.1 ∧ p.1 ≤ 1 ∧ -1 ≤ p.2.2 ∧ p.2.2 ≤ 1 ∧
       (2 /. Real.pi) * p.2.2 * Real.arcsin p.2.2 ≤ p.2.1 ∧ p.2.1 ≤ 1}

def Int4123Full (a b c : ℝ) : ℝ :=
  a * b * c * DefInt 0 1 (fun u =>
    DefInt (-1) 1 (fun w => DefInt ((2 /. Real.pi) * w * Real.arcsin w) 1 (fun v => diff v) * diff w) * diff u)

def Int4123Even (a b c : ℝ) : ℝ :=
  2 * a * b * c * DefInt 0 1 (fun w => (1 - (2 /. Real.pi) * w * Real.arcsin w) * diff w)

def Int4123Parts (a b c : ℝ) : ℝ :=
  2 * a * b * c - ((2 * a * b * c) /. Real.pi) * DefInt 0 1 (fun w => Real.arcsin w * diff (w ^ 2))

def Int4123Sqrt (a b c : ℝ) : ℝ :=
  a * b * c + ((2 * a * b * c) /. Real.pi) * DefInt 0 1 (fun w => w ^ 2 * (1 - w ^ 2) ^ (-(1 /. 2)) * diff w)

def Int4123BetaIntegral (a b c : ℝ) : ℝ :=
  a * b * c + (a * b * c * DefInt 0 1 (fun t => t ^ (1 /. 2) * (1 - t) ^ (-(1 /. 2)) * diff t)) /. Real.pi

theorem proof_gap_exercise_4123_1
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c) :
  Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c) := by
  sorry

theorem proof_gap_exercise_4123_2
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) :
  Jac3 x y z /. Jac3 u v w = a * b * c := by
  sorry

theorem proof_gap_exercise_4123_3
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c))
  (h16 : Jac3 x y z /. Jac3 u v w = a * b * c) :
  V = Region4123uvw := by
  sorry

theorem proof_gap_exercise_4123_4
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) (h16 : Jac3 x y z /. Jac3 u v w = a * b * c)
  (h17 : V = Region4123uvw) :
  Vol = Int4123Full a b c := by
  sorry

theorem proof_gap_exercise_4123_5
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) (h16 : Jac3 x y z /. Jac3 u v w = a * b * c)
  (h17 : V = Region4123uvw) (h18 : Vol = Int4123Full a b c) :
  Vol = Int4123Even a b c := by
  sorry

theorem proof_gap_exercise_4123_6
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) (h16 : Jac3 x y z /. Jac3 u v w = a * b * c)
  (h17 : V = Region4123uvw) (h18 : Vol = Int4123Full a b c) (h19 : Vol = Int4123Even a b c) :
  Vol = Int4123Parts a b c := by
  sorry

theorem proof_gap_exercise_4123_7
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) (h16 : Jac3 x y z /. Jac3 u v w = a * b * c)
  (h17 : V = Region4123uvw) (h18 : Vol = Int4123Full a b c) (h19 : Vol = Int4123Even a b c)
  (h20 : Vol = Int4123Parts a b c) :
  Vol = Int4123Sqrt a b c := by
  sorry

theorem proof_gap_exercise_4123_8
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) (h16 : Jac3 x y z /. Jac3 u v w = a * b * c)
  (h17 : V = Region4123uvw) (h18 : Vol = Int4123Full a b c) (h19 : Vol = Int4123Even a b c)
  (h20 : Vol = Int4123Parts a b c) (h21 : Vol = Int4123Sqrt a b c) :
  Vol = Int4123BetaIntegral a b c := by
  sorry

theorem proof_gap_exercise_4123_9
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) (h16 : Jac3 x y z /. Jac3 u v w = a * b * c)
  (h17 : V = Region4123uvw) (h18 : Vol = Int4123Full a b c) (h19 : Vol = Int4123Even a b c)
  (h20 : Vol = Int4123Parts a b c) (h21 : Vol = Int4123Sqrt a b c)
  (h22 : Vol = Int4123BetaIntegral a b c) :
  Vol = a * b * c + (a * b * c * B ((3 /. 2), (1 /. 2))) /. Real.pi := by
  sorry

theorem proof_gap_exercise_4123_10
  (a b c x y z Vol D : ℝ) (V : Region3) (B : ℝ × ℝ → ℝ) (u v w : ℝ → ℝ → ℝ → ℝ)
  (ha : a > 0) (hb : b > 0) (hc : c > 0) (hV : V = Region4123xyz a b c)
  (hu : u = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a)
  (hv : v = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b)
  (hw : w = fun x : ℝ => fun y : ℝ => fun z : ℝ => x /. a + y /. b + z /. c)
  (h15 : Jac3 u v w /. Jac3 x y z = 1 /. (a * b * c)) (h16 : Jac3 x y z /. Jac3 u v w = a * b * c)
  (h17 : V = Region4123uvw) (h18 : Vol = Int4123Full a b c) (h19 : Vol = Int4123Even a b c)
  (h20 : Vol = Int4123Parts a b c) (h21 : Vol = Int4123Sqrt a b c)
  (h22 : Vol = Int4123BetaIntegral a b c)
  (h23 : Vol = a * b * c + (a * b * c * B ((3 /. 2), (1 /. 2))) /. Real.pi) :
  Vol = (3 /. 2) * a * b * c := by
  sorry
