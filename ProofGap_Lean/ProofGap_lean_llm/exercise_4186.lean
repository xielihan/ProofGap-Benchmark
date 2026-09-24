import Mathlib

set_option linter.style.longLine false

open scoped BigOperators Topology

open Filter

/-- A textual formalization carrier for generated proof gaps in this no-compile batch.
The full RNFL/FNFL-style assumptions and conclusion are preserved in each theorem comment. -/
def FormalizedGap (_exercise : String) (_gap : Nat) (_assumptions : String) (_goal : String) : Prop := True

/-!
exercise: exercise_4186
Original problem source follows.


===== ORIGINAL | Exercise 4186 =====
【4186】证明：若 1) 函数 $\varphi \left( {x,y}\right)$ 在有界区域 $a \leq  x \leq  A,b \leq  y \leq  B$（其中 $a,A,b,B\in\mathbb R$ 且 $a<A,b<B$） 内连续；2) 函数 $f\left( x\right)$ 在闭区间 $a \leq  x \leq  A$ 上连续；3) $p < 1$且 $p\in\mathbb R$，则积分 ${\int }_{a}^{A}\mathrm{\;d}x{\int }_{b}^{B}\frac{\varphi \left( {x,y}\right) }{{\left| f\left( x\right)  - y\right| }^{p}}\mathrm{\;d}y$ 收敛.

证 首先注意,由于 $p < 1$ ,故积分 ${\int }_{b}^{B}\frac{\mathrm{d}y}{{\left| f\left( x\right)  - y\right| }^{p}}$ 对每个固定的 $x \in  \left\lbrack  {a,A}\right\rbrack$ 恒收敛,(若 $f\left( x\right)  \in  \left\lbrack  {b,B}\right\rbrack$ 此为瑕积分,点 $f\left( x\right)$ 是瑕点,由于 $p < 1$ ,它收敛; 若 $f\left( x\right)  \in  \left\lbrack  {b,B}\right\rbrack$ ,则为常义积分,当然收敛). 再根据 $\varphi \left( {x,y}\right)$ 的有界性,即知: 对每个固定的 $x \in  \left\lbrack  {a,A}\right\rbrack$ ,积分 ${\int }_{b}^{B}\frac{\varphi \left( {x,y}\right) }{{\left| f\left( x\right)  - y\right| }^{p}}\mathrm{\;d}y$ 都收敛. 令

$$
F\left( x\right)  = {\int }_{b}^{B}\frac{\varphi \left( {x,y}\right) }{{\left| f\left( x\right)  - y\right| }^{p}}\mathrm{\;d}y\;\left( {a \leq  x \leq  A}\right) .
$$

下面我们证明 $F\left( x\right)$ 是 $a \leq  x \leq  A$ 上的连续函数. 若已获证,则积分

$$
{\int }_{a}^{A}\mathrm{\;d}x{\int }_{b}^{B}\frac{\varphi \left( {x,y}\right) }{{\left| f\left( x\right)  - y\right| }^{p}}\mathrm{\;d}y = {\int }_{a}^{A}F\left( x\right) \mathrm{d}x
$$

显然是收敛的 (右端为常义积分). 于是本题获证. 令 $c = \mathop{\max }\limits_{{a \leq  x \leq  A++}}}\left| {f\left( x\right) }\right|$ . 今将函数 $\varphi \left( {x,y}\right)$ 连续地延拓到有界闭矩形 $R\left( {a \leq  x \leq  A,b - {2c} \leq  y \leq  B + {2c}}\right)$ 上(只要规定

$$
\varphi \left( {x,y}\right)  = \left\{  \begin{array}{l} \varphi \left( {x,B}\right) ,a \leq  x \leq  A,B < y \leq  B + {2c} \\  \varphi \left( {x,b}\right) ,a \leq  x \leq  A,b - {2c} \leq  y < b \end{array}\right.
$$

即可). 延拓后的函数仍记为 $\varphi \left( {x,y}\right)$ . 由于 $\varphi \left( {x,y}\right)$ 及 ${\left| f\left( x\right)  - y\right| }^{1 - p}$ 都在 $R$ 上连续,故有界且一致连续: 存在常数 $M$ ,使对一切 $\left( {x,y}\right)  \in  R$ ,有

$$
\left| {\varphi \left( {x,y}\right) }\right|  \leq  M.\;{\left| f\left( x\right)  - y\right| }^{1 - p} \leq  M. \tag{1}
$$

任给 $\varepsilon  > 0$ ,存在 ${\delta }_{1} > 0$ (取 ${\delta }_{1} < {\left( \frac{\varepsilon }{2}\right) }^{\frac{1}{1 - p}}$ ),使当 $\left| {{x}_{1} - {x}_{2}}\right|  < {\delta }_{1},\left| {{y}_{1} - {y}_{2}}\right|  < {\delta }_{1}\left( {\left( {{x}_{1},{y}_{1}}\right)  \in  R,\left( {{x}_{2},{y}_{2}}\right)  \in  R}\right)$ 时,

恒有

$$
\left| {\varphi \left( {{x}_{1},{y}_{1}}\right)  - \varphi \left( {{x}_{2},{y}_{2}}\right) }\right|  < \varepsilon , \tag{2}
$$

$$
\left| {{\left| f\left( {x}_{1}\right)  - {y}_{1}\right| }^{1 - p} - {\left| f\left( {x}_{2}\right)  - {y}_{2}\right| }^{1 - p}}\right|  < \varepsilon . \tag{3}
$$

又由 $f\left( x\right)$ 在 $\left\lbrack  {a,A}\right\rbrack$ 上的一致连续性可知,存在 ${\delta }_{2} > 0$ . 使当 $\left| {{x}_{1} - {x}_{2}}\right|  < {\delta }_{2}\left( {{x}_{1},{x}_{2} \in  \left\lbrack  {a,A}\right\rbrack  }\right)$ ,恒有

$$
\left| {f\left( {x}_{1}\right)  - f\left( {x}_{2}\right) }\right|  < {\delta }_{1}. \tag{4}
$$

令 $\delta  = \min \left\{  {{\delta }_{1},{\delta }_{2}}\right\}$ . 于是,由 (2) 式可知: 当 $\left| {{x}_{1} - {x}_{2}}\right|  < \delta \left( {{x}_{1},{x}_{2} \in  \left\lbrack  {a,A}\right\rbrack  }\right)$ 时,对一切 $b - c \leq  y \leq  B + c$ ,恒有

$$
\left| {\varphi \left( {{x}_{1},y + f\left( {x}_{1}\right) }\right)  - \varphi \left( {{x}_{2},y + f\left( {x}_{2}\right) }\right) }\right|  < \varepsilon . \tag{5}
$$

现设 $\left| {{x}_{1} - {x}_{2}}\right|  < \delta ,\left( {{x}_{1},{x}_{2} \in  \left\lbrack  {a,A}\right\rbrack  }\right)$ . 不失一般性,设 $f\left( {x}_{1}\right)  \geq  f\left( {x}_{2}\right)$ ,我们有

$$
F\left( {x}_{1}\right)  - F\left( {x}_{2}\right)  = {\int }_{b}^{B}\frac{\varphi \left( {{x}_{1},y}\right) }{{\left| f\left( {x}_{1}\right)  - y\right| }^{p}}\mathrm{\;d}y - {\int }_{b}^{B}\frac{\varphi \left( {{x}_{2},y}\right) }{{\left| f\left( {x}_{2}\right)  - y\right| }^{p}}\mathrm{\;d}y
$$

$$
= {\int }_{b - f\left( {x}_{1}\right) }^{B - f\left( {x}_{1}\right) }\frac{\varphi \left( {{x}_{1},u + f\left( {x}_{1}\right) }\right) }{{\left| u\right| }^{p}}\mathrm{\;d}u - {\int }_{b - f\left( {x}_{2}\right) }^{B - f\left( {x}_{2}\right) }\frac{\varphi \left( {{x}_{2},u + f\left( {x}_{2}\right) }\right) }{{\left| u\right| }^{p}}\mathrm{\;d}u
$$

$$
= {\int }_{b - f\left( {x}_{1}\right) }^{B - f\left( {x}_{2}\right) }\frac{\varphi \left( {{x}_{1},u + f\left( {x}_{1}\right) }\right)  - \varphi \left( {{x}_{2},u + f\left( {x}_{2}\right) }\right) }{{\left| u\right| }^{p}}\mathrm{\;d}u - {\int }_{B - f\left( {x}_{1}\right) }^{B - f\left( {x}_{2}\right) }\frac{\varphi \left( {{x}_{1},u + f\left( {x}_{1}\right) }\right) }{{\left| u\right| }^{p}}\mathrm{\;d}u
$$

$$
+ {\int }_{b - f\left( {x}_{1}\right) }^{b - f\left( {x}_{2}\right) }\frac{\varphi \left( {{x}_{2},u + f\left( {x}_{2}\right) }\right) }{{\left| u\right| }^{p}}\mathrm{\;d}u
$$

$$
= {I}_{1} - {I}_{2} + {I}_{3}, \tag{6}
$$

其中 ${I}_{1},{I}_{2},{I}_{3}$ 分别表上式中的三个积分. 易知 $\left( {p < 1}\right)$

$$
{\int }_{\alpha }^{\beta }\frac{\mathrm{d}u}{{\left| u\right| }^{p}} = \left\{  \begin{array}{ll} \frac{1}{1 - p}\left\lbrack  {{\beta }^{1 - p} - {\alpha }^{1 - p}}\right\rbrack  , & 0 \leq  \alpha  \leq  \beta , \\  \frac{1}{1 - p}\left\lbrack  {{\left( -\alpha \right) }^{1 - p} - {\left( -\beta \right) }^{1 - p}}\right\rbrack  , & \alpha  \leq  \beta  \leq  0, \\  \frac{1}{1 - p}\left\lbrack  {{\beta }^{1 - p} + {\left( -\alpha \right) }^{1 - p}}\right\rbrack  , & \alpha  < 0 < \beta . \end{array}\right.
$$

从而, 在任何情形下均有

$$
{\int }_{\alpha }^{\beta }\frac{\mathrm{d}u}{{\left| u\right| }^{p}} \leq  \frac{1}{1 - p}\left( {{\left| \beta \right| }^{1 - p} + {\left| \alpha \right| }^{1 - p}}\right) ; \tag{7}
$$

而当 $\alpha ,\beta$ 同号时,有

$$
{\int }_{\alpha }^{\beta }\frac{\mathrm{d}u}{{\left| u\right| }^{p}} = \frac{1}{1 - p}\left| {{\left| \beta \right| }^{1 - p} - {\left| \alpha \right| }^{1 - p}}\right| . \tag{8}
$$

于是,由 (5) 式、(1) 式及 (7) 式,得

$$
\left| {I}_{1}\right|  < \varepsilon {\int }_{b - f\left( {x}_{1}\right) }^{b - f\left( {x}_{2}\right) }\frac{\mathrm{d}u}{{\left| u\right| }^{p}} \leq  \frac{\varepsilon }{1 - p}\left( {{\left| B - f\left( {x}_{2}\right) \right| }^{1 - p} + {\left| b - f\left( {x}_{1}\right) \right| }^{1 - p}}\right)  \leq  \frac{2M\varepsilon }{1 - p}. \tag{9}
$$

下面估计 ${I}_{2}$ : 若 $B - f\left( {x}_{2}\right)$ 与 $B - f\left( {x}_{1}\right)$ 同号,则由 (1) 式、(8) 式及 (3) 式,有

$$
\left| {I}_{2}\right|  \leq  M{\int }_{B - f\left( {x}_{1}\right) }^{B - f\left( {x}_{2}\right) }\frac{\mathrm{d}u}{{\left| u\right| }^{p}} = \frac{M}{1 - p}{\left| B - f\left( {x}_{2}\right) \right| }^{1 - p} - {\left| B - f\left( {x}_{1}\right) \right| }^{1 - p}\left|  < \right| \frac{M\varepsilon }{1 - p};
$$

若 $B - f\left( {x}_{2}\right)$ 与 $B - f\left( {x}_{1}\right)$ 异号,即 $B - f\left( {x}_{1}\right)  < 0 < B - f\left( {x}_{2}\right)$ . 由于 $\left\lbrack  {B - f\left( {x}_{2}\right) }\right\rbrack   - \left\lbrack  {B - f\left( {x}_{1}\right) }\right\rbrack   = f\left( {x}_{1}\right)$ $- f\left( {x}_{2}\right)  < {\delta }_{1}$ ,故有 $\left| {B - f\left( {x}_{1}\right) }\right|  < {\delta }_{1},\left| {B - f\left( {x}_{2}\right) }\right|  < {\delta }_{1}$ . 于是,由 (7) 式并注意到 ${\delta }_{1} < {\left( \frac{\varepsilon }{2}\right) }^{\frac{1}{1 - p}}$ ,即得

$$
\left| {I}_{2}\right|  \leq  M{\int }_{B - f\left( {x}_{1}\right) }^{B - f\left( {x}_{2}\right) }\frac{\mathrm{d}u}{{\left| u\right| }^{p}} \leq  \frac{M}{1 - p}\left( {{\left| B - f\left( {x}_{2}\right) \right| }^{1 - p} + {\left| B - f\left( {x}_{1}\right) \right| }^{1 - p}}\right)  < \frac{M}{1 - p}\left( {{\delta }_{i}^{1 - p} + {\delta }_{i}^{1 - p}}\right)  < \frac{M\varepsilon }{1 - p}.
$$

所以, 在任何情况下均有

$$
\left| {I}_{2}\right|  < \frac{M\varepsilon }{1 - p} \tag{10}
$$

同理, 可得 (在任何情况下)

$$
\left| {I}_{3}\right|  < \frac{M\varepsilon }{1 - p} \tag{11}
$$

于是,由 (6) 式、(9)式、(10)式及(11)式,即得

$$
\left| {F\left( {x}_{1}\right)  - F\left( {x}_{2}\right) }\right|  < \left| {I}_{1}\right|  + \left| {I}_{2}\right|  + \left| {I}_{3}\right|  < \frac{4M\varepsilon }{1 - p}.
$$

由此可知, $F\left( x\right)$ 在 $a \leq  x \leq  A$ 上 (一致) 连续,证毕.

-/

/-
Exercise 4186, gap 1
PROOF GAP @1
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞

METHOD:
-/
theorem proof_gap_exercise_4186_1 :
    FormalizedGap "exercise_4186" 1 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])" "forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞" := by
  sorry

/-
Exercise 4186, gap 2
PROOF GAP @2
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞

METHOD:
-/
theorem proof_gap_exercise_4186_2 :
    FormalizedGap "exercise_4186" 2 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞" "forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞" := by
  sorry

/-
Exercise 4186, gap 3
PROOF GAP @3
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞

GOAL:
forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞

METHOD:
[@method 根据 "φ在有界闭区域上有界及比较判别法" @]
-/
theorem proof_gap_exercise_4186_3 :
    FormalizedGap "exercise_4186" 3 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞" "forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞" := by
  sorry

/-
Exercise 4186, gap 4
PROOF GAP @4
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])

GOAL:
ContinuousFuncOn(φ, R)

METHOD:
-/
theorem proof_gap_exercise_4186_4 :
    FormalizedGap "exercise_4186" 4 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])" "ContinuousFuncOn(φ, R)" := by
  sorry

/-
Exercise 4186, gap 5
PROOF GAP @5
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)

GOAL:
ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)

METHOD:
-/
theorem proof_gap_exercise_4186_5 :
    FormalizedGap "exercise_4186" 5 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)" "ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)" := by
  sorry

/-
Exercise 4186, gap 6
PROOF GAP @6
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)

GOAL:
UniformContinuousFuncOn(φ, R)

METHOD:
-/
theorem proof_gap_exercise_4186_6 :
    FormalizedGap "exercise_4186" 6 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)" "UniformContinuousFuncOn(φ, R)" := by
  sorry

/-
Exercise 4186, gap 7
PROOF GAP @7
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)

GOAL:
UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)

METHOD:
-/
theorem proof_gap_exercise_4186_7 :
    FormalizedGap "exercise_4186" 7 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)" "UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)" := by
  sorry

/-
Exercise 4186, gap 8
PROOF GAP @8
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)

GOAL:
exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)

METHOD:
-/
theorem proof_gap_exercise_4186_8 :
    FormalizedGap "exercise_4186" 8 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)" "exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)" := by
  sorry

/-
Exercise 4186, gap 9
PROOF GAP @9
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))

METHOD:
-/
theorem proof_gap_exercise_4186_9 :
    FormalizedGap "exercise_4186" 9 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))" := by
  sorry

/-
Exercise 4186, gap 10
PROOF GAP @10
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))

METHOD:
-/
theorem proof_gap_exercise_4186_10 :
    FormalizedGap "exercise_4186" 10 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))" := by
  sorry

/-
Exercise 4186, gap 11
PROOF GAP @11
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))

METHOD:
-/
theorem proof_gap_exercise_4186_11 :
    FormalizedGap "exercise_4186" 11 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))" := by
  sorry

/-
Exercise 4186, gap 12
PROOF GAP @12
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))

METHOD:
-/
theorem proof_gap_exercise_4186_12 :
    FormalizedGap "exercise_4186" 12 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))" := by
  sorry

/-
Exercise 4186, gap 13
PROOF GAP @13
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))

METHOD:
-/
theorem proof_gap_exercise_4186_13 :
    FormalizedGap "exercise_4186" 13 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))" := by
  sorry

/-
Exercise 4186, gap 14
PROOF GAP @14
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))

METHOD:
-/
theorem proof_gap_exercise_4186_14 :
    FormalizedGap "exercise_4186" 14 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))" := by
  sorry

/-
Exercise 4186, gap 15
PROOF GAP @15
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))

METHOD:
-/
theorem proof_gap_exercise_4186_15 :
    FormalizedGap "exercise_4186" 15 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))" := by
  sorry

/-
Exercise 4186, gap 16
PROOF GAP @16
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))

METHOD:
-/
theorem proof_gap_exercise_4186_16 :
    FormalizedGap "exercise_4186" 16 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))" := by
  sorry

/-
Exercise 4186, gap 17
PROOF GAP @17
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))

METHOD:
-/
theorem proof_gap_exercise_4186_17 :
    FormalizedGap "exercise_4186" 17 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))" := by
  sorry

/-
Exercise 4186, gap 18
PROOF GAP @18
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))

METHOD:
-/
theorem proof_gap_exercise_4186_18 :
    FormalizedGap "exercise_4186" 18 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))" := by
  sorry

/-
Exercise 4186, gap 19
PROOF GAP @19
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))
40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))

GOAL:
forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))

METHOD:
[@method 同理 @]
-/
theorem proof_gap_exercise_4186_19 :
    FormalizedGap "exercise_4186" 19 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))\n40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))" "forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))" := by
  sorry

/-
Exercise 4186, gap 20
PROOF GAP @20
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))
40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))

GOAL:
ContinuousFuncOn(F, [a, A])

METHOD:
-/
theorem proof_gap_exercise_4186_20 :
    FormalizedGap "exercise_4186" 20 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))\n40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))" "ContinuousFuncOn(F, [a, A])" := by
  sorry

/-
Exercise 4186, gap 21
PROOF GAP @21
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))
40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
42. ContinuousFuncOn(F, [a, A])

GOAL:
ContinuousFuncOn(F, [a, A])

METHOD:
-/
theorem proof_gap_exercise_4186_21 :
    FormalizedGap "exercise_4186" 21 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))\n40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n42. ContinuousFuncOn(F, [a, A])" "ContinuousFuncOn(F, [a, A])" := by
  sorry

/-
Exercise 4186, gap 22
PROOF GAP @22
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))
40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
42. ContinuousFuncOn(F, [a, A])
43. ContinuousFuncOn(F, [a, A])

GOAL:
DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))

METHOD:
-/
theorem proof_gap_exercise_4186_22 :
    FormalizedGap "exercise_4186" 22 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))\n40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n42. ContinuousFuncOn(F, [a, A])\n43. ContinuousFuncOn(F, [a, A])" "DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))" := by
  sorry

/-
Exercise 4186, gap 23
PROOF GAP @23
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))
40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
42. ContinuousFuncOn(F, [a, A])
43. ContinuousFuncOn(F, [a, A])
44. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))

GOAL:
DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞

METHOD:
-/
theorem proof_gap_exercise_4186_23 :
    FormalizedGap "exercise_4186" 23 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))\n40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n42. ContinuousFuncOn(F, [a, A])\n43. ContinuousFuncOn(F, [a, A])\n44. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))" "DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞" := by
  sorry

/-
Exercise 4186, gap 24
PROOF GAP @24
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))
40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
42. ContinuousFuncOn(F, [a, A])
43. ContinuousFuncOn(F, [a, A])
44. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))
45. DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞

GOAL:
DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞

METHOD:
-/
theorem proof_gap_exercise_4186_24 :
    FormalizedGap "exercise_4186" 24 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))\n40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n42. ContinuousFuncOn(F, [a, A])\n43. ContinuousFuncOn(F, [a, A])\n44. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))\n45. DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞" "DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞" := by
  sorry

/-
Exercise 4186, gap 25
PROOF GAP @25
ASSUM:
1. a ∈ RealSet
2. A ∈ RealSet
3. b ∈ RealSet
4. B ∈ RealSet
5. p ∈ RealSet
6. φ : CartesianProd(RealSet, RealSet) → RealSet
7. f : RealSet → RealSet
8. F : RealSet → RealSet
9. R ⊆ CartesianProd(RealSet, RealSet)
10. a < A
11. b < B
12. p < 1
13. R = CartesianProd([a, A], [b, B])
14. ContinuousFuncOn(φ, R)
15. ContinuousFuncOn(f, [a, A])
16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞
19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))
20. c = max({ |f(x)| | x ∈ [a, A] })
21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])
22. ContinuousFuncOn(φ, R)
23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
24. UniformContinuousFuncOn(φ, R)
25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)
26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)
27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))
28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))
29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))
30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))
31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))
35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))
36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))
37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))
38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))
39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))
40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))
42. ContinuousFuncOn(F, [a, A])
43. ContinuousFuncOn(F, [a, A])
44. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))
45. DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞
46. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞

GOAL:
DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞

METHOD:
-/
theorem proof_gap_exercise_4186_25 :
    FormalizedGap "exercise_4186" 25 "1. a ∈ RealSet\n2. A ∈ RealSet\n3. b ∈ RealSet\n4. B ∈ RealSet\n5. p ∈ RealSet\n6. φ : CartesianProd(RealSet, RealSet) → RealSet\n7. f : RealSet → RealSet\n8. F : RealSet → RealSet\n9. R ⊆ CartesianProd(RealSet, RealSet)\n10. a < A\n11. b < B\n12. p < 1\n13. R = CartesianProd([a, A], [b, B])\n14. ContinuousFuncOn(φ, R)\n15. ContinuousFuncOn(f, [a, A])\n16. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∈ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n17. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ∧ f(x) ∉ [b, B] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(1, |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n18. forall (x), x ∈ RealSet ∧ x ∈ [a, A] ⇒ DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)) < +∞\n19. F = (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y)))\n20. c = max({ |f(x)| | x ∈ [a, A] })\n21. R = CartesianProd([a, A], [b - 2 * c, B + 2 * c])\n22. ContinuousFuncOn(φ, R)\n23. ContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n24. UniformContinuousFuncOn(φ, R)\n25. UniformContinuousFuncOn(fun x, y [x ∈ RealSet ∧ y ∈ RealSet] . |f(x) - y|^{1 - p}, R)\n26. exists (M), M ∈ RealSet ∧ M > 0 ∧ (forall (x) (y), x ∈ RealSet ∧ y ∈ RealSet ∧ (x, y) ∈ R ⇒ |φ(x, y)| ≤ M ∧ |f(x) - y|^{1 - p} ≤ M)\n27. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{1} < frac(ε, 2)^{frac(1, 1 - p)} ∧ (forall (x_{1}) (x_{2}) (y_{1}) (y_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ y_{1} ∈ RealSet ∧ y_{2} ∈ RealSet ∧ (x_{1}, y_{1}) ∈ R ∧ (x_{2}, y_{2}) ∈ R ∧ |x_{1} - x_{2}| < δ_{1} ∧ |y_{1} - y_{2}| < δ_{1} ⇒ |φ(x_{1}, y_{1}) - φ(x_{2}, y_{2})| < ε ∧ ||f(x_{1}) - y_{1}|^{1 - p} - |f(x_{2}) - y_{2}|^{1 - p}| < ε))\n28. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ_{1}) (δ_{2}), δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ (forall (x_{1}) (x_{2}), x_{1} ∈ RealSet ∧ x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ_{2} ⇒ |f(x_{1}) - f(x_{2})| < δ_{1}))\n29. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (δ_{1}) (δ_{2}), δ ∈ RealSet ∧ δ > 0 ∧ δ_{1} ∈ RealSet ∧ δ_{1} > 0 ∧ δ_{2} ∈ RealSet ∧ δ_{2} > 0 ∧ δ = min(δ_{1}, δ_{2}))\n30. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (u), u ∈ RealSet ∧ b - c ≤ u ∧ u ≤ B + c ⇒ |φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2}))| < ε))))\n31. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) - DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) + DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n32. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{1} = DefInt(b - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})) - φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n33. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{2} = DefInt(B - f(x_{1}), B - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{1}, u + f(x_{1})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n34. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ I_{3} = DefInt(b - f(x_{1}), b - f(x_{2}), (fun u [u ∈ RealSet] . frac(φ(x_{2}, u + f(x_{2})), |u|^{p})) * diff(fun u [u ∈ RealSet] . u)))))\n35. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (I_{2}) (I_{3}), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ I_{2} ∈ RealSet ∧ I_{3} ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ F(x_{1}) - F(x_{2}) = I_{1} - I_{2} + I_{3})))\n36. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ), δ ∈ RealSet ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ (forall (α) (β), α ∈ RealSet ∧ β ∈ RealSet ∧ p < 1 ∧ α ≤ β ⇒ DefInt(α, β, (fun u [u ∈ RealSet] . frac(1, |u|^{p})) * diff(fun u [u ∈ RealSet] . u)) ≤ frac(1, 1 - p) * (|β|^{1 - p} + |α|^{1 - p})))))\n37. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{1}) (M), δ ∈ RealSet ∧ I_{1} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{1}| < frac(2 * M * ε, 1 - p))))\n38. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{2}) (M), δ ∈ RealSet ∧ I_{2} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{2}| < frac(M * ε, 1 - p))))\n39. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (I_{3}) (M), δ ∈ RealSet ∧ I_{3} ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |I_{3}| < frac(M * ε, 1 - p))))\n40. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) ≥ f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n41. forall (ε), ε ∈ RealSet ∧ ε > 0 ⇒ (exists (δ) (M), δ ∈ RealSet ∧ M ∈ RealSet ∧ M > 0 ∧ δ > 0 ∧ (forall (x_{1}), x_{1} ∈ RealSet ⇒ (forall (x_{2}), x_{2} ∈ RealSet ∧ x_{1} ∈ [a, A] ∧ x_{2} ∈ [a, A] ∧ |x_{1} - x_{2}| < δ ∧ f(x_{1}) < f(x_{2}) ⇒ |F(x_{1}) - F(x_{2})| < frac(4 * M * ε, 1 - p))))\n42. ContinuousFuncOn(F, [a, A])\n43. ContinuousFuncOn(F, [a, A])\n44. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) = DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x))\n45. DefInt(a, A, F * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞\n46. DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞" "DefInt(a, A, (fun x [x ∈ RealSet ∧ x ∈ [a, A]] . DefInt(b, B, (fun y [y ∈ RealSet ∧ y ∈ [b, B]] . frac(φ(x, y), |f(x) - y|^{p})) * diff(fun y [y ∈ RealSet ∧ y ∈ [b, B]] . y))) * diff(fun x [x ∈ RealSet ∧ x ∈ [a, A]] . x)) < +∞" := by
  sorry
