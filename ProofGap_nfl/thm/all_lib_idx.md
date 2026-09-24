Thm 1. (EmptySetSubset)
forall (A), (∅ ⊆ A)

Thm 2. (EmptySetHasNoElements)
forall (A), Not (A ∈ ∅)

Thm 3. (SubsetFromElementImplication)
forall (A) (B), (forall (x), (x ∈ A) => (x ∈ B)) => (A ⊆ B)

Thm 4. (ElementImplicationFromSubset)
forall (A) (B), (A ⊆ B) => (forall (x), (x ∈ A) => (x ∈ B))

Thm 5. (SingletonSubset)
forall (A) (x), (x ∈ A) => ({x} ⊆ A)

Thm 6. (SubsetTransitive)
forall (A) (B) (C), (A ⊆ B) => (B ⊆ C) => (A ⊆ C)

Thm 7. (EqualSetsLeftSubset)
forall (A) (B), (A = B) => (A ⊆ B)

Thm 8. (EqualSetsRightSubset)
forall (A) (B), (A = B) => (B ⊆ A)

Thm 9. (SetEqualityFromMutualSubset)
forall (A) (B), (A ⊆ B) => (B ⊆ A) => (A = B)

Thm 10. (IntersectionMemberLeft)
forall (A) (B) (x), (x ∈ A ∩ B) => (x ∈ A)

Thm 11. (IntersectionMemberRight)
forall (A) (B) (x), (x ∈ A ∩ B) => (x ∈ B)

Thm 12. (IntersectionMemberIntro)
forall (A) (B) (x), (x ∈ A) => (x ∈ B) => (x ∈ A ∩ B)

Thm 13. (UnionMemberElim)
forall (A) (B) (x), (x ∈ A ∪ B) => ((x ∈ A) \/ (x ∈ B))

Thm 14. (UnionMemberLeftIntro)
forall (A) (B) (x), (x ∈ A) => (x ∈ A ∪ B)

Thm 15. (UnionMemberRightIntro)
forall (A) (B) (x), (x ∈ B) => (x ∈ A ∪ B)

Thm 16. (SetDifferenceMemberElim)
forall (A) (B) (x), (x ∈ SetMinus(A, B)) => ((x ∈ A) /\ Not(x ∈ B))

Thm 17. (SetDifferenceMemberIntro)
forall (A) (B) (x), (x ∈ A) => Not(x ∈ B) => (x ∈ SetMinus(A, B))

Thm 18. (OrderedPairEqualityFirst)
forall (a) (b) (c) (d), ((a, b) = (c, d)) => (a = c)

Thm 19. (OrderedPairEqualitySecond)
forall (a) (b) (c) (d), ((a, b) = (c, d)) => (b = d)

Thm 20. (OrderedPairEqualityIntro)
forall (a) (b) (c) (d), (a = c) => (b = d) => ((a, b) = (c, d))

Thm 21. (PowerSetMemberElim)
forall (A) (B), (B ∈ PowerSet(A)) => (B ⊆ A)

Thm 22. (PowerSetMemberIntro)
forall (A) (B), (B ⊆ A) => (B ∈ PowerSet(A))

Thm 23. (GeneralUnionMemberElim)
forall (A) (B), (B ∈ GeneralUnion(A)) => (exists (C), (C ∈ A) /\ (B ∈ C))

Thm 24. (GeneralUnionMemberIntro)
forall (A) (B), (exists (C), (C ∈ A) /\ (B ∈ C)) => (B ∈ GeneralUnion(A))

Thm 25. (IndexedUnionMember)
forall (x) (y), (y ∈ union_{i=0}^{infty}(x_i)) => (exists (n), (n ∈ NonNegIntegerSet) /\ (y ∈ x_n))

Thm 26. (IndexedIntersectionMember)
forall (x) (y), (forall (n), (n ∈ NonNegIntegerSet) => (y ∈ x_n)) => (y ∈ inter_{i=0}^{infty}(x_i))

Thm 27. (CartesianProductSetBuilder)
forall (A) (B), CartesianProd(A,B) = { (a,b) | a ∈ A /\ b ∈ B }

Thm 28. (CartesianProductMemberLeft)
forall (A) (B) (a) (b), ((a,b) ∈ CartesianProd(A,B)) => (a ∈ A)

Thm 29. (CartesianProductMemberRight)
forall (A) (B) (a) (b), ((a,b) ∈ CartesianProd(A,B)) => (b ∈ B)

Thm 30. (CartesianProductMemberIntro)
forall (A) (B) (a) (b), (a ∈ A) => (b ∈ B) => ((a,b) ∈ CartesianProd(A,B))

Thm 31. (ReflexiveRelationElim)
forall (S) (R) (a), (R ⊆ CartesianProd(S,S)) => ReflexiveBinRel(R) => (a ∈ S) => ((a, a) ∈ R)

Thm 32. (ReflexiveRelationIntro)
forall (S) (R), (R ⊆ CartesianProd(S,S)) => ((forall (a), (a ∈ S) => ((a, a) ∈ R)) => ReflexiveBinRel(R))

Thm 33. (SymmetricRelationElim)
forall (R) (a) (b), SymmetricBinRel(R) => ((a, b) ∈ R) => ((b, a) ∈ R)

Thm 34. (SymmetricRelationIntro)
forall (S) (R), (R ⊆ CartesianProd(S,S)) => ((forall (a) (b), (a ∈ S) => (b ∈ S) => ((a, b) ∈ R) => ((b, a) ∈ R)) => SymmetricBinRel(R))

Thm 35. (AntisymmetricRelationElim)
forall (R) (a) (b), AntisymmetricBinRel(R) => ((a, b) ∈ R) => ((b, a) ∈ R) => (a = b)

Thm 36. (AntisymmetricRelationIntro)
forall (S) (R), (R ⊆ CartesianProd(S,S)) => ((forall (a) (b), (a ∈ S) => (b ∈ S) => ((a, b) ∈ R) => ((b, a) ∈ R) => (a = b)) => AntisymmetricBinRel(R))

Thm 37. (TransitiveRelationElim)
forall (R) (a) (b) (c), TransitiveBinRel(R) => ((a, b) ∈ R) => ((b, c) ∈ R) => ((a, c) ∈ R)

Thm 38. (TransitiveRelationIntro)
forall (S) (R), (R ⊆ CartesianProd(S,S)) => ((forall (a) (b) (c), (a ∈ S) => (b ∈ S) => (c ∈ S) => ((a, b) ∈ R) => ((b, c) ∈ R) => ((a, c) ∈ R)) => TransitiveBinRel(R))

Thm 39. (InverseRelationMemberIntro)
forall (R) (a) (b), ((a, b) ∈ R) => ((b, a) ∈ InverseBinRel(R))

Thm 40. (InverseRelationMemberElim)
forall (R) (a) (b), ((b, a) ∈ InverseBinRel(R)) => ((a, b) ∈ R)

Thm 41. (InverseRelationMonotone)
forall (R1) (R2), (R1 ⊆ R2) => (InverseBinRel(R1) ⊆ InverseBinRel(R2))

Thm 42. (InverseRelationCongruent)
forall (R1) (R2), (R1 = R2) => (InverseBinRel(R1) = InverseBinRel(R2))

Thm 43. (RelationCompositionElim)
forall (R1) (R2) (a) (b), ((a, b) ∈ R1 ∘ R2) => (exists (c), ((a, c) ∈ R2) /\ ((c, b) ∈ R1))

Thm 44. (RelationCompositionIntro)
forall (R1) (R2) (a) (b), (exists (c), ((a, c) ∈ R1) /\ ((c, b) ∈ R2)) => ((a, b) ∈ R2 ∘ R1)

Thm 45. (EquivalenceImpliesReflexive)
forall (R), EquivalenceBinRel(R) => ReflexiveBinRel(R)

Thm 46. (EquivalenceImpliesSymmetric)
forall (R), EquivalenceBinRel(R) => SymmetricBinRel(R)

Thm 47. (EquivalenceImpliesTransitive)
forall (R), EquivalenceBinRel(R) => TransitiveBinRel(R)

Thm 48. (EquivalenceRelationIntro)
forall (R), ReflexiveBinRel(R) => SymmetricBinRel(R) => TransitiveBinRel(R) => EquivalenceBinRel(R)

Thm 49. (EquivalenceClassSetBuilder)
forall (R) (a), EquivClass(a, R) = {b | (a, b) ∈ R}

Thm 50. (EquivalenceClassMemberElim)
forall (R) (a) (b), (b ∈ EquivClass(a, R)) => ((a, b) ∈ R)

Thm 51. (EquivalenceClassReverseMember)
forall (R) (a) (b), (b ∈ EquivClass(a, R)) => ((b, a) ∈ R)

Thm 52. (EquivalenceClassMemberIntro)
forall (R) (a) (b), ((a, b) ∈ R) => (b ∈ EquivClass(a, R))

Thm 53. (EquivalenceClassReverseIntro)
forall (R) (a) (b), ((a, b) ∈ R) => (a ∈ EquivClass(b, R))

Thm 54. (PartitionBlocksNonempty)
forall (A) (P), SetPartition(P,A) => (forall (B), (B ∈ P) => Not(B = ∅))

Thm 55. (PartitionBlocksDisjoint)
forall (A) (P), SetPartition(P,A) => (forall (B) (C), Not(B = C) => (B ∩ C = ∅))

Thm 56. (PartitionCoversSet)
forall (A) (P), SetPartition(P,A) => (GeneralUnion(P) = A)

Thm 57. (SetPartitionIntro)
forall (A) (P), (forall (B), (B ∈ P) => Not(B = ∅)) => (forall (B) (C), Not(B = C) => (B ∩ C = ∅)) => (GeneralUnion(P) = A) => SetPartition(P,A)

Thm 58. (SetPartitionPropertiesForward)
forall (A) (P), SetPartition(P, A) => ((forall (a), (a ∈ A) => exists (B), (B ∈ P) /\ (a ∈ B)) /\ (forall (a) (B1) (B2), (a ∈ A) /\ (B1 ∈ P) /\ (B2 ∈ P) /\ (a ∈ B1) /\ (a ∈ B2) => (B1 = B2)) /\ (forall (B), (B ∈ P) => exists (x), (x ∈ A) /\ (x ∈ B)))

Thm 59. (SetPartitionPropertiesReverse)
forall (A) (P), ((forall (a), (a ∈ A) => exists (B), (B ∈ P) /\ (a ∈ B)) /\ (forall (a) (B1) (B2), (a ∈ A) /\ (B1 ∈ P) /\ (B2 ∈ P) /\ (a ∈ B1) /\ (a ∈ B2) => (B1 = B2)) /\ (forall (B), (B ∈ P) => exists (x), (x ∈ A) /\ (x ∈ B))) => SetPartition(P, A)

Thm 60. (UniquePartitionBlock)
forall (A) (P) (a), SetPartition(P, A) => (a ∈ A) => (exists (B), (B ∈ P) /\ (a ∈ B) /\ (forall (C), (C ∈ P) /\ (a ∈ C) => (C = B)))

Thm 61. (TransitiveClosureDefinition)
forall (R) (R0), (R0 ⊆ R) => TransitiveBinRel(R) => (forall (T), (R0 ⊆ T) => (TransitiveBinRel(T)) => (R ⊆ T)) => (TransitiveClosure(R0) = R)

Thm 62. (TransitiveClosureContainsRelation)
forall (R), R ⊆ TransitiveClosure(R)

Thm 63. (TransitiveClosureIsTransitive)
forall (R), TransitiveBinRel(TransitiveClosure(R))

Thm 64. (TransitiveClosureMinimal)
forall (R) (T), (R ⊆ T) => (TransitiveBinRel(T)) => (TransitiveClosure(R) ⊆ T)

Thm 65. (RelationPowerZero)
forall (A) (R), (BinRelComp(R, 0) = IdentityBinRel(A))

Thm 66. (RelationPowerOne)
forall (A) (R), (BinRelComp(R, 1) = R)

Thm 67. (RelationPowerSuccessor)
forall (A) (R) (n), (n ∈ PosIntegerSet) => (BinRelComp(R, n+1) = BinRelComp(R, n) ∘ R)

Thm 68. (RelationPowerAdd)
forall (R) (n) (m), (n ∈ PosIntegerSet) => (m ∈ PosIntegerSet) => (BinRelComp(R, n+m) = BinRelComp(R, n) ∘ BinRelComp(R, m))

Thm 69. (TransitiveClosureAsPowerUnion)
forall (R), TransitiveClosure(R) = union_{n = 1}^{infty}(BinRelComp(R, n))

Thm 70. (ReflexiveTransitiveClosureDefinition)
forall (R) (R0), (R0 ⊆ R) => TransitiveBinRel(R) => ReflexiveBinRel(R) => (forall (T), (R0 ⊆ T) => (TransitiveBinRel(T)) => (R ⊆ T)) => (RelTransClosure(R0) = R)

Thm 71. (ReflexiveTransitiveClosureContainsRelation)
forall (R), R ⊆ RelTransClosure(R)

Thm 72. (ReflexiveTransitiveClosureIsTransitive)
forall (R), TransitiveBinRel(RelTransClosure(R))

Thm 73. (ReflexiveTransitiveClosureIsReflexive)
forall (R), ReflexiveBinRel(RelTransClosure(R))

Thm 74. (ReflexiveTransitiveClosureMinimal)
forall (R) (T), (R ⊆ T) => TransitiveBinRel(T) => ReflexiveBinRel(T) => (RelTransClosure(R) ⊆ T)

Thm 75. (ReflexiveTransitiveClosureAsPowerUnion)
forall (R), RelTransClosure(R) = union_{n = 0}^{infty}(BinRelComp(R, n))

Thm 76. (FunctionValueExists)
forall (A) (B) (f), f : A -> B => (forall (x), (x ∈ A) => (exists (y), (y ∈ B) /\ (f(x) = y)))

Thm 77. (FunctionValueUnique)
forall (A) (B) (f), f : A -> B => (forall (x) (y1) (y2), (f(x) = y1 /\ f(x) = y2) => y1 = y2)

Thm 78. (FunctionEqualityPointwise)
forall (A) (B) (f) (g), f : A -> B => g : A -> B => (f = g) => (forall (x), (x ∈ A) => (f(x)=g(x)))

Thm 79. (FunctionEqualityFromPointwise)
forall (A) (B) (f) (g), f : A -> B => g : A -> B => (forall (x), (x ∈ A) => (f(x)=g(x))) => (f = g)

Thm 80. (FunctionCompositionApply)
forall (A) (B) (C) (f) (g), f : B -> C => g : A -> B => (forall (x), (x ∈ A) => ((f ∘ g)(x) = f(g(x))))

Thm 81. (InjectionElim)
forall (A) (B) (f), f : A -> B => IsInjection(f) => (forall (a) (b), (a ∈ A) => (b ∈ A) => (f(a) = f(b)) => (a = b))

Thm 82. (InjectionIntro)
forall (A) (B) (f), f : A -> B => (forall (a) (b), (a ∈ A) => (b ∈ A) => (f(a) = f(b)) => (a = b)) => IsInjection(f)

Thm 83. (SurjectionElim)
forall (A) (B) (f), f : A -> B => IsSurjection(f) => (forall (b), (b ∈ B) => (exists (a), (a ∈ A /\ f(a) = b)))

Thm 84. (SurjectionIntro)
forall (A) (B) (f), f : A -> B => (forall (b), (b ∈ B) => (exists (a), (a ∈ A /\ f(a) = b))) => IsSurjection(f)

Thm 85. (BijectionImpliesInjection)
forall (A) (B) (f), f : A -> B => IsBijection(f) => IsInjection(f)

Thm 86. (BijectionImpliesSurjection)
forall (A) (B) (f), f : A -> B => IsBijection(f) => IsSurjection(f)

Thm 87. (BijectionIntro)
forall (A) (B) (f), f : A -> B => IsInjection(f) => IsSurjection(f) => IsBijection(f)

Thm 88. (InjectionComposition)
forall (A) (B) (C) (f) (g), f : B -> C => g : A -> B => (IsInjection(f) => IsInjection(g) => IsInjection(f ∘ g))

Thm 89. (CompositionInjectionImpliesInnerInjection)
forall (A) (B) (C) (f) (g), f : B -> C => g : A -> B => (IsInjection(f ∘ g)) => IsInjection(g)

Thm 90. (SurjectionComposition)
forall (A) (B) (C) (f) (g), f : B -> C => g : A -> B => (IsSurjection(f) => IsSurjection(g) => IsSurjection(f ∘ g))

Thm 91. (InverseOfBijection)
forall (A) (B) (f), f : A -> B => IsBijection(f) => IsBijection(InverseFunc(f))

Thm 92. (SchroederBernsteinTheorem)
forall (A) (B) (f) (g), f : A -> B => g : B -> A => IsInjection(f) => IsInjection(g) => (exists (h), (h:A->B) /\ IsBijection(h))

Thm 93. (EquinumerousImpliesBijection)
forall (A) (B), Equinumerous(A, B) => (exists (f), (f:A->B) /\ (IsBijection(f)))

Thm 94. (BijectionImpliesEquinumerous)
forall (A) (B), (exists (f), (f:A->B) /\ (IsBijection(f))) => Equinumerous(A, B)

Thm 95. (CantorTheorem)
forall (S), Not(Equinumerous(S, PowerSet(S)))

Thm 96. (CountableImpliesEquinumerousNaturals)
forall (S), CountableSet(S) => Equinumerous(S, NonNegIntegerSet)

Thm 97. (EquinumerousNaturalsImpliesCountable)
forall (S), Equinumerous(S, NonNegIntegerSet) => CountableSet(S)

Thm 98. (UncountableImpliesNotCountable)
forall (S), UncountableSet(S) => Not(CountableSet(S))

Thm 99. (NotCountableImpliesUncountable)
forall (S), Not(CountableSet(S)) => UncountableSet(S)

Thm 100. (RealsUncountable)
UncountableSet(RealSet)

Thm 101. (NaturalsEquinumerousRationals)
Equinumerous(NonNegIntegerSet, Rational)

Thm 102. (RealsEquinumerousPowerSetNaturals)
Equinumerous(PowerSet(NonNegIntegerSet), RealSet)

Thm 103. (InductiveSetContainsEmpty)
forall (X), InductiveSet(X) => ((∅ ∈ X) /\ (forall (y), (y ∈ X) => ((y ∪ {y}) ∈ X)))

Thm 104. (InductiveSetClosedUnderSuccessor)
forall (X), (∅ ∈ X) => (forall (y), (y ∈ X) => ((y ∪ {y}) ∈ X)) => InductiveSet(X)

Thm 105. (InductiveSetEmptyProperty)
forall (X), InductiveSet(X) => (∅ ∈ X)

Thm 106. (InductiveSetSuccessorProperty)
forall (X), InductiveSet(X) => (forall (y), (y ∈ X) => ((y ∪ {y}) ∈ X))

Thm 107. (NaturalsAreInductive)
InductiveSet(NonNegIntegerSet)

Thm 108. (NaturalsAreLeastInductiveSet)
forall (X), InductiveSet(X) => (NonNegIntegerSet ⊆ X)

Thm 109. (NaturalSuccessorIsNatural)
forall (y), (y ∈ NonNegIntegerSet) => ((y ∪ {y}) ∈ NonNegIntegerSet)

Thm 110. (RolleTheorem)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a < b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(f, (a,b)) => f(a) = f(b) => exists (c ∈ (a,b)), FunDeri(f, 1, 1)(c) = 0

Thm 111. (LagrangeMeanValueTheorem)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a < b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(f, (a,b)) => exists (c ∈ (a,b)), FunDeri(f, 1, 1)(c) = (f(b) - f(a)) / (b - a)

Thm 112. (CauchyMeanValueTheorem)
forall (f) (g) (a) (b), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a < b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(f, (a,b)) => ContinuousFuncOn(g, [a,b]) => DiffableFuncOn(g, (a,b)) => exists (c ∈ (a,b)), (f(b) - f(a)) * FunDeri(g, 1, 1)(c) = (g(b) - g(a)) * FunDeri(f, 1, 1)(c)

Thm 113. (LHopitalZeroOverZero)
forall (f) (g) (a) (L), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => L ∈ RealSet => lim_{x -> a} (f(x)) = 0 => lim_{x -> a} (g(x)) = 0 => (exists (δ), δ ∈ RealSet /\ δ > 0 /\ DiffableFuncOn(f, (a - δ, a) ∪ (a, a + δ)) /\ DiffableFuncOn(g, (a - δ, a) ∪ (a, a + δ)) /\ (forall (x), x ∈ (a - δ, a) ∪ (a, a + δ) => FunDeri(g, 1, 1)(x) ≠ 0 /\ g(x) ≠ 0)) => lim_{x -> a} (FunDeri(f, 1, 1)(x) / FunDeri(g, 1, 1)(x)) = L => lim_{x -> a} (f(x) / g(x)) = L

Thm 114. (SineOverArgumentLimit)
lim_{x -> 0} (sin(x) / x) = 1

Thm 115. (ExponentialDefiningLimit)
lim_{x -> +∞} ((1 + 1 / x) ^ x) = e /\ lim_{x -> -∞} ((1 + 1 / x) ^ x) = e

Thm 116. (SqueezeTheoremAtInfinity)
forall (f) (g) (h) (L), f : RealSet -> RealSet => g : RealSet -> RealSet => h : RealSet -> RealSet => L ∈ RealSet => (exists (N), N ∈ RealSet /\ (forall (x), x ∈ RealSet => x >= N => f(x) <= g(x) /\ g(x) <= h(x))) => lim_{x -> +∞}(f(x)) = L => lim_{x -> +∞}(h(x)) = L => lim_{x -> +∞}(g(x)) = L

Thm 117. (MonotoneBoundedSequenceConverges)
forall (a), (MonoIncSeq(a) \/ MonoDecSeq(a)) => (BoundedSeq(a)) => ConvergentSeq(a)

Thm 118. (CauchyConvergenceCriterion)
forall (a), ConvergentSeq(a) <==> (forall (ε), ε > 0 => (exists (N), forall (m) (n), m >= N => n >= N => |a(m) - a(n)| < ε))

Thm 119. (BolzanoWeierstrassTheorem)
forall (a), (ConvergentSeq(a) => (exists (b) (L), (StrictMonoIncSeq(b) \/ StrictMonoDecSeq(b)) /\ lim_{n -> +∞} (a(b(n))) = L)) => ((exists (b) (L), (StrictMonoIncSeq(b) \/ StrictMonoDecSeq(b)) => lim_{n -> +∞} (a(b(n))) = L) => ConvergentSeq(a))

Thm 120. (HeineSequentialCriterion)
forall (f) (x0), (exists (δ), δ > 0 /\ (x0 - δ, x0) ∈ Dom(f) /\ (x0, x0 + δ) ∈ Dom(f)) => (lim_{x -> x0} (f(x)) = A <==> (forall (x), (forall (n), x(n) ∈ Dom(f)) => (forall (n), x(n) ≠ x0) => lim_{n -> +∞} (x(n)) = x0 => lim_{n -> +∞} (f(x(n))) = A))

Thm 121. (FermatStationaryPointLemma)
forall (f) (a), f : RealSet -> RealSet => a ∈ RealSet => DiffableFuncAt(f, a) => ((exists (δ), δ ∈ RealSet /\ δ > 0 /\ (forall (x), x ∈ (a - δ, a + δ) => f(x) <= f(a))) \/ (exists (δ), δ ∈ RealSet /\ δ > 0 /\ (forall (x), x ∈ (a - δ, a + δ) => f(x) >= f(a)))) => FunDeri(f, 1, 1)(a) = 0

Thm 122. (FirstDerivativeLocalMaximumTest)
forall (f) (a) (δ), f : RealSet -> RealSet => a ∈ RealSet => δ ∈ RealSet => δ > 0 => ContinuousFuncAt(f, a) => DiffableFuncOn(f, (a - δ, a) ∪ (a, a + δ)) => (forall (x), x ∈ (a - δ, a) => FunDeri(f, 1, 1)(x) > 0) => (forall (x), x ∈ (a, a + δ) => FunDeri(f, 1, 1)(x) < 0) => (forall (x), x ∈ (a - δ, a + δ) => x ≠ a => f(x) < f(a))

Thm 123. (SecondDerivativeLocalMaximumTest)
forall (f) (a) (δ), f : RealSet -> RealSet => a ∈ RealSet => δ ∈ RealSet => δ > 0 => DiffableFuncOn(f, (a - δ, a + δ)) => DiffableFuncOn(FunDeri(f, 1, 1), (a - δ, a + δ)) => FunDeri(f, 1, 1)(a) = 0 => (forall (x), x ∈ (a - δ, a + δ) => FunDeri(f, 1, 2)(x) < 0) => (forall (x), x ∈ (a - δ, a + δ) => x ≠ a => f(x) < f(a))

Thm 124. (TaylorTheoremLagrangeRemainder)
forall (f) (n) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => n ∈ NonNegIntegerSet => a < b => FuncOfClassKOn(f, [a,b], n+1) => exists (c), c ∈ (a,b) /\ f(b) = f(a) + sum_{k = 1}^{n}((FunDeri(f, 1, k)(a) / k!) * (b - a) ^ k) + (FunDeri(f, 1, n+1)(c) / (n + 1)!) * (b - a) ^ (n+1)

Thm 125. (NewtonLeibnizFormula)
forall (f) (F) (a) (b), f : RealSet -> RealSet => F : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a <= b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(F, (a,b)) => ContinuousFuncOn(F, [a,b]) => (forall (x), x ∈ (a,b) => FunDeri(F, 1, 1)(x) = f(x)) => DefInt(a, b, f(x) * diff(x)) = F(b) - F(a)

Thm 126. (IntegralMeanValueTheorem)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a < b => ContinuousFuncOn(f, [a,b]) => exists (c), c ∈ (a,b) /\ DefInt(a, b, f(x) * diff(x)) = f(c) * (b - a)

Thm 127. (FundamentalTheoremCalculusDerivative)
forall (f) (a) (x), f : RealSet -> RealSet => a ∈ RealSet => x ∈ RealSet => (exists (l) (u), l ∈ RealSet /\ u ∈ RealSet /\ l < a /\ l < x /\ a < u /\ x < u /\ ContinuousFuncOn(f, [l,u])) => FunDeri(fun x . DefInt(a, x, f(t) * diff(t)), 1, 1)(x) = f(x)

Thm 128. (FundamentalTheoremCalculusEvaluation)
forall (f) (F) (a) (b), f : RealSet -> RealSet => F : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a <= b => ContinuousFuncOn(f, [a,b]) => ContinuousFuncOn(F, [a,b]) => DiffableFuncOn(F, (a,b)) => (forall (x), x ∈ (a,b) => FunDeri(F, 1, 1)(x) = f(x)) => DefInt(a, b, f(x) * diff(x)) = F(b) - F(a)

Thm 129. (SeriesComparisonTest)
forall (a) (b), (exists (N), N ∈ NonNegIntegerSet /\ (forall (n), n ∈ NonNegIntegerSet => n >= N => 0 <= a(n) /\ a(n) <= b(n))) => ConvergentSeries(sum_{n = 0}^{+∞}(b(n))) => ConvergentSeries(sum_{n = 0}^{+∞}(a(n)))

Thm 130. (SeriesRatioTest)
forall (a) (L), L ∈ RealSet => (forall (n), n ∈ NonNegIntegerSet => a(n) > 0) => seqlim_{n -> +∞}(a(n+1) / a(n)) = L => (L < 1 => ConvergentSeries(sum_{n = 0}^{+∞}(a(n)))) /\ (L > 1 => DivergentSeries(sum_{n = 0}^{+∞}(a(n))))

Thm 131. (SeriesRootTest)
forall (a) (L), L ∈ RealSet => (forall (n), n ∈ NonNegIntegerSet => a(n) >= 0) => seqlim_{n -> +∞}(sqrt(n + 1, a(n + 1))) = L => (L < 1 => ConvergentSeries(sum_{n = 0}^{+∞}(a(n)))) /\ (L > 1 => DivergentSeries(sum_{n = 0}^{+∞}(a(n))))

Thm 132. (IntegralTestForSeries)
forall (f) (a), f : RealSet -> RealSet => ContinuousFuncOn(f, [1, +∞)) => MonoDecFuncOn(f, [1, +∞)) => (forall (x), x ∈ [1, +∞) => f(x) >= 0) => (forall (n), n ∈ PosIntegerSet => a(n) = f(n)) => (ConvergentSeries(sum_{n = 1}^{+∞}(a(n))) <==> (exists (I), I ∈ RealSet /\ lim_{b -> +∞}(DefInt(1, b, f(x) * diff(x))) = I))

Thm 133. (AlternatingSeriesTest)
forall (a), (forall (n), n ∈ NonNegIntegerSet => a(n) >= 0) => MonoDecSeq(a) => seqlim_{n -> +∞}(a(n)) = 0 => ConvergentSeries(sum_{n = 0}^{+∞}((-1) ^ n * a(n)))

Thm 134. (CauchyCondensationTest)
forall (a), MonoDecSeq(a) => PosSeq(a) => ((ConvergentSeries(sum_{n = 0}^{+∞}(2 ^ n * a(2 ^ n))) => ConvergentSeries(sum_{n = 0}^{+∞}(a(n)))) /\ (ConvergentSeries(sum_{n = 0}^{+∞}(a(n))) => ConvergentSeries(sum_{n = 0}^{+∞}(2 ^ n * a(2 ^ n)))))

Thm 135. (AbsoluteConvergenceImpliesConvergence)
forall (a), ConvergentSeries(sum_{n = 0}^{+∞}(|a(n)|)) => ConvergentSeries(sum_{n = 0}^{+∞}(a(n)))

Thm 136. (DirichletSeriesTest)
forall (a) (b), BoundedSeq(fun n: NonNegIntegerSet . sum_{k=0}^{n}(a(k))) => MonoDecSeq(b) => seqlim_{n -> +∞}(b(n)) = 0 => ConvergentSeries(sum_{n = 0}^{+∞}(a(n) * b(n)))

Thm 137. (AbelSeriesTest)
forall (a) (b), ConvergentSeries(sum_{n = 0}^{+∞}(a(n))) => (MonoDecSeq(b) \/ MonoIncSeq(b)) => BoundedSeq(b) => ConvergentSeries(sum_{n = 0}^{+∞}(a(n) * b(n)))

Thm 138. (PowerSeriesFiniteRadiusCriterion)
forall (a) (R) (rho), R ∈ RealSet => rho ∈ RealSet => R > 0 => rho > 0 => seqlimsup_{n -> +∞}(sqrt(n + 1, |a(n + 1)|)) = rho => R = 1 / rho => (forall (x), x ∈ RealSet => |x| < R => ConvergentSeries(sum_{n = 1}^{+∞}(a(n) * x ^ n))) /\ (forall (x), x ∈ RealSet => |x| > R => DivergentSeries(sum_{n = 1}^{+∞}(a(n) * x ^ n)))

Thm 139. (UniformCauchyCriterion)
forall (f) (S), IsSet(S) => (forall (n), n ∈ NonNegIntegerSet => f(n) : RealSet -> RealSet) => ((exists (g), g : RealSet -> RealSet /\ (forall (ε), ε ∈ RealSet => ε > 0 => (exists (N), N ∈ NonNegIntegerSet /\ (forall (n), n ∈ NonNegIntegerSet => n >= N => (forall (x), x ∈ S => |f(n)(x) - g(x)| < ε))))) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (N), N ∈ NonNegIntegerSet /\ (forall (m) (n), m ∈ NonNegIntegerSet => n ∈ NonNegIntegerSet => m >= N => n >= N => (forall (x), x ∈ S => |f(n)(x) - f(m)(x)| < ε)))))

Thm 140. (WeierstrassMTest)
forall (f) (M) (I), IsSet(I) => (forall (n), n ∈ NonNegIntegerSet => f(n) : RealSet -> RealSet) => (forall (n), n ∈ NonNegIntegerSet => M(n) >= 0) => (forall (n) (x), n ∈ NonNegIntegerSet => x ∈ I => |f(n)(x)| <= M(n)) => ConvergentSeries(sum_{n = 0}^{+∞}(M(n))) => (exists (g), g : RealSet -> RealSet /\ (forall (ε), ε ∈ RealSet => ε > 0 => exists (N), N ∈ NonNegIntegerSet /\ (forall (K), K ∈ NonNegIntegerSet => K >= N => (forall (x), x ∈ I => |sum_{n = 0}^{K}(f(n)(x)) - g(x)| < ε))))

Thm 141. (LimitArithmeticRules)
forall (f) (g) (a) (L1) (L2), lim_{x -> a} (f(x)) = L1 /\ lim_{x -> a} (g(x)) = L2 => lim_{x -> a} (f(x) + g(x)) = L1 + L2 /\ lim_{x -> a} (f(x) - g(x)) = L1 - L2 /\ lim_{x -> a} (f(x) * g(x)) = L1 * L2 /\ (L2 ≠ 0 => lim_{x -> a} (f(x) / g(x)) = L1 / L2)

Thm 142. (LimitCompositionRule)
forall (f) (g) (a) (L1) (L2), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => L1 ∈ RealSet => L2 ∈ RealSet => (ContinuousFuncAt(f, L2) \/ (exists (δ), δ ∈ RealSet /\ δ > 0 /\ (forall (x), x ∈ RealSet => (0 < |x - a| /\ |x - a| < δ) => g(x) ≠ L2))) => lim_{x -> L2}(f(x)) = L1 => lim_{x -> a}(g(x)) = L2 => lim_{x -> a}(f(g(x))) = L1

Thm 143. (DerivativeArithmeticRules)
forall (f) (g) (x), DiffableFuncAt(f, x) => DiffableFuncAt(g, x) => (f(x) + g(x))' = f'(x) + g'(x) /\ (f(x) - g(x))' = f'(x) - g'(x) /\ (f(x) * g(x))' = f'(x) * g(x) + f(x) * g'(x) /\ (g(x) ≠ 0 => (f(x) / g(x))' = (f'(x) * g(x) - f(x) * g'(x)) / (g(x)) ^ 2)

Thm 144. (ChainRule)
forall (f) (g) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => x ∈ RealSet => DiffableFuncAt(g, x) => DiffableFuncAt(f, g(x)) => FunDeri(fun x . f(g(x)), 1, 1)(x) = FunDeri(f, 1, 1)(g(x)) * FunDeri(g, 1, 1)(x)

Thm 145. (InverseFunctionDerivative)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => BijectiveFunc(f) => DiffableFuncAt(f, x) => FunDeri(f, 1, 1)(x) ≠ 0 => ContinuousFuncAt(InverseFunc(f), f(x)) => (DiffableFuncAt(InverseFunc(f), f(x)) /\ FunDeri(InverseFunc(f), 1, 1)(f(x)) = 1 / FunDeri(f, 1, 1)(x))

Thm 146. (PowerSeriesExpansionUnique)
forall (f) (c) (d) (x0) (R), f : RealSet -> RealSet => x0 ∈ RealSet => R ∈ RealSet => R > 0 => (forall (x), x ∈ RealSet => |x - x0| < R => ConvergentSeries(sum_{n = 1}^{+∞}(c(n) * (x - x0) ^ n)) /\ f(x) = c(0) + sum_{n = 1}^{+∞}(c(n) * (x - x0) ^ n)) => (forall (x), x ∈ RealSet => |x - x0| < R => ConvergentSeries(sum_{n = 1}^{+∞}(d(n) * (x - x0) ^ n)) /\ f(x) = d(0) + sum_{n = 1}^{+∞}(d(n) * (x - x0) ^ n)) => (forall (n), n ∈ NonNegIntegerSet => c(n) = d(n))

Thm 147. (PowerSeriesTermwiseDerivative)
forall (f) (coeff) (a) (R), f : RealSet -> RealSet => a ∈ RealSet => R ∈ RealSet => R > 0 => (forall (x), x ∈ RealSet => |x - a| < R => ConvergentSeries(sum_{n = 0}^{+∞}(coeff(n) * (x - a) ^ n)) /\ f(x) = sum_{n = 0}^{+∞}(coeff(n) * (x - a) ^ n)) => (DiffableFuncOn(f, (a - R, a + R)) /\ (forall (x), x ∈ RealSet => |x - a| < R => FunDeri(f, 1, 1)(x) = sum_{n = 1}^{+∞}(n * coeff(n) * (x - a) ^ (n - 1))))

Thm 148. (ComplexRealImaginaryRepresentation)
forall (z), z ∈ ComplexSet => (exists (a) (b), a ∈ RealSet /\ b ∈ RealSet /\ z = a + b * __IMAGINARY_UNIT__)

Thm 149. (ComplexDivisionPolarForm)
forall (z1) (z2) (r1) (r2) (θ1) (θ2), r1 ∈ RealSet => r2 ∈ RealSet => θ1 ∈ RealSet => θ2 ∈ RealSet => z1 ∈ ComplexSet => z2 ∈ ComplexSet => (z2 ≠ 0 => z1 = r1 * (cos(θ1) + __IMAGINARY_UNIT__ * sin(θ1)) => z2 = r2 * (cos(θ2) + __IMAGINARY_UNIT__ * sin(θ2)) => z1 / z2 = (r1 / r2) * (cos(θ1 - θ2) + __IMAGINARY_UNIT__ * sin(θ1 - θ2)))

Thm 150. (DeMoivreFormulaIntegerPower)
forall (z) (r) (θ) (n), r ∈ RealSet => θ ∈ RealSet => z ∈ ComplexSet => n ∈ IntegerSet => (r > 0 => z = r * (cos(θ) + __IMAGINARY_UNIT__ * sin(θ)) => z ^ n = r ^ n * (cos(n * θ) + __IMAGINARY_UNIT__ * sin(n * θ)))

Thm 151. (ComplexExponentialEulerFormula)
forall (θ), θ ∈ RealSet => (e ^ (__IMAGINARY_UNIT__ * θ) = cos(θ) + __IMAGINARY_UNIT__ * sin(θ))

Thm 152. (BinomialTheorem)
forall (a) (b) (n), a ∈ RealSet => b ∈ RealSet => n ∈ NonNegIntegerSet => ((a + b) ^ n = sum_{k = 0}^{n}((n! / (k! * (n-k)!)) * a ^ (n-k) * b ^ k))

Thm 153. (ArchimedeanPropertyOfReals)
forall (x), x ∈ RealSet => (x > 0 => exists (n), n ∈ PosIntegerSet /\ 1 / n < x)

Thm 154. (DensityOfReals)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a < b => exists (c), c ∈ RealSet /\ a < c /\ c < b)

Thm 155. (DensityOfRationals)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a < b => exists (p) (d), p ∈ IntegerSet /\ d ∈ PosIntegerSet /\ a < p / d /\ p / d < b)

Thm 156. (FunctionLimitUnique)
forall (f) (a) (L1) (L2), f : RealSet -> RealSet => a ∈ RealSet => L1 ∈ RealSet => L2 ∈ RealSet => (lim_{x -> a}(f(x)) = L1 => lim_{x -> a}(f(x)) = L2 => L1 = L2)

Thm 157. (FunctionLimitLocallyBounded)
forall (f) (a) (L), f : RealSet -> RealSet => a ∈ RealSet => L ∈ RealSet => (lim_{x -> a}(f(x)) = L => exists (δ) (M), δ ∈ RealSet /\ M ∈ RealSet /\ δ > 0 /\ M > 0 /\ forall (x), x ∈ RealSet => (0 < |x - a| /\ |x - a| < δ => |f(x)| < M))

Thm 158. (PositiveLimitEventuallyPositive)
forall (f) (a) (L), f : RealSet -> RealSet => a ∈ RealSet => L ∈ RealSet => (lim_{x -> a}(f(x)) = L => L > 0 => exists (δ), δ ∈ RealSet /\ δ > 0 /\ forall (x), x ∈ RealSet => (0 < |x - a| /\ |x - a| < δ => f(x) > 0))

Thm 159. (ContinuousFunctionLocallyBounded)
forall (f) (a), f : RealSet -> RealSet => a ∈ RealSet => (ContinuousFuncAt(f, a) => exists (δ) (M), δ ∈ RealSet /\ M ∈ RealSet /\ δ > 0 /\ M > 0 /\ forall (x), x ∈ RealSet => (|x - a| < δ => |f(x)| < M))

Thm 160. (ContinuousFunctionArithmetic)
forall (f) (g) (a), ContinuousFuncAt(f, a) => ContinuousFuncAt(g, a) => ContinuousFuncAt(f + g, a) => ContinuousFuncAt(f - g, a) => ContinuousFuncAt(f * g, a) => (g(a) ≠ 0 => ContinuousFuncAt(f / g, a))

Thm 161. (ContinuousFunctionComposition)
forall (f) (g) (a), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => (ContinuousFuncAt(g, a) => ContinuousFuncAt(f, g(a)) => ContinuousFuncAt(f ∘ g, a))

Thm 162. (BolzanoZeroTheorem)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => (a < b => ContinuousFuncOn(f, [a, b]) => f(a) * f(b) < 0 => exists (c), c ∈ (a,b) /\ f(c) = 0)

Thm 163. (IntermediateValueTheorem)
forall (f) (a) (b) (y), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => y ∈ RealSet => (a <= b => ContinuousFuncOn(f, [a, b]) => ((f(a) <= y /\ y <= f(b)) \/ (f(b) <= y /\ y <= f(a))) => exists (c), c ∈ [a, b] /\ f(c) = y)

Thm 164. (ContinuousOnClosedIntervalBounded)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => (a <= b => ContinuousFuncOn(f, [a, b]) => exists (M), M ∈ RealSet /\ M >= 0 /\ forall (x), x ∈ RealSet => (x ∈ [a, b] => |f(x)| <= M))

Thm 165. (ContinuousOnClosedIntervalExtrema)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => (a <= b => ContinuousFuncOn(f, [a, b]) => exists (xmin) (xmax), xmin ∈ [a, b] /\ xmax ∈ [a, b] /\ forall (x), x ∈ RealSet => (x ∈ [a, b] => f(xmin) <= f(x) /\ f(x) <= f(xmax)))

Thm 166. (SineBounded)
forall (x), x ∈ RealSet => -1 <= sin(x) /\ sin(x) <= 1

Thm 167. (CosineBounded)
forall (x), x ∈ RealSet => -1 <= cos(x) /\ cos(x) <= 1

Thm 168. (PythagoreanTrigonometricIdentity)
forall (x), x ∈ RealSet => (sin(x)) ^ 2 + (cos(x)) ^ 2 = 1

Thm 169. (SinePeriodicity)
forall (x) (k), x ∈ RealSet => k ∈ IntegerSet => sin (x + 2 * k * π) = sin(x)

Thm 170. (CosinePeriodicity)
forall (x) (k), x ∈ RealSet => k ∈ IntegerSet => cos (x + 2 * k * π) = cos(x)

Thm 171. (TangentDefinition)
forall (x), x ∈ RealSet => cos(x) ≠ 0 => tan(x) = sin(x) / cos(x)

Thm 172. (ExponentialMonotonicity)
forall (x) (y) (a), x ∈ RealSet => y ∈ RealSet => a ∈ RealSet => (a > 0 => a ≠ 1 => x < y => ((a > 1 => a ^ x < a ^ y) /\ (a < 1 => a ^ x > a ^ y)))

Thm 173. (LogarithmMonotonicity)
forall (x) (y) (a), x ∈ RealSet => y ∈ RealSet => a ∈ RealSet => (x > 0 => y > 0 => a > 0 => a ≠ 1 => x < y => ((a > 1 => log(a, x) < log(a, y)) /\ (a < 1 => log(a, x) > log(a, y))))

Thm 174. (ExponentialLogarithmInverse)
forall (x) (a), x ∈ RealSet => a ∈ RealSet => (a > 0 => a ≠ 1 => (log(a, a ^ x) = x /\ (x > 0 => a ^ (log(a, x)) = x)))

Thm 175. (PositiveIntegerPowerMonotonicity)
forall (x) (y) (n), x ∈ RealSet => y ∈ RealSet => n ∈ NonNegIntegerSet => (n > 0 => x >= 0 => y >= 0 => x < y => x ^ n < y ^ n)

Thm 176. (NaturalExponentialDerivative)
forall (x), x ∈ RealSet => FunDeri(fun x . e ^ x, 1, 1)(x) = e ^ x

Thm 177. (NaturalLogarithmDerivative)
forall (x), x ∈ RealSet => x > 0 => FunDeri(fun x . ln(x), 1, 1)(x) = 1 / x

Thm 178. (SineDerivative)
forall (x), x ∈ RealSet => FunDeri(fun x . sin(x), 1, 1)(x) = cos(x)

Thm 179. (CosineDerivative)
forall (x), x ∈ RealSet => FunDeri(fun x . cos(x), 1, 1)(x) = -sin(x)

Thm 180. (SineAdditionFormula)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => sin (x + y) = sin(x) * cos(y) + cos(x) * sin(y)

Thm 181. (SineSubtractionFormula)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => sin (x - y) = sin(x) * cos(y) - cos(x) * sin(y)

Thm 182. (CosineAdditionFormula)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => cos (x + y) = cos(x) * cos(y) - sin(x) * sin(y)

Thm 183. (CosineSubtractionFormula)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => cos (x - y) = cos(x) * cos(y) + sin(x) * sin(y)

Thm 184. (TangentAdditionFormula)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => cos(x) ≠ 0 => cos(y) ≠ 0 => cos (x + y) ≠ 0 => tan (x + y) = (tan(x) + tan(y)) / (1 - tan(x) * tan(y))

Thm 185. (TangentSubtractionFormula)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => cos(x) ≠ 0 => cos(y) ≠ 0 => cos (x - y) ≠ 0 => tan (x - y) = (tan(x) - tan(y)) / (1 + tan(x) * tan(y))

Thm 186. (LogarithmProductFormula)
forall (x) (y) (a), x ∈ RealSet => y ∈ RealSet => a ∈ RealSet => (a > 0 => a ≠ 1 => x > 0 => y > 0 => log(a, x * y) = log(a, x) + log(a, y))

Thm 187. (LogarithmQuotientFormula)
forall (x) (y) (a), x ∈ RealSet => y ∈ RealSet => a ∈ RealSet => (a > 0 => a ≠ 1 => x > 0 => y > 0 => log(a, x / y) = log(a, x) - log(a, y))

Thm 188. (LogarithmPowerFormula)
forall (a) (x) (n), a ∈ RealSet => x ∈ RealSet => n ∈ IntegerSet => (a > 0 => a ≠ 1 => x > 0 => log(a, x ^ n) = n * log(a, x))

Thm 189. (LogarithmChangeOfBase)
forall (a) (b) (x), a ∈ RealSet => b ∈ RealSet => x ∈ RealSet => (a > 0 => b > 0 => a ≠ 1 => b ≠ 1 => x > 0 => log(a, x) = log(b, x) / log(b, a))

Thm 190. (SineDoubleAngle)
forall (x), x ∈ RealSet => sin (2 * x) = 2 * sin(x) * cos(x)

Thm 191. (CosineDoubleAngle)
forall (x), x ∈ RealSet => cos (2 * x) = (cos(x)) ^ 2 - (sin(x)) ^ 2

Thm 192. (CosineDoubleAngleSquareCosine)
forall (x), x ∈ RealSet => cos (2 * x) = 2 * (cos(x)) ^ 2 - 1

Thm 193. (CosineDoubleAngleSquareSine)
forall (x), x ∈ RealSet => cos (2 * x) = 1 - 2 * (sin(x)) ^ 2

Thm 194. (SineHalfAngle)
forall (x), x ∈ RealSet => sin (x / 2) ^ 2 = (1 - cos(x)) / 2

Thm 195. (CosineHalfAngle)
forall (x), x ∈ RealSet => cos (x / 2) ^ 2 = (1 + cos(x)) / 2

Thm 196. (TangentHalfAngle)
forall (x), x ∈ RealSet => cos(x) ≠ -1 => tan (x / 2) ^ 2 = (1 - cos(x)) / (1 + cos(x))

Thm 197. (SumToProductSineSum)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => sin(x) + sin(y) = 2 * sin ((x + y) / 2) * cos ((x - y) / 2)

Thm 198. (SumToProductSineDifference)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => sin(x) - sin(y) = 2 * cos ((x + y) / 2) * sin ((x - y) / 2)

Thm 199. (SumToProductCosineSum)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => cos(x) + cos(y) = 2 * cos ((x + y) / 2) * cos ((x - y) / 2)

Thm 200. (SumToProductCosineDifference)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => cos(x) - cos(y) = -2 * sin ((x + y) / 2) * sin ((x - y) / 2)

Thm 201. (NaturalLogarithmProduct)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => (x > 0 => y > 0 => ln (x * y) = ln(x) + ln(y))

Thm 202. (NaturalLogarithmQuotient)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => (x > 0 => y > 0 => ln (x / y) = ln(x) - ln(y))

Thm 203. (NaturalLogarithmPower)
forall (x) (y), (x > 0 => ln (x ^ y) = y * ln(x))

Thm 204. (ExponentAdditionLaw)
forall (a) (x) (y), a ∈ RealSet => x ∈ RealSet => y ∈ RealSet => (a > 0 => a ^ (x + y) = a ^ x * a ^ y)

Thm 205. (ExponentSubtractionLaw)
forall (a) (x) (y), a ∈ RealSet => x ∈ RealSet => y ∈ RealSet => (a > 0 => a ^ (x - y) = a ^ x / a ^ y)

Thm 206. (PowerOfPowerLaw)
forall (a) (x) (y), a ∈ RealSet => x ∈ RealSet => y ∈ RealSet => (a > 0 => (a ^ x) ^ y = a ^ (x * y))

Thm 207. (RealPowerDerivative)
forall (r) (x), r ∈ RealSet => x ∈ RealSet => x > 0 => FunDeri(fun t . t ^ r, 1, 1)(x) = r * x ^ (r - 1)

Thm 208. (GeneralExponentialDerivative)
forall (a) (x), a ∈ RealSet => x ∈ RealSet => a > 0 => FunDeri(fun t . a ^ t, 1, 1)(x) = a ^ x * ln(a)

Thm 209. (GeneralLogarithmDerivative)
forall (a) (x), a ∈ RealSet => x ∈ RealSet => x > 0 => a > 0 => a ≠ 1 => FunDeri(fun x . log(a, x), 1, 1)(x) = 1 / (x * ln(a))

Thm 210. (SquareRootRationalization)
forall (f) (g) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => x ∈ RealSet => (f(x) >= 0 => g(x) >= 0 => sqrt(f(x)) + sqrt(g(x)) ≠ 0 => sqrt(f(x)) - sqrt(g(x)) = (f(x) - g(x)) / (sqrt(f(x)) + sqrt(g(x))))

Thm 211. (DifferenceOfCubes)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2))

Thm 212. (ConjugateArithmeticRules)
forall (z) (w), bar(z + w) = bar(z) + bar(w) => bar(z - w) = bar(z) - bar(w) => bar(z * w) = bar(z) * bar(w) => ((w ≠ 0) => bar(z / w) = bar(z) / bar(w))

Thm 213. (EulerFormulaForRealAngle)
forall (x), x ∈ RealSet => (e ^ (__IMAGINARY_UNIT__ * x) = cos(x) + __IMAGINARY_UNIT__ * sin(x))

Thm 214. (DeMoivreFormulaTrigonometricPower)
forall (x) (n), x ∈ RealSet => n ∈ IntegerSet => ((cos(x) + __IMAGINARY_UNIT__ * sin(x)) ^ n = cos(n * x) + __IMAGINARY_UNIT__ * sin(n * x))

Thm 215. (HigherDerivativeOfSine)
forall (n) (x), x ∈ RealSet => n ∈ NonNegIntegerSet => FunDeri(fun x . sin(x), 1, n)(x) = sin(x + n * π / 2)

Thm 216. (HigherDerivativeOfCosine)
forall (n) (x), x ∈ RealSet => n ∈ NonNegIntegerSet => FunDeri(fun x . cos(x), 1, n)(x) = cos(x + n * π / 2)

Thm 217. (ComplexEqualityComponents)
forall (z1) (z2) (a1) (b1) (a2) (b2), a1 ∈ RealSet => b1 ∈ RealSet => a2 ∈ RealSet => b2 ∈ RealSet => z1 ∈ ComplexSet => z2 ∈ ComplexSet => (z1 = a1 + b1 * __IMAGINARY_UNIT__ => z2 = a2 + b2 * __IMAGINARY_UNIT__ => (z1 = z2 <==> a1 = a2 /\ b1 = b2))

Thm 218. (ComplexAdditionComponents)
forall (z1) (z2) (a1) (b1) (a2) (b2), a1 ∈ RealSet => b1 ∈ RealSet => a2 ∈ RealSet => b2 ∈ RealSet => z1 ∈ ComplexSet => z2 ∈ ComplexSet => (z1 = a1 + b1 * __IMAGINARY_UNIT__ => z2 = a2 + b2 * __IMAGINARY_UNIT__ => z1 + z2 = (a1 + a2) + (b1 + b2) * __IMAGINARY_UNIT__)

Thm 219. (ComplexMultiplicationComponents)
forall (z1) (z2) (a1) (b1) (a2) (b2), a1 ∈ RealSet => b1 ∈ RealSet => a2 ∈ RealSet => b2 ∈ RealSet => z1 ∈ ComplexSet => z2 ∈ ComplexSet => (z1 = a1 + b1 * __IMAGINARY_UNIT__ => z2 = a2 + b2 * __IMAGINARY_UNIT__ => z1 * z2 = (a1 * a2 - b1 * b2) + (a1 * b2 + b1 * a2) * __IMAGINARY_UNIT__)

Thm 220. (ComplexModulusComponents)
forall (z) (a) (b), a ∈ RealSet => b ∈ RealSet => z ∈ ComplexSet => (z = a + b * __IMAGINARY_UNIT__ => |z| = sqrt(a ^ 2 + b ^ 2))

Thm 221. (ComplexConjugateComponents)
forall (z) (a) (b), a ∈ RealSet => b ∈ RealSet => z ∈ ComplexSet => (z = a + b * __IMAGINARY_UNIT__ => bar(z) = a - b * __IMAGINARY_UNIT__)

Thm 222. (DoubleComplexConjugate)
forall (z), z ∈ ComplexSet => (bar(bar(z)) = z)

Thm 223. (ComplexTimesConjugate)
forall (z), z ∈ ComplexSet => (z * bar(z) = |z| ^ 2)

Thm 224. (ConjugateOfComplexSum)
forall (z) (w), z ∈ ComplexSet => w ∈ ComplexSet => (bar(z + w) = bar(z) + bar(w))

Thm 225. (ConjugateOfComplexProduct)
forall (z) (w), z ∈ ComplexSet => w ∈ ComplexSet => (bar(z * w) = bar(z) * bar(w))

Thm 226. (ComplexDivisionByConjugate)
forall (z) (w), z ∈ ComplexSet => w ∈ ComplexSet => (w ≠ 0 => z / w = (z * bar(w)) / |w| ^ 2)

Thm 227. (NonzeroComplexPolarParametersUnique)
forall (z) (r) (s) (θ) (φ), r ∈ RealSet => s ∈ RealSet => θ ∈ RealSet => φ ∈ RealSet => z ∈ ComplexSet => z ≠ 0 => r > 0 => s > 0 => z = r * (cos(θ) + __IMAGINARY_UNIT__ * sin(θ)) => z = s * (cos(φ) + __IMAGINARY_UNIT__ * sin(φ)) => (r = s /\ r = |z| /\ exists (k), k ∈ IntegerSet /\ θ = φ + 2 * k * π)

Thm 228. (ComplexMultiplicationPolarForm)
forall (z1) (z2) (r1) (r2) (θ1) (θ2), r1 ∈ RealSet => r2 ∈ RealSet => θ1 ∈ RealSet => θ2 ∈ RealSet => z1 ∈ ComplexSet => z2 ∈ ComplexSet => (z1 = r1 * (cos(θ1) + __IMAGINARY_UNIT__ * sin(θ1)) => z2 = r2 * (cos(θ2) + __IMAGINARY_UNIT__ * sin(θ2)) => z1 * z2 = r1 * r2 * (cos(θ1+θ2) + __IMAGINARY_UNIT__ * sin(θ1+θ2)))

Thm 229. (ComplexExponentialAddition)
forall (z1) (z2), z1 ∈ ComplexSet => z2 ∈ ComplexSet => (e ^ (z1 + z2) = e ^ (z1) * e ^ (z2))

Thm 230. (ComplexNthRoots)
forall (z) (r) (θ) (n), r ∈ RealSet => θ ∈ RealSet => z ∈ ComplexSet => n ∈ PosIntegerSet => (r >= 0 => z = r * (cos(θ) + __IMAGINARY_UNIT__ * sin(θ)) => {w | w ∈ ComplexSet /\ w ^ n = z} = {sqrt(n, r) * (cos((θ + 2 * k * π) / n) + __IMAGINARY_UNIT__ * sin((θ + 2 * k * π) / n)) | k ∈ NonNegIntegerSet /\ k < n})

Thm 231. (SquareOfSum)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => ((a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2)

Thm 232. (SquareOfDifference)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => ((a - b) ^ 2 = a ^ 2 - 2 * a * b + b ^ 2)

Thm 233. (DifferenceOfSquares)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a ^ 2 - b^2 = (a + b) * (a - b))

Thm 234. (CubeOfSum)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => ((a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3)

Thm 235. (CubeOfDifference)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => ((a - b) ^ 3 = a ^ 3 - 3 * a ^ 2 * b + 3 * a * b ^ 2 - b ^ 3)

Thm 236. (RationalizeTwoRadicals)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a >= 0 => b >= 0 => sqrt(a) - sqrt(b) ≠ 0 => sqrt(a) + sqrt(b) = (a - b) / (sqrt(a) - sqrt(b)))

Thm 237. (SumOfCubesFactorization)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a ^ 3 + b ^ 3 = (a + b) * (a ^ 2 - a * b + b ^ 2))

Thm 238. (DifferenceOfCubesFactorization)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a ^ 3 - b ^ 3 = (a - b) * (a ^ 2 + a * b + b ^ 2))

Thm 239. (CubeSumRelation)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => ((a + b) ^ 3 = a ^ 3 + b ^ 3 + 3 * a * b * (a + b))

Thm 240. (CubeDifferenceRelation)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => ((a - b) ^ 3 = a ^ 3 - b ^ 3 - 3 * a * b * (a - b))

Thm 241. (PerfectCubeFactorization)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3 = (a + b) ^ 3)

Thm 242. (HyperbolicSineDefinition)
forall (x), x ∈ RealSet => sinh(x) = (e ^ x - e ^ (-x)) / 2

Thm 243. (HyperbolicCosineDefinition)
forall (x), x ∈ RealSet => cosh(x) = (e ^ x + e ^ (-x)) / 2

Thm 244. (HyperbolicTangentDefinition)
forall (x), x ∈ RealSet => tanh(x) = sinh(x) / cosh(x)

Thm 245. (HyperbolicCotangentDefinition)
forall (x), x ∈ RealSet => x ≠ 0 => coth(x) = cosh(x) / sinh(x)

Thm 246. (HyperbolicSecantDefinition)
forall (x), x ∈ RealSet => sech(x) = 1 / cosh(x)

Thm 247. (HyperbolicCosecantDefinition)
forall (x), x ∈ RealSet => x ≠ 0 => csch(x) = 1 / sinh(x)

Thm 248. (SignFunctionDefinition)
forall (x), x ∈ RealSet => ((x > 0 => sgn(x) = 1) /\ (x = 0 => sgn(x) = 0) /\ (x < 0 => sgn(x) = -1))

Thm 249. (FloorGreatestInteger)
forall (x) (n), x ∈ RealSet => n ∈ IntegerSet => (n <= x => (forall (m), m ∈ IntegerSet => m <= x => m <= n) => floor(x) = n)

Thm 250. (FloorIntervalCharacterization)
forall (x) (n), x ∈ RealSet => n ∈ IntegerSet => (floor(x) = n => n <= x /\ x < n + 1)

Thm 251. (CeilingLeastInteger)
forall (x) (n), x ∈ RealSet => n ∈ IntegerSet => (x <= n => (forall (m), m ∈ IntegerSet => x <= m => n <= m) => ceil(x) = n)

Thm 252. (CeilingIntervalCharacterization)
forall (x) (n), x ∈ RealSet => n ∈ IntegerSet => (ceil(x) = n => n - 1 < x /\ x <= n)

Thm 253. (GradientDefinition)
forall (f) (x) (y) (z), (forall (u) (v) (w), u ∈ RealSet => v ∈ RealSet => w ∈ RealSet => f(u, v, w) ∈ RealSet) => DiffableFuncAt(fun t . f(t, y, z), x) => DiffableFuncAt(fun t . f(x, t, z), y) => DiffableFuncAt(fun t . f(x, y, t), z) => (grad(f)(x, y, z) = (FunDeri(fun t . f(t, y, z), 1, 1)(x), FunDeri(fun t . f(x, t, z), 1, 1)(y), FunDeri(fun t . f(x, y, t), 1, 1)(z)))

Thm 254. (DivergenceDefinition)
forall (Fx) (Fy) (Fz) (x) (y) (z), (forall (u) (v) (w), u ∈ RealSet => v ∈ RealSet => w ∈ RealSet => Fx(u, v, w) ∈ RealSet /\ Fy(u, v, w) ∈ RealSet /\ Fz(u, v, w) ∈ RealSet) => DiffableFuncAt(fun t . Fx(t, y, z), x) => DiffableFuncAt(fun t . Fy(x, t, z), y) => DiffableFuncAt(fun t . Fz(x, y, t), z) => (div(fun u, v, w . (Fx(u, v, w), Fy(u, v, w), Fz(u, v, w)))(x, y, z) = FunDeri(fun t . Fx(t, y, z), 1, 1)(x) + FunDeri(fun t . Fy(x, t, z), 1, 1)(y) + FunDeri(fun t . Fz(x, y, t), 1, 1)(z))

Thm 255. (CurlDefinition)
forall (Fx) (Fy) (Fz) (x) (y) (z), (forall (u) (v) (w), u ∈ RealSet => v ∈ RealSet => w ∈ RealSet => Fx(u, v, w) ∈ RealSet /\ Fy(u, v, w) ∈ RealSet /\ Fz(u, v, w) ∈ RealSet) => DiffableFuncAt(fun t . Fz(x, t, z), y) => DiffableFuncAt(fun t . Fy(x, y, t), z) => DiffableFuncAt(fun t . Fx(x, y, t), z) => DiffableFuncAt(fun t . Fz(t, y, z), x) => DiffableFuncAt(fun t . Fy(t, y, z), x) => DiffableFuncAt(fun t . Fx(x, t, z), y) => (rot(fun u, v, w . (Fx(u, v, w), Fy(u, v, w), Fz(u, v, w)))(x, y, z) = (FunDeri(fun t . Fz(x, t, z), 1, 1)(y) - FunDeri(fun t . Fy(x, y, t), 1, 1)(z), FunDeri(fun t . Fx(x, y, t), 1, 1)(z) - FunDeri(fun t . Fz(t, y, z), 1, 1)(x), FunDeri(fun t . Fy(t, y, z), 1, 1)(x) - FunDeri(fun t . Fx(x, t, z), 1, 1)(y)))

Thm 256. (NablaActionDefinition)
forall (f) (x) (y) (z), (forall (u) (v) (w), u ∈ RealSet => v ∈ RealSet => w ∈ RealSet => f(u, v, w) ∈ RealSet) => DiffableFuncAt(fun t . f(t, y, z), x) => DiffableFuncAt(fun t . f(x, t, z), y) => DiffableFuncAt(fun t . f(x, y, t), z) => (nabla(f)(x, y, z) = (FunDeri(fun t . f(t, y, z), 1, 1)(x), FunDeri(fun t . f(x, t, z), 1, 1)(y), FunDeri(fun t . f(x, y, t), 1, 1)(z)))

Thm 257. (SetUnionMemberCharacterization)
forall (S) (x), (x ∈ SetUnion(S)) <==> (exists (A), (A ∈ S) /\ (x ∈ A))

Thm 258. (SetIntersectionMemberCharacterization)
forall (S) (x), (x ∈ SetInter(S)) <==> (forall (A), (A ∈ S) => (x ∈ A))

Thm 259. (PowerSetDefinition)
forall (S) (A), (A ∈ PowerSet(S)) <==> (A ⊆ S)

Thm 260. (SetDifferenceDefinition)
forall (A) (B) (x), (x ∈ SetMinus(A, B)) <==> ((x ∈ A) /\ Not(x ∈ B))

Thm 261. (CartesianProductDefinition)
forall (A) (B) (p), (p ∈ CartesianProd(A, B)) <==> (exists (a) (b), (a ∈ A) /\ (b ∈ B) /\ (p = (a, b)))

Thm 262. (FunctionDomainDefinition)
forall (f), Dom(f) = { x | exists (y), (x, y) ∈ f }

Thm 263. (InverseFunctionDefinition)
forall (f), InverseFunc(f) = { (y, x) | (x, y) ∈ f }

Thm 264. (GlobalMaximumPointChoice)
forall (f), f : RealSet -> RealSet => (exists (x), x ∈ RealSet /\ forall (y), y ∈ RealSet => f(y) <= f(x)) => (MaximumPoint(f) ∈ RealSet /\ forall (y), y ∈ RealSet => f(y) <= f(MaximumPoint(f)))

Thm 265. (GlobalMinimumPointChoice)
forall (f), f : RealSet -> RealSet => (exists (x), x ∈ RealSet /\ forall (y), y ∈ RealSet => f(y) >= f(x)) => (MinimumPoint(f) ∈ RealSet /\ forall (y), y ∈ RealSet => f(y) >= f(MinimumPoint(f)))

Thm 266. (MaximumPointOnSetChoice)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (exists (x), x ∈ S /\ forall (y), y ∈ S => f(y) <= f(x)) => (MaximumPointOn(f, S) ∈ S /\ forall (y), y ∈ S => f(y) <= f(MaximumPointOn(f, S)))

Thm 267. (MinimumPointOnSetChoice)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (exists (x), x ∈ S /\ forall (y), y ∈ S => f(y) >= f(x)) => (MinimumPointOn(f, S) ∈ S /\ forall (y), y ∈ S => f(y) >= f(MinimumPointOn(f, S)))

Thm 268. (FunctionRestrictionDefinition)
forall (f) (S) (x) (y), ((x, y) ∈ RestrictFunc(f, S)) <==> ((x, y) ∈ f) /\ (x ∈ S)

Thm 269. (OscillationOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => S ≠ ∅ => BoundedFuncOn(f, S) => (OscillationOn(f, S) = sup({|f(x) - f(y)| | x ∈ S /\ y ∈ S}))

Thm 270. (OscillationAtPointDefinition)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => ((exists (delta0), delta0 ∈ RealSet /\ delta0 > 0 /\ BoundedFuncOn(f, (x - delta0, x + delta0))) => OscillationAt(f, x) = lim_{δ -> 0^+}(OscillationOn(f, (x - δ, x + δ))))

Thm 271. (SequenceAccumulationPointDefinition)
forall (a) (L), L ∈ RealSet => ((L ∈ AccumulationPointSet(a)) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (forall (N), N ∈ NonNegIntegerSet => exists (n), n ∈ NonNegIntegerSet /\ n > N /\ |a(n) - L| < ε)))

Thm 272. (PowerSeriesRadiusDefinition)
forall (a), RadiusOfConvergence(a) = sup ({r | r >= 0 /\ (forall (x), |x| < r => ConvergentSeries(sum_{n = 0}^{+∞} (a(n) * x ^ n))) })

Thm 273. (OddIntegerDefinition)
forall (n), Odd(n) <==> (n ∈ IntegerSet) /\ (exists (k), (k ∈ IntegerSet) /\ (n = 2*k + 1))

Thm 274. (EvenIntegerDefinition)
forall (n), Even(n) <==> (n ∈ IntegerSet) /\ (exists (k), (k ∈ IntegerSet) /\ (n = 2*k))

Thm 275. (SetPredicateDefinition)
forall (S), IsSet(S)

Thm 276. (CountableSetDefinition)
forall (S), CountableSet(S) <==> Equinumerous(S, NonNegIntegerSet) \/ (FiniteSet(S))

Thm 277. (UncountableSetDefinition)
forall (S), UncountableSet(S) <==> Not(CountableSet(S))

Thm 278. (RelationFunctionDefinition)
forall (R), IsFunc(R) <==> (forall (x) (y1) (y2), ((x, y1) ∈ R) /\ ((x, y2) ∈ R) => y1 = y2)

Thm 279. (OddFunctionDefinition)
forall (f), f : RealSet -> RealSet => (OddFunc(f) <==> (forall (x), x ∈ RealSet => f(-x) = -f(x)))

Thm 280. (EvenFunctionDefinition)
forall (f), f : RealSet -> RealSet => (EvenFunc(f) <==> (forall (x), x ∈ RealSet => f(-x) = f(x)))

Thm 281. (InjectiveFunctionDefinition)
forall (f), f : RealSet -> RealSet => (InjectiveFunc(f) <==> (forall (x1) (x2), x1 ∈ RealSet => x2 ∈ RealSet => f(x1) = f(x2) => x1 = x2))

Thm 282. (SurjectiveFunctionDefinition)
forall (f) (A) (B), f : A -> B => IsSet(A) => IsSet(B) => (SurjectiveFunc(f) <==> (forall (y), y ∈ B => exists (x), x ∈ A /\ f(x) = y))

Thm 283. (BijectiveFunctionDefinition)
forall (f) (A) (B), f : A -> B => IsSet(A) => IsSet(B) => (BijectiveFunc(f) <==> ((forall (x1) (x2), x1 ∈ A => x2 ∈ A => f(x1) = f(x2) => x1 = x2) /\ (forall (y), y ∈ B => exists (x), x ∈ A /\ f(x) = y)))

Thm 284. (PeriodicFunctionDefinition)
forall (f) (T), f : RealSet -> RealSet => T ∈ RealSet => (PeriodicFunc(f, T) <==> (T > 0 /\ (forall (x), x ∈ RealSet => f(x + T) = f(x))))

Thm 285. (AntiperiodicFunctionDefinition)
forall (f) (T), f : RealSet -> RealSet => T ∈ RealSet => (AntiperiodicFunc(f, T) <==> (T > 0 /\ (forall (x), x ∈ RealSet => f(x + T) = -f(x))))

Thm 286. (ConvexFunctionDefinition)
forall (f), f : RealSet -> RealSet => (ConvexFunc(f) <==> (forall (x) (y) (t), x ∈ RealSet => y ∈ RealSet => t ∈ RealSet => (0 <= t /\ t <= 1) => f(t*x + (1-t)*y) <= t*f(x) + (1-t)*f(y)))

Thm 287. (ConcaveFunctionDefinition)
forall (f), f : RealSet -> RealSet => (ConcaveFunc(f) <==> (forall (x) (y) (t), x ∈ RealSet => y ∈ RealSet => t ∈ RealSet => (0 <= t /\ t <= 1) => f(t*x + (1-t)*y) >= t*f(x) + (1-t)*f(y)))

Thm 288. (ConvexFunctionOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (ConvexFuncOn(f, S) <==> ((forall (x) (y) (t), t ∈ RealSet => x ∈ S => y ∈ S => (0 <= t /\ t <= 1) => t*x + (1-t)*y ∈ S) /\ (forall (x) (y) (t), t ∈ RealSet => x ∈ S => y ∈ S => (0 <= t /\ t <= 1) => f(t*x + (1-t)*y) <= t*f(x) + (1-t)*f(y))))

Thm 289. (ConcaveFunctionOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (ConcaveFuncOn(f, S) <==> ((forall (x) (y) (t), t ∈ RealSet => x ∈ S => y ∈ S => (0 <= t /\ t <= 1) => t*x + (1-t)*y ∈ S) /\ (forall (x) (y) (t), t ∈ RealSet => x ∈ S => y ∈ S => (0 <= t /\ t <= 1) => f(t*x + (1-t)*y) >= t*f(x) + (1-t)*f(y))))

Thm 290. (BoundedFunctionDefinition)
forall (f), f : RealSet -> RealSet => (BoundedFunc(f) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (x), x ∈ RealSet => |f(x)| <= M))

Thm 291. (BoundedAboveFunctionDefinition)
forall (f), f : RealSet -> RealSet => (BoundedAboveFunc(f) <==> (exists (M), M ∈ RealSet /\ forall (x), x ∈ RealSet => f(x) <= M))

Thm 292. (BoundedBelowFunctionDefinition)
forall (f), f : RealSet -> RealSet => (BoundedBelowFunc(f) <==> (exists (M), M ∈ RealSet /\ forall (x), x ∈ RealSet => f(x) >= M))

Thm 293. (BoundedFunctionOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (BoundedFuncOn(f, S) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (x), x ∈ S => |f(x)| <= M))

Thm 294. (BoundedAboveFunctionOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (BoundedAboveFuncOn(f, S) <==> (exists (M), M ∈ RealSet /\ forall (x), x ∈ S => f(x) <= M))

Thm 295. (BoundedBelowFunctionOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (BoundedBelowFuncOn(f, S) <==> (exists (M), M ∈ RealSet /\ forall (x), x ∈ S => f(x) >= M))

Thm 296. (MonotoneIncreasingFunctionDefinition)
forall (f), f : RealSet -> RealSet => (MonoIncFunc(f) <==> (forall (x) (y), x ∈ RealSet => y ∈ RealSet => x <= y => f(x) <= f(y)))

Thm 297. (MonotoneDecreasingFunctionDefinition)
forall (f), f : RealSet -> RealSet => (MonoDecFunc(f) <==> (forall (x) (y), x ∈ RealSet => y ∈ RealSet => x <= y => f(x) >= f(y)))

Thm 298. (StrictlyIncreasingFunctionDefinition)
forall (f), f : RealSet -> RealSet => (StrictMonoIncFunc(f) <==> (forall (x) (y), x ∈ RealSet => y ∈ RealSet => x < y => f(x) < f(y)))

Thm 299. (StrictlyDecreasingFunctionDefinition)
forall (f), f : RealSet -> RealSet => (StrictMonoDecFunc(f) <==> (forall (x) (y), x ∈ RealSet => y ∈ RealSet => x < y => f(x) > f(y)))

Thm 300. (MonotoneIncreasingOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (MonoIncFuncOn(f, S) <==> (forall (x) (y), x ∈ S => y ∈ S => x <= y => f(x) <= f(y)))

Thm 301. (MonotoneDecreasingOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (MonoDecFuncOn(f, S) <==> (forall (x) (y), x ∈ S => y ∈ S => x <= y => f(x) >= f(y)))

Thm 302. (StrictlyIncreasingOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (StrictMonoIncFuncOn(f, S) <==> (forall (x) (y), x ∈ S => y ∈ S => x < y => f(x) < f(y)))

Thm 303. (StrictlyDecreasingOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (StrictMonoDecFuncOn(f, S) <==> (forall (x) (y), x ∈ S => y ∈ S => x < y => f(x) > f(y)))

Thm 304. (ContinuousFunctionDefinition)
forall (f), f : RealSet -> RealSet => (ContinuousFunc(f) <==> (forall (x), x ∈ RealSet => ContinuousFuncAt(f, x)))

Thm 305. (ContinuousFunctionOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (ContinuousFuncOn(f, S) <==> (forall (x), x ∈ S => (forall (ε), ε ∈ RealSet => ε > 0 => exists (δ), δ ∈ RealSet /\ δ > 0 /\ forall (y), y ∈ S => (|y - x| < δ => |f(y) - f(x)| < ε))))

Thm 306. (ContinuousAtEpsilonDelta)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => (ContinuousFuncAt(f, x) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (δ), δ ∈ RealSet /\ δ > 0 /\ (forall (y), y ∈ RealSet => |y - x| < δ => |f(y) - f(x)| < ε))))

Thm 307. (PiecewiseContinuousFunctionDefinition)
forall (f), f : RealSet -> RealSet => (PiecewiseContinuousFunc(f) <==> (forall (a) (b), a ∈ RealSet => b ∈ RealSet => a < b => PiecewiseContinuousFuncOn(f, [a, b])))

Thm 308. (PiecewiseContinuousOnIntervalDefinition)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a < b => (PiecewiseContinuousFuncOn(f, [a, b]) <==> (exists (m) (p), m ∈ NonNegIntegerSet /\ m > 0 /\ p(0) = a /\ p(m) = b /\ (forall (j), j ∈ NonNegIntegerSet => j < m => (p(j) < p(j+1) /\ ContinuousFuncOn(f, (p(j), p(j+1))) /\ (exists (Lright), Lright ∈ RealSet /\ lim_{x -> p(j)^+}(f(x)) = Lright) /\ (exists (Lleft), Lleft ∈ RealSet /\ lim_{x -> p(j+1)^-}(f(x)) = Lleft)))))

Thm 309. (UniformlyContinuousFunctionDefinition)
forall (f), f : RealSet -> RealSet => (UniformContinuousFunc(f) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (δ), δ ∈ RealSet /\ δ > 0 /\ (forall (x) (y), x ∈ RealSet => y ∈ RealSet => |x - y| < δ => |f(x) - f(y)| < ε))))

Thm 310. (UniformlyContinuousOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (UniformContinuousFuncOn(f, S) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (δ), δ ∈ RealSet /\ δ > 0 /\ (forall (x) (y), x ∈ S => y ∈ S => |x - y| < δ => |f(x) - f(y)| < ε))))

Thm 311. (LipschitzContinuousFunctionDefinition)
forall (f), f : RealSet -> RealSet => (LipschitzContinuousFunc(f) <==> (exists (L), L ∈ RealSet /\ L >= 0 /\ (forall (x) (y), x ∈ RealSet => y ∈ RealSet => |f(x) - f(y)| <= L * |x - y|)))

Thm 312. (LipschitzContinuousOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (LipschitzContinuousFuncOn(f, S) <==> (exists (L), L ∈ RealSet /\ L >= 0 /\ (forall (x) (y), x ∈ S => y ∈ S => |f(x) - f(y)| <= L * |x - y|)))

Thm 313. (DifferentiableFunctionDefinition)
forall (f), f : RealSet -> RealSet => (DiffableFunc(f) <==> (forall (x), x ∈ RealSet => DiffableFuncAt(f, x)))

Thm 314. (DifferentiableOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (DiffableFuncOn(f, S) <==> (forall (x), x ∈ S => DiffableFuncAt(f, x)))

Thm 315. (DifferentiableAtLimitDefinition)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => (DiffableFuncAt(f, x) <==> (exists (L), L ∈ RealSet /\ lim_{h -> 0} ((f(x+h) - f(x)) / h) = L))

Thm 316. (LeftDifferentiableFunctionDefinition)
forall (f), f : RealSet -> RealSet => (LeftDiffableFunc(f) <==> (forall (x), x ∈ RealSet => LeftDiffableFuncAt(f, x)))

Thm 317. (LeftDifferentiableOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (LeftDiffableFuncOn(f, S) <==> (forall (x), x ∈ S => LeftDiffableFuncAt(f, x)))

Thm 318. (LeftDifferentiableAtLimitDefinition)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => (LeftDiffableFuncAt(f, x) <==> (exists (L), L ∈ RealSet /\ lim_{h -> 0^-} ((f(x+h) - f(x)) / h) = L))

Thm 319. (RightDifferentiableFunctionDefinition)
forall (f), f : RealSet -> RealSet => (RightDiffableFunc(f) <==> (forall (x), x ∈ RealSet => RightDiffableFuncAt(f, x)))

Thm 320. (RightDifferentiableOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (RightDiffableFuncOn(f, S) <==> (forall (x), x ∈ S => RightDiffableFuncAt(f, x)))

Thm 321. (RightDifferentiableAtLimitDefinition)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => (RightDiffableFuncAt(f, x) <==> (exists (L), L ∈ RealSet /\ lim_{h -> 0^+} ((f(x+h) - f(x)) / h) = L))

Thm 322. (ContinuouslyDifferentiableDefinition)
forall (f), f : RealSet -> RealSet => (ContinuouslyDiffableFunc(f) <==> DiffableFunc(f) /\ ContinuousFunc(FunDeri(f, 1, 1)))

Thm 323. (ClassKFunctionDefinition)
forall (f) (k), f : RealSet -> RealSet => k ∈ NonNegIntegerSet => (FuncOfClassK(f, k) <==> ((k = 0 /\ ContinuousFunc(f)) \/ (k > 0 /\ DiffableFunc(f) /\ (forall (n), n ∈ NonNegIntegerSet => (0 < n /\ n < k) => DiffableFunc(FunDeri(f, 1, n))) /\ ContinuousFunc(FunDeri(f, 1, k)))))

Thm 324. (ClassKFunctionOnSetDefinition)
forall (f) (S) (k), f : RealSet -> RealSet => IsSet(S) => k ∈ NonNegIntegerSet => (FuncOfClassKOn(f, S, k) <==> ((k = 0 /\ ContinuousFuncOn(f, S)) \/ (k > 0 /\ DiffableFuncOn(f, S) /\ (forall (n), n ∈ NonNegIntegerSet => (0 < n /\ n < k) => DiffableFuncOn(FunDeri(f, 1, n), S)) /\ ContinuousFuncOn(FunDeri(f, 1, k), S))))

Thm 325. (SmoothFunctionDefinition)
forall (f), f : RealSet -> RealSet => (SmoothFunc(f) <==> (forall (k), k ∈ NonNegIntegerSet => FuncOfClassK(f, k)))

Thm 326. (SmoothFunctionOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (SmoothFuncOn(f, S) <==> (forall (k), k ∈ NonNegIntegerSet => FuncOfClassKOn(f, S, k)))

Thm 327. (SquareIntegrableFunctionDefinition)
forall (f), f : RealSet -> RealSet => (SquareIntegrableFunc(f) <==> IntegrableFunc(fun x . |f(x)| ^ {2}))

Thm 328. (SquareIntegrableOnSetDefinition)
forall (f) (S), f : RealSet -> RealSet => IsSet(S) => (SquareIntegrableFuncOn(f, S) <==> IntegrableFuncOn(fun x . |f(x)| ^ {2}, S))

Thm 329. (UniformlyBoundedFunctionFamilyDefinition)
forall (F) (S), IsSet(F) => IsSet(S) => (forall (f), f ∈ F => f : RealSet -> RealSet) => (UniformlyBoundedFuncFamily(F, S) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (f), f : RealSet -> RealSet => f ∈ F => forall (x), x ∈ S => |f(x)| <= M))

Thm 330. (SequenceDefinition)
forall (a), IsSeq(a)

Thm 331. (SubsequenceIndexFunctionDefinition)
forall (p), IsSubseqIndexFunc(p) <==> (p: NonNegIntegerSet -> NonNegIntegerSet) /\ StrictMonoIncFunc(p)

Thm 332. (PositiveSequenceDefinition)
forall (a), (PosSeq(a) <==> (forall (n), n ∈ NonNegIntegerSet => a(n) > 0))

Thm 333. (NegativeSequenceDefinition)
forall (a), (NegSeq(a) <==> (forall (n), n ∈ NonNegIntegerSet => a(n) < 0))

Thm 334. (NonnegativeSequenceDefinition)
forall (a), (NonNegSeq(a) <==> (forall (n), n ∈ NonNegIntegerSet => a(n) >= 0))

Thm 335. (AlternatingSignSequenceDefinition)
forall (a), (AlterSeq(a) <==> (forall (n), n ∈ NonNegIntegerSet => a(n) * a(n+1) < 0))

Thm 336. (MonotoneIncreasingSequenceDefinition)
forall (a), (MonoIncSeq(a) <==> (forall (n) (m), n ∈ NonNegIntegerSet => m ∈ NonNegIntegerSet => n <= m => a(n) <= a(m)))

Thm 337. (MonotoneDecreasingSequenceDefinition)
forall (a), (MonoDecSeq(a) <==> (forall (n) (m), n ∈ NonNegIntegerSet => m ∈ NonNegIntegerSet => n <= m => a(n) >= a(m)))

Thm 338. (StrictlyIncreasingSequenceDefinition)
forall (a), (StrictMonoIncSeq(a) <==> (forall (n) (m), n ∈ NonNegIntegerSet => m ∈ NonNegIntegerSet => n < m => a(n) < a(m)))

Thm 339. (StrictlyDecreasingSequenceDefinition)
forall (a), (StrictMonoDecSeq(a) <==> (forall (n) (m), n ∈ NonNegIntegerSet => m ∈ NonNegIntegerSet => n < m => a(n) > a(m)))

Thm 340. (BoundedSequenceDefinition)
forall (a), (BoundedSeq(a) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (n), n ∈ NonNegIntegerSet => |a(n)| <= M))

Thm 341. (BoundedAboveSequenceDefinition)
forall (a), (BoundedAboveSeq(a) <==> (exists (M), M ∈ RealSet /\ forall (n), n ∈ NonNegIntegerSet => a(n) <= M))

Thm 342. (BoundedBelowSequenceDefinition)
forall (a), (BoundedBelowSeq(a) <==> (exists (M), M ∈ RealSet /\ forall (n), n ∈ NonNegIntegerSet => a(n) >= M))

Thm 343. (ConvergentSequenceDefinition)
forall (a), (ConvergentSeq(a) <==> (exists (L), L ∈ RealSet /\ seqlim_{n -> +∞}(a(n)) = L))

Thm 344. (SequenceConvergesToDefinition)
forall (a) (L), L ∈ RealSet => (ConvergentSeqTo(a, L) <==> seqlim_{n -> +∞}(a(n)) = L)

Thm 345. (DivergentSequenceDefinition)
forall (a), (DivergentSeq(a) <==> Not(ConvergentSeq(a)))

Thm 346. (CauchySequenceDefinition)
forall (a), (CauchySeq(a) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (N), N ∈ NonNegIntegerSet /\ forall (m) (n), m ∈ NonNegIntegerSet => n ∈ NonNegIntegerSet => (m >= N /\ n >= N) => |a(m) - a(n)| < ε)))

Thm 347. (UniformSequenceOfFunctionsConvergence)
forall (F) (S) (g), g : RealSet -> RealSet => IsSet(S) => (UniformConvergent(F, S, g) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (N), N ∈ NonNegIntegerSet /\ forall (n), n ∈ NonNegIntegerSet => n >= N => (forall (x), x ∈ S => |F(n)(x) - g(x)| < ε))))

Thm 348. (ConvergentSeriesDefinition)
forall (a), (ConvergentSeries(sum_{n = 0}^{+∞}(a(n))) <==> (exists (s), (forall (n), n ∈ NonNegIntegerSet => s(n) = sum_{k = 0}^{n}(a(k))) /\ ConvergentSeq(s)))

Thm 349. (SeriesConvergesToDefinition)
forall (a) (L), L ∈ RealSet => (ConvergentSeriesTo(sum_{n = 0}^{+∞}(a(n)), L) <==> seqlim_{n -> +∞}(sum_{k = 0}^{n}(a(k))) = L)

Thm 350. (DivergentSeriesDefinition)
forall (a), DivergentSeries(sum_{n = 0}^{+∞} (a(n))) <==> Not(ConvergentSeries(sum_{n = 0}^{+∞} (a(n))))

Thm 351. (AbsolutelyConvergentSeriesDefinition)
forall (a), AbsoluteConvergentSeries(sum_{n = 0}^{+∞} (a(n))) <==> ConvergentSeries(sum_{n = 0}^{+∞} (|a(n)|))

Thm 352. (ConditionallyConvergentSeriesDefinition)
forall (a), ConditionalConvergentSeries(sum_{n = 0}^{+∞} (a(n))) <==> ConvergentSeries(sum_{n = 0}^{+∞} (a(n))) /\ Not(AbsoluteConvergentSeries(sum_{n = 0}^{+∞} (a(n))))

Thm 353. (AbsoluteValueNonnegative)
forall (x), x ∈ RealSet => (|x| >= 0)

Thm 354. (EqualityPreservedBySquaring)
forall (x) (y), x ∈ RealSet => y ∈ RealSet => (x = y => x^2 = y^2)

Thm 355. (NonnegativeNthRoot)
forall (x) (n), x ∈ RealSet => n ∈ IntegerSet => (x >= 0 => n > 0 => sqrt(n, x) >= 0)

Thm 356. (PositiveDerivativeStrictlyIncreasing)
forall (f), f : RealSet -> RealSet => DiffableFunc(f) => (forall (x), x ∈ RealSet => FunDeri(f, 1, 1)(x) > 0) => StrictMonoIncFunc(f)

Thm 357. (PositiveDerivativeIntervalStrictIncrease)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a <= b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(f, (a,b)) => (forall (x), x ∈ (a,b) => FunDeri(f, 1, 1)(x) > 0) => StrictMonoIncFuncOn(f, [a,b])

Thm 358. (NegativeDerivativeStrictlyDecreasing)
forall (f), f : RealSet -> RealSet => DiffableFunc(f) => (forall (x), x ∈ RealSet => FunDeri(f, 1, 1)(x) < 0) => StrictMonoDecFunc(f)

Thm 359. (NegativeDerivativeIntervalStrictDecrease)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a <= b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(f, (a,b)) => (forall (x), x ∈ (a,b) => FunDeri(f, 1, 1)(x) < 0) => StrictMonoDecFuncOn(f, [a,b])

Thm 360. (NonnegativeDerivativeMonotoneIncreasing)
forall (f), f : RealSet -> RealSet => DiffableFunc(f) => (forall (x), x ∈ RealSet => FunDeri(f, 1, 1)(x) >= 0) => MonoIncFunc(f)

Thm 361. (NonnegativeDerivativeIntervalIncrease)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a <= b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(f, (a,b)) => (forall (x), x ∈ (a,b) => FunDeri(f, 1, 1)(x) >= 0) => MonoIncFuncOn(f, [a,b])

Thm 362. (NonpositiveDerivativeMonotoneDecreasing)
forall (f), f : RealSet -> RealSet => DiffableFunc(f) => (forall (x), x ∈ RealSet => FunDeri(f, 1, 1)(x) <= 0) => MonoDecFunc(f)

Thm 363. (NonpositiveDerivativeIntervalDecrease)
forall (f) (a) (b), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => a <= b => ContinuousFuncOn(f, [a,b]) => DiffableFuncOn(f, (a,b)) => (forall (x), x ∈ (a,b) => FunDeri(f, 1, 1)(x) <= 0) => MonoDecFuncOn(f, [a,b])

Thm 364. (NonzeroTermLimitImpliesSeriesDiverges)
forall (a), ¬ConvergentSeqTo(a, 0) => DivergentSeries(sum_{n = 0}^{+∞}(a(n)))

Thm 365. (PSeriesDivergesForExponentAtMostOne)
forall (p), p ∈ RealSet => p <= 1 => DivergentSeries(sum_{n = 1}^{+∞}(1 / n ^ p))

Thm 366. (PSeriesConvergesForExponentAboveOne)
forall (p), p ∈ RealSet => p > 1 => ConvergentSeries(sum_{n = 1}^{+∞}(1 / n ^ p))

Thm 367. (IntegerSquareRootSquared)
forall (n), n ∈ IntegerSet => (n >= 0 => sqrt(2, n) * sqrt(2, n) = n)

Thm 368. (CosineAtIntegerPi)
forall (n), n ∈ IntegerSet => cos(n * π) = (-1) ^ n

Thm 369. (CosineAtOddHalfPi)
forall (n), n ∈ IntegerSet => cos((2 * n + 1) * π / 2) = 0

Thm 370. (SineAtIntegerPi)
forall (n), n ∈ IntegerSet => sin(n * π) = 0

Thm 371. (SineAtOddHalfPi)
forall (n), n ∈ IntegerSet => sin((2 * n + 1) * π / 2) = (-1) ^ n

Thm 372. (TangentAtIntegerPi)
forall (n), n ∈ IntegerSet => tan(n * π) = 0

Thm 373. (TangentCotangentProduct)
forall (x), x ∈ RealSet => (sin(x) ≠ 0 => cos(x) ≠ 0 => tan(x) * cot(x) = 1)

Thm 374. (OneRaisedToRealPower)
forall (x), x ∈ RealSet => (1 ^ x = 1)

Thm 375. (MinusOneEvenPower)
forall (n), n ∈ IntegerSet => (-1) ^ (2 * n) = 1

Thm 376. (MinusOneOddPower)
forall (n), n ∈ IntegerSet => (-1) ^ (2 * n + 1) = -1

Thm 377. (AbsoluteValueSquared)
forall (x), x ∈ RealSet => (|x| ^ 2 = x ^ 2)

Thm 378. (SequenceAdditionPointwise)
forall (x) (y) (n), n ∈ NonNegIntegerSet => ((x + y)(n) = x(n) + y(n))

Thm 379. (SequenceMultiplicationPointwise)
forall (x) (y) (n), n ∈ NonNegIntegerSet => ((x * y)(n) = x(n) * y(n))

Thm 380. (ConstantSequenceLimit)
forall (a) (c), c ∈ RealSet => ((forall (n), n ∈ NonNegIntegerSet => a(n) = c) => seqlim_{n -> +∞}(a(n)) = c)

Thm 381. (ContinuityAtPointAsLimit)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => (ContinuousFuncAt(f, x) <==> lim_{t -> x} (f(t)) = f(x))

Thm 382. (PowerProductDistribution)
forall (a) (b) (r), a ∈ RealSet => b ∈ RealSet => r ∈ RealSet => (a > 0 => b > 0 => (a * b) ^ r = (a ^ r) * (b ^ r))

Thm 383. (BivariateEndpointDifference)
forall (f) (a1) (a2) (b1) (b2), (forall (x) (y), x ∈ RealSet => y ∈ RealSet => f(x, y) ∈ RealSet) => (fun x, y . f(x, y))|_{(a1, a2)}^{(b1, b2)} = f(b1, b2) - f(a1, a2)

Thm 384. (ArccosCosRightInverse)
forall (u), u ∈ RealSet => u ∈ [0, π] => arccos(cos(u)) = u

Thm 385. (ArcsinPrincipalRange)
forall (u), u ∈ RealSet => |u| ≤ 1 => arcsin(u) ∈ [-(π / 2), (π / 2)]

Thm 386. (NthRootNSequenceLimit)
seqlim_{n -> +∞} (sqrtn(n + 1, n + 1)) = 1

Thm 387. (PositiveBasePowerPositive)
forall (a) (u), a ∈ RealSet => u ∈ RealSet => a > 0 => a ^ u > 0

Thm 388. (SineTripleAngle)
forall (x), x ∈ RealSet => sin(3 * x) = 3 * sin(x) - 4 * sin(x) ^ 3

Thm 389. (TangentArctangentInverseRange)
forall (u), u ∈ RealSet => (arctan(u) ∈ (-(π / 2), (π / 2)) /\ tan(arctan(u)) = u)

Thm 390. (DifferentialNotationForDerivative)
forall (g), g : RealSet -> RealSet => DiffableFunc(g) => diff(fun x . g(x)) = FunDeri(g, 1, 1) * diff(fun x . x)

Thm 391. (CompositeExponentialDerivative)
forall (a) (u) (x), u : RealSet -> RealSet => a ∈ RealSet => x ∈ RealSet => a > 0 => DiffableFuncAt(u, x) => FunDeri(fun t . a ^ (u(t)), 1, 1)(x) = a ^ (u(x)) * ln(a) * FunDeri(u, 1, 1)(x)

Thm 392. (DifferentialCoefficientExtraction)
forall (Y) (G), Y : RealSet -> RealSet => G : RealSet -> RealSet => DiffableFunc(Y) => diff(fun x . Y(x)) = (fun x . G(x)) * diff(fun x . x) => (forall (x), x ∈ RealSet => FunDeri(Y, 1, 1)(x) = G(x))

Thm 393. (FiniteSupremumDefinition)
forall (S) (M), IsSet(S) => (sup(S) = M <==> ((forall (x), x ∈ S => x <= M) /\ (forall (ε), ε ∈ RealSet => ε > 0 => exists (u), u ∈ S /\ M - ε < u)))

Thm 394. (MultiplyInequalityByPositiveEquivalence)
forall (a) (b) (c), a ∈ RealSet => b ∈ RealSet => c ∈ RealSet => c > 0 => (a <= b <==> a * c <= b * c)

Thm 395. (MultiplyStrictInequalityByPositive)
forall (a) (b) (c), a ∈ RealSet => b ∈ RealSet => c ∈ RealSet => c > 0 => (a < b <==> a * c < b * c)

Thm 396. (ArctangentTangentPrincipalInverse)
forall (theta), theta ∈ RealSet => -frac(π, 2) < theta /\ theta < frac(π, 2) => arctan(tan(theta)) = theta

Thm 397. (AbsoluteValueOfProduct)
forall (u) (v), u ∈ RealSet => v ∈ RealSet => |u * v| = |u| * |v|

Thm 398. (ProductNonzeroIffFactorsNonzero)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a * b != 0 <==> (a != 0 /\ b != 0))

Thm 399. (BivariateImageSetMembership)
forall (G) (A) (B) (z), (forall (s) (t), s ∈ RealSet => t ∈ RealSet => G(s, t) ∈ RealSet) => IsSet(A) => IsSet(B) => (z ∈ {G(s, t) | s ∈ A /\ t ∈ B} <==> exists (s) (t), (s ∈ A /\ t ∈ B) /\ z = G(s, t))

Thm 400. (MinimumOfTwoRealsDefinition)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => ((min(a, b) = a <==> a <= b) /\ (min(a, b) = b <==> b <= a))

Thm 401. (PositiveSecondDerivativeLocalMonotonicity)
forall (f) (a) (b) (xi), f : RealSet -> RealSet => a ∈ RealSet => b ∈ RealSet => xi ∈ RealSet => FuncOfClassKOn(f, (a, b), 2) => a < xi => xi < b => FunDeri(f, 1, 2)(xi) > 0 => FunDeri(f, 1, 1)(xi) = 0 => exists (delta), delta ∈ RealSet /\ delta > 0 /\ [xi - delta, xi + delta] ⊆ (a, b) /\ MonoDecFuncOn(f, [xi - delta, xi]) /\ MonoIncFuncOn(f, [xi, xi + delta])

Thm 402. (CotangentOdd)
forall (x), x ∈ RealSet => sin(x) ≠ 0 => cot(-x) = -cot(x)

Thm 403. (CosecantDefinition)
forall (x), x ∈ RealSet => sin(x) != 0 => csc(x) = frac(1, sin(x))

Thm 404. (CosineEven)
forall (x), x ∈ RealSet => cos(-x) = cos(x)

Thm 405. (CotangentComplementEqualsTangent)
forall (theta), theta ∈ RealSet => cos(theta) ≠ 0 => cot(π / 2 - theta) = tan(theta)

Thm 406. (DerivativeOfEvenFunctionIsOddPointwise)
forall (f), f : RealSet -> RealSet => DiffableFunc(f) => forall (x), x ∈ RealSet => EvenFunc(f) => FunDeri(f, 1, 1)(x) = -FunDeri(f, 1, 1)(-x)

Thm 407. (MaximumPointGivesRestrictedImageSupremum)
forall (f) (S) (x0), IsSet(S) => (forall (x), x ∈ S => x ∈ Dom(f) /\ f(x) ∈ RealSet) => x0 ∈ S => (exists (xm), xm ∈ S /\ forall (x), x ∈ S => f(x) <= f(xm)) => MaximumPointOn(f, S) = x0 => sup(ImageOn(f, S)) = f(x0)

Thm 408. (FractionScalingByNonzeroFactor)
forall (a) (b) (c), a ∈ RealSet => b ∈ RealSet => c ∈ RealSet => b ≠ 0 => c ≠ 0 => frac(a * c, b * c) = frac(a, b)

Thm 409. (FractionEqualityToCrossProduct)
forall (A) (B) (C), A ∈ RealSet => B ∈ RealSet => C ∈ RealSet => B != 0 => frac(A, B) = C => A = B * C

Thm 410. (SumFirstPositiveIntegers)
forall (n), n ∈ PosIntegerSet => sum_{k = 1}^{n} (k) = frac(n * (n + 1), 2)

Thm 411. (SingletonMembership)
forall (x) (a), x ∈ { a } ⇔ x = a

Thm 412. (HyperbolicCosineDerivative)
forall (x), x ∈ RealSet => FunDeri(fun u . cosh(u), 1, 1)(x) = sinh(x)

Thm 413. (HyperbolicCosinePositive)
forall (u), u ∈ RealSet => cosh(u) > 0

Thm 414. (HyperbolicSquareDifferenceIdentity)
forall (u), u ∈ RealSet => cosh(u) ^ 2 - sinh(u) ^ 2 = 1

Thm 415. (ArctangentAdditionPrincipalFormula)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => a * b < 1 => arctan((a + b) / (1 - a * b)) = arctan(a) + arctan(b)

Thm 416. (ArctangentLimitAtPositiveInfinity)
lim_{x -> +∞} (arctan(x)) = π / 2

Thm 417. (ArctangentOdd)
forall (u), u ∈ RealSet => arctan(-u) = -arctan(u)

Thm 418. (ArctangentAbsoluteBound)
forall (z), z ∈ RealSet => |arctan(z)| <= frac(π, 2)

Thm 419. (ArcsineStandardLimit)
lim_{t -> 0} (frac(arcsin(t), t)) = 1

Thm 420. (ArcsineSpecialValue)
arcsin(frac(1, sqrtn(2, 2))) = frac(π, 4)

Thm 421. (RightUnboundedOpenIntervalMembership)
forall (x) (a), x ∈ RealSet => a ∈ RealSet => (x ∈ (a, +∞) <==> x > a)

Thm 422. (FloorEquivalentDefinition)
forall (x) (n), x ∈ RealSet => n ∈ RealSet => (floor(x) = n <==> (n ∈ IntegerSet) /\ (n <= x) /\ (x < n + 1))

Thm 423. (DerivativeOfPeriodicFunctionPeriodic)
forall (f) (T), f : RealSet -> RealSet => T ∈ RealSet => DiffableFunc(f) => PeriodicFunc(f, T) => forall (x), x ∈ RealSet => FunDeri(f, 1, 1)(x + T) = FunDeri(f, 1, 1)(x)

Thm 424. (ZeroSumImpliesNegation)
forall (u) (a), u ∈ RealSet => a ∈ RealSet => u + a = 0 => u = -a

Thm 425. (ConjugateMultiplication)
forall (z) (w), z ∈ ComplexSet => w ∈ ComplexSet => bar(z * w) = bar(z) * bar(w)

Thm 426. (ConjugateSubtraction)
forall (z) (w), z ∈ ComplexSet => w ∈ ComplexSet => bar(z - w) = bar(z) - bar(w)

Thm 427. (ConjugateAddition)
forall (z) (w), z ∈ ComplexSet => w ∈ ComplexSet => bar(z + w) = bar(z) + bar(w)

Thm 428. (ConjugateDivision)
forall (z) (w), z ∈ ComplexSet => w ∈ ComplexSet => w ≠ 0 => bar(z / w) = bar(z) / bar(w)

Thm 429. (ReciprocalPowerBelowOne)
forall (x), x ∈ RealSet => x > 1 => x ^ (-1) < 1

Thm 430. (IntegerAtLeastOneIsPositiveInteger)
forall (x), x ∈ IntegerSet => x >= 1 => x ∈ PosIntegerSet

Thm 431. (DerivativeOfOddFunctionIsEven)
forall (f), f : RealSet -> RealSet => DiffableFunc(f) => OddFunc(f) => EvenFunc(FunDeri(f, 1, 1))

Thm 432. (PositiveRealProductCharacterization)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a * b > 0 <==> ((a > 0 /\ b > 0) \/ (a < 0 /\ b < 0)))

Thm 433. (NegativeRealProductCharacterization)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a * b < 0 <==> ((a > 0 /\ b < 0) \/ (a < 0 /\ b > 0)))

Thm 434. (NonnegativeRealProductCharacterization)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => (a * b >= 0 <==> ((a >= 0 /\ b >= 0) \/ (a <= 0 /\ b <= 0)))

Thm 435. (RealsEqualUnboundedOpenInterval)
RealSet = (-∞, +∞)

Thm 436. (ProductDerivativeWithKnownValues)
forall (f) (g) (A) (B) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => A ∈ RealSet => B ∈ RealSet => x ∈ RealSet => FunDeri(f, 1, 1)(x) = A => FunDeri(g, 1, 1)(x) = B => FunDeri(fun u . f(u) * g(u), 1, 1)(x) = A * g(x) + f(x) * B

Thm 437. (DerivativeDifferenceQuotientSubstitution)
forall (f) (a) (L), f : RealSet -> RealSet => a ∈ RealSet => L ∈ RealSet => (lim_{x -> a}((f(x) - f(a)) / (x - a)) = L <==> lim_{h -> 0}((f(a + h) - f(a)) / h) = L)

Thm 438. (ProductRule)
forall (f) (g) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => x ∈ RealSet => DiffableFuncAt(f, x) => DiffableFuncAt(g, x) => FunDeri(fun t . f(t) * g(t), 1, 1)(x) = FunDeri(f, 1, 1)(x) * g(x) + f(x) * FunDeri(g, 1, 1)(x)

Thm 439. (DifferenceRule)
forall (f) (g) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => x ∈ RealSet => DiffableFuncAt(f, x) => DiffableFuncAt(g, x) => FunDeri(fun t . f(t) - g(t), 1, 1)(x) = FunDeri(f, 1, 1)(x) - FunDeri(g, 1, 1)(x)

Thm 440. (SumRule)
forall (f) (g) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => x ∈ RealSet => DiffableFuncAt(f, x) => DiffableFuncAt(g, x) => FunDeri(fun t . f(t) + g(t), 1, 1)(x) = FunDeri(f, 1, 1)(x) + FunDeri(g, 1, 1)(x)

Thm 441. (DerivativeAsDifferenceQuotientLimit)
forall (f) (x), f : RealSet -> RealSet => x ∈ RealSet => DiffableFuncAt(f, x) => FunDeri(f, 1, 1)(x) = lim_{h -> 0} (frac(f(x + h) - f(x), h))

Thm 442. (QuotientRule)
forall (f) (g) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => x ∈ RealSet => DiffableFuncAt(f, x) => DiffableFuncAt(g, x) => g(x) ≠ 0 => FunDeri(fun t . f(t) / g(t), 1, 1)(x) = (FunDeri(f, 1, 1)(x) * g(x) - f(x) * FunDeri(g, 1, 1)(x)) / (g(x)) ^ 2

Thm 443. (LeftOpenRightClosedIntervalMembership)
forall (x) (a) (b), x ∈ RealSet => a ∈ RealSet => b ∈ RealSet => (x ∈ (a, b] <==> a < x /\ x <= b)

Thm 444. (LeftUnboundedOpenIntervalMembership)
forall (x) (b), x ∈ RealSet => b ∈ RealSet => (x ∈ (-∞, b) <==> x < b)

Thm 445. (HigherDerivativeOfDifference)
forall (phi) (psi) (k) (x), phi : RealSet -> RealSet => psi : RealSet -> RealSet => x ∈ RealSet => k ∈ NonNegIntegerSet => FuncOfClassK(phi, k) => FuncOfClassK(psi, k) => FunDeri(fun t . phi(t) - psi(t), 1, k)(x) = FunDeri(phi, 1, k)(x) - FunDeri(psi, 1, k)(x)

Thm 446. (DifferenceQuotientLimitImpliesDifferentiable)
forall (F) (a) (L), F : RealSet -> RealSet => a ∈ RealSet => L ∈ RealSet => lim_{h -> 0} (frac(F(a + h) - F(a), h)) = L => DiffableFuncAt(F, a)

Thm 447. (SquareZeroImpliesZero)
forall (u), u ∈ RealSet => u ^ 2 = 0 => u = 0

Thm 448. (SquareCompositionFirstDerivative)
forall (y) (u) (x), y : RealSet -> RealSet => u : RealSet -> RealSet => x ∈ RealSet => (forall (t), t ∈ RealSet => y(t) = u(t) ^ 2) => DiffableFuncAt(u, x) => FunDeri(y, 1, 1)(x) = 2 * u(x) * FunDeri(u, 1, 1)(x)

Thm 449. (SquareCompositionSecondDerivative)
forall (y) (u) (x), y : RealSet -> RealSet => u : RealSet -> RealSet => x ∈ RealSet => (forall (t), t ∈ RealSet => y(t) = u(t) ^ 2) => DiffableFuncAt(u, x) => DiffableFuncAt(FunDeri(u, 1, 1), x) => FunDeri(y, 1, 2)(x) = 2 * FunDeri(u, 1, 1)(x) ^ 2 + 2 * u(x) * FunDeri(u, 1, 2)(x)

Thm 450. (SquareRootSquareCancellation)
forall (u), u ∈ RealSet => u >= 0 => sqrtn(2, u)^2 = u

Thm 451. (SquareArgumentCompositionDerivative)
forall (y) (f) (x), y : RealSet -> RealSet => f : RealSet -> RealSet => x ∈ RealSet => (forall (t), t ∈ RealSet => y(t) = f(t ^ 2)) => DiffableFuncAt(f, x ^ 2) => FunDeri(y, 1, 1)(x) = 2 * x * FunDeri(f, 1, 1)(x ^ 2)

Thm 452. (OpenIntervalMembership)
forall (x) (a) (b), x ∈ RealSet => a ∈ RealSet => b ∈ RealSet => (x ∈ (a, b) <==> (x > a /\ x < b))

Thm 453. (ConvergentSequenceBounded)
forall (a), ConvergentSeq(a) => BoundedSeq(a)

Thm 454. (SequenceMaximumGivesImageSupremum)
forall (x) (S) (n0), IsSet(S) => (forall (n), n ∈ S => n ∈ PosIntegerSet) => n0 ∈ S => (exists (nm), nm ∈ S /\ forall (n), n ∈ S => x(n) <= x(nm)) => MaximumPointOn(x, S) = n0 => sup(ImageOn(x, S)) = x(n0)

Thm 455. (SequenceMinimumGivesImageInfimum)
forall (x) (S) (n0), IsSet(S) => (forall (n), n ∈ S => n ∈ PosIntegerSet) => n0 ∈ S => (exists (nm), nm ∈ S /\ forall (n), n ∈ S => x(nm) <= x(n)) => MinimumPointOn(x, S) = n0 => inf(ImageOn(x, S)) = x(n0)

Thm 456. (IntegerParityDecomposition)
forall (k), k ∈ IntegerSet => (exists (m), m ∈ IntegerSet /\ k = 2 * m) \/ (exists (m), m ∈ IntegerSet /\ k = 2 * m + 1)

Thm 457. (IntegerDiscreteness)
forall (a) (b) , a ∈ IntegerSet =>b ∈ IntegerSet => a > b => a >= b+1

Thm 458. (MaximumElementGivesSupremum)
forall (A) (m), IsSet(A) => (m ∈ A /\ (forall (a), a ∈ A => a <= m)) => sup(A) = m

Thm 459. (FiniteSeriesTermsDoNotAffectConvergence)
forall (a) (N) (M), N ∈ NonNegIntegerSet => M ∈ NonNegIntegerSet => (ConvergentSeries(sum_{n = N}^{+∞} (a(n))) <==> ConvergentSeries(sum_{n = M}^{+∞} (a(n))))

Thm 460. (StandardRadicalQuotientDerivative)
forall (u), u ∈ RealSet => FunDeri(fun x . x / sqrt(2, 1 + x ^ 2), 1, 1)(u) = 1 / ((1 + u ^ 2) ^ (3 / 2))

Thm 461. (PositiveDenominatorRadicalSimplification)
forall (a) (b), a ∈ RealSet => b ∈ RealSet => b > 0 => sqrtn(2, frac(a^2, b^2)) = frac(|a|, b)

Thm 462. (TangentOdd)
forall (x), x ∈ RealSet => cos(x) ≠ 0 => tan(-x) = -tan(x)

Thm 463. (PositiveArctangentPrincipalRange)
forall (u), u ∈ RealSet => u > 0 => (0 < arctan(u) /\ arctan(u) < π / 2)

Thm 464. (PositiveBasePowerProductLaw)
forall (a) (b) (r), a ∈ RealSet => b ∈ RealSet => r ∈ RealSet => a > 0 => b > 0 => (a * b) ^ r = a ^ r * b ^ r

Thm 465. (PositiveBasePowerQuotientLaw)
forall (a) (b) (r), a ∈ RealSet => b ∈ RealSet => r ∈ RealSet => a > 0 => b > 0 => (a / b) ^ r = (a ^ r / b ^ r)

Thm 466. (SineOdd)
forall (x), x ∈ RealSet => sin(-x) = -sin(x)

Thm 467. (SinePositiveOnPositiveHalfPeriod)
forall (n) (t), t ∈ RealSet => n ∈ IntegerSet => (2 * n * π < t /\ t < (2 * n + 1) * π) => sin(t) > 0

Thm 468. (ExponentialDecayDominatesPower)
forall (a) (r), a ∈ RealSet => r ∈ RealSet => a > 0 => r > 0 => lim_{x -> +∞} ((x ^ r) * (e ^ (-a * x))) = 0

Thm 469. (SmallerPositiveDenominatorIncreasesFraction)
forall (a) (b) (c), a ∈ RealSet => b ∈ RealSet => c ∈ RealSet => a > 0 => b > 0 => c > 0 => b - c > 0 => frac(a, b) < frac(a, b - c)

Thm 470. (QuotientOfPositiveIntegerPowers)
forall (u) (v) (n), u ∈ RealSet => v ∈ RealSet => n ∈ PosIntegerSet => v ≠ 0 => frac(u ^ n, v ^ n) = (frac(u, v)) ^ n

Thm 471. (PositiveLinearSequenceTendsToInfinity)
forall (c), c ∈ RealSet => c > 0 => seqlim_{k -> +∞} (c * k) = +∞

Thm 472. (FunctionLimitQuotientAtInfinity)
forall (f) (g) (L1) (L2), f : RealSet -> RealSet => g : RealSet -> RealSet => L1 ∈ RealSet => L2 ∈ RealSet => L2 ≠ 0 => lim_{x -> +∞} (f(x)) = L1 => lim_{x -> +∞} (g(x)) = L2 => lim_{x -> +∞} (f(x) / g(x)) = L1 / L2

Thm 473. (PointwiseCompositionChainDerivative)
forall (Y) (F) (U) (V), Y : RealSet -> RealSet => F : RealSet -> RealSet => U : RealSet -> RealSet => V : RealSet -> RealSet => DiffableFunc(F) => DiffableFunc(V) => (forall (x), x ∈ RealSet => Y(x) = F(U(x))) => (forall (x), x ∈ RealSet => U(x) = V(x)) => (forall (x), x ∈ RealSet => FunDeri(Y, 1, 1)(x) = FunDeri(F, 1, 1)(U(x)) * FunDeri(V, 1, 1)(x))

Thm 474. (DerivativesRespectPointwiseEquality)
forall (f) (g) (n) (x), f : RealSet -> RealSet => g : RealSet -> RealSet => x ∈ RealSet => n ∈ NonNegIntegerSet => (forall (u), u ∈ RealSet => f(u) = g(u)) => FunDeri(f, 1, n)(x) = FunDeri(g, 1, n)(x)

Thm 475. (AdjacentNonincreaseImpliesMonotoneSequence)
forall (a), (forall (n), n ∈ NonNegIntegerSet => a(n + 1) <= a(n)) => MonoDecSeq(a)

Thm 476. (EqualityPreservedByMultiplication)
forall (a) (b) (c), a ∈ RealSet => b ∈ RealSet => c ∈ RealSet => a = b => a * c = b * c

Thm 477. (AbsoluteValueTriangleInequality)
forall (u) (v), u ∈ RealSet => v ∈ RealSet => |u + v| <= |u| + |v|

Thm 478. (AbsoluteValueReverseTriangleInequality)
forall (u) (v), u ∈ RealSet => v ∈ RealSet => |u + v| >= ||u| - |v||

Thm 479. (NonzeroSineInsidePiRadius)
forall (x), x ∈ RealSet => 0 < |x| => |x| < π => sin(x) != 0

Thm 480. (GeometricPowerSequenceTendsToZero)
forall (r), r ∈ RealSet => |r| < 1 => seqlim_{n -> +∞} (r ^ (n + 1)) = 0

Thm 481. (ContinuousFunctionProduct)
forall (f) (g) (a), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => ContinuousFuncAt(f, a) => ContinuousFuncAt(g, a) => ContinuousFuncAt(f * g, a)

Thm 482. (ContinuousFunctionDifference)
forall (f) (g) (a), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => ContinuousFuncAt(f, a) => ContinuousFuncAt(g, a) => ContinuousFuncAt(f - g, a)

Thm 483. (ContinuousFunctionSum)
forall (f) (g) (a), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => ContinuousFuncAt(f, a) => ContinuousFuncAt(g, a) => ContinuousFuncAt(f + g, a)

Thm 484. (ContinuousFunctionValueLimit)
forall (f) (a), f : RealSet -> RealSet => a ∈ RealSet => ContinuousFuncAt(f, a) => lim_{x -> a} (f(x)) = f(a)

Thm 485. (ContinuousFunctionQuotient)
forall (f) (g) (a), f : RealSet -> RealSet => g : RealSet -> RealSet => a ∈ RealSet => ContinuousFuncAt(f, a) => ContinuousFuncAt(g, a) => g(a) ≠ 0 => ContinuousFuncAt(f / g, a)

Thm 486. (NonnegativeTermsHaveNonnegativeFiniteSum)
forall (f) (m) (n), m ∈ IntegerSet => n ∈ IntegerSet => m <= n => (forall (k), k ∈ IntegerSet => m <= k => k <= n => f(k) >= 0) => sum_{k = m}^{n}(f(k)) >= 0

Thm 487. (ClosedIntervalMembership)
forall (x) (a) (b), x ∈ RealSet => a ∈ RealSet => b ∈ RealSet => (x ∈ [a, b] <==> (x >= a /\ x <= b))

Thm 488. (ProductLimitAtZero)
forall (F) (G) (A) (B), F : RealSet -> RealSet => G : RealSet -> RealSet => A ∈ RealSet => B ∈ RealSet => lim_{h -> 0}(F(h)) = A => lim_{h -> 0}(G(h)) = B => lim_{h -> 0}(F(h) * G(h)) = A * B

Thm 489. (AbsoluteValueOfNonpositiveReal)
forall (x), x ∈ RealSet => (x <= 0 <==> |x| = -x)

Thm 490. (AbsoluteValueOfNonnegativeReal)
forall (x), x ∈ RealSet => (x >= 0 <==> |x| = x)

Thm 491. (PositiveRealPowerOfNonnegativeQuotient)
forall (a) (b) (r), a ∈ RealSet => b ∈ RealSet => r ∈ RealSet => a >= 0 => b > 0 => r > 0 => (frac(a, b)) ^ r = frac(a ^ r, b ^ r)

Thm 492. (PositivePowerPreservesNonnegativeOrder)
forall (a) (b) (t), a ∈ RealSet => b ∈ RealSet => t ∈ RealSet => a >= 0 => b >= 0 => t > 0 => a <= b => a ^ t <= b ^ t

Thm 493. (PositivePowerPreservesStrictNonnegativeOrder)
forall (a) (b) (t), a ∈ RealSet => b ∈ RealSet => t ∈ RealSet => a >= 0 => b >= 0 => t > 0 => a < b => a ^ t < b ^ t

Thm 494. (NonzeroConstantProductZeroFactor)
forall (c) (P) (Q) (u), P : RealSet -> RealSet => Q : RealSet -> RealSet => c ∈ RealSet => u ∈ RealSet => c != 0 => c * P(u) * Q(u) = 0 => P(u) = 0 \/ Q(u) = 0

Thm 495. (PeriodicPhiCharacterization)
forall (φ) (T), φ : RealSet -> RealSet => T ∈ RealSet => (PeriodicFunc(φ, T) <==> (T > 0 /\ (forall (x), x ∈ RealSet => φ(x + T) = φ(x))))

Thm 496. (PeriodicChiCharacterization)
forall (χ) (T), χ : RealSet -> RealSet => T ∈ RealSet => (PeriodicFunc(χ, T) <==> (T > 0 /\ (forall (x), x ∈ RealSet => χ(x + T) = χ(x))))

Thm 497. (PeriodicPsiCharacterization)
forall (ψ) (T), ψ : RealSet -> RealSet => T ∈ RealSet => (PeriodicFunc(ψ, T) <==> (T > 0 /\ (forall (x), x ∈ RealSet => ψ(x + T) = ψ(x))))

Thm 498. (BoundedFunctionFOnSetCharacterization)
forall (F) (S), F : RealSet -> RealSet => IsSet(S) => (BoundedFuncOn(F, S) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (x), x ∈ S => |F(x)| <= M))

Thm 499. (BoundedFunctionFStarOnSetCharacterization)
forall (F_{star}) (S), F_{star} : RealSet -> RealSet => IsSet(S) => (BoundedFuncOn(F_{star}, S) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (x), x ∈ S => |F_{star}(x)| <= M))

Thm 500. (BoundedFunctionGOnSetCharacterization)
forall (g) (S), g : RealSet -> RealSet => IsSet(S) => (BoundedFuncOn(g, S) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (x), x ∈ S => |g(x)| <= M))

Thm 501. (MonotoneIncreasingGOnSetCharacterization)
forall (G) (S), G : RealSet -> RealSet => IsSet(S) => (MonoIncFuncOn(G, S) <==> (forall (x) (y), x ∈ S => y ∈ S => x <= y => G(x) <= G(y)))

Thm 502. (MonotoneDecreasingGOnSetCharacterization)
forall (G) (S), G : RealSet -> RealSet => IsSet(S) => (MonoDecFuncOn(G, S) <==> (forall (x) (y), x ∈ S => y ∈ S => x <= y => G(x) >= G(y)))

Thm 503. (ContinuousFunctionFCharacterization)
forall (F), F : RealSet -> RealSet => (ContinuousFunc(F) <==> (forall (x), x ∈ RealSet => ContinuousFuncAt(F, x)))

Thm 504. (ContinuousFunctionGOnSetCharacterization)
forall (g) (S), g : RealSet -> RealSet => IsSet(S) => (ContinuousFuncOn(g, S) <==> (forall (x), x ∈ S => (forall (ε), ε ∈ RealSet => ε > 0 => exists (δ), δ ∈ RealSet /\ δ > 0 /\ forall (y), y ∈ S => (|y - x| < δ => |g(y) - g(x)| < ε))))

Thm 505. (DifferentiableGOnSetCharacterization)
forall (g) (S), g : RealSet -> RealSet => IsSet(S) => (DiffableFuncOn(g, S) <==> (forall (x), x ∈ S => DiffableFuncAt(g, x)))

Thm 506. (DifferentiableGAtPointCharacterization)
forall (g) (x), g : RealSet -> RealSet => x ∈ RealSet => (DiffableFuncAt(g, x) <==> (exists (L), L ∈ RealSet /\ lim_{h -> 0} ((g(x+h) - g(x)) / h) = L))

Thm 507. (BoundedSequenceXCharacterization)
forall (x), (BoundedSeq(x) <==> (exists (M), M ∈ RealSet /\ M >= 0 /\ forall (n), n ∈ NonNegIntegerSet => |x(n)| <= M))

Thm 508. (CauchySequenceXCharacterization)
forall (x), (CauchySeq(x) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (N), N ∈ NonNegIntegerSet /\ forall (m) (n), m ∈ NonNegIntegerSet => n ∈ NonNegIntegerSet => (m >= N /\ n >= N) => |x(m) - x(n)| < ε)))

Thm 509. (CauchySequenceXZeroCharacterization)
forall (x0), (CauchySeq(x0) <==> (forall (ε), ε ∈ RealSet => ε > 0 => (exists (N), N ∈ NonNegIntegerSet /\ forall (m) (n), m ∈ NonNegIntegerSet => n ∈ NonNegIntegerSet => (m >= N /\ n >= N) => |x0(m) - x0(n)| < ε)))

Thm 510. (DifferenceQuotientImpliesDifferentiableF)
forall (f) (a) (L), f : RealSet -> RealSet => a ∈ RealSet => L ∈ RealSet => lim_{h -> 0} (frac(f(a + h) - f(a), h)) = L => DiffableFuncAt(f, a)

Thm 511. (ConvergentSequenceXBounded)
forall (x), ConvergentSeq(x) => BoundedSeq(x)

Thm 512. (PointwiseCompositionChainRuleVariables)
forall (y) (f) (u) (φ), y : RealSet -> RealSet => f : RealSet -> RealSet => u : RealSet -> RealSet => φ : RealSet -> RealSet => DiffableFunc(f) => DiffableFunc(φ) => (forall (x), x ∈ RealSet => y(x) = f(u(x))) => (forall (x), x ∈ RealSet => u(x) = φ(x)) => (forall (x), x ∈ RealSet => FunDeri(y, 1, 1)(x) = FunDeri(f, 1, 1)(u(x)) * FunDeri(φ, 1, 1)(x))

Thm 513. (AdjacentNonincreaseSequenceX)
forall (x), (forall (n), n ∈ NonNegIntegerSet => x(n + 1) <= x(n)) => MonoDecSeq(x)

Thm 514. (ContinuousFunctionFLimit)
forall (F) (a), F : RealSet -> RealSet => a ∈ RealSet => ContinuousFuncAt(F, a) => lim_{x -> a} (F(x)) = F(a)

Thm 515. (IteratedDerivativeOrderAddition)
forall (f) (m) (n) (x), f : RealSet -> RealSet => m ∈ NonNegIntegerSet => n ∈ NonNegIntegerSet => x ∈ RealSet => FuncOfClassK(f, m + n) => FunDeri(FunDeri(f, 1, m), 1, n)(x) = FunDeri(f, 1, m + n)(x)

Thm 516. (PositiveIntegerIsNonnegativeInteger)
forall (x), x ∈ PosIntegerSet => x ∈ NonNegIntegerSet

Thm 517. (PositiveIntegerIsInteger)
forall (x), x ∈ PosIntegerSet => x ∈ IntegerSet

Thm 518. (PositiveIntegerIsReal)
forall (x), x ∈ PosIntegerSet => x ∈ RealSet

Thm 519. (PositiveIntegerIsComplex)
forall (x), x ∈ PosIntegerSet => x ∈ ComplexSet

Thm 520. (NonnegativeIntegerIsInteger)
forall (x), x ∈ NonNegIntegerSet => x ∈ IntegerSet

Thm 521. (NonnegativeIntegerIsReal)
forall (x), x ∈ NonNegIntegerSet => x ∈ RealSet

Thm 522. (NonnegativeIntegerIsComplex)
forall (x), x ∈ NonNegIntegerSet => x ∈ ComplexSet

Thm 523. (IntegerIsReal)
forall (x), x ∈ IntegerSet => x ∈ RealSet

Thm 524. (IntegerIsComplex)
forall (x), x ∈ IntegerSet => x ∈ ComplexSet

Thm 525. (RealIsComplex)
forall (x), x ∈ RealSet => x ∈ ComplexSet
