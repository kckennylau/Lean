# Roadmap to algebraic closure of field F

Implicitly, in what I write below, p=1 if char(F)=0.

## Field theory

1. Any finite subgroup of F* is cyclic
2. Freshman's dream: (x+y)^p = x^p + y^p

## Polynomials

3. division algorithm
4. F[X] is a ED (3)
5. ED -> PID -> UFD -> GCD
6. F[X] is a PID (4,5)
7. F[X] is a UFD (4,5)
8. F[X] is a GCD (4,5)

## Algebraic extensions

9. Integral elements form subring

## Splitting fields

10. Every polynomial splits in some extension (6,7)

## Separable polynomials

11. Resultant of two polynomials
12. Discriminant of polynomials (11)
13. f in F[X] is separable := discriminant(f) is non-zero (12)
14. f is separable iff gcd(f,Df)=1 (8,11)
15. f is separable iff it has no double root in every extension in which it splits (10)
16. For every irreducible f in F[X] there is n in N and h in F[X] such that f(x) = h(x^(p^n)) and h is separable (14)
17. If If K/F then f in F[X] is separable iff (coe f) in K[X] is separable. (13)
18. f is separable iff all its factors are separable
19. Primitive element theorem (1,10,15,17,18)
20. F perfect := every polynomial is separable
21. Perfect iff Frobenius surjective (2,16)

## Proof

22. For every irreducible f in F[X] let Xf be an indeterminate.
23. Let R := F[{Xf | f irredcuible}] be a big polynomial ring.
24. Let I := span {f(Xf) | f irreducible} an ideal in R.
25. I is a proper ideal. (10)
26. Let L := R/M where M is a maximal ideal that contains I (25).
27. L is a field algebraic over F. (9)
28. Let K := {x in L | exists n, x^(p^n) in F}.
29. K is a subfield. (2)
30. K is perfect. (2,21)
31. Every polynomial in K[X] has a root in L. (2)
32. Every polynomial in K[X] splits in L. (19,30,31)
33. L is algebraically closed. (32)
34. L is an algebraic closure of F. (27,33)
