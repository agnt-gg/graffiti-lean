# Graffiti 290, 292 and 295 in Lean 4

Complete, kernel-checked proofs of conjectures 290, 292 and 295 from S. Fajtlowicz,
*Written on the Wall*. All three are listed as open in Table 1 of
[Roucairol and Cazenave](https://arxiv.org/abs/2409.18626).

> **290.** If girth is at least 5, then $-\lambda_{n-1} \le m / \overline{Gr}$.
>
> **292.** If girth is at least 5, then the least positive eigenvalue is at most
> $n / \overline{Gr}$.
>
> **295.** If girth is at least 5, then the number of positive eigenvalues of the distance
> matrix is at most $n / \overline{Gr}$.

Here $\lambda_1 \ge \dots \ge \lambda_n$ are the adjacency eigenvalues, $m$ is the number of edges
("size"), and $\overline{Gr}$ is the mean of the gravity matrix (*Written on the Wall*, p. 52):
entry $0$ on the diagonal and

$$Gr(u, v) = \frac{d(u)\, d(v)}{(n - 1)\, \operatorname{dist}(u, v)} \qquad (u \ne v).$$

The entry is also $0$ when no path joins $u$ and $v$. Conjectures that involve distance are for
connected graphs (p. 2), and eigenvalues are adjacency eigenvalues (p. 1).

Informal proofs: [*A Proof of Graffiti 292*](https://agnt.gg/whitepapers/a-proof-of-graffiti-292.html)
(Section 2.5), [*A Proof of Graffiti 290*](https://agnt.gg/whitepapers/a-proof-of-graffiti-290.html)
and [*A Proof of Graffiti 295*](https://agnt.gg/whitepapers/a-proof-of-graffiti-295.html).

## What is proved

| File | Theorem | Statement |
| --- | --- | --- |
| `Graffiti/Graffiti290.lean` | `graffiti_290` | 290, mean over all $n^2$ entries |
| | `graffiti_290.variants.off_diagonal_mean` | 290, mean over the $n(n-1)$ off-diagonal entries |
| | `graffiti_290.variants.abs_le` | every eigenvalue: $\lvert\lambda\rvert \le m / \overline{Gr}$, without connectivity |
| `Graffiti/Graffiti292.lean` | `graffiti_292` | 292, mean over all $n^2$ entries |
| | `graffiti_292.variants.off_diagonal_mean` | 292, mean over the $n(n-1)$ off-diagonal entries |
| | `graffiti_292.variants.strict` | $\lambda_+ \le n - 1 < n \le n / \overline{Gr}$, without connectivity |
| `Graffiti/Graffiti295.lean` | `graffiti_295` | 295, mean over all $n^2$ entries |
| | `graffiti_295.variants.off_diagonal_mean` | 295, mean over the $n(n-1)$ off-diagonal entries |

The source does not define the mean of a matrix, so both readings are proved.

`Graffiti/Gravity.lean` defines `SimpleGraph.gravity`, `SimpleGraph.meanGravity` and
`SimpleGraph.meanGravityOffDiagonal`, and `Graffiti/DistanceMatrix.lean` defines
`SimpleGraph.distanceMatrix`. These definitions, and the six conjecture statements, are
character-for-character identical to those proposed for
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(`FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Gravity.lean`, `DistanceMatrix.lean` and
`FormalConjectures/Arxiv/2409.18626/`). Degree, distance, girth (`SimpleGraph.egirth`) and the
eigenvalues (`Matrix.IsHermitian.eigenvalues`, and `eigenvalues₀` sorted in decreasing order) are
Mathlib's own. Acyclic graphs have `egirth = ⊤`, so they satisfy the girth hypothesis.

## Proof outline

`Graffiti/Basic.lean`:

1. With girth at least $5$, for each vertex $a$ the sets $N(v) \setminus \{a\}$ ($v \in N(a)$) are
   pairwise disjoint and miss $N(a) \cup \{a\}$. So $\sum_v d(v)^2 \le n(n - 1)$, and by
   Cauchy–Schwarz $(2m)^2 \le n^2 (n - 1)$.
2. Off the diagonal $\operatorname{dist}(u, v) \ge 1$, so
   $\sum Gr \le \bigl((2m)^2 - \sum_v d(v)^2\bigr) / (n - 1) \le (2m)^2 / n$.
3. Hence both readings of $\overline{Gr}$ are at most $1$.
4. Every real eigenvalue satisfies $\lvert\lambda\rvert \le \Delta \le \min(n - 1, m)$.

So $-\lambda_{n-1} \le m \le m / \overline{Gr}$ (290) and $\lambda_+ \le n - 1 < n \le n / \overline{Gr}$ (292).
For 295, the distance matrix has at most $n$ eigenvalues, so at most $n \le n / \overline{Gr}$
positive ones; with no edges the distance matrix is $0$. Eigenvalues are counted with
multiplicity as roots of the characteristic polynomial, as in `SimpleGraph.cvetkovic`.
For 292 this is Section 2.5 of the paper, which credits the argument to Spanky McDoob.

## Check it

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

The build prints the axioms of all eight theorems. Each is
`[propext, Classical.choice, Quot.sound]`. There is no `sorry`, no custom axiom and no
`native_decide`. Tested with Lean `v4.33.1` and Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`, the version used by formal-conjectures),
with warnings treated as errors.

## Authors

Nathan Wilbanks and Annie (AGNT Labs).

## License

Apache License 2.0. See [LICENSE](LICENSE).
