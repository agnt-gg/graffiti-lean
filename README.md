# Graffiti 292 in Lean 4

A complete, kernel-checked proof of conjecture 292 from S. Fajtlowicz, *Written on the Wall*.

> If a connected graph $G$ on $n$ vertices has girth at least $5$, then its least positive
> adjacency eigenvalue is at most $n / \overline{Gr}$, where $\overline{Gr}$ is the mean of the
> gravity matrix of $G$.

The gravity matrix (*Written on the Wall*, p. 52) has entry $0$ on the diagonal and

$$Gr(u, v) = \frac{d(u)\, d(v)}{(n - 1)\, \operatorname{dist}(u, v)} \qquad (u \ne v).$$

The entry is also $0$ when no path joins $u$ and $v$. [Roucairol and Cazenave](https://arxiv.org/abs/2409.18626)
list conjecture 292 as open (Table 1). The informal proof is in
[*A Proof of Graffiti 292*](https://agnt.gg/whitepapers/a-proof-of-graffiti-292.html), Section 2.5.

## What is proved

All statements are in [`Graffiti292.lean`](Graffiti292.lean), namespace `Graffiti292`.

| Theorem | Statement |
| --- | --- |
| `graffiti_292` | The conjecture, with the mean taken over all $n^2$ entries. |
| `graffiti_292.variants.off_diagonal_mean` | The conjecture, with the mean taken over the $n(n-1)$ off-diagonal entries. |
| `graffiti_292.variants.strict` | Every positive eigenvalue is at most $n - 1$, and $n \le n / \overline{Gr}$. Connectivity is not needed. |

The source does not define the mean of a matrix, so both readings are proved. The definitions
`gravity`, `meanGravity` and `meanGravityOffDiagonal` and the two conjecture statements are
character-for-character identical to the statement file
`FormalConjectures/Arxiv/2409.18626/Graffiti292.lean` proposed for
[google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures).

Only Mathlib definitions are used for degree, distance, girth (`SimpleGraph.egirth`) and the
eigenvalues of the adjacency matrix (`Matrix.IsHermitian.eigenvalues`). Acyclic graphs have
`egirth = ⊤`, so they satisfy the girth hypothesis, as in the source.

## Proof outline

1. Off the diagonal, $\operatorname{dist}(u, v) \ge 1$, so
   $\overline{Gr} \le (2m)^2 / ((n - 1) n^2)$.
2. With girth at least $5$, for each vertex $a$ the sets $N(v) \setminus \{a\}$ ($v \in N(a)$)
   are pairwise disjoint and miss $N(a) \cup \{a\}$. So $\sum_{v \in N(a)} d(v) \le n - 1$, and
   summing over $a$ gives $\sum_v d(v)^2 \le n(n - 1)$. By Cauchy–Schwarz,
   $(2m)^2 \le n^2 (n - 1)$, so $\overline{Gr} \le 1$.
3. Every real eigenvalue is at most the maximum degree, so at most $n - 1$.

Together: $\lambda_+ \le n - 1 < n \le n / \overline{Gr}$.

## Check it

```bash
lake exe cache get   # prebuilt Mathlib
lake build
```

The build prints the axioms of the three theorems:

```text
'Graffiti292.graffiti_292' depends on axioms: [propext, Classical.choice, Quot.sound]
'Graffiti292.graffiti_292.variants.off_diagonal_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Graffiti292.graffiti_292.variants.strict' depends on axioms: [propext, Classical.choice, Quot.sound]
```

There is no `sorry` and no custom axiom. Tested with Lean `v4.33.1` and Mathlib `v4.33.1`
(commit `0df444a360eaa60ab8c11dca51a86af692955474`, the version used by formal-conjectures),
and also with Lean `v4.32.2` and Mathlib `v4.32.2`. `lake build` runs with `--wfail` clean.

## Authors

Nathan Wilbanks and Annie (AGNT Labs). The argument formalised here is Section 2.5 of the paper,
which credits it to Spanky McDoob.

## License

Apache License 2.0. See [LICENSE](LICENSE).
