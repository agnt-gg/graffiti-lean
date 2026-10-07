import Graffiti.Basic

/-!
# Graffiti conjecture 290

The two statements below are identical to `FormalConjectures/Arxiv/2409.18626/Graffiti290.lean`
in google-deepmind/formal-conjectures.

Proof: for girth at least five, both readings of the mean gravity are at most `1`
(`meanGravity_le_one`, `meanGravityOffDiagonal_le_one`). Every real eigenvalue `λ` satisfies
`|λ| ≤ Δ ≤ m`. So `-λ_{n-1} ≤ |λ_{n-1}| ≤ m ≤ m / mean(Gr)`. This gives the stronger statement
`graffiti_290.variants.abs_le` for every eigenvalue, without connectivity.
-/

open Finset Matrix SimpleGraph Graffiti

namespace Graffiti290

set_option linter.unusedVariables false in
/-- **Graffiti 290.** For a connected graph with `n ≥ 2` vertices, `m` edges and girth at least
five, `-λ_{n-1} ≤ m / mean(Gr)`, where `λ_{n-1}` is the second-smallest adjacency eigenvalue.
The hypothesis `hconn` is part of the faithful statement; the proof does not need it. -/
theorem graffiti_290 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth)
    (hn : 2 ≤ Fintype.card α) :
    -(G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨Fintype.card α - 2, by omega⟩ ≤
      G.edgeFinset.card / G.meanGravity := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq (G := G) ⟨Fintype.card α - 2, by omega⟩
  rw [← hi]
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  exact (neg_le_abs _).trans <| abs_le_card_edgeFinset_div
    (abs_eigenvalue_le_card_edgeFinset _ _ hx h) (fun hm => meanGravity_pos hn hm)
    (meanGravity_le_one hgirth hn)

set_option linter.unusedVariables false in
/-- **Graffiti 290, off-diagonal mean.** The same bound with the mean taken over the `n (n - 1)`
off-diagonal entries. -/
theorem graffiti_290.variants.off_diagonal_mean {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth)
    (hn : 2 ≤ Fintype.card α) :
    -(G.isHermitian_adjMatrix ℝ).eigenvalues₀ ⟨Fintype.card α - 2, by omega⟩ ≤
      G.edgeFinset.card / G.meanGravityOffDiagonal := by
  obtain ⟨i, hi⟩ := exists_eigenvalues_eq (G := G) ⟨Fintype.card α - 2, by omega⟩
  rw [← hi]
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  exact (neg_le_abs _).trans <| abs_le_card_edgeFinset_div
    (abs_eigenvalue_le_card_edgeFinset _ _ hx h) (fun hm => meanGravityOffDiagonal_pos hn hm)
    (meanGravityOffDiagonal_le_one hgirth hn)

/-- **Stronger form.** Every adjacency eigenvalue of a graph with `n ≥ 2` vertices and girth at
least five satisfies `|λ| ≤ m / mean(Gr)`. Connectivity is not used. -/
theorem graffiti_290.variants.abs_le {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hgirth : 5 ≤ G.egirth) (hn : 2 ≤ Fintype.card α) (i : α) :
    |(G.isHermitian_adjMatrix ℝ).eigenvalues i| ≤ G.edgeFinset.card / G.meanGravity := by
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  exact abs_le_card_edgeFinset_div (abs_eigenvalue_le_card_edgeFinset _ _ hx h)
    (fun hm => meanGravity_pos hn hm) (meanGravity_le_one hgirth hn)

end Graffiti290

#print axioms Graffiti290.graffiti_290
#print axioms Graffiti290.graffiti_290.variants.off_diagonal_mean
#print axioms Graffiti290.graffiti_290.variants.abs_le
