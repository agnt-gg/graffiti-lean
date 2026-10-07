import Graffiti.Basic

/-!
# Graffiti conjecture 292

The two statements below are identical to `FormalConjectures/Arxiv/2409.18626/Graffiti292.lean`
in google-deepmind/formal-conjectures. The proof is the uniform argument of Section 2.5 of
*A Proof of Graffiti 292* (Nathan Wilbanks and Annie, AGNT Labs, 2026), which the paper credits to
Spanky McDoob: `λ₊ ≤ n - 1 < n ≤ n / mean(Gr)`, because `mean(Gr) ≤ 1` for girth at least five.
-/

open Finset Matrix SimpleGraph Graffiti

namespace Graffiti292

set_option linter.unusedVariables false in
/-- **Graffiti 292.** The least positive adjacency eigenvalue of a connected graph with girth at
least five is at most `n / mean(Gr)`. The hypotheses `hconn` and `hleast` are part of the
faithful statement; the proof does not need them. -/
theorem graffiti_292 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) (i : α)
    (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i)
    (hleast : ∀ j, 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues j →
      (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues j) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ Fintype.card α / G.meanGravity := by
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  obtain ⟨hle, hge⟩ := eigenvalue_strict hgirth _ _ hx h hpos
  linarith

set_option linter.unusedVariables false in
/-- **Graffiti 292, off-diagonal mean.** The same bound with the mean taken over the `n (n - 1)`
off-diagonal entries. -/
theorem graffiti_292.variants.off_diagonal_mean {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth)
    (i : α) (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i)
    (hleast : ∀ j, 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues j →
      (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues j) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤
      Fintype.card α / G.meanGravityOffDiagonal := by
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  obtain ⟨hle, hedge⟩ := eigenvalue_le_card_sub_one _ _ hx h
  have hm := hedge hpos
  have hn : 2 ≤ Fintype.card α := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hm
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact Fintype.one_lt_card_iff.mpr ⟨a, b, he.ne⟩
  have hpos' := meanGravityOffDiagonal_pos (G := G) hn hm
  have hle1 := meanGravityOffDiagonal_le_one hgirth hn
  have hn0 : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  calc (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (Fintype.card α : ℝ) - 1 := hle
    _ ≤ Fintype.card α := by linarith
    _ ≤ Fintype.card α / G.meanGravityOffDiagonal := le_div_self hn0 hpos' hle1

/-- **Strict uniform form.** Every positive adjacency eigenvalue of a graph with girth at least
five is at most `n - 1`, and `n ≤ n / mean(Gr)`. Connectivity is not used. -/
theorem graffiti_292.variants.strict {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hgirth : 5 ≤ G.egirth) (i : α)
    (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (Fintype.card α : ℝ) - 1 ∧
      (Fintype.card α : ℝ) ≤ Fintype.card α / G.meanGravity := by
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  exact eigenvalue_strict hgirth _ _ hx h hpos

end Graffiti292

#print axioms Graffiti292.graffiti_292
#print axioms Graffiti292.graffiti_292.variants.off_diagonal_mean
#print axioms Graffiti292.graffiti_292.variants.strict
