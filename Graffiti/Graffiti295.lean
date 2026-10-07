import Graffiti.Basic
import Graffiti.DistanceMatrix

/-!
# Graffiti conjecture 295

The two statements below are identical to `FormalConjectures/Arxiv/2409.18626/Graffiti295.lean`
in google-deepmind/formal-conjectures.

Proof: the distance matrix has at most `n` eigenvalues, so at most `n` positive ones. If the
graph has an edge, then `n ≥ 2` and, for girth at least five, both readings of the mean gravity
lie in `(0, 1]` (`Graffiti.Basic`), so `n ≤ n / mean(Gr)`. If the graph has no edge, every
distance is `0`, the distance matrix is `0`, and it has no positive eigenvalue.
-/

open Finset Matrix SimpleGraph Graffiti

namespace Graffiti295

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
/-- The distance matrix has at most `n` positive eigenvalues. -/
lemma countP_pos_le_card :
    G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) ≤ Fintype.card α :=
  (Multiset.countP_le_card _ _).trans
    ((Polynomial.card_roots' _).trans (Matrix.charpoly_natDegree_eq_dim _).le)

omit [DecidableEq α] in
/-- A graph with no edges has distance matrix `0`. -/
lemma distanceMatrix_eq_zero (hm : #G.edgeFinset = 0) : G.distanceMatrix = 0 := by
  ext u v
  rw [distanceMatrix_apply, Matrix.zero_apply, Nat.cast_eq_zero]
  by_cases huv : u = v
  · subst huv
    exact SimpleGraph.dist_self
  · apply SimpleGraph.dist_eq_zero_of_not_reachable
    rintro ⟨p⟩
    cases p with
    | nil => exact huv rfl
    | cons h _ =>
      have hmem : s(u, _) ∈ G.edgeFinset := (SimpleGraph.mem_edgeFinset).mpr h
      rw [Finset.card_eq_zero] at hm
      simp [hm] at hmem

/-- A graph with no edges has no positive distance eigenvalue. -/
lemma countP_pos_eq_zero (hm : #G.edgeFinset = 0) :
    G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) = 0 := by
  rw [distanceMatrix_eq_zero hm, Matrix.charpoly_zero, Polynomial.roots_X_pow]
  exact Multiset.countP_eq_zero.mpr (by simp)

omit [DecidableEq α] in
/-- An edge forces two vertices. -/
lemma two_le_card (hm : 0 < #G.edgeFinset) : 2 ≤ Fintype.card α := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp hm
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    exact Fintype.one_lt_card_iff.mpr ⟨a, b, he.ne⟩

/-- The positive distance eigenvalues number at most `n / A` for any mean `A ≥ 0` that lies
in `(0, 1]` whenever the graph has an edge. -/
lemma countP_pos_le_div {A : ℝ} (hA0 : 0 ≤ A) (hApos : 0 < #G.edgeFinset → 0 < A)
    (hA1 : 0 < #G.edgeFinset → A ≤ 1) :
    (G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) : ℝ) ≤ Fintype.card α / A := by
  rcases Nat.eq_zero_or_pos (#G.edgeFinset) with hm | hm
  · rw [countP_pos_eq_zero hm, Nat.cast_zero]
    exact div_nonneg (Nat.cast_nonneg _) hA0
  · calc (G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) : ℝ)
        ≤ Fintype.card α := by exact_mod_cast countP_pos_le_card
      _ ≤ Fintype.card α / A := le_div_self (Nat.cast_nonneg _) (hApos hm) (hA1 hm)

lemma meanGravityOffDiagonal_nonneg : 0 ≤ G.meanGravityOffDiagonal := by
  unfold SimpleGraph.meanGravityOffDiagonal
  apply div_nonneg (Finset.sum_nonneg fun u _ => Finset.sum_nonneg fun v _ => G.gravity_nonneg u v)
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h | h
  · simp [h]
  · have : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast h
    nlinarith

set_option linter.unusedVariables false in
/-- **Graffiti 295.** For a connected graph with girth at least five, the number of positive
eigenvalues of the distance matrix is at most `n / mean(Gr)`. The hypothesis `hconn` is part of
the faithful statement; the proof does not need it. -/
theorem graffiti_295 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) :
    (G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) : ℝ) ≤
      Fintype.card α / G.meanGravity := by
  exact countP_pos_le_div G.meanGravity_nonneg (fun hm => meanGravity_pos (two_le_card hm) hm)
    (fun hm => meanGravity_le_one hgirth (two_le_card hm))

set_option linter.unusedVariables false in
/-- **Graffiti 295, off-diagonal mean.** The same bound with the mean taken over the `n (n - 1)`
off-diagonal entries. -/
theorem graffiti_295.variants.off_diagonal_mean {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) :
    (G.distanceMatrix.charpoly.roots.countP (fun x => 0 < x) : ℝ) ≤
      Fintype.card α / G.meanGravityOffDiagonal := by
  exact countP_pos_le_div meanGravityOffDiagonal_nonneg
    (fun hm => meanGravityOffDiagonal_pos (two_le_card hm) hm)
    (fun hm => meanGravityOffDiagonal_le_one hgirth (two_le_card hm))

end Graffiti295

#print axioms Graffiti295.graffiti_295
#print axioms Graffiti295.graffiti_295.variants.off_diagonal_mean
