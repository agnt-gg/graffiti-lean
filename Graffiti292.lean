import Mathlib

/-!
# Graffiti conjecture 292: a formal proof

*References:*
- S. Fajtlowicz, *Written on the Wall* (July 2004 version): conjecture 292 (p. 80), the gravity
  matrix (p. 52), adjacency eigenvalues as the default (p. 1), and connected graphs for
  conjectures that involve distance (p. 2).
- M. Roucairol and T. Cazenave, *Refutation of Spectral Graph Theory Conjectures with Search
  Algorithms*, arXiv:2409.18626. Table 1 lists conjecture 292 as open; Section 5.2 restates the
  gravity matrix of *Written on the Wall*.
- N. Wilbanks and Annie, *A Proof of Graffiti 292*, AGNT Labs (2026),
  https://agnt.gg/whitepapers/a-proof-of-graffiti-292.html. Section 2.5 gives the argument
  formalised here; the paper credits it to Spanky McDoob.

**Conjecture 292.** If a connected graph `G` on `n` vertices has girth at least five, then its
least positive adjacency eigenvalue is at most `n / mean(Gr)`. Here `Gr` is the gravity matrix:
`Gr u v = d(u) d(v) / ((n - 1) dist(u, v))` for `u ≠ v`, and `Gr u u = 0`.

The source does not define the mean of a matrix. `graffiti_292` uses the mean of all `n²`
entries. `graffiti_292.variants.off_diagonal_mean` uses the mean of the `n (n - 1)` off-diagonal
entries. The definitions and both statements are identical to those in
`FormalConjectures/Arxiv/2409.18626/Graffiti292.lean` of google-deepmind/formal-conjectures.

## Proof

1. `meanGravity_le`: `dist u v ≥ 1` off the diagonal, so `mean(Gr) ≤ (2m)² / ((n - 1) n²)`.
2. `sum_degree_neighbors_le`: with girth at least five, the sets `N(v) \ {a}` for `v ∈ N(a)` are
   pairwise disjoint (no 4-cycle) and miss `N(a) ∪ {a}` (no triangle). So
   `Σ_{v ∈ N(a)} d(v) ≤ n - 1`. Summing over `a` gives `Σ d(v)² ≤ n (n - 1)`. This is the counting
   bound of Section 2.5, proved by neighbourhoods instead of paths of length two. Cauchy–Schwarz
   then gives `(2m)² ≤ n² (n - 1)` (`edge_bound`), so `mean(Gr) ≤ 1` (`meanGravity_le_one`).
3. `eigenvalue_le_degree`: every real eigenvalue is at most the maximum degree, so at most `n - 1`.

Together: `λ₊ ≤ n - 1 < n ≤ n / mean(Gr)` (`graffiti_292.variants.strict`). The proof does not
use connectivity.
-/

open Finset Matrix

namespace Graffiti292

/-! ### Definitions, identical to the formal-conjectures statement file -/

/-- The gravity matrix of `G`. The $(u, v)$ entry is $0$ if $u = v$, and otherwise
$\frac{d(u) d(v)}{(n - 1) \operatorname{dist}(u, v)}$, where $n$ is the number of vertices.
If no path joins $u$ and $v$, then `G.dist u v = 0` and the entry is $0$, as in the source. -/
noncomputable def gravity {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (u v : α) : ℝ :=
  if u = v then 0
  else (G.degree u * G.degree v : ℝ) / ((Fintype.card α - 1 : ℝ) * G.dist u v)

/-- The mean of the $n^2$ entries of the gravity matrix of `G`. -/
noncomputable def meanGravity {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] : ℝ :=
  (∑ u, ∑ v, gravity G u v) / (Fintype.card α : ℝ) ^ 2

/-- The mean of the $n(n-1)$ off-diagonal entries of the gravity matrix of `G`. -/
noncomputable def meanGravityOffDiagonal {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  (∑ u, ∑ v, gravity G u v) / (Fintype.card α * (Fintype.card α - 1) : ℝ)

/-! ### Proof -/

variable {α : Type*} [Fintype α] [DecidableEq α] {G : SimpleGraph α} [DecidableRel G.Adj]

omit [Fintype α] [DecidableEq α] [DecidableRel G.Adj] in
lemma no_triangle (hg : 5 ≤ G.egirth) {a b c : α}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hw : w.IsCycle := by
    have h1 := hab.ne
    have h2 := hbc.ne
    have h3 := hca.ne
    simp only [w, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.cons_isPath_iff,
      SimpleGraph.Walk.isPath_iff_nil, SimpleGraph.Walk.nil_nil, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, Sym2.eq_iff]
    grind
  have : (5 : ℕ∞) ≤ 3 := by simpa [w] using hg.trans (SimpleGraph.egirth_le_length hw)
  exact absurd this (by decide)

omit [Fintype α] [DecidableEq α] [DecidableRel G.Adj] in
lemma no_square (hg : 5 ≤ G.egirth) {a v b v' : α}
    (hav : G.Adj a v) (hvb : G.Adj v b) (hbv' : G.Adj b v') (hv'a : G.Adj v' a)
    (hab : a ≠ b) (hvv' : v ≠ v') : False := by
  let w : G.Walk a a := .cons hav (.cons hvb (.cons hbv' (.cons hv'a .nil)))
  have hw : w.IsCycle := by
    have h1 := hav.ne
    have h2 := hvb.ne
    have h3 := hbv'.ne
    have h4 := hv'a.ne
    simp only [w, SimpleGraph.Walk.cons_isCycle_iff, SimpleGraph.Walk.cons_isPath_iff,
      SimpleGraph.Walk.isPath_iff_nil, SimpleGraph.Walk.nil_nil, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil, SimpleGraph.Walk.edges_cons, SimpleGraph.Walk.edges_nil,
      List.mem_cons, List.not_mem_nil, Sym2.eq_iff]
    grind
  have : (5 : ℕ∞) ≤ 4 := by simpa [w] using hg.trans (SimpleGraph.egirth_le_length hw)
  exact absurd this (by decide)

/-- Girth `≥ 5`: the degrees of the neighbours of any vertex sum to at most `n - 1`. -/
lemma sum_degree_neighbors_le (hg : 5 ≤ G.egirth) (a : α) :
    ∑ v ∈ G.neighborFinset a, G.degree v ≤ Fintype.card α - 1 := by
  have hdisj : (↑(G.neighborFinset a) : Set α).PairwiseDisjoint
      (fun v => (G.neighborFinset v).erase a) := by
    intro v hv v' hv' hne
    simp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro b hb hb'
    simp only [Finset.mem_coe, SimpleGraph.mem_neighborFinset] at hv hv'
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hb hb'
    exact no_square hg hv hb.2 hb'.2.symm hv'.symm (Ne.symm hb.1) hne
  have hsub : (G.neighborFinset a).biUnion (fun v => (G.neighborFinset v).erase a) ⊆
      univ \ insert a (G.neighborFinset a) := by
    intro b hb
    simp only [Finset.mem_biUnion, Finset.mem_erase, SimpleGraph.mem_neighborFinset] at hb
    obtain ⟨v, hav, hba, hvb⟩ := hb
    simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert,
      SimpleGraph.mem_neighborFinset, true_and, not_or]
    exact ⟨hba, fun hab => no_triangle hg hav hvb hab.symm⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_insert_of_notMem (by simp), Finset.card_univ,
    SimpleGraph.card_neighborFinset_eq_degree] at hcard
  have herase : ∀ v ∈ G.neighborFinset a, ((G.neighborFinset v).erase a).card + 1 =
      G.degree v := by
    intro v hv
    rw [SimpleGraph.mem_neighborFinset] at hv
    rw [Finset.card_erase_of_mem (by simpa using hv.symm),
      SimpleGraph.card_neighborFinset_eq_degree]
    have : 0 < G.degree v := (G.degree_pos_iff_exists_adj v).mpr ⟨a, hv.symm⟩
    omega
  have hsplit : ∑ v ∈ G.neighborFinset a, G.degree v =
      (∑ v ∈ G.neighborFinset a, ((G.neighborFinset v).erase a).card) + G.degree a := by
    rw [← Finset.sum_congr rfl herase, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
      mul_one, SimpleGraph.card_neighborFinset_eq_degree]
  have hlt := G.degree_lt_card_verts a
  omega

/-- Girth `≥ 5`: `Σ d(v)² ≤ n (n - 1)`. -/
lemma sum_degree_sq_le (hg : 5 ≤ G.egirth) :
    ∑ v, G.degree v ^ 2 ≤ Fintype.card α * (Fintype.card α - 1) := by
  have hswap : ∑ v, G.degree v ^ 2 = ∑ a, ∑ v ∈ G.neighborFinset a, G.degree v := by
    calc ∑ v, G.degree v ^ 2 = ∑ v, ∑ a ∈ G.neighborFinset v, G.degree v := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [Finset.sum_const, smul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree, sq]
      _ = ∑ v, ∑ a, if G.Adj v a then G.degree v else 0 := by
          simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
      _ = ∑ a, ∑ v, if G.Adj a v then G.degree v else 0 := by
          rw [Finset.sum_comm]
          simp only [G.adj_comm]
      _ = ∑ a, ∑ v ∈ G.neighborFinset a, G.degree v := by
          simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rw [hswap]
  calc ∑ a, ∑ v ∈ G.neighborFinset a, G.degree v ≤ ∑ _a : α, (Fintype.card α - 1) :=
        Finset.sum_le_sum fun a _ => sum_degree_neighbors_le hg a
    _ = Fintype.card α * (Fintype.card α - 1) := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

/-- Girth `≥ 5`: `(2m)² ≤ n · n · (n - 1)`. -/
lemma edge_bound (hg : 5 ≤ G.egirth) :
    (2 * #G.edgeFinset) ^ 2 ≤ Fintype.card α * (Fintype.card α * (Fintype.card α - 1)) := by
  rw [← G.sum_degrees_eq_twice_card_edges]
  calc (∑ v, G.degree v) ^ 2 ≤ #(univ : Finset α) * ∑ v, G.degree v ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ Fintype.card α * (Fintype.card α * (Fintype.card α - 1)) := by
        rw [Finset.card_univ]
        exact Nat.mul_le_mul_left _ (sum_degree_sq_le hg)

omit [DecidableEq α] in
/-- Every real eigenvalue is bounded in absolute value by the degree of some vertex. -/
lemma eigenvalue_le_degree (μ : ℝ) (x : α → ℝ) (hx : x ≠ 0)
    (h : G.adjMatrix ℝ *ᵥ x = μ • x) : ∃ i, |μ| ≤ G.degree i := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image univ (fun k => |x k|) ⟨j, mem_univ j⟩
  have hxi : 0 < |x i| := lt_of_lt_of_le (abs_pos.mpr hj) (hi j (mem_univ j))
  refine ⟨i, ?_⟩
  have hrow := congrFun h i
  rw [SimpleGraph.adjMatrix_mulVec_apply, Pi.smul_apply, smul_eq_mul] at hrow
  have hbound : |μ| * |x i| ≤ (G.degree i : ℝ) * |x i| := by
    calc |μ| * |x i| = |∑ u ∈ G.neighborFinset i, x u| := by rw [hrow, abs_mul]
      _ ≤ ∑ u ∈ G.neighborFinset i, |x u| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _u ∈ G.neighborFinset i, |x i| := Finset.sum_le_sum fun u _ => hi u (mem_univ u)
      _ = (G.degree i : ℝ) * |x i| := by
          rw [Finset.sum_const, nsmul_eq_mul, SimpleGraph.card_neighborFinset_eq_degree]
  exact le_of_mul_le_mul_right hbound hxi

omit [DecidableEq α] in
/-- Every real eigenvalue is at most `n - 1`, and a positive one forces an edge. -/
lemma eigenvalue_le_card_sub_one (μ : ℝ) (x : α → ℝ) (hx : x ≠ 0)
    (h : G.adjMatrix ℝ *ᵥ x = μ • x) :
    μ ≤ (Fintype.card α : ℝ) - 1 ∧ (0 < μ → 0 < #G.edgeFinset) := by
  obtain ⟨i, hi⟩ := eigenvalue_le_degree μ x hx h
  have hlt : G.degree i + 1 ≤ Fintype.card α := G.degree_lt_card_verts i
  have hltR : (G.degree i : ℝ) + 1 ≤ Fintype.card α := by exact_mod_cast hlt
  refine ⟨by linarith [le_abs_self μ], fun hμ => ?_⟩
  have hdeg : 0 < G.degree i := by
    have : (0 : ℝ) < G.degree i := lt_of_lt_of_le (abs_pos.mpr hμ.ne') hi
    exact_mod_cast this
  obtain ⟨j, hij⟩ := (G.degree_pos_iff_exists_adj i).mp hdeg
  exact Finset.card_pos.mpr ⟨s(i, j), (SimpleGraph.mem_edgeFinset).mpr hij⟩

lemma gravity_nonneg (u v : α) : 0 ≤ gravity G u v := by
  unfold gravity
  split_ifs with huv
  · exact le_rfl
  · have hn : 1 < Fintype.card α := Fintype.one_lt_card_iff.mpr ⟨u, v, huv⟩
    have hn' : (1 : ℝ) < Fintype.card α := by exact_mod_cast hn
    exact div_nonneg (by positivity) (mul_nonneg (by linarith) (Nat.cast_nonneg _))

lemma gravity_le (hn : 2 ≤ Fintype.card α) (u v : α) :
    gravity G u v ≤ (G.degree u : ℝ) * G.degree v / ((Fintype.card α : ℝ) - 1) := by
  have hn1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
    linarith
  unfold gravity
  split_ifs with huv
  · exact div_nonneg (by positivity) hn1.le
  · rcases Nat.eq_zero_or_pos (G.dist u v) with h0 | hpos
    · rw [h0, Nat.cast_zero, mul_zero, div_zero]
      exact div_nonneg (by positivity) hn1.le
    · apply div_le_div_of_nonneg_left (by positivity) hn1
      have : (1 : ℝ) ≤ G.dist u v := by exact_mod_cast hpos
      nlinarith

/-- Lemma 1 of the paper: `mean(Gr) ≤ (2m)² / ((n - 1) n²)`. -/
lemma meanGravity_le (hn : 2 ≤ Fintype.card α) :
    meanGravity G ≤ (2 * (#G.edgeFinset : ℝ)) ^ 2 /
      (((Fintype.card α : ℝ) - 1) * (Fintype.card α : ℝ) ^ 2) := by
  have hdeg : (∑ i, (G.degree i : ℝ)) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hdouble : ∑ u, ∑ v, (G.degree u : ℝ) * G.degree v / ((Fintype.card α : ℝ) - 1) =
      (2 * (#G.edgeFinset : ℝ)) ^ 2 / ((Fintype.card α : ℝ) - 1) := by
    rw [← hdeg, sq, Finset.sum_mul_sum, Finset.sum_div]
    simp_rw [Finset.sum_div]
  unfold meanGravity
  calc (∑ u, ∑ v, gravity G u v) / (Fintype.card α : ℝ) ^ 2
      ≤ (∑ u, ∑ v, (G.degree u : ℝ) * G.degree v / ((Fintype.card α : ℝ) - 1)) /
          (Fintype.card α : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => gravity_le hn u v
    _ = (2 * (#G.edgeFinset : ℝ)) ^ 2 /
          (((Fintype.card α : ℝ) - 1) * (Fintype.card α : ℝ) ^ 2) := by
        rw [hdouble, div_div]

/-- Girth `≥ 5` and at least one edge: `mean(Gr) ≤ 1`. -/
lemma meanGravity_le_one (hg : 5 ≤ G.egirth) (hn : 2 ≤ Fintype.card α) :
    meanGravity G ≤ 1 := by
  have hkey := edge_bound hg
  have hkeyR : (2 * (#G.edgeFinset : ℝ)) ^ 2 ≤
      (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hkey
    push_cast [Nat.cast_sub (show 1 ≤ Fintype.card α by omega)] at this
    exact this
  have hnR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  refine (meanGravity_le hn).trans ?_
  rw [div_le_one (by have : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by linarith
                     positivity)]
  nlinarith [hkeyR]

lemma meanGravity_pos (hn : 2 ≤ Fintype.card α) (hm : 0 < #G.edgeFinset) :
    0 < meanGravity G := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp hm
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hn1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by
      have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
      linarith
    have hda : 0 < G.degree a := (G.degree_pos_iff_exists_adj a).mpr ⟨b, he⟩
    have hdb : 0 < G.degree b := (G.degree_pos_iff_exists_adj b).mpr ⟨a, he.symm⟩
    have hab : 0 < gravity G a b := by
      unfold gravity
      rw [if_neg he.ne, (SimpleGraph.dist_eq_one_iff_adj).mpr he]
      push_cast
      exact div_pos (by positivity) (by linarith)
    have hrow : gravity G a b ≤ ∑ v, gravity G a v :=
      Finset.single_le_sum (fun v _ => gravity_nonneg a v) (Finset.mem_univ b)
    have hall : ∑ v, gravity G a v ≤ ∑ u, ∑ v, gravity G u v :=
      Finset.single_le_sum (f := fun u => ∑ v, gravity G u v)
        (fun u _ => Finset.sum_nonneg fun v _ => gravity_nonneg u v) (Finset.mem_univ a)
    unfold meanGravity
    exact div_pos (by linarith) (by positivity)

/-- The uniform strict form (§2.5): a positive eigenvalue `μ` of a graph of girth at least five
satisfies `μ ≤ n - 1 < n ≤ n / mean(Gr)`. -/
theorem eigenvalue_strict (hg : 5 ≤ G.egirth) (μ : ℝ) (x : α → ℝ) (hx : x ≠ 0)
    (h : G.adjMatrix ℝ *ᵥ x = μ • x) (hμ : 0 < μ) :
    μ ≤ (Fintype.card α : ℝ) - 1 ∧ (Fintype.card α : ℝ) ≤ Fintype.card α / meanGravity G := by
  obtain ⟨hle, hedge⟩ := eigenvalue_le_card_sub_one μ x hx h
  have hm := hedge hμ
  have hn : 2 ≤ Fintype.card α := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hm
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact Fintype.one_lt_card_iff.mpr ⟨a, b, he.ne⟩
  have hpos := meanGravity_pos hn hm
  refine ⟨hle, ?_⟩
  rw [le_div_iff₀ hpos]
  have : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  nlinarith [meanGravity_le_one hg hn]

lemma eigenvectorBasis_eigen (i : α) :
    (⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i) : α → ℝ) ≠ 0 ∧
      G.adjMatrix ℝ *ᵥ ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i) =
        (G.isHermitian_adjMatrix ℝ).eigenvalues i •
          ⇑((G.isHermitian_adjMatrix ℝ).eigenvectorBasis i) := by
  refine ⟨fun h0 => ?_, by simpa using (G.isHermitian_adjMatrix ℝ).mulVec_eigenvectorBasis i⟩
  apply (G.isHermitian_adjMatrix ℝ).eigenvectorBasis.orthonormal.ne_zero i
  ext j
  simpa using congrFun h0 j

/-! ### The statements, identical to `FormalConjectures/Arxiv/2409.18626/Graffiti292.lean` -/

set_option linter.unusedVariables false in
/-- **Graffiti 292.** The least positive adjacency eigenvalue of a connected graph with girth at
least five is at most `n / mean(Gr)`. The hypotheses `hconn` and `hleast` are part of the
faithful statement; the proof does not need them. -/
theorem graffiti_292 {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hconn : G.Connected) (hgirth : 5 ≤ G.egirth) (i : α)
    (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i)
    (hleast : ∀ j, 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues j →
      (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues j) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ Fintype.card α / meanGravity G := by
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
      Fintype.card α / meanGravityOffDiagonal G := by
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  obtain ⟨hle, hedge⟩ := eigenvalue_le_card_sub_one _ _ hx h
  have hm := hedge hpos
  have hn : 2 ≤ Fintype.card α := by
    obtain ⟨e, he⟩ := Finset.card_pos.mp hm
    induction e using Sym2.ind with
    | h a b =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact Fintype.one_lt_card_iff.mpr ⟨a, b, he.ne⟩
  have hnR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hmg := meanGravity_pos hn hm
  have hmg1 := meanGravity_le_one hgirth hn
  have hn0 : (Fintype.card α : ℝ) ≠ 0 := by linarith
  have hS : (∑ u, ∑ v, gravity G u v) = meanGravity G * (Fintype.card α : ℝ) ^ 2 :=
    (div_mul_cancel₀ _ (pow_ne_zero 2 hn0)).symm
  have hrw : (Fintype.card α : ℝ) / meanGravityOffDiagonal G =
      ((Fintype.card α : ℝ) - 1) / meanGravity G := by
    unfold meanGravityOffDiagonal
    rw [hS, div_div_eq_mul_div,
      div_eq_div_iff (mul_pos hmg (pow_pos (by linarith) 2)).ne' hmg.ne']
    ring
  rw [hrw, le_div_iff₀ hmg]
  calc (G.isHermitian_adjMatrix ℝ).eigenvalues i * meanGravity G
      ≤ (G.isHermitian_adjMatrix ℝ).eigenvalues i * 1 := mul_le_mul_of_nonneg_left hmg1 hpos.le
    _ ≤ (Fintype.card α : ℝ) - 1 := by linarith

/-- **Stronger uniform form (paper, §2.5).** Every positive adjacency eigenvalue of a graph with
girth at least five is at most `n - 1`, and `n ≤ n / mean(Gr)`. So the inequality of
conjecture 292 is strict. Connectivity is not used. -/
theorem graffiti_292.variants.strict {α : Type*} [Fintype α] [DecidableEq α] (G : SimpleGraph α)
    [DecidableRel G.Adj] (hgirth : 5 ≤ G.egirth) (i : α)
    (hpos : 0 < (G.isHermitian_adjMatrix ℝ).eigenvalues i) :
    (G.isHermitian_adjMatrix ℝ).eigenvalues i ≤ (Fintype.card α : ℝ) - 1 ∧
      (Fintype.card α : ℝ) ≤ Fintype.card α / meanGravity G := by
  obtain ⟨hx, h⟩ := eigenvectorBasis_eigen (G := G) i
  exact eigenvalue_strict hgirth _ _ hx h hpos

/-! ### Sanity checks on the definitions -/

/-- `K₂`: each off-diagonal entry is `1·1/((2-1)·1) = 1`, so the mean of the four entries
is `1/2`. Pins the `n²` normalisation and the `(n - 1)` factor. -/
example : meanGravity (⊤ : SimpleGraph (Fin 2)) = 1 / 2 := by
  have hdist : (⊤ : SimpleGraph (Fin 2)).dist 0 1 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
  have hdist' : (⊤ : SimpleGraph (Fin 2)).dist 1 0 = 1 :=
    SimpleGraph.dist_eq_one_iff_adj.mpr (by decide)
  simp [meanGravity, gravity, Fin.sum_univ_two, hdist, hdist', SimpleGraph.complete_graph_degree]
  norm_num

/-- The hypotheses are satisfiable: `K₂` is connected and acyclic, so its girth is `∞ ≥ 5`. -/
example : (⊤ : SimpleGraph (Fin 2)).Connected ∧ 5 ≤ (⊤ : SimpleGraph (Fin 2)).egirth := by
  refine ⟨SimpleGraph.connected_top, ?_⟩
  rw [SimpleGraph.egirth_eq_top.mpr (SimpleGraph.IsAcyclic.of_card_le_two (by simp))]
  exact le_top

end Graffiti292

#print axioms Graffiti292.graffiti_292
#print axioms Graffiti292.graffiti_292.variants.off_diagonal_mean
#print axioms Graffiti292.graffiti_292.variants.strict
