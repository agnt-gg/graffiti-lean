import Graffiti.Gravity

/-!
# Lemmas for Graffiti conjectures 290 and 292

Girth at least five gives no triangles and no 4-cycles, hence `Σ d(v)² ≤ n (n - 1)` and
`(2m)² ≤ n² (n - 1)`. With the gravity bound `Σ Gr ≤ (2m)² / n`, both readings of the mean
gravity are at most `1`. Every real eigenvalue is at most the maximum degree in absolute value.
-/

open Finset Matrix SimpleGraph

namespace Graffiti

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

lemma gravity_le (hn : 2 ≤ Fintype.card α) (u v : α) :
    G.gravity u v ≤ (G.degree u : ℝ) * G.degree v / ((Fintype.card α : ℝ) - 1) := by
  have hn1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by
    have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
    linarith
  unfold SimpleGraph.gravity
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
    G.meanGravity ≤ (2 * (#G.edgeFinset : ℝ)) ^ 2 /
      (((Fintype.card α : ℝ) - 1) * (Fintype.card α : ℝ) ^ 2) := by
  have hdeg : (∑ i, (G.degree i : ℝ)) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  have hdouble : ∑ u, ∑ v, (G.degree u : ℝ) * G.degree v / ((Fintype.card α : ℝ) - 1) =
      (2 * (#G.edgeFinset : ℝ)) ^ 2 / ((Fintype.card α : ℝ) - 1) := by
    rw [← hdeg, sq, Finset.sum_mul_sum, Finset.sum_div]
    simp_rw [Finset.sum_div]
  unfold SimpleGraph.meanGravity
  calc (∑ u, ∑ v, G.gravity u v) / (Fintype.card α : ℝ) ^ 2
      ≤ (∑ u, ∑ v, (G.degree u : ℝ) * G.degree v / ((Fintype.card α : ℝ) - 1)) /
          (Fintype.card α : ℝ) ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => gravity_le hn u v
    _ = (2 * (#G.edgeFinset : ℝ)) ^ 2 /
          (((Fintype.card α : ℝ) - 1) * (Fintype.card α : ℝ) ^ 2) := by
        rw [hdouble, div_div]

/-- Girth `≥ 5` and at least one edge: `mean(Gr) ≤ 1`. -/
lemma meanGravity_le_one (hg : 5 ≤ G.egirth) (hn : 2 ≤ Fintype.card α) :
    G.meanGravity ≤ 1 := by
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
    0 < G.meanGravity := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp hm
  induction e using Sym2.ind with
  | h a b =>
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    have hn1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by
      have : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
      linarith
    have hda : 0 < G.degree a := (G.degree_pos_iff_exists_adj a).mpr ⟨b, he⟩
    have hdb : 0 < G.degree b := (G.degree_pos_iff_exists_adj b).mpr ⟨a, he.symm⟩
    have hab : 0 < G.gravity a b := by
      unfold SimpleGraph.gravity
      rw [if_neg he.ne, (SimpleGraph.dist_eq_one_iff_adj).mpr he]
      push_cast
      exact div_pos (by positivity) (by linarith)
    have hrow : G.gravity a b ≤ ∑ v, G.gravity a v :=
      Finset.single_le_sum (fun v _ => G.gravity_nonneg a v) (Finset.mem_univ b)
    have hall : ∑ v, G.gravity a v ≤ ∑ u, ∑ v, G.gravity u v :=
      Finset.single_le_sum (f := fun u => ∑ v, G.gravity u v)
        (fun u _ => Finset.sum_nonneg fun v _ => G.gravity_nonneg u v) (Finset.mem_univ a)
    unfold SimpleGraph.meanGravity
    exact div_pos (by linarith) (by positivity)

/-- The uniform strict form (§2.5): a positive eigenvalue `μ` of a graph of girth at least five
satisfies `μ ≤ n - 1 < n ≤ n / mean(Gr)`. -/
theorem eigenvalue_strict (hg : 5 ≤ G.egirth) (μ : ℝ) (x : α → ℝ) (hx : x ≠ 0)
    (h : G.adjMatrix ℝ *ᵥ x = μ • x) (hμ : 0 < μ) :
    μ ≤ (Fintype.card α : ℝ) - 1 ∧ (Fintype.card α : ℝ) ≤ Fintype.card α / G.meanGravity := by
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

/-! ### Lemmas for Graffiti 290 and the off-diagonal mean -/

/-- Subtracting the diagonal: `Σ Gr ≤ ((2m)² - Σ d²) / (n - 1) ≤ (2m)² / n`. -/
lemma sum_gravity_le (hn : 2 ≤ Fintype.card α) :
    ∑ u, ∑ v, G.gravity u v ≤ (2 * (#G.edgeFinset : ℝ)) ^ 2 / Fintype.card α := by
  have hN : (2 : ℝ) ≤ (Fintype.card α : ℝ) := by exact_mod_cast hn
  set N : ℝ := (Fintype.card α : ℝ) with hN_def
  have hdeg : (∑ i, (G.degree i : ℝ)) = 2 * (#G.edgeFinset : ℝ) := by
    exact_mod_cast G.sum_degrees_eq_twice_card_edges
  set M : ℝ := 2 * (#G.edgeFinset : ℝ)
  set D : ℝ := ∑ i, (G.degree i : ℝ) ^ 2 with hD_def
  have hCS : M ^ 2 ≤ N * D := by
    have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := fun i => (G.degree i : ℝ))
    rw [card_univ, hdeg] at h
    exact h
  have hterm : ∀ u v : α, G.gravity u v ≤
      (G.degree u : ℝ) * G.degree v / (N - 1) -
        (if u = v then (G.degree u : ℝ) * G.degree v / (N - 1) else 0) := by
    intro u v
    split_ifs with h
    · simp [h]
    · simpa using gravity_le hn u v
  have hall : ∑ u, ∑ v, ((G.degree u : ℝ) * G.degree v / (N - 1)) = M ^ 2 / (N - 1) := by
    rw [← hdeg, sq, Finset.sum_mul_sum, Finset.sum_div]
    simp_rw [Finset.sum_div]
  have hdiag : ∑ u, (G.degree u : ℝ) * G.degree u / (N - 1) = D / (N - 1) := by
    rw [hD_def, Finset.sum_div]
    exact Finset.sum_congr rfl fun u _ => by ring
  calc ∑ u, ∑ v, G.gravity u v
      ≤ ∑ u, ∑ v, ((G.degree u : ℝ) * G.degree v / (N - 1) -
          (if u = v then (G.degree u : ℝ) * G.degree v / (N - 1) else 0)) :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hterm u v
    _ = (M ^ 2 - D) / (N - 1) := by
        simp only [Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hall,
          hdiag]
        ring
    _ ≤ M ^ 2 / N := by
        rw [div_le_div_iff₀ (by linarith) (by linarith)]
        nlinarith [hCS]

/-- With at least one edge, the gravity sum is positive. -/
lemma sum_gravity_pos (hn : 2 ≤ Fintype.card α) (hm : 0 < #G.edgeFinset) :
    0 < ∑ u, ∑ v, G.gravity u v := by
  have h := meanGravity_pos hn hm
  unfold SimpleGraph.meanGravity at h
  exact (div_pos_iff_of_pos_right (by positivity)).mp h

/-- Girth `≥ 5`: the off-diagonal mean gravity is at most `1`. -/
lemma meanGravityOffDiagonal_le_one (hg : 5 ≤ G.egirth) (hn : 2 ≤ Fintype.card α) :
    G.meanGravityOffDiagonal ≤ 1 := by
  have hkey := edge_bound hg
  have hkeyR : (2 * (#G.edgeFinset : ℝ)) ^ 2 ≤
      (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1)) := by
    have := (Nat.cast_le (α := ℝ)).mpr hkey
    push_cast [Nat.cast_sub (show 1 ≤ Fintype.card α by omega)] at this
    exact this
  have hnR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hS := sum_gravity_le (G := G) hn
  unfold SimpleGraph.meanGravityOffDiagonal
  rw [div_le_one (by nlinarith)]
  calc ∑ u, ∑ v, G.gravity u v ≤ (2 * (#G.edgeFinset : ℝ)) ^ 2 / Fintype.card α := hS
    _ ≤ (Fintype.card α : ℝ) * ((Fintype.card α : ℝ) - 1) := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith [hkeyR]

/-- With at least one edge, the off-diagonal mean gravity is positive. -/
lemma meanGravityOffDiagonal_pos (hn : 2 ≤ Fintype.card α) (hm : 0 < #G.edgeFinset) :
    0 < G.meanGravityOffDiagonal := by
  have hnR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  unfold SimpleGraph.meanGravityOffDiagonal
  exact div_pos (sum_gravity_pos hn hm) (by nlinarith)

/-- Each entry of the sorted spectrum `eigenvalues₀` is an eigenvalue `eigenvalues i`. -/
lemma exists_eigenvalues_eq (k : Fin (Fintype.card α)) :
    ∃ i, (G.isHermitian_adjMatrix ℝ).eigenvalues i = (G.isHermitian_adjMatrix ℝ).eigenvalues₀ k :=
  ⟨Fintype.equivOfCardEq (Fintype.card_fin _) k, by simp [Matrix.IsHermitian.eigenvalues]⟩

omit [DecidableEq α] in
/-- Every real eigenvalue is at most the number of edges in absolute value. -/
lemma abs_eigenvalue_le_card_edgeFinset (μ : ℝ) (x : α → ℝ) (hx : x ≠ 0)
    (h : G.adjMatrix ℝ *ᵥ x = μ • x) : |μ| ≤ #G.edgeFinset := by
  obtain ⟨i, hi⟩ := eigenvalue_le_degree μ x hx h
  exact hi.trans (by exact_mod_cast G.degree_le_card_edgeFinset i)

omit [DecidableEq α] in
/-- If `|μ| ≤ m`, then `|μ| ≤ m / A` for every mean `A` that is at most `1` and is positive
whenever the graph has an edge. -/
lemma abs_le_card_edgeFinset_div {μ A : ℝ} (hμ : |μ| ≤ #G.edgeFinset)
    (hA : 0 < #G.edgeFinset → 0 < A) (hA1 : A ≤ 1) : |μ| ≤ #G.edgeFinset / A := by
  rcases Nat.eq_zero_or_pos (#G.edgeFinset) with hm | hm
  · rw [hm, Nat.cast_zero] at hμ ⊢
    rw [zero_div]
    exact hμ
  · exact hμ.trans (le_div_self (Nat.cast_nonneg _) (hA hm) hA1)

end Graffiti
