import Mathlib

/-!
# The distance matrix of a graph

The distance matrix of a graph $G$ has entry $\operatorname{dist}(u, v)$ at $(u, v)$. Mathlib's
`SimpleGraph.dist` is $0$ when no path joins $u$ and $v$.
-/

namespace SimpleGraph

variable {α : Type*}

/-- The distance matrix of `G`, with real entries `G.dist u v`. -/
noncomputable def distanceMatrix (G : SimpleGraph α) : Matrix α α ℝ :=
  Matrix.of fun u v => (G.dist u v : ℝ)

@[simp]
lemma distanceMatrix_apply (G : SimpleGraph α) (u v : α) :
    G.distanceMatrix u v = G.dist u v :=
  rfl

lemma isSymm_distanceMatrix (G : SimpleGraph α) : G.distanceMatrix.IsSymm := by
  ext u v
  simp [distanceMatrix, dist_comm]

end SimpleGraph
