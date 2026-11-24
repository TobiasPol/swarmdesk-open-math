import Mathlib

namespace Targets.ErdosGyarfas.Spec

/-- A simple graph on `Fin n` has a simple cycle whose length is `2^k` with `k ≥ 2` (length ≥ 4). -/
def HasPowerOfTwoCycle {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ k : ℕ, 2 ≤ k ∧ ∃ f : Fin (2 ^ k) → Fin n,
    Function.Injective f ∧
    ∀ i : Fin (2 ^ k), G.Adj (f i) (f ⟨(i.val + 1) % 2 ^ k, Nat.mod_lt _ (by positivity)⟩)

/-- Every vertex of `G` has degree at least 3. -/
def MinDegAtLeastThree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : Prop :=
  ∀ v : Fin n, 3 ≤ (Finset.univ.filter (fun u => G.Adj v u)).card

/-- Erdős-Gyárfás Conjecture: every non-empty finite simple graph with min degree ≥ 3 has a 2^k-cycle. -/
def Statement : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < n → (∀ v : Fin n, 3 ≤ (Finset.univ.filter (fun u => G.Adj v u)).card) →
      HasPowerOfTwoCycle G

/-- Blueprint Lemma: Any non-empty finite graph with min degree ≥ 3 contains an inclusion-minimal
    non-empty subgraph whose induced minimum degree is at least 3. -/
def LemmaMinimalSubgraph : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    0 < n → (∀ v : Fin n, 3 ≤ (Finset.univ.filter (fun u => G.Adj v u)).card) →
    ∃ S : Finset (Fin n), S.Nonempty ∧
      (∀ v ∈ S, 3 ≤ (S.filter (fun u => G.Adj v u)).card) ∧
      ∀ T : Finset (Fin n), T ⊂ S → T.Nonempty →
        ∃ v ∈ T, (T.filter (fun u => G.Adj v u)).card < 3

end Targets.ErdosGyarfas.Spec
