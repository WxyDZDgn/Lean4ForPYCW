-- This module serves as the root of the `FK` library.
-- Import modules here that should be built as part of the library.
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Factorial.Basic

example (n: Nat): ∑ i ∈ Finset.range n, (i + 1) = n * (n + 1) / 2 := by {
    induction n with
    | zero => simp
    | succ n ih => {
        simp [Finset.sum_range_succ]
        simp [← Nat.succ_eq_add_one]
        simp [Nat.add_assoc]
        rw [ih]
        ring_nf
        omega
    }
}
