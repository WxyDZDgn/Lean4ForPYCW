import Mathlib.Data.Multiset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic.Linarith

inductive Element where
| nat: Nat → Element
| omega: Element
deriving DecidableEq, Repr

open Element

structure Chain where
  nodes: List Element
  length_geq_two: nodes.length ≥ 2
  deriving DecidableEq, Repr

def Chain.ends (c: Chain): Element × Element :=
  let lst := c.nodes
  (lst.head (by {
    have h_len : c.nodes.length ≥ 2 := c.length_geq_two
    apply List.length_pos_iff.mp
    linarith
  }), lst.getLast (by {
    have h_len : c.nodes.length ≥ 2 := c.length_geq_two
    apply List.length_pos_iff.mp
    linarith
  }))

structure Level where
  chains: List Chain
  length_geq_one: chains.length ≥ 1
  deriving Repr

def Level.neZero (level : Level) : NeZero level.chains.length :=
  ⟨Nat.one_le_iff_ne_zero.mp level.length_geq_one⟩

def Chain.validForAxiom1 (c: Chain): Bool :=
  let ends := c.ends
  ends = (nat 0, omega) || ends = (omega, nat 0)

def Chain.splitAt (c: Chain) (q: Nat): Option (Chain × Chain) :=
  let n := c.nodes.length
  if h: 1 ≤ q ∧ q ≤ n - 2 ∧ 3 ≤ n then
    let leftNodes := c.nodes.take (q + 1)
    let rightNodes := c.nodes.drop q
    some (⟨leftNodes, by {
      simp [leftNodes]
      have h_len : c.nodes.length ≥ 2 := c.length_geq_two
      change 1 ≤ q ∧ 2 ≤ n
      rcases h with ⟨h1, h2, h3⟩
      have h2_l : 2 ≤ n := by linarith
      exact ⟨h1, h2_l⟩
    }⟩, ⟨rightNodes, by {
      simp [rightNodes]
      have h_len : c.nodes.length ≥ 2 := c.length_geq_two
      rcases h with ⟨h1, h2, h3⟩
      change 2 ≤ n - q
      have h2_1 : 2 ≤ n := by linarith
      have h2_2: q + 2 ≤ (n - 2) + 2 := Nat.add_le_add_right h2 2
      rw [Nat.sub_add_cancel h2_1] at h2_2
      apply Nat.le_sub_of_add_le
      rw [Nat.add_comm]
      exact h2_2
    }⟩)
  else
    none

def Chain.is_valid_sublist (sublist: List Element) (lst: List Element): Bool :=
  let subChainLength := sublist.length
  let chainLength := lst.length
  if h_grater_than_two: subChainLength < 2 ∨ chainLength < 2 then false
  else if subChainLength > chainLength then false
  else
    let res := sublist = lst.take subChainLength
    if not res then
      Chain.is_valid_sublist sublist lst.tail
    else res
termination_by lst.length
decreasing_by
  simp at h_grater_than_two
  rcases h_grater_than_two.right with h_grater_than_two_2
  have h_ne: lst ≠ [] := by {
    intro h_nil
    change 2 ≤ lst.length at h_grater_than_two_2
    rw [h_nil] at h_grater_than_two_2
    contradiction
  }
  cases lst with
  | nil => contradiction
  | cons a as => {
    simp only [List.tail, List.length]
    apply Nat.lt_succ_self
  }

def Chain.removeChain (level: Level) (subchain_idx: Fin level.chains.length) (chain_idx: Fin level.chains.length): Level :=
  if h_stay_same: (subchain_idx = chain_idx ∨ ¬Chain.is_valid_sublist (level.chains.get subchain_idx).nodes (level.chains.get chain_idx).nodes) then level
  else
    let subchain := level.chains.get subchain_idx
    -- let chain := level.chains.get chain_idx
    let chains := level.chains.erase subchain
    Level.mk chains (by {
      simp at h_stay_same
      rcases h_stay_same with ⟨h_idx_neq, h_valid_sub⟩
      sorry
    })

inductive Beatable: Level → Prop where
| axiom1 (c: Chain) (h: c.validForAxiom1 = true): Beatable (Level.mk [c] (by simp))
| rule1_1 {level: Level} (newChain: Chain) (h: Beatable level): Beatable (Level.mk (level.chains ++ [newChain]) (by simp))
| rule1_2 {level: Level} (subchain_idx chain_idx: Fin level.chains.length) (h_level: Beatable level): Beatable (Chain.removeChain level subchain_idx chain_idx)

syntax "(" term,+ "⟩" : term
macro_rules
  | `(( $es:term,* ⟩) => do
    let listExpr := ← `([$es,*])
    `(Chain.mk $listExpr (by decide))

instance : ToString Chain where
  toString c :=
    let parts := c.nodes.map fun
      | nat n => toString n
      | omega => "ω"
    ("--".intercalate parts)
