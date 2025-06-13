import Mathlib.Data.Multiset.Basic

inductive Element where
| nat: Nat → Element
| omega: Element
deriving DecidableEq, Repr

open Element

structure Chain where
  nodes: List Element
  nonempty: nodes ≠ []
  deriving Repr

def Chain.ends (c: Chain): Element × Element :=
  let lst := c.nodes
  (lst.head (by {
    simp
    exact c.nonempty
  }), lst.getLast (by {
    simp
    exact c.nonempty
  }))

structure Level where
  chains: Multiset Chain


def Chain.validForAxiom1 (c: Chain): Bool :=
  let ends := c.ends
  ends = (nat 0, omega) || ends = (omega, nat 0)

inductive Beatable: Level → Prop where
| apply_axiom1 (c: Chain) (h: c.validForAxiom1 = true): Beatable (Level.mk [c])

syntax "(" term,+ "⟩" : term
macro_rules
  | `(( $es:term,* ⟩) => do
    let listExpr := ← `([$es,*])
    `(Chain.mk $listExpr (by decide))

instance : Repr Chain where
  reprPrec c _ :=
    let parts := c.nodes.map fun
      | nat n => toString n
      | omega => "ω"
    "(" ++ (" -- ".intercalate parts) ++ "⟩"
