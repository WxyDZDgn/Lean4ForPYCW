import PYCW.Definitions

theorem statement1: Beatable (
  Level.mk [
    (Element.nat 0, Element.nat 1, Element.nat 2, Element.omega⟩
    ]
    ) := by {
  apply Beatable.apply_axiom1
  decide
}
