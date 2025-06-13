import PYCW.Definitions

-- 命题 1.1：证明关卡 {0--1--2--w} 可以过关
theorem statement1_1: Beatable (
  Level.mk [
    (Element.nat 0, Element.nat 1, Element.nat 2, Element.omega⟩
    ] (by simp)
    ) := by {
  apply Beatable.axiom1
  decide
}

-- 命题 1.2：证明关卡 {2--1--0--w--3} 可以过关
-- theorem statement1_2: Beatable (
--   Level.mk [
--     (Element.nat 2, Element.nat 1, Element.nat 0, Element.omega, Element.nat 3⟩
--     ]
--     ) := by {
--   have h: Beatable (Level.mk [(Element.nat 0, Element.omega⟩] (by simp)) := by {
--     apply Beatable.axiom1
--     decide
--   }
--   apply Beatable.rule1_1 (Element.nat 2, Element.nat 1, Element.nat 0, Element.omega, Element.nat 3⟩ at h
--   simp at h
--   apply Beatable.rule1_2 (1:Fin 2) (1:Fin 2) h


-- }

-- #eval (Element.nat 0, Element.nat 1, Element.nat 2, Element.omega⟩
#eval List.concat [1, 2, 3] 4
