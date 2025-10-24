/-
  # philib.Ethics.Meta
  This file formalizes concepts from meta-ethics, exploring the nature of
  moral judgments themselves.
-/
import Philib.Ethics.Core

namespace Philib.Ethics.Meta

-- A MoralJudgment is a statement about the moral status of something,
-- e.g., "Action X is good" or "State Y is just".
-- We can represent a judgment as a structure containing the subject and
-- the moral predicate being applied.
inductive MoralPredicate
| IsGood
| IsBad
| IsRight
| IsWrong

structure MoralJudgment where
  subject : Type u
  predicate : MoralPredicate
  -- In a more advanced model, the subject would be a specific instance,
  -- e.g., an action or a state.

-- The central question of meta-ethics is: What is the semantic status of a
-- MoralJudgment? Does it express a proposition that can be true or false?

-- We define a typeclass `MoralSemantics` to represent a meta-ethical theory.
-- Each theory will provide its own interpretation of what a moral judgment means.
class MoralSemantics (T : Type) where
  -- `eval` function takes a moral judgment and returns its meaning
  -- according to the theory `T`. The return type is polymorphic to
  -- accommodate different theories.
  eval (judgment : MoralJudgment) : Type v

end Philib.Ethics.Meta
