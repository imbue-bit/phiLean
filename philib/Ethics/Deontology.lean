/-
  # philib.Ethics.Deontology
  This file formalizes concepts from deontological ethics, primarily inspired
  by Kant's Categorical Imperative.
-/
import Philib.Ethics.Core
import Philib.Logic.Modal -- We'll need modality for "possible worlds"

namespace Philib.Ethics.Deontology

open Philib.Ethics.Core

-- In Kantian ethics, the core idea is not the action itself, but the
-- principle or rule behind the action, which is called a "maxim".
-- A Maxim is a function that, for any agent in any state, proposes an action.
def Maxim (Agent Action State : Type) := Agent → State → Action

-- The first formulation of the Categorical Imperative involves checking if
-- a maxim can be "universalized".
-- `is_universalizable` is a high-level predicate that checks two conditions:
-- 1. Conception Contradiction: Is a world where everyone follows the maxim
--    logically conceivable? (e.g., a world where everyone makes false promises
--    to get loans is inconceivable, because the institution of promising
--    would collapse).
-- 2. Will Contradiction: Would a rational agent *will* for such a universalized
--    world to exist? (e.g., a world where no one ever helps others in need
--    is conceivable, but a rational agent wouldn't will it, as they themselves
--    might one day need help).

-- For our formalization, we will model this as abstract predicates.
-- A full formalization of these contradictions is a massive undertaking.
variable {Agent Action State : Type}

-- `is_conceivable` checks if a world governed by the universalized maxim is possible.
-- It takes a maxim and returns `Prop`.
def is_conceivable (maxim : Maxim Agent Action State) : Prop :=
  -- This is an abstract property. A full implementation would require a
  -- sophisticated world-simulation logic. We define it as an axiom in problems.
  sorry

-- `is_rationally_willed` checks the second condition.
def is_rationally_willed (maxim : Maxim Agent Action State) : Prop :=
  -- Also an abstract property.
  sorry

-- An action is permissible under deontology if it is performed according to a
-- maxim that is universalizable.
def is_permissible (maxim : Maxim Agent Action State) (action : Action)
  (agent : Agent) (state : State) : Prop :=
  maxim agent state = action ∧
  is_conceivable maxim ∧
  is_rationally_willed maxim

-- An action is obligatory if it follows from a universalizable maxim, and its
-- opposite follows from a non-universalizable maxim. This defines a "perfect duty".
def is_obligatory (maxim : Maxim Agent Action State) (neg_maxim : Maxim Agent Action State)
  (action : Action) (agent : Agent) (state : State) : Prop :=
  is_permissible maxim action agent state ∧
  (¬ is_conceivable neg_maxim ∨ ¬ is_rationally_willed neg_maxim)

end Philib.Ethics.Deontology
