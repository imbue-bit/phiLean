/-
  # philib.Ethics.Core
  This file defines the foundational concepts for formalizing ethical theories.

  - `Agent`: An entity that can perform actions.
  - `Action`: Something an agent can do.
  - `State`: A representation of the state of the world.
  - `ConsequenceFunction`: A function that maps an action in a given state
    to a resulting state.
  - `UtilityFunction`: A function that assigns a numerical value (utility)
    to a state.
-/

namespace Philib.Ethics.Core

-- An Agent is the actor in our ethical framework.
-- We can reuse the Agent type from Epistemic logic or define a new one.
-- Let's define it here for modularity.
variable (Agent : Type u)

-- An Action is specific to an agent.
variable (Action : Type v)

-- A State represents a snapshot of the world. All outcomes are states.
variable (State : Type w)

-- A ConsequenceFunction determines the outcome of an action in a state.
-- For simplicity, we assume deterministic consequences.
-- `(consequence s a)` is the state that results from performing action `a` in state `s`.
def ConsequenceFunction := State → Action → State

-- A UtilityFunction assigns a value to each state. Higher values are better.
-- We use Int for simplicity, allowing for negative utility.
def UtilityFunction := State → Int

-- A scenario is defined by a set of available actions for an agent
-- in a particular state.
structure Scenario where
  agent : Agent
  initial_state : State
  available_actions : Set Action

end Philib.Ethics.Core
