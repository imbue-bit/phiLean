/-
  # philib.Problems.Trolley
  A formal analysis of a simplified Trolley Problem using the utilitarian
  framework developed in `philib`.
-/
import Philib.Ethics.Consequentialism

namespace Philib.Problems.Trolley

-- Define the actions available to the agent.
inductive Action
| DoNothing
| PullLever

-- Define the possible states (outcomes).
-- We can represent the state by the number of people who survive.
def State := ℕ -- Natural numbers represent the number of survivors.

-- The agent is anonymous for this problem.
def agent : Unit := ()

-- The initial state is irrelevant as consequences are fully defined by actions.
def initial_state : State := 0

-- The consequence function maps actions to outcomes (number of survivors).
def consequence : Philib.Ethics.Core.ConsequenceFunction Action State
| _, Action.DoNothing => 1 -- On the side track
| _, Action.PullLever => 5 -- On the main track

-- The utility function: utility is simply the number of survivors.
def utility : Philib.Ethics.Core.UtilityFunction State :=
  fun s => Int.ofNat s -- Convert ℕ to Int

-- Define the specific scenario for the Trolley Problem.
def trolley_scenario : Philib.Ethics.Core.Scenario Unit Action where
  agent := agent
  initial_state := initial_state
  available_actions := {Action.DoNothing, Action.PullLever}

-- Let's analyze the scenario using our utilitarian calculus.
open Philib.Ethics.Consequentialism

-- Theorem: According to utilitarianism, pulling the lever is obligatory.
theorem pull_lever_is_obligatory :
  is_obligatory utility consequence trolley_scenario Action.PullLever :=
begin
  unfold is_obligatory is_permissible utility_of_action,
  simp [consequence, utility, trolley_scenario], -- simp unfolds definitions and simplifies
  -- The goal becomes:
  -- (∀ (a' : Action), a' = Action.DoNothing ∨ a' = Action.PullLever →
  --   (if a' = Action.DoNothing then 1 else 5) ≤ 5) ∧
  -- (∀ (a' : Action), a' = Action.DoNothing ∨ a' = Action.PullLever →
  --   a' ≠ Action.PullLever → (if a' = Action.DoNothing then 1 else 5) < 5)

  apply And.intro,
  { -- Prove permissibility
    intro a' ha',
    cases a'; simp, -- Check both cases for a': DoNothing and PullLever
  },
  { -- Prove it's strictly better than all other options
    intro a' ha' h_neq,
    cases a', -- a' must be DoNothing
    { simp },
    { -- a' is PullLever, but h_neq says a' ≠ PullLever, a contradiction
      contradiction
    },
  },
end

-- Theorem: Doing nothing is not permissible.
theorem do_nothing_is_not_permissible :
  ¬ (is_permissible utility consequence trolley_scenario Action.DoNothing) :=
begin
  unfold is_permissible utility_of_action,
  simp [consequence, utility, trolley_scenario],
  -- Goal: ¬ (∀ a', ... → utility(a') ≤ 1)
  -- We need to find a counterexample: PullLever.
  push_neg,
  use Action.PullLever,
  simp, -- Simplifies to `5 > 1`, which is true.
end

end Philib.Problems.Trolley
