/-
  # philib.Ethics.Consequentialism
  This file formalizes the core tenets of consequentialism, with a focus
  on classical utilitarianism.
-/
import Philib.Ethics.Core
import Mathlib.Data.Set.Finite

namespace Philib.Ethics.Consequentialism

open Philib.Ethics.Core

-- We work within the context of our core ethical framework.
variable {Agent Action State : Type}
variable (consequence : ConsequenceFunction Action State)
variable (utility : UtilityFunction State)

-- The utility of an action `a` taken in a state `s` is the utility of the
-- resulting state.
def utility_of_action (s : State) (a : Action) : Int :=
  utility (consequence s a)

-- An action `a` is permissible under utilitarianism if no other available
-- action has a strictly greater utility.
def is_permissible (scenario : Scenario Agent Action) (a : Action) : Prop :=
  a ∈ scenario.available_actions ∧
  ∀ a' ∈ scenario.available_actions,
    utility_of_action utility consequence scenario.initial_state a' ≤
    utility_of_action utility consequence scenario.initial_state a

-- An action `a` is obligatory (the right action) if it is permissible and
-- strictly better than any other *non-equivalent* action. For simplicity,
-- let's define it as the unique best action, if one exists.
-- A stronger definition: `a` is obligatory if it is the *only* permissible action.
def is_obligatory (scenario : Scenario Agent Action) (a : Action) : Prop :=
  is_permissible utility consequence scenario a ∧
  ∀ a' ∈ scenario.available_actions, a' ≠ a →
    utility_of_action utility consequence scenario.initial_state a' <
    utility_of_action utility consequence scenario.initial_state a

-- The core principle of utilitarianism: one *ought* to perform an obligatory action.
-- This can be formulated as a theorem: for any scenario, if an obligatory
-- action exists, one should choose it.
theorem utilitarian_imperative (scenario : Scenario Agent Action)
  (h_finite : Set.Finite scenario.available_actions)
  (h_nonempty : scenario.available_actions.Nonempty) :
  ∃ a, is_permissible utility consequence scenario a :=
begin
  -- This proof requires finding the maximum element in a finite, non-empty set,
  -- which is guaranteed to exist by the properties of integers.
  -- `Set.Finite.exists_maximal_wrt` from mathlib is perfect for this.
  let f := fun a => utility_of_action utility consequence scenario.initial_state a,
  have h_exists_max := Set.Finite.exists_maximal_wrt f scenario.available_actions h_finite h_nonempty,
  rcases h_exists_max with ⟨a, ha_mem, ha_is_max⟩,
  use a,
  exact ⟨ha_mem, ha_is_max⟩,
end

end Philib.Ethics.Consequentialism
