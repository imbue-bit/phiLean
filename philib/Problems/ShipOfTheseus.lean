/-
  # philib.Problems.ShipOfTheseus
  A formalization of the Ship of Theseus paradox.

  The paradox deals with identity over time. If an object has all of its
  components replaced, does it remain the same object?

  Our model:
  - Time is a discrete sequence (Nat).
  - A Ship is an Individual.
  - A ship is defined by its set of planks (`Set Plank`).
  - We define two ships:
    1. ShipA: The ship that is continuously repaired (one plank at a time).
    2. ShipB: The ship reassembled from the old planks.
  - The question: Is ShipA at the end the same as the original Ship of Theseus?
    Is ShipB?
-/
import Philib.Ontology.Core
import Mathlib.Data.Set.Basic -- We need sets from mathlib

namespace Philib.Problems.ShipOfTheseus

-- Let's define the components.
variable (Plank : Type) -- The type of planks

-- A ship's state at a given time is its set of planks.
def ShipState := Set Plank

-- An `Individual` representing a ship. Let's call it a `Vessel`.
variable (Vessel : Type) [Inhabited Vessel] -- A type for ships, non-empty.

-- A history tracks the physical composition of a vessel over time.
variable (history : Vessel → Nat → ShipState)

-- Let's define the original Ship of Theseus at time 0.
variable (theseus_original : Vessel)
variable (original_planks : Set Plank)
axiom h_initial_state : history theseus_original 0 = original_planks

-- The scenario: At each step `t`, one original plank is replaced.
-- `plank_out t` is the original plank removed at time t.
-- `plank_in t` is the new plank added at time t.
variable (plank_out plank_in : Nat → Plank)
variable (num_planks : Nat) -- Total number of planks

-- Assumption: The replacement process replaces every plank exactly once.
axiom h_planks_out_are_original : ∀ t < num_planks, plank_out t ∈ original_planks
axiom h_planks_in_are_new : ∀ t < num_planks, plank_in t ∉ original_planks

-- We define ShipA, the repaired ship. It's the vessel that undergoes changes.
-- We can identify it with `theseus_original` undergoing evolution.
def ship_A := theseus_original

-- The state of ShipA at time `t+1` is the state at `t`, minus one old plank,
-- plus one new plank.
axiom h_ship_A_evolution :
  ∀ t < num_planks,
    history ship_A (t + 1) = (history ship_A t) \ {plank_out t} ∪ {plank_in t}

-- At the end of the process (time `num_planks`), ShipA has no original planks.
def final_planks_A : Set Plank :=
  history ship_A num_planks

-- Now, let's define ShipB. It's a new vessel, assembled from old planks.
variable (ship_B : Vessel)
axiom h_ship_B_is_new : ship_B ≠ ship_A

-- The state of ShipB at the end is exactly the set of original planks.
axiom h_ship_B_final_state : history ship_B num_planks = original_planks

/-
  The Philosophical Question Formalized:
  Which vessel at time `num_planks` is the true "Ship of Theseus"?

  This leads to two competing identity claims. Let's state them as propositions
  that we might try to prove under different theories of identity.
-/

-- Claim 1: Identity is based on spatio-temporal continuity.
-- ShipA is the Ship of Theseus because it has a continuous history.
def IdentityClaim1 := ship_A = theseus_original

-- Claim 2: Identity is based on material composition.
-- ShipB is the Ship of Theseus because it's made of the original parts.
def IdentityClaim2 := ship_B = theseus_original

-- The paradox arises because both claims seem plausible, but they cannot
-- both be true if ShipA and ShipB are distinct objects.
theorem paradox (h_num_planks_positive : num_planks > 0) :
  (IdentityClaim1 ∧ IdentityClaim2) → False :=
begin
  intro h_claims,
  cases h_claims with claim1 claim2,
  -- From claim1, we have `ship_A = theseus_original`.
  -- From claim2, we have `ship_B = theseus_original`.
  -- By transitivity of equality, `ship_A = ship_B`.
  have h_A_eq_B : ship_A = ship_B := by rw [claim1, claim2],
  -- But we defined ShipB as being distinct from ShipA.
  contradiction,
end

-- phiLean's role here is not to *solve* the paradox, but to formalize it.
-- It makes the hidden assumptions (like what defines identity) explicit.
-- A philosopher could now introduce a formal theory of identity, e.g.,
-- `axiom theory_of_continuity : ∀ v, is_continuous(history v) → v = theseus_original`
-- and then use it to prove `IdentityClaim1`.

end Philib.Problems.ShipOfTheseus
