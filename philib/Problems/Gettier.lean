/-
  A formalization of a Gettier-style counterexample to the JTB
  theory of knowledge.
-/
import Philib.Logic.Epistemic

namespace Philib.Problems.Gettier

-- Let's define the agents.
inductive Agent
| Smith
| Jones

open Agent

-- We need at least two possible worlds to model Smith's uncertainty.
-- w_real: The actual world.
-- w_believed: The world Smith thinks he is in.
inductive World
| w_real
| w_believed

open World

-- Define the propositions relevant to the story.
variable (gets_job : Agent → World → Prop)
variable (has_10_coins : Agent → World → Prop)

-- Describe the facts in each world.
-- In the real world: Smith gets the job, and both have 10 coins.
axiom real_world_facts :
  gets_job Smith w_real ∧ ¬ (gets_job Jones w_real) ∧
  has_10_coins Smith w_real ∧ has_10_coins Jones w_real

-- In the world Smith believes he is in: Jones gets the job, and both have 10 coins.
-- (He is wrong about the job, but right about the coins for Jones).
axiom believed_world_facts :
  ¬ (gets_job Smith w_believed) ∧ gets_job Jones w_believed ∧
  has_10_coins Smith w_believed ∧ has_10_coins Jones w_believed

-- Let's define the epistemic frame for Smith.
-- Smith, in the real world, considers `w_believed` to be possible.
-- He doesn't consider the real world possible because his evidence points away from it.
-- For simplicity, let's say `w_believed` is the *only* world he considers possible.
def smith_accessibility_relation : Agent → World → World → Prop
| Smith, w_real, w_believed => True
| _, _, _ => False -- All other relations are false

-- Define our epistemic frame instance.
def gettier_frame : Philib.Logic.Epistemic.EpistemicFrame Agent World where
  R := smith_accessibility_relation

-- Define some complex propositions based on the primitives.
def jones_gets_job_and_has_10_coins : Philib.Logic.Epistemic.KripkeProp World :=
  fun w => gets_job Jones w ∧ has_10_coins Jones w

-- This is the crucial Gettier proposition P:
-- "The person who will get the job has 10 coins in their pocket."
def P : Philib.Logic.Epistemic.KripkeProp World :=
  fun w => ∃ (a : Agent), gets_job a w ∧ has_10_coins a w

-- Let's define justification for this case. Smith's justification for P
-- stems from his justified belief in `jones_gets_job_and_has_10_coins`.
-- We state this as an axiom. Let's assume justification transfers
-- through logical deduction.
def smiths_justification_for_P : Philib.Logic.Epistemic.KripkeProp World :=
  -- Smith's justification holds because he has evidence for the Jones premise.
  -- We model this by saying the justification is true in the real world.
  fun w => w = w_real

-- Theorem: In the real world, Smith has a Justified True Belief in P.
theorem smith_has_JTB_for_P :
  (P w_real) ∧
  ((Smith Believes P) w_real) ∧
  (smiths_justification_for_P w_real) :=
begin
  -- Let's use the definitions from Epistemic logic
  let B := Philib.Logic.Epistemic.believes Smith (frame := gettier_frame)
  
  apply And.intro,
  { -- 1. Prove P is TRUE in the real world.
    unfold P,
    -- We need to show `∃ a, gets_job a w_real ∧ has_10_coins a w_real`.
    -- That agent is Smith.
    use Smith,
    exact real_world_facts.1,
  },
  apply And.intro,
  { -- 2. Prove Smith BELIEVES P in the real world.
    unfold Philib.Logic.Epistemic.believes,
    -- This means P must be true in all worlds accessible to Smith from w_real.
    -- The only such world is `w_believed`.
    intro w' h_accessible,
    -- We need to prove `P w'`. Since w' must be w_believed, we prove `P w_believed`.
    have h_w' : w' = w_believed := by cases h_accessible; rfl,
    rw [h_w'],
    unfold P,
    -- We need to show `∃ a, gets_job a w_believed ∧ has_10_coins a w_believed`.
    -- That agent is Jones in the believed world.
    use Jones,
    exact believed_world_facts.2.1,
  },
  { -- 3. Prove Smith has a JUSTIFICATION for P in the real world.
    unfold smiths_justification_for_P,
    simp, -- This is true by definition.
  }
end

-- The conclusion of the Gettier problem is that even though `smith_has_JTB_for_P`
-- is provably true, intuitively, Smith doesn't *know* P.
-- His justification is based on a false premise (`gets_job Jones`).
-- This shows that the JTB definition is insufficient.

end Philib.Problems.Gettier
