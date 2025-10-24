import Philib.Logic.Modal
namespace Philib.Logic.Epistemic
variable (A : Type u) -- Type of Agents
variable (W : Type v) -- Type of Worlds
structure EpistemicFrame where
  R : A → W → W → Prop
variable (frame : EpistemicFrame A W)
abbrev KripkeProp := Philib.Logic.KripkeProp W
def knows (a : A) (p : KripkeProp) : KripkeProp :=
  fun w => ∀ w' : W, frame.R a w w' → p w'
def believes (a : A) (p : KripkeProp) : KripkeProp :=
  fun w => ∀ w' : W, frame.R a w w' → p w'
notation:80 a " Knows " p => knows a p
notation:80 a " Believes " p => believes a p
open Philib.Logic (IsValid)
theorem axiom_T (h_refl : ∀ a w, frame.R a w w) (a : A) (p : KripkeProp) :
  IsValid ((a Knows p) → p) :=
begin
  intro w,      -- For any world w...
  intro h_knows,  -- Assume `a` knows `p` at `w`.
  unfold knows at h_knows,
  -- `h_knows` is now `∀ w', frame.R a w w' → p w'`.
  -- Since the relation is reflexive, `frame.R a w w` is true.
  let h_p_at_w := h_knows w (h_refl a w),
  exact h_p_at_w,
end
def Justifies (a : A) (p : KripkeProp) : KripkeProp :=.
  sorry
def knows_JTB (a : A) (p : KripkeProp) (j : KripkeProp) : KripkeProp :=
  fun w => p w ∧ (a Believes p) w ∧ j w
end Philib.Logic.Epistemic
