namespace Philib.Logic

structure KripkeFrame (W : Type u) where
  R : W → W → Prop

variable {W : Type u} (frame : KripkeFrame W)

def KripkeProp := W → Prop

def box (p : KripkeProp) : KripkeProp :=
  fun w => ∀ w' : W, frame.R w w' → p w'

def diamond (p : KripkeProp) : KripkeProp :=
  fun w => ∃ w' : W, frame.R w w' ∧ p w'

prefix:80 "□" => box frame
prefix:80 "◇" => diamond frame

def IsValid (p : KripkeProp) : Prop :=
  ∀ w : W, p w

theorem diamond_as_neg_box_neg (p : KripkeProp) :
  IsValid ( (◇p) ↔ (¬(□(¬p))) ) :=
begin
  intro w, -- To prove validity, we prove it for an arbitrary world w.
  unfold diamond,
  unfold box,
  simp only, -- `simp` will unfold `¬` and simplify the expression
  apply Iff.intro,
  { -- Proof for ◇p → ¬□¬p
    intro h_diamond, -- Assume ∃ w', R w w' ∧ p w'
    intro h_box_neg_p, -- Assume ∀ w', R w w' → ¬p w'
    cases h_diamond with w' h,
    cases h with h_R h_p,
    let h_neg_p_at_w' := h_box_neg_p w' h_R,
    contradiction, -- We have p w' and ¬p w', a contradiction.
  },
  { -- Proof for ¬□¬p → ◇p
    intro h_not_box_neg_p,
    -- We need to show ∃ w', R w w' ∧ p w'. This is equivalent to
    -- ¬∀ w', ¬(R w w' ∧ p w').
    -- The assumption `h_not_box_neg_p` is ¬(∀ w', R w w' → ¬p w'),
    -- which simplifies to ∃ w', R w w' ∧ p w'.
    push_neg at h_not_box_neg_p,
    exact h_not_box_neg_p,
  }
end

end Philib.Logic
