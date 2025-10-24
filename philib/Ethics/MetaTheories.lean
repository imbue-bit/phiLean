/-
  # philib.Ethics.MetaTheories
  This file provides formal implementations of specific meta-ethical theories,
  namely Moral Realism and Emotivism.
-/
import Philib.Ethics.Meta

namespace Philib.Ethics.MetaTheories

open Philib.Ethics.Meta

/-! ### Moral Realism ### -/

-- Moral Realism holds that moral judgments express propositions about
-- objective moral facts.
structure MoralRealism where
  -- A realist theory posits the existence of a function that maps
  -- subjects to their objective moral properties.
  -- For example, `moral_facts Action.PullLever` might evaluate to `IsRight`.
  moral_facts (subject : Type u) : MoralPredicate

-- The semantics of Moral Realism: A moral judgment evaluates to a proposition (`Prop`).
-- This proposition is true if and only if the judgment corresponds to the
-- objective moral facts.
instance : MoralSemantics MoralRealism where
  eval (judgment : MoralJudgment) : Type :=
    -- The meaning of a judgment is a truth-apt proposition.
    Prop

-- A specific realist theory needs to be provided to evaluate a judgment.
def eval_realist (theory : MoralRealism) (judgment : MoralJudgment) : Prop :=
  theory.moral_facts judgment.subject = judgment.predicate

-- Example theorem under realism: Law of Excluded Middle applies to moral judgments.
-- Any given moral judgment is either true or false.
theorem realist_excluded_middle (theory : MoralRealism) (judgment : MoralJudgment) :
  eval_realist theory judgment ∨ ¬ (eval_realist theory judgment) :=
by apply Or.em

/-! ### Emotivism ### -/

-- Emotivism (a simple version) holds that moral judgments express emotional
-- attitudes, not propositions. They are not truth-apt.
-- We can model an attitude as a type.
inductive Attitude
| Approval   -- "Hooray for X!"
| Disapproval -- "Boo for X!"

-- The semantics of Emotivism: A moral judgment evaluates to an Attitude.
instance : MoralSemantics Attitude where
  eval (judgment : MoralJudgment) : Type :=
    -- The meaning of a judgment is an emotional expression, not a Prop.
    Attitude

-- The evaluation function for emotivism maps predicates to attitudes.
def eval_emotivist (judgment : MoralJudgment) : Attitude :=
  match judgment.predicate with
  | MoralPredicate.IsGood   => Attitude.Approval
  | MoralPredicate.IsRight  => Attitude.Approval
  | MoralPredicate.IsBad    => Attitude.Disapproval
  | MoralPredicate.IsWrong  => Attitude.Disapproval

-- Example theorem under emotivism: Moral judgments are not propositions.
-- We can demonstrate this by showing that trying to treat them as such
-- leads to a type error. The following function will not compile if uncommented,
-- because `eval_emotivist judgment` has type `Attitude`, not `Prop`.

-- def emotivist_judgment_is_prop (judgment : MoralJudgment) : Prop :=
--   eval_emotivist judgment -- TYPE ERROR: expected Prop, got Attitude

-- This type error is not just a programming mistake; it is the formal
-- representation of the core philosophical claim of emotivism. It formally
  -- captures the idea that asking "Is the statement 'Giving to charity is good'
  -- true?" is a category mistake, like asking "Is the color green loud?".

theorem emotivism_disagreement_is_not_contradiction
  (judgment_good : MoralJudgment) (h_good : judgment_good.predicate = MoralPredicate.IsGood)
  (judgment_bad : MoralJudgment) (h_bad : judgment_bad.predicate = MoralPredicate.IsBad)
  (h_subj : judgment_good.subject = judgment_bad.subject) :
  -- Two people expressing opposite moral views on the same subject are not
  -- in a state of logical contradiction. One says "Hooray!" the other "Boo!".
  -- Their expressions are different, but `Approval ≠ Disapproval` is not `False`.
  eval_emotivist judgment_good ≠ eval_emotivist judgment_bad :=
begin
  unfold eval_emotivist,
  rw [h_good, h_bad],
  simp, -- Proves that `Attitude.Approval ≠ Attitude.Disapproval`
end

end Philib.Ethics.MetaTheories
