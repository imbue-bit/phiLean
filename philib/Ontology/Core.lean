namespace Philib.Ontology
variable (I : Type u)
def Property := I → Prop
def instantiates (i : I) (p : Property I) : Prop :=
  p i
theorem indiscernibility_of_identicals (i j : I) (h : i = j) :
  ∀ (p : Property I), instantiates i p ↔ instantiates j p :=
begin
  rw [h],
  simp,
end
end Philib.Ontology
