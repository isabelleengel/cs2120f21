import .lecture_24

/-
BASIC SETUP
-/
namespace relations
section relation

/-
Define relation, r, as two-place predicate on 
a type, β, with notation, x ≺ y, for (r x y). 
-/
variables {α β γ : Type}  (r : β → β → Prop)
local infix `≺`:50 := r  

/-
ORDERING RELATIONS ON A TYPE, β 
-/

def strict_ordering :=  asymmetric r ∧ transitive r


def ordering :=         reflexive r ∧ transitive r ∧ anti_symmetric r


def partial_order :=    reflexive r ∧ transitive r ∧ anti_symmetric r ∧ ¬strongly_connected r --not total 


def total_order :=      reflexive r ∧ transitive r ∧ anti_symmetric r ∧ strongly_connected r

end relation
end relations

/-
Well order.
-/
variables (α β γ : Type )

def well_ordering := total_order r ∧ 
(∀ (s: set β), ∃ (b: β), (∀ (b': β), b' ∈ s → b ≺ b')) := 
begin 
end 

def inverse (r :α → β → Prop) : β → α → Prop := 
λ (b: β) (a: α), r a b