import data.set

/-
CS2120 F21 HW5

The goals of this assignment are to give you
practice with proofs of propositions that use
existential quantificaton, and to develop your
understanding of formal and informal proofs in
set theory.
-/

/-
PART I: EXISTENTIAL QUANTIFICATION.
-/

/-
To start, suppose that α and β are arbitrary
types, and p and q are predicates on values
of these types: α and β, respectively.
-/

axioms 
  (α β : Type)    -- data types
  (p : α → Prop)  -- predicates
  (q : β → Prop)

/-
In this context complete the following tasks:

(1) Write a fluent English-language statement
of the proposition to be proved. 

(2) Provide a formal proof of the proposition. (Lean)

(3) Write an informal proof of the proposition. (English language proof)
-/

-- here's the proposition
example : 
  (∃ (f : α → β), ∀ (a : α), p a → q (f a)) →
  (∃ (a : α), p a) → 
  (∃ (b : β), q b) := 

/-
What does this propositon say? Explain it in
plain English. Here's a start: "If there's a 
function that maps/takes every α value that ... 
-- your completed English rendition here:

If there's a function f that takes every α value and returns a 
β value such that, when prop p is applied to a of type α, it implies q applied 
to the value of f when applied to a. This implies that there exists a value 
a of type α that, when p is applied to a, implies that a value b of type β 
exists where q is applied to b. 
-/

--because f applied to α results in type β, q (f a) can be resolved to q b  

-- Give your formal proof here
begin
  assume h a,
  cases h with x y, 
  cases a with w z, 
  apply exists.intro (x w), 
  exact (y w z), 
end
  

/- INFORMAL PROOF 
After assuming there exsits a function that turns α to β, where for all 
a α, applying p to a implies q applied to the function f applied to a (thus 
creating type β), and also assuming that there exists an α a where p is applied 
to a, we must prove there exists a b β where q is applied to b. First we start with
cases analysis of both of these assumptions. This leaves us with proof that α → β, proof 
that we can apply that proof of α → β to all values a where p a → q (proof α → β) a, proof 
of α, and proof that p can be applied to that proof of α. So, we apply exists.intro to the 
proof that α → β and to the proof of α to show there exists (b: β). Now, we can exact 
a value using the proofs that our function that states α → β, proof of α, and proof that
p can be applied to our proof of α to imply q is applied to the value β created by the 
function that transforms α to β, and our proof is complete. QED. 
-/