--import data.set, 
import tactic.ring, 

namespace relation
-- PRELIMINARY SETUP

/-
Preliminary set up. For the rest of this file,
we specify an arbitrary binary relation, r, on
an arbitrary type, β, as a two-place predicate, 
with infix notation x ≺ y for (r x y). One can
pronounce these expressions in English as "x is
related to y".
-/
variables {α β : Type}  (r : β → β → Prop)
local infix `≺` : 50 := r  


/-
The default Lean libraries are missing definitions
for the assympetric property of relations and for
the notion of a powerset. We define these terms for
use in the rest of this file.
-/
def asymmetric := ∀ ⦃x y⦄, x ≺ y → ¬ y ≺ x
def powerset (s : set β) := { s' | s' ⊆ s}


-- PROBLEMS

-- Prove both formally and in English.
/- 
#1: Give both a formal and an English-language proof. Then
answer the question, is the proposition true if you remove
the first condition, that β is inhabited? Briefly explain
your answer (in English).
-/
example : (∃ (b : β), true) → asymmetric r → ¬reflexive r :=
begin
  unfold asymmetric reflexive, 
  assume ex assym,
  --negation: assume that it is true and prove false
  assume refl,
  --need proof r x x for some x to plug into h and get proof of not r x x 
  --what if there is no x of type β (β is empty set)? Must and ∃ statement
  --Proposition is actually not true because it's false over the empty set. (without ∃)
  cases ex with b pf, 
  have rbb := refl b, 
  have contra := assym rbb, 
  contradiction, 
end

/-
English Proof: 
If we know that b of β exists, and we know it is asymmetric, we can do exists 
elimination (cases) on our proof that b exists. Now, we must prove through 
negation. So, let's create a proof that r b b is true through reflexitivty. 
If we apply asymmetery to this same case, we get a proof of ¬ r b b, since 
asymmetry does not allow these these two to be related. Thus, we have a contradiction;
QED. 

What if b was uninhabited? 
Well, you would be left unable to even start this proof. After all, our case
hinges on the idea that we perform exists elimination. If we didn't have this 
distinction clarified for us, then we would be left with the possibility 
of an empty set. You can prove that the empty set is both asymmetric and 
not reflexive, so this would not be true if it was not clarified that b exists. 
-/

/-
#2. Logic, like programming, is subtle. It's very easy for humans
to miss subtle corner cases. As an example, today I ran across
a problem in a textbook by Paul Traiger, a professor emeritus
of philosophy and cognitive science at Occidental College. He
asks students to prove that if a relation is both transitive and 
reflexive that it cannot be anti-symmetric. See the question at
the very bottom of the page here:
https://sites.oxy.edu/traiger/logic/exercises/chapter13/properties_of_relations_exercise.html

Is the conjecture actually logically valid? If not, what condition 
needs to be added to make it so? Try prove this/his version of the
conjecture, as articulated slightly differently below. If you get
stuck, then you need to figure out an additional condition that needs 
to be added as a premise to make the proposition true. In that case,
add the premise and then show that the updated conjecture is true.

The original conjecture was not logically valid, for one small and nuanced reason;
it must be declared that the set is inhabited, since the empty set is 
asymmetric. 
-/
example : (∃ (b: β), true) → transitive r → reflexive r → ¬ asymmetric r :=
begin
  unfold transitive reflexive asymmetric, 
  assume b trans rfl, 
  --proof by negation
  assume assym, 
  cases b,
  have rbb := rfl b_w, 
  have nrbb := assym rbb, 
  contradiction, 
end

/-
#3: Prove that the subset relation on the powerset of any
set, s, is antisymmetric. Formally state and prove, and
then give an informal proof of, this proposition.
-/
example : ∀ (s : set β) 
            (s1 s2 ∈ powerset s), 
            s1 ⊆ s2 → 
            s2 ⊆ s1 → 
            s1 = s2 :=
begin
  unfold powerset, 
  assume s s1 s2,
  assume s1ins s2ins, 
  assume s1subs2 s2subs1, 
  apply set.ext _ , 
  assume x, 
  apply iff.intro, 
  apply s1subs2, 
  --backwards 
  apply s2subs1, 
end
/- 
Informal proof #3: 
First, we must unfold the definition of powerset, telling us that
there is a set of all subsets of set s,  and assume our intros. 
Then, we unfold the definition of subset, showing that every member of 
the subset will be a memeber of the superset. Now, using these definitions,
it is easy to prove that, if s1 is a subset of s2 and s2 is a subset of s1,
it must follow that s1 = s2, since all memebers of each set must be included 
in the other. 
-/


/-
Given two natural numbers, n and m, we will say that m divides n
if there is a natural number, k, such that n = k*m. Here's a formal
definition of this relation.
-/
def divides (m n : ℕ) := ∃ k, n = k * m


/- 
#4: Formally and informally state and prove each of the following
propositions. Remember that the ring tactic is useful for producing
proofs of simple algebraic equalities involving + and *. You can use
the phrase, "by basic algebra" when translating the use of this tactic
into English. (Or if you wanted to be truly Hobbit-like you could say 
"by the ring axioms!")
-/

-- A: For any n, 1 divides n.
example : ∀ n, divides 1 n :=
begin
  unfold divides, 
  assume n, 
  apply exists.intro(n: ℕ), 
  ring, 
end
/-
For this proof, we simply use exists.intro to show that, 
when a number is divided by 1, it will always result in the quotient
being equal to the dividend, proving this proposition true. 

-/

-- B. For any n, n divides n
example : ∀ n, divides n n :=
begin
  unfold divides, 
  assume n, 
  apply exists.intro (1: ℕ),
  ring, 
end
/- 
Use exists.intro to show that, when a number is divided by itself, 
it will always result in the quotient
equalling 1, proving this proposition true. 
-/

-- #C. prove that divides is reflexive 
example : reflexive divides :=
begin
  unfold reflexive, 
  unfold divides, 
  assume n,
  apply exists.intro (1: ℕ), 
  ring,
end 
/-
After unfolding the definitions of reflextivity and division, and assuming
our intros, we simply show that every number can divide itself by proving 
that any number divided by itself will always equal 1. QED. 
-/


-- #D. prove that divides is transitive
example : transitive divides :=
begin
  unfold transitive, 
  unfold divides, 
  assume n n1 n2 a b, 
  --show n2 = k1 k2 n 
  cases a with a d, 
  cases b with b f, 
  apply exists.intro (b * a), 
  rw f, 
  rw d, 
  ring,
end 
/- 
First, we unfold the definitions of division and transitivity and assume our intros.
Then we perform case analysis and apply exists.intro using the assumed natural
number (constants) as our arguement. Then, with rewriting and algebraic analysis,
we prove that division is transitive. 
-/

/- 
E. Is divides symmetric? if yes, give a proof, otherwise 
give a counterexample and a brief explanation to show that 
it's not.
-/

/- No, divides is not symmetric. If divides were symmetric, that would mean that,
if a/b, then b/a, which is blantantly false in discrete mathematics. For example, 
let's take the numbers 12 (a) and 4 (b). 12/4 = 3, meaning that in this instance,
a/b. However, 4/12 does not resolve to a number, therefore, b/a is false and 
divides is not symmetric. 
-/ 


/- 
#F. Prove that divides is antisymmetric. 
-/
--anti-symmetry; a/b → b/a iff a = b
example : anti_symmetric divides := 
begin  
  unfold anti_symmetric, 
  unfold divides, 
  assume x y a b, 
  --use rewriting hint from class (can i do that for all these?)
  --if k = 1 we know this must work right? 
  cases a with c d, 
  cases b with e f, 
  have foo : x = y := sorry, 
  -- y = c * e * y  
  /-have foo : x = y := sorry, 
  apply foo, -/
end

/- 
We know divides is not truly symmetric because, as I explained in part e, if a 
and b are not equal then b can not divide a. However, if the numbers are equal,
then we know that b/a, as proven by the proposition in part (B) showing that every
n: ℕ divides itself. Thus, divides is anti symmetric, since it is only symmetric
when a = b. 
-/


/- #4
Prove the following propositions. Remember that
throughout this file, each definition implicitly
includes β as a type and r as an arbitrary binary 
relation on β. In addition to formal proofs, give
an English language proof of the last of the three
problems.
-/

-- A
example : asymmetric r → irreflexive r :=
begin
  unfold asymmetric, 
  unfold irreflexive, 
  assume x y r, 
  apply x r, 
  apply r,
end
/- 
Asymmetry means that, if a is related to b, b will never be 
related to a, even if they are equal. Therefore, it follows that this 
implies irreflexitivity; a number will never be related to itself, therefore
this relation is irreflexive. QED.  
-/

-- B
example : irreflexive r → transitive r → asymmetric r :=
begin
  unfold irreflexive,
  unfold transitive, 
  unfold asymmetric, 
  assume x y b c, 
  assume rbc rcb, 
  apply x b, 
  have foo := y rbc rcb, 
  apply foo, 
end

/-
First, we unfold all our definitions and assume our intros. Then, we can 
create a proposition (with the intention of contradiction) of reflexitivity
using our proof of irreflexitivity and the intentions of using false elimination.
Now, how to prove this new goal of ours? Well, we can create a proof of reflexitivity
by applying our proof of transitivity to assumptions that only contain two differnet
varuiables. Now, we can apply this newfound proof of reflexitivity to prove our 
proposition. QED.  
-/

-- C: is this valid or nah? 
example : transitive r → ¬ symmetric r → ¬ irreflexive r :=
begin
  unfold transitive symmetric irreflexive, 
  assume x y z, 
  sorry, 
end
/-
Part C is not true. Here's why: 
Transitivity means if a rel b and b rel c, a rel c. 
For this relationship to not be symmetric, if a is related to b, b could 
not be related to a. 
If this is not irreflexive, then a will be related to itself. 
We know that this situation is false when we look at the situation where 
all three of these variables are the same. To provide a counterexample, let's 
say that we are using variable d. If this were not symmetric, and the relation was 
between d and d, then this would contradict the statement that this was not irreflexive,
which would state that d must be related to d. 
Therefore, this can not be proved. QED. 
-/


end relation

/- HW 7 HELP
x = k1 n 
y = k2 x

rewrite x as k1 y and/or y = k2 x
x = k1 k2 y
thus k1 and k2 both must be 1 and x = y

have foo : k1 = 1 := sorry --adds k1 to context

last example; contemplate possibility that this isn't true
sometimes need to add assumptions (exists, inhabited domain, etc.)

extra credit for counter examples

-/