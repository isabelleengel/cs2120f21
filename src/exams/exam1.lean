/- 
   *******************************
   PART 1 of 2: AXIOMS [50 points]
   *******************************
-/

/-
Explain the inference (introduction and
elimination) rules of predicate logic as
directed below. To give you guidance on
how to answer these questions we include
answers for some questions.
-/


-- -------------------------------------

/- #1: → implies [5 points]

INTRODUCTION

Explain the introduction rule for →. 

[We give you the answer here.]

In English: Given propositions, P and Q, 
a derivation (computation) a proof of Q 
from any proof of P, is a proof of P → Q.

In constructive logic, a derivation is a
given as a function definition. A proof
of P → Q literally is a function, that,
when given any proof of P as an argument
returns a proof of Q. If you define such
a function, you have proved P → Q.

ELIMINATION

Complete the definition of the elimination
rule for →.

(P Q : Prop) (p2q : P → Q) (p : P)
---------------------------------- elim 
          ( q:  Q )
-/

-- Give a formal proof of the following
example : ∀ (P Q : Prop) (p2q : P → Q) (p : P), Q :=
begin
  assume P Q h, 
  assume p, 
  apply h p, 
end

-- Extra credit [2 points]. Who invented this principle?
--The Ancient Greeks 


/- #2: true [5 points]

INTRODUCTION

Give the introduction rule for true using
inference rule notation.

[Here's our answer.]

---------- intro
(pf: true)

Give a brief English language explanation of
the introduction rule for true.

The introduction rule for true states that you can 
always exact a proof of true, because the definition of 
true is something that can always be proven. In Lean, we use 
this by using true.intro. 

ELIMINATION

Give an English language description of the
eliimination rule for true.

[Our answer]

A proof of true carries no information so
there's no use for an elimination rule.
-/

-- Give a formal proof of the following:

example : true := 
begin 
  exact true.intro, 
end 

-- -------------------------------------

/- #3: ∧ - and [10 points]

INTRODUCTION

Using inference rule notation, give the 
introduction rule for ∧.

[Our answer]

(P Q : Prop) (p : P) (q : Q)
---------------------------- intro
        (pq : P ∧ Q)

Given an English language description of
this inference rule. What does it really
say, in plain simple English. 

The introduction rule for and states that, when we 
have a proof p of proposition P and a proof q of proposition
Q, we can create a proof of P ∧ Q. Because we know that 
both of these propositions are true, and.intro allows us to 
merge them and create a proof of P ∧ Q. 

ELIMINATION

Give the elimination rules for ∧ in both
inference rule and English language forms.

(P Q: Prop) (pq: P ∧ Q)
----------------------------- elim 
(p: P) (left)/(q: Q) (right)


The and elimination rule states that, when we have a proof of 
P ∧ Q, we can derive a proof of both P (through left elimination)
and of Q (through right elimination). Because we know P ∧ Q is true,
both of these propositions must also be true, allowing us to 
deduce proofs of them individually. 
-/

/-
Formally state and prove the theorem that, 
for any propositions P and Q,  Q ∧ P → P. 
-/

example : ∀ (P Q), Q ∧ P → P := 
begin
  assume P Q h, 
  apply and.elim_right h, 
end 


-- -------------------------------------

/- #4: ∀ - for all [10 points]

INTRODUCTION

Explain in English the introduction rule for ∀. If 
T is any type (such as nat) and Q is any proposition 
(often in the form of a predicate on values of the
given type), how do you prove ∀ (t : T), Q? What is
the introduction rule for ∀?

/- The introduction rule for ∀ allows us to assume an arbitrary 
t (of type T) and then show that t has prop Q. 
-/ 

ELIMINATION

Here's an inference rule representation of the elim
rule for ∀. First, complete the inference rule by
filling in the bottom half, then Explain in English
what it says.

(T : Type) (Q : Prop), (pf : ∀ (t : T), Q) (t : T)
-------------------------------------------------- elim
                  t: Q 

-- This infrence rule representation of the elim rule for ∀ 
tells us that, if we have proof that all objects t of type T
have property Q, we can deduce that any individual object
t will have property Q. 

Given a proof, (pf : ∀ (t : T), Q), and a value, (t : T),
briefly explain in English how you *use* pf to derive a
proof of Q.

-- If we have a proof pf that all t of type T have property Q,
then we can /apply pf/ to show that each individual value t (again,
of the type T that must always have property Q) also has this property
Q. 
-/
/-
Consider the following assumptions, and then in the
context of these assumptions, given answers to the
challenge problems.
-/

axioms
  (Person : Type)
  (KnowsLogic BetterComputerScientist : Person → Prop)
  (LogicMakesYouBetterAtCS: 
    ∀ (p : Person), KnowsLogic p → BetterComputerScientist p)
  -- formalizee the following assumptions here
  -- (1) Lynn is a person
  (Lynn: Person)
  -- (2) Lynn knows logic
  (LKL: KnowsLogic Lynn)
  -- add answer here

/-
Now, formally state and prove the proposition that
Lynn is a better computer scientist
-/
example :  KnowsLogic Lynn → BetterComputerScientist Lynn := 
begin 
  assume lkl, 
  apply LogicMakesYouBetterAtCS, 
  apply lkl, 
end 



-- -------------------------------------

/- #5: ¬ - not [10 points] 

The ¬ connective in Lean is short for *not*. Give
the short formal definition of ¬ in Lean. Note that
surround the place where you give your answer with
a namespace. This is just to avoid conflicting with
Lean's definition of not.
-/

namespace hidden
def not (P : Prop) := P → false -- fill in the placeholder
end hidden

/-
Explain precisely in English the "proof strategy"
of "proof by negation." Explain how one uses this
strategy to prove a proposition, ¬P. 
-/

/-
 The objective of proof by negation, proving ¬P, 
is to show that a proof of P → false; that for P
to be true, the impossible would have to occur. 
So, we assume P, and show that it leads to a false 
proposition. 
-/

/-
Explain precisely in English the "proof strategy"
of "proof by contradiction." Explain how one uses
this strategy to prove a proposition, P (notice 
the lack of a ¬ in front of the P). 

Fill in the blanks the following partial answer:

To prove P, assume ¬ P and show that this leads to a contradiction.
From this derivation you can conclude P is true.
Then you apply the rule of negation elimination
to that result to arrive a a proof of P. We have
seen that the inference rule you apply in the 
last step is not constructively valid but that it
is logically valid, and that accepting the axiom
of the excluded middle suffices to establish negation
elimination (better called double negation elimination)
as a theorem.
-/



-- -------------------------------------

/- 
#6: ↔ - if and only if, equivalent to [10 points]
-/

/-
ELIMINATION 

As with ∧, ↔ has two elimination rules. You can 
see their statements here.
-/
#check @iff.elim_left
#check @iff.elim_right

/-
Formally state and prove the theorem that 
biimplication, ↔, is *commutative*. Note: 
put parentheses around each ↔ proposition,
as → has higher precedence than ↔. Recall
that iff has both elim_left and elim_right
rules, just like ∧.
-/

example : ∀ (P Q), (P ↔ Q) → (Q ↔ P) :=
begin
  assume P Q, 
  assume pq, 
  apply iff.intro, 
  have qp: Q → P := iff.elim_right pq, 
  apply qp, 
  have pq2: P → Q := iff.elim_left pq, 
  apply pq2, 
end


/- 
   ************************************************
   PART 2 of 3: PROPOSITIONS AND PROOFS [50 points]
   ************************************************
-/

/- #7 [20 points]

First, give a fluent English rendition of
the following proposition. Note that the
identifier we use, elantp, is short for
"everyone likes a nice, talented person."
Then give a formal proof. Hint: try the
"intros" tactic by itself where you'd
previously have used assume followed by
a list of identifiers. Think about what
each expression means. 
-/

/- 
This proposition states that we have a Type Person; each instance
of type Person can potentially have the quality of being
Nice and/or Talented (or neither). Additionally, a Person
can Like a Person. Then, there's the idea that everyone 
likes a Nice and Talented Person p; that is, if there is a Person
that is both Nice and Talented, every single object of type
Person (q) will Like this particular Person p. 

Then we have JohnLennon, an object of Type Person. JLNT states
that Person JohnLennon is both Nice and Talented. Therefore,
we must prove that all objects of Person (p) Likes JohnLennon.
-/

def ELJL : Prop := 
  ∀ (Person : Type) 
    (Nice : Person → Prop)
    (Talented : Person → Prop)
    (Likes : Person → Person → Prop)
    (elantp : ∀ (p : Person), 
      Nice p → Talented p → 
      ∀ (q : Person), Likes q p)

    (JohnLennon : Person)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 
    

example : ELJL :=
begin
  unfold ELJL, 
  intros, 
  have niceJL: Nice JohnLennon := and.elim_left JLNT, 
  have talentedJL: Talented JohnLennon := and.elim_right JLNT, 
  apply elantp JohnLennon niceJL talentedJL, 
end



/- #8 [10 points]

If every car is either heavy or light, and red or 
blue, and we want a prove by cases that every car 
is rad, then: 

-- how many cases will need to be considered? 4
-- list the cases (informaly)
    -- answer here
    Case where car is heavy and red 
    Case where car is light and red
    Case where car is heavy and blue 
    Case where car is light and blue 

-/

/-
  *********
  RELATIONS
  *********
-/


/- #9 [20 points]
Equality can be understood as a binary relation
on objects of a given type. There is a binary 
equality relation on natural numbers, rational 
numbers, on strings, on Booleans, and so forth.

We also saw that from the two axioms (inference
rules) for equality, we could prove that it is
not only reflexive, but also both symmetric and
transitive.

Complete the following definitions to express
the propositions that equality is respectively
symmetric and transitive. (Don't worry about
proving these propositions. We just want you
to write them formally, to show that you what
the terms means.)
-/

def eq_is_symmetric : Prop :=
  ∀ (T : Type) (x y : T), x = y → y = x

def eq_is_transitive : Prop := 
∀ (T: Type) (x y z: T), x = y → y = z → z = x


/-
  ************
  EXTRA CREDIT
  ************
-/

/- 
EXTRA CREDIT: State and prove the proposition
that (double) negation elimination is equivalent
to excluded middle. You get 1 point for writing
the correct proposition, 2 points for proving it
in one direction and five points for proving it
both directions. 
-/

def negelim_equiv_exmid : Prop := 
∀ (P: Prop), ¬¬ P ↔ (P ∨ ¬ P) 

example: negelim_equiv_exmid := 
begin 
  assume P, 
  apply iff.intro, 
  assume nnp, 
  have pornp := classical.em P, 
  assumption,
  assume pornp, 
  cases pornp, 
  assume nnp, 
  contradiction, 
  --how to show ¬ P → false? 
  assume np, 

end 



/- 
EXTRA CREDIT: Formally express and prove the
proposition that if there is someone everyone
loves, and loves is a symmetric relation, then 
thre is someone who loves everyone. [5 points]
-/

--SYMMETRIC RELATION: IF I LOVE YOU YOU LOVE ME 

axioms --(Person: Type)
 (Loves : Person → Person → Prop)

  (Lover : Person)

  (∀ (p: Person), Loves Lover p)
    (JLNT : Nice JohnLennon ∧ Talented JohnLennon),
    (∀ (p : Person), Likes p JohnLennon) 

example : ∃ Person l   := _
