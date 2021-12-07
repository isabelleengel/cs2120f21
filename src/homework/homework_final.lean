import algebra.algebra.basic tactic.ring

/-
Read, understand (collaborating if necessary) the material
in chapter 17 of Jeremy Avigad's *Logic and Proof.* It's here:
https://leanprover.github.io/logic_and_proof/the_natural_numbers_and_induction.html
-/

/-
The following problems are listed in the Problems section of 
the chapter.-/

/-#1. Solve probem #1, first sentence only.
Write the principle of complete induction using the notation of symbolic logic.
-/

--complete induction principle 


--set up: 
def less_than (m n : ℕ) : Prop := m - n < 0 
def less_than_nat (n: ℕ) : set ℕ := {m : ℕ | less_than n}
def P : Prop (nat) sorry, --used sorry because does not matter what Prop P is for us, only that it exists 
--If P is true for all ℕ < (n: ℕ), then P is true for n 
∀ (n: ℕ), (∀ P (less_than_nat n) → true) → (P n → true) 

/-#2. Solve one of #2 and #3. Give
detailed but informal proofs. -/

--2. Show that for every 𝑛, 0^2+1^2+2^2+…𝑛^2=1/6𝑛(1+𝑛)(1+2𝑛).
--WRITE INFORMAL PROOF 
/-
To show that, for all natural numbers, the sum of the squares of all numbers
up to n^2 is 1/6(n)(1+n)(2*n), we need to use proof by induction. First,
we must define this function that will allow us to find the sum of the 
squares up to any n: ℕ. The base case, when n=0, will be 0. Then, we defne the function 
for the successor of any other natural number n'. The "square sum" of the successor of n' 
will be the square of the successor of n' added to the "square sum" function of n'. 
By using recursion, we will be able to have this function dwindle down until it reaches the
base case, and therefore give us the correct sum of squares for any ℕ. 

Now, we must prove that this is true using our definition and proof by induction. 
We begin by assuming the natural numbers and breaking our proof into the base 
case (0) and the inductive case. For the base case, we simply use reflexitivity to show 
that 0=0. For the inductive case, we must do a lot of rewriting to manipulate the 
equation for our proof. First, we expand the definition of the "square sum" that we 
have already defined and explained. Then we use the distributive property  so that a portion
of what we want to prove is 6 * "square sum" of a natural number n, which we can 
substitute with our inductive hypothesis. Then, we show that the successor of n is n + 1. 
Finally, we do some basic algebra, soon proving that these statements are in fact equal. 
QED. 
-/

--have the sum of squares here 
def square_sum : nat → nat 
| 0 := 0 
--how to get multiplying nat.succ to nat.succ on its own? 
| (nat.succ n') := (square_sum n') + ((nat.succ n') * (nat.succ n'))

--now it's go time! 
example: ∀ (n: ℕ), 6 * (square_sum n) = ((n) * (1+n) * (1 + (2 * n))) :=
begin
    assume n, 
    induction n with n' induced,
    --base case
    apply rfl, 
    --recursive/inductive case
    simp [square_sum], 
    rw left_distrib, 
    rw induced, 
    rw nat.succ_eq_add_one, 
    --basic algebra now :)
    ring_nf, 
    ring_nf, 
end 

/-
To test out of the final exam ...

#1: Give a formal proof for #2 or #3.
#2: Formal or detailed informal proofs 10-13 -/

--WRITE BETTER PROOFS OF THESE- LONG WAY 
/-10. Give an informal but detailed proof that for every natural number 𝑛, 1⋅𝑛=𝑛, 
using a proof by induction, the definition of multiplication, and the theorems proved in Section 17.4.-/
example : ∀ (n: ℕ), (1 * n) = n := 
begin 
    assume n, 
    induction n, 
    --basic algebra for base case
    apply rfl, 
    rw nat.succ_eq_add_one, 
    --basic algebra for inductive case
    ring, 
end 

/-11. Show that multiplication distributes over addition.
 In other words, prove that for natural numbers 𝑚, 𝑛, and 𝑘, 𝑚(𝑛+𝑘)=𝑚𝑛+𝑚𝑘. 
 You should use the definitions of addition and multiplication and facts proved in Section 17.4 (but nothing more).-/

example: ∀ (m n k: ℕ), (m * (n + k)) = ((m*n) + (m*k) ) := 
begin 
    assume m n k, 
    induction m with  m' ih, 
    --basic algebra for base case
    ring, 
    rw nat.succ_eq_add_one, 
    --basic algebra for inductive case
    rw left_distrib, 
end 

/-12. Prove the multiplication is associative, in the same way. 
You can use any of the facts proved in Section 17.4 and the previous exercise.-/


example: ∀ (m n k: ℕ), (m * (n*k)) =  ((m*n) *k) := 
begin 
    assume m n k,
    induction m with m' ih, 
    --basic algebra for base case
    ring, 
    rw nat.succ_eq_add_one, 
      --basic algebra for inductive case
    ring, 
end 

/-13. Prove that multiplication is commutative.-/
example: ∀ (m n: ℕ), (m * n) = (n* m) := 
begin 
    assume m n, 
    induction m with m' ih, 
    --basic algebra for base case
    ring, 
    rw nat.succ_eq_add_one, 
    --basic algebra for inductive case 
    ring, 
end 

/-#3 (Extra Credit): #5 or #9-/

def fib : nat → nat 
| 0 := 0
| 1 := 1 
| (nat.succ (nat.succ n)) := fib(nat.succ n) + fib(n) 

/- #5: Cassini's Identity (Fibonacci) -/

-- (-1)^n means -1 if n is odd, 1 if n is even (includes 0) 
def ev (n : ℕ) := n % 2 = 0
def od (n : ℕ) := n % 2 = 1 


example: ∀ (n: ℕ), (ev n → (fib(nat.succ n)*fib(nat.succ n)) - (fib(nat.succ (nat.succ n)) * fib(n)) = 1) ∧ 
 (od n → (fib(nat.succ (nat.succ n)) * fib(n)) - (fib(nat.succ n)*fib(nat.succ n)) = 1) := 
begin 
    assume n, 
    apply and.intro, 
    induction n with n' ev_ih, 
    unfold fib ev, 
    assume zero, 
    ring_nf, 
    rw nat.succ_eq_add_one, 
    unfold fib,  
    ring_nf,
    rw right_distrib, 
    rw right_distrib, 
    ring_nf, 

end 