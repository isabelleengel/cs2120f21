import algebra.algebra.basic tactic.ring

namespace hidden 

/-
SUCCESSION WORKS WITH TWO SMALLER MACHINES: 
ANSWER FOR BASE CASE AND FOR  n' + 1 

Note: I'm just a bit confused why we have to keep using nat.succ 
for stuff like add, mult, etc when we are using the functions
that are built into Lean and they would work otherwise
-/

inductive nat : Type 
| zero : nat
| succ (n' : nat) : nat 

def z := nat.zero 
def o := nat.succ z 
def t := nat.succ o --etc etc.... 

--four 
def f : nat := 
begin 
  exact nat.succ (nat.succ t)
end 

--define increment functions 
def inc' : nat → nat := 
begin 
  assume n, 
  exact nat.succ n, 
end 

def inc : nat → nat 
| n := nat.succ n 

--all functions in lean must be total 
def dec : nat → nat 
| (nat.zero) := nat.zero 
| (nat.succ n') := n' 

def add : nat → nat → nat 
| (nat.zero) (m) := m
| (nat.succ n') (m) := 
--answer for n' 
nat.succ (add n' m) 

def mul : nat → nat → nat 
| (nat.zero) (m) := nat.zero 
| (nat.succ n') (m) := add (m) (mul n' m)
--know m and n', through recursion we assume we can get to nat.succ n' 

#reduce mul f f 

--HW/EXAM Q: DEF EXPONENTIATION (ITERATED MULTIPLICATION)
def expo : nat → nat → nat 
| (nat.zero) (x) := o 
| (nat.succ n') (x) := mul (x) (mul n' x) 

def sum_to : nat → nat 
| (nat.zero) := nat.zero 
| (nat.succ n') := add (sum_to n') (nat.succ n') 

#reduce sum_to o 
#check z --shows type 
#reduce z --to evaluate; replace z w def 
#check t 
#reduce t --internal notation  

def P : nat → Prop 
| n := sum_to n = n * (n*1) 

end hidden 