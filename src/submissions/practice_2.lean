/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.  
-/

example : true := 
begin 
  exact true.intro, 
end 

example : false :=   -- trick question? why?

/- this is a trick question because false is defined 
as a proposition with no possible proof. 
Therefore, I would never be able to prove this 
because the proof is impossible. -/

--OR 

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _, 
  --forward
  assume porp, 
  apply or.elim porp, 
  assume p, 
  exact p, 
  --left disjunct is true 
  assume p, 
  exact p, 
  --right disjunct is true
  assume p, 
  apply or.intro_right, 
  exact p, 
end

--AND 
-- iff means we must prove forwards and backwards, both prove e/o
--write in lean by using iff.intro
example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P, 
  apply iff.intro _ _, 
  --proove forwards; use and.elim (either direction)
  apply and.elim_right, 
  --prove backwards; use and.intro to divide P ∧ P,
  --then prove P 
  assume p, 
  apply and.intro, 
  --exact p twice because need to do it for both sides of ∧ 
  exact p, 
  exact p, 
end

--P OR Q iff Q OR P; implication goes both ways 
example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
  assume P Q, 
  apply iff.intro _ _, 
  --go forwards
  assume porq,
  --break into individual props implying or statement 
  apply or.elim porq, 
  assume p, 
  --have proof of P, so use or.intro to ignore Q 
  apply or.intro_right, 
  exact p, 
  --now switch cases and assume Q 
  assume q, 
  apply or.intro_left, 
  exact q, 
  --must prove reverse direction because iff 
  assume qorp, 
  apply or.elim qorp, 
  assume q, 
  apply or.intro_right, 
  exact q, 
  --now do it having proof of P 
  assume p, 
  apply or.intro_left, 
  exact p, 
end

example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q, 
  apply iff.intro _ _, 
  --go forwards 
  assume pandq, 
  have p: P := and.elim_left pandq, 
  have q: Q := and.elim_right pandq, 
  apply and.intro q p, 
 --and the other way around! 
 assume qandp, 
 have q: Q := and.elim_left qandp, 
 have p: P := and.elim_right qandp, 
 apply and.intro p q, 
end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
/- we know P must be true because it's P AND Q or R 
additionally, either Q or R is true 
therefore, we can assume that P ∧ Q OR P ∧ R is true. Cases!-/ 
begin
  assume P Q R, 
  apply iff.intro, 
  --go written direction 
  assume pqr, 
  --proof of P (p) 
  have p: P := and.elim_left pqr, 
  have qorr: Q ∨ R := and.elim_right pqr, 
  --must check case where q is true and then case where r is true.
  cases qorr, 
  apply or.intro_left, 
  apply and.intro p qorr, 
  --case where Q is true checked! Now check when R is true: 
  apply or.intro_right, 
  apply and.intro p qorr, 
  --all cases checked, forward direction proven! 
  --now prove backwards: 
  assume pqpr, 
  cases pqpr,
  have p: P := and.elim_left pqpr, 
  have q: Q := and.elim_right pqpr, 
  --need to break up P ∧ (Q ∨ R) because have proof of P and this case Q 
  --therefore, use and.intro to break
  apply and.intro, 
  exact p, 
  --shows which case we are proving: first Q (left), then R (right)
  apply or.intro_left, 
  exact q, 
  --and restate for the other case when R is proven true! 
  have p: P := and.elim_left pqpr,
  have r: R := and.elim_right pqpr, 
  apply and.intro, 
  exact p, 
  apply or.intro_right, 
  exact r, 
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro, 
  assume pqr, 
  --going forward, break into cases 
  cases pqr, 
  --break the and statement, then prove the or statement on each side
  --through proof of P (case or.inl)
  apply and.intro, 
  apply or.intro_left , 
  exact pqr, 
  apply or.intro_left, 
  exact pqr, 
  --now, when given proof Q ∧ R, prove the same things 
  apply and.intro, 
  apply or.intro_right, 
  have q: Q := and.elim_left pqr, 
  exact q, 
  apply or.intro_right, 
  have r: R := and.elim_right pqr, 
  exact r, 
  --great! now go backwards because iff 
  assume pqpr,
 have pq: P ∨ Q := and.elim_left pqpr, 
 have pr: P ∨ R := and.elim_right pqpr, 
  --need to show that P must always be true and will either need Q or R not both 
  cases pq, 
  cases pr, 
  apply or.intro_left, 
  exact pq, 
  apply or.intro_left, 
  exact pq, 
  cases pr, 
  apply or.intro_left, 
  exact pr, 
  apply or.intro_right, 
  apply and.intro pq pr, 
end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q, 
  apply iff.intro, 
  apply and.elim_left, 
  --need to show that P imples P (obv) AND that P implies P or Q
  --which we proove by showing again that P implies P 
  assume p, 
  apply and.intro, 
  exact p, 
  apply or.intro_left, 
  exact p, 
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q, 
  apply iff.intro, 
  assume ppq, 
  cases ppq, 
  exact ppq, 
  apply and.elim_left ppq, 
  assume p, 
  apply or.intro_left, 
  exact p, 
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P, 
  apply iff.intro, 
  assume pt, 
  exact true.intro, 
  assume t, 
  apply or.intro_right, 
  exact true.intro, 
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P, 
  apply iff.intro, 
  assume pf, 
  cases pf, 
  exact pf, 
  --false can imply anything 
  cases pf, 
  assume p, 
  apply or.intro_left, 
  exact p, 
end 

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P, 
  apply iff.intro, 
  assume pt, 
  apply and.elim_left pt, 
  assume p, 
  apply and.intro, 
  exact p, 
  exact true.intro, 
end

--for false; check all cases because cases [false]
--returns 0 cases to proove (when used correctly)
example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro, 
  assume pf, 
  apply and.elim_right pf, 
  assume f, 
  cases f, 
end