import data.set
open set
/-
NOTE: The final exam is comprehensive, but this practice
exam is not. In addition to working through this practice
exam, you should revisit the exam1 and exam2 practice
exams.
-/

/- SETS -/
namespace sets

/-
1.

Prove that 1 is in the set {1, 2, 3, 4, 5}.
-/

example: 1 ∈ ({1, 2, 3, 4, 5}: set ℕ) :=
begin
  right, right, right, right, left,
  exact rfl,
end

/-
2.

Prove that 1 is not in the set {2, 3, 4}.
-/

example: 1 ∉ ({2, 3, 4}: set ℕ) :=
begin
  assume pf_in,
  cases pf_in with one_is_4 pf_in,
    -- case with hypothesis 1 = 4
    have one_isnt_4: 1 ≠ 4 := dec_trivial,
    exact one_isnt_4 one_is_4,
    -- case with hypothesis 1 ∈ {2, 3}
    cases pf_in with one_is_3 pf_in,
      -- case with hypothesis 1 = 3
      have one_isnt_3: 1 ≠ 3 := dec_trivial,
      exact one_isnt_3 one_is_3,
      -- case with hypothesis 1 ∈ {2}
      cases pf_in with one_is_2 pf_in,
        -- case with hypothesis 1 = 2
        have one_isnt_2: 1 ≠ 2 := dec_trivial,
        exact one_isnt_2 one_is_2,
        -- case with hypothesis 1 ∈ ∅
        assumption
end

/-
3.

Prove that there does not exist any natural number that is
a member of the empty set of natural numbers.
-/

example: ¬(∃ n:ℕ, n ∈ (∅: set ℕ)) :=
begin
  assume pf_exists_n,
  apply exists.elim pf_exists_n,
  assume w pf_w_in_empty,
  assumption
end

/-
4.

Prove that the intersection of the sets of natural numbers
{1, 2} and {3, 4} is empty by showing that for all natural
numbers, they are not in the intersection of {1, 2} and
{3, 4}.
-/

#reduce 2 ∈ ({3, 4}: set ℕ)

example: ∀n: ℕ, n ∉ ({1, 2}: set ℕ) ∩ ({3, 4}: set ℕ) :=
begin
  intros n,
  assume pf_n_in_intersection,
  cases pf_n_in_intersection with pf_n_in_12 pf_n_in_34,
    cases pf_n_in_12 with pf_n_is_2 pf_n_in_1,
      rw pf_n_is_2 at pf_n_in_34,
      cases pf_n_in_34 with pf_2_is_4 pf_2_in_3,
        have pf_2_isnt_4: 2 ≠ 4 := dec_trivial,
        exact pf_2_isnt_4 pf_2_is_4,

        cases pf_2_in_3 with pf_2_is_3 pf_2_in_empty,
          have pf_2_isnt_3: 2 ≠ 3 := dec_trivial,
          exact pf_2_isnt_3 pf_2_is_3,

          assumption,

      cases pf_n_in_1 with pf_n_is_1 pf_n_in_empty,
        rw pf_n_is_1 at pf_n_in_34,
        cases pf_n_in_34 with pf_1_is_4 pf_1_in_3,
          have pf_1_isnt_4: 1 ≠ 4 := dec_trivial,
          exact pf_1_isnt_4 pf_1_is_4,

          cases pf_1_in_3 with pf_1_is_3 pf_1_in_empty,
            have pf_1_isnt_3: 1 ≠ 3 := dec_trivial,
            exact pf_1_isnt_3 pf_1_is_3,

            assumption,
        
        assumption,
end

/-
5.

Prove that 1 is in the difference between {1, 2, 3} and {3, 4}
-/

example: 1 ∈ ({1, 2, 3}: set ℕ) \ ({3, 4}: set ℕ) :=
begin
  split,
    right, right, left,
    exact rfl,

    assume pf_1_in_34,
    cases pf_1_in_34 with pf_1_is_4 pf_1_in_3,
      have pf_1_isnt_4: 1 ≠ 4 := dec_trivial,
      exact pf_1_isnt_4 pf_1_is_4,

      cases pf_1_in_3 with pf_1_is_3 pf_1_in_empty,
        have pf_1_isnt_3: 1 ≠ 3 := dec_trivial,
        exact pf_1_isnt_3 pf_1_is_3,

        assumption,
end

/-
6.

Prove that {2, 3} is a subset of the union of {1, 2} and {3, 4}
Note: use ⊆ not ⊂
-/

example: ({2, 3}: set ℕ) ⊆ ({1, 2}: set ℕ) ∪ ({3, 4}: set ℕ) :=
begin
  intros a,
  assume pf_a_in_23,
  cases pf_a_in_23 with pf_a_is_3 pf_a_in_2,
    apply or.inr,
    right, left, assumption,

    cases pf_a_in_2 with pf_a_is_2 pf_false,
      apply or.inl,
      left, assumption,

      exact false.elim pf_false,
end

/-
7.

Prove that {2, 3} is an element of the powerset of {1, 2, 3, 4}
-/

#reduce {2, 3} ∈ 𝒫({1, 2, 3, 4}: set ℕ)
-- ∀ ⦃a : ℕ⦄, a = 3 ∨ a = 2 ∨ false → a = 4 ∨ a = 3 ∨ a = 2 ∨ a = 1 ∨ false

example: {2, 3} ∈ 𝒫({1, 2, 3, 4}: set ℕ) :=
begin
  change ∀(a : ℕ), a = 3 ∨ a = 2 ∨ false → a = 4 ∨ a = 3 ∨ a = 2 ∨ a = 1 ∨ false,
  intros a,
  assume pf_a_in_23,
  cases pf_a_in_23 with pf_a_is_3 pf_a_in_2,
    right, left, assumption,

    cases pf_a_in_2 with pf_a_is_2 pf_false,
      right, right, left, assumption,
      exact false.elim pf_false,
end

end sets

/- RELATIONS -/
namespace relations

/-
1.

Prove that disjunction has the symmetric property
-/

example: symmetric or :=
begin
  unfold symmetric,
  intros x y,
  assume pf_x_or_y,
  cases pf_x_or_y with pf_x pf_y,
    exact or.inr pf_x,
    exact or.inl pf_y
end

/-
2.

Prove that conjunction is a subrelation of disjunction
-/

example: subrelation and or :=
begin
  unfold subrelation,
  intros x y,
  assume pf_x_and_y,
  have pf_x := and.elim_left pf_x_and_y,
  exact or.inl pf_x,
end

end relations

/-
===================================================
Inductive types, functions, properties, and proofs.
====================================================
-/

/-
1.

Create sub_mynat that subtracts two mynats n and m with
the condition that if m > n that it returns 0, otherwise
it returns n - m
Hint: 3 - 2 = 2 - 1 = 1 - 0
-/

namespace mynat

inductive mynat : Type 
| zero : mynat
| succ : mynat → mynat

def sub_mynat: mynat → mynat → mynat
| n mynat.zero := n
| mynat.zero m := mynat.zero
| (mynat.succ n') (mynat.succ m') := 
    sub_mynat n' m'

/-
2.

Prove that ∀ n, sub_mynat n n = 0.
-/

example: ∀(n: mynat), sub_mynat n n = mynat.zero :=
begin
  intros n,
  induction n with n' h,
    -- base case
    simp [sub_mynat],

    simp [sub_mynat],
    assumption
end

/-
3.

We give you a copy of the add_mynat function
below. Show that our definition of add_mynat 
is associative. 
-/

def add_mynat: mynat → mynat → mynat
| mynat.zero m := m
| (mynat.succ n') m :=
    mynat.succ (add_mynat n' m)

example: ∀(a b c: mynat),
  add_mynat a (add_mynat b c) = add_mynat (add_mynat a b) c :=
begin
  intros a b c,
  induction a with a' h,
    -- base case
    simp [add_mynat],

    have h': add_mynat (mynat.succ a') (add_mynat b c) =
      mynat.succ (add_mynat a' (add_mynat b c)) :=
        begin
          simp [add_mynat],
        end,

    have h'': add_mynat (mynat.succ a') b =
      mynat.succ (add_mynat a' b) :=
        begin
          simp [add_mynat],
        end,
    
    rw h',
    rw h'',

    have h''': add_mynat (mynat.succ (add_mynat a' b)) c =
      mynat.succ (add_mynat (add_mynat a' b) c):=
        begin
          simp [add_mynat],
        end,
    
    rw h''',
    rw h,
end

end mynat



/-
Simple inductive types.
-----------------------
-/

/-
3.

Define a new type called day having
these seven constant constructors: 
sunday, monday, tuesday, wednesday,
thursday, friday, saturday. We will
interpret these constructors as 
representing the actual days of the
week. Write your code below here now.
-/

inductive day : Type
| sunday
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday

-- We suggest you open the day namespace

open day


/-
4.

Define a function, nextday : day → day,
that, when given a value, d : day, returns 
the day value that represents the next day
of the week. Hint: either write a function
using a match d with ... end, or, if you
can use a tactic script (to write code!).
Use cases d and for each possible case of
d, specify the exact day to be returned in
that case. For extra credit do it both ways
and write a single sentence to describe how
these two representations correspond.
-/

def nextday (d : day) : day :=
begin
  cases d,
    exact monday,
    exact tuesday,
    exact wednesday,
    exact thursday,
    exact friday,
    exact saturday,
    exact sunday,
end


def nextday' (d : day) :=
match d with
| sunday := monday
| monday := tuesday
| tuesday := wednesday
| wednesday := thursday
| thursday := friday
| friday := saturday
| saturday := sunday
end

/-
5.

Formalize and prove the proposition that 
for any day, d, if you apply nextday to d
then nextday to the result, seven times, 
the result is that very same d. 
-/

example : ∀ d : day, 
nextday ( nextday ( nextday (nextday (nextday (nextday (nextday d)))))) = d :=
begin
  assume d,
  cases d,
  repeat { apply rfl }, -- don't write it 7 times!
end



/-
Recursive (nested) inductive types.
-----------------------------------
-/

/-
6.

Give an inductive type definition for nat_list,
so that values of this type represent lists of
values of type ℕ.

While there's an infinity of such lists, we can
cleverly define the set inductively with just two
rules.

First, there is an empty list of natural numbers. We will represent it with the constant constructor, 
nil_nat. Make it one of the nat_list constructors.

Second, if we are given a nat_list value, l, and 
a ℕ value, e : ℕ, we can always construct a list
that is one longer than by prepending e to l. To
do this, define a constructor called nat_cons. It take arguments, e : ℕ and l : ₤st_nat, and yield a 
nat_list.
-/

inductive nat_list : Type 
| nat_nil : nat_list
| nat_cons : ℕ → nat_list → nat_list 

-- we suggest you open the nat_list namespace

open nat_list


/-
7.

Define X to be the nat_list value that we
interpret as representing the empty list of
natural numbers, []; Y to be the nat_list 
value that represents the list, [1]; and
finally Z to represent the list, [2, 1].
-/

def X := nat_nil
def Y := (nat_cons 1 nat_nil)
def Z := (nat_cons 2 Y)


/-
8.

Define a function (it will be recursive)
that takes any nat_list value and that
returns its length (a natural number that
indicates how many values are in the list). 
Call the function, length.

The challenge is to see the recursion in 
the definition of the length of a list.
Hint questions: What is the length of the
empty list? What is the length of a list
that is not empty, and that thus must be
of the form (nat_cons h t), where h is the
value at the head of the list and t is the
rest of the list.
-/


def length : nat_list → ℕ 
| nat_nil := 0
| (nat_cons h t) := 1 + length t


/-
The stuff that follows is challenging
Get solid on the basic stuff before 
going here.
-/

/-
9.

Define a function, app (short for "append"), 
that takes two nat_list values, let's call them
l1 and l2, and that returns the nat_list with 
the elements of the first list followed by the
elements of the second list. For example, 
(app Y Z) should return the list [1, 2, 1].

Hint: Consider the possible forms of l1. It 
can only be either nat_nil or (nat_cons h t),
where, once again, h is is first element in 
l1, and t is the rest of the list. Write the 
function recursively accordingly.
-/

def app : nat_list → nat_list → nat_list
| nat_nil l2 := l2
| (nat_cons h t) l2 := nat_cons h (app t l2)


/-
10.

Prove the following

∀ l1 l2 : nat_list, 
(length l1 + length l2) = length (append l1 l2)

Hint: use proof by induction on l1. There will be
two cases. In the first, l1 will be nat_nil, and
its length will reduce directly to 0. In the second
case, you will show that the property is true for a
next bigger list: one in the form of (nat_cons h t).
-/

example : ∀ l1 l2 : nat_list, 
(length l1 + length l2) = 
length (app l1 l2) :=
begin
  intros l1 l2,
  induction l1 with l1' n h,
    -- base case
    -- simplify using rules in app and length defs
    simp [app],
    simp [length],

    -- inductive case
    -- simplify using app and length rules in one line
    simp [app,length],
    -- now use induction hypothesis to rewrite goal
    rw <-h,
    -- and the rest is simple arithmetic manipulation
    simp,
    --rw 
end

/- Formal Languages -/

namespace formal
/-
1.

Extend the following formal language to incorporate "or"
-/

inductive pVar : Type 
| mk : ℕ → pVar

inductive pExp : Type
| mk_lit_pexp : bool → pExp
| mk_var_pexp : pVar → pExp
| mk_not_pexp : pExp → pExp
| mk_and_pexp : pExp → pExp → pExp
-- ADD THIS
| mk_or_pexp :  pExp → pExp → pExp

open pExp

def pInterp := pVar → bool

def pEval : pExp → pInterp → bool 
-- how to evaluate literal expression
| (mk_lit_pexp b) i := b
-- how to evaluate variable expression
| (mk_var_pexp v) i := i v
-- how to evaluate a "not" expression
| (mk_not_pexp e) i := bnot (pEval e i)
-- how to evaluate an "and" expression
| (mk_and_pexp e1 e2) i := 
    band (pEval e1 i) (pEval e2 i)
-- AND ADD THIS
| (mk_or_pexp e1 e2) i := 
    bor (pEval e1 i) (pEval e2 i)

end formal
