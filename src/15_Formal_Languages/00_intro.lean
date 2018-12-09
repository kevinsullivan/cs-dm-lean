/-
A logic is a "formal language" that has
a mathematically defined syntax and a
mathematically defined semantics. 

We now drill down on the notions of the
syntax and semantics of a formal language.
The syntax of a language defines the set
of valid expressions in the language. In
predicate logic, for example, ∀ p: Person,
∃ m : Person, motherOf p m is syntactically
well formed, but ()∀ ∃ r() is not.

The semantics of a language then assigns 
a meaning each "well formed" expression
in the language.

When the formal language is a logic, the
syntax defines a language of propositions,
predicates, etc., while a semantics tells
us how to evaluate the truth of any such
expression.
-/

/-
In this unit we formalize the syntax and
semantics of what we call propositional 
(as opposed to predicate) logic. 

Propositional logic is a very simple logic.
It essentially mirrors (is "isomorphic to") 
the language of Boolean expressions.

There are only a few kinds of expressions
in propositional logic. These constitute
the syntax of this formal language.

* "literal expressions" for true and false
* "variable expressions"
* "not expressions"
* "and expressions"
* "or expressions"
* etc.

The semantics then gives us a way to decide
what each expression in a language means.
In propositional logic an expression means
("is") either true or false. Here are the
rules.

* literal true evaluates to true

* literal false evaluates to false

* the value of an "and" expression, 
e1 ∧ e2, is the Boolean conjunction 
of the values of e1 and e2, resp.

* the value of a "not" expression,
¬ e, is the Boolean negation of the 
value of e

* this leaves the question of the value 
of a variable expression. For this we 
need an additional idea: that of an 
interpretation. An interpretation is an
assignment of Boolean values to each of
the variables that might appear in some 
expression. Now, to evaluate a variable 
expression, X, we just "look up" its value
in a given interpretation. A variable 
expression will thus have different values 
under different interpretations. Thus, 
expressions, in general, because they 
generally involve variables, will have 
different values under different 
interpretations.

We now show you how not only to make these
ideas precise, but how to automate them, in
Lean. You are about to implement your own
simple automated logical reasoning system!
-/

-- Syntax

/-
We formalize the syntax of a language 
with an inductive definition of the set
of valid expressions.

An expression in propositional logic 
is built from a (1) a logical constant,
true or false, (2) a propositional (you
can think "Boolean") variable, or (3) a
logical connective (and, or, not, etc)
and one or more smaller expressions.
-/

/-
To formalize this idea, we need to 
define what we mean by a variable. 
We do with with a new type, pVar,
where each such variable holds a ℕ
value that distinguishes it from any
other propVar. 
-/

inductive pVar : Type 
| mk : ℕ → pVar

-- Examples

#check (pVar.mk 0)

-- Nice names for a few pVars

def X := pVar.mk 0
def Y := pVar.mk 1
def Z := pVar.mk 2
def W := pVar.mk 3

/-
Now we formalize a language of
expressions in propositional logic. 
-/

inductive pExp : Type
| mk_lit_pexp : bool → pExp
| mk_var_pexp : pVar → pExp
| mk_not_pexp : pExp → pExp
| mk_and_pexp : pExp → pExp → pExp

open pExp

-- Examples of expressions

def false_exp := mk_lit_pexp ff
#check false_exp

def true_exp := mk_lit_pexp tt

def X_exp := mk_var_pexp X
def Y_exp := mk_var_pexp Y
def Z_exp := mk_var_pexp Z
#reduce Z_exp

def not_X_exp := mk_not_pexp X_exp
def and_X_Y_exp := mk_and_pexp X_exp Y_exp
def and_X_Z_exp := mk_and_pexp X_exp Z_exp
#reduce and_X_Z_exp

-- syntactic sugar!

notation e1 ∧ e2 :=  mk_and_pexp e1 e2
notation ¬ e := mk_not_pexp e

-- expressions using our notation!
def not_X_exp' := ¬ X_exp
def and_X_Y_exp' := X_exp ∧ Y_exp
def and_X_Z_exp' := X_exp ∧ Z_exp


-- Quiz

def tf := (mk_lit_pexp tt) ∧ (mk_lit_pexp ff)
def nt := ¬ (mk_lit_pexp tt)
def nxy := ¬ (X_exp ∧ Y_exp)
def foo := nt ∧ nxy
def bar := (¬ nxy) ∧ foo
def baz : pExp := tf

def jab := ¬ (X_exp ∧ Y_exp)
#reduce jab 

-- Semantics

/-
To formalize a semantics for our
realization of propositional logic,
we need to formally define what we
mean by an interpretation.

An interpretation in propositional 
logic is a function from propositional
variables to corresponding (Boolean)
truth values. An interpretation tells
us what each variable "means" -- i.e.,
whether it means true, or false. 

We now define a name for the type
of an interpretation (pVar → bool).
Then we present several examples of
interpretations.
-/

def pInterp := pVar → bool

-- an "all false" interpretation
def falseInterp (v : pVar) : bool :=
    ff

-- an "all true" interpretation
def trueInterp (v : pVar) :=
    tt

-- X = tt, Y=ff, Z=tt, _ = ff

def anInterp: pInterp :=
λ(v: pVar),
  match v with
  | (pVar.mk 0) := tt     -- X
  | (pVar.mk 1) := ff     -- Y
  | (pVar.mk 2) := tt     -- Z
  | _ := ff               -- otherwise
  end

-- Semantics

/-
We now define a semantics for our
language in the form of a function
that, when given any expression in
our language *and* an interpretation
for the variables that might appear
in it, evaluates its truth value and
returns it as a result.

The definition is by cases, i.e., 
with one rule for each possible form
(constructor) of expression.

Note: Lean "overloads" logical
operator notations, such as ∧, ∨, 
and ¬. Here they are applied not to
values of type Prop, but to values 
of type bool, where they have their
usual means from Boolean algebra.
-/

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

/-
And now we have a formal language, with
a syntax, interpretations, and semantics.
Let's evaluate some of our expressions
under varying interpretations.
-/

-- literal expressions

/-
#reduce pEval tt_exp falseInterp
#reduce pEval tt_exp trueInterp
#reduce pEval tt_exp anInterp

#reduce pEval ff_exp falseInterp
#reduce pEval ff_exp trueInterp
#reduce pEval ff_exp anInterp
-/

-- variable expressions
#reduce pEval X_exp falseInterp
#reduce pEval X_exp trueInterp
#reduce pEval X_exp anInterp

#reduce pEval Y_exp falseInterp
#reduce pEval Y_exp trueInterp
#reduce pEval Y_exp anInterp

#reduce pEval Z_exp falseInterp
#reduce pEval Z_exp trueInterp
#reduce pEval Z_exp anInterp

#reduce pEval (mk_var_pexp W) falseInterp
#reduce pEval (mk_var_pexp W) trueInterp
#reduce pEval (mk_var_pexp W) anInterp

-- We don't have to give variables names
#reduce pEval (mk_var_pexp (pVar.mk 10)) anInterp

-- not expression
#reduce pEval not_X_exp falseInterp
#reduce pEval not_X_exp trueInterp
#reduce pEval not_X_exp anInterp

-- and expressio
#reduce pEval and_X_Z_exp falseInterp
#reduce pEval and_X_Z_exp trueInterp
#reduce pEval and_X_Z_exp anInterp

#reduce pEval and_X_Z_exp' falseInterp
#reduce pEval and_X_Z_exp' trueInterp
#reduce pEval and_X_Z_exp' anInterp

#reduce pEval and_X_Y_exp anInterp

/-
So there you have it: a complete
formal definition of the syntax,
interpretation, and semantics of
propositional logic, in Lean, with
a nice "surface syntax," to boot.
(Ok, it's complete except for the
definitions for the other logical
connectives. You will add some of
them in homework and on the exam.)
-/

/-
From here, we can define richer
functions, such as functions that
analyze expressions; and we can
even state and prove theorems 
about our language.
-/

/-
Let's define a function that 
returns the set of variables 
in a given pExp. This will be
useful in the future.
-/

/-
We start by defining a recursive 
helper function that adds all the 
variables in given expression to 
the given, often already non-empty, 
set of variables.

Understand the type and purpose of
this function, then go on to read 
the following main function. Study
its purpose, type, and implementation,
then come back for a deeper look at 
how this function is implemented.
Learn to use functions knowing only
their type and purpose, ignoring, at
least at first, their implementation
details. Pratice mental abstracting.

We implement (prove) this recursive 
function (type) by case analysis on 
possible forms of the given pExp.
-/
def vars_in_exp_helper: 
    pExp → set pVar → set pVar

-- literal expressions add no variables to the set
| (mk_lit_pexp _) s := s
-- a variable expression adds variable v to the set
| (mk_var_pexp v) s := s ∪ { v }
-- a (not e) expression adds the variables in e
| (mk_not_pexp e) s := 
    s ∪ (vars_in_exp_helper e s)
-- an (and e1 e2), add the variables in e1 and e2 
| (mk_and_pexp e1 e2) s := 
    s ∪ 
    (vars_in_exp_helper e1 s) ∪ 
    (vars_in_exp_helper e2 s)

/-
Main function: a non-recursive function
that passes an initially empty set of
variables to the helper function and 
then gets back a set of all, and only,
the variables in the given expression.
-/
def vars_in_exp (e: pExp) : set pVar :=
    vars_in_exp_helper e ({}: set pVar)


/-
Examples of its use
-/
#reduce vars_in_exp and_X_Y_exp
-- A predicate defining the set { X, Y 

/-
Another example
-/
#reduce vars_in_exp and_X_Z_exp

/-
EXERCISE: Write a function that when
given an expression, e, returns the 
"nesting depth" of the expression. The
nesting depth of a literal or variable
expression is 1. The depth of a (not e) 
expression is 1 + the depth of e. And
the depth of an (and e1 e2) expression
is 1 + the max of the depths of e1 and
e2. You can use the Lean-provided max 
function in your answer.
-/

#reduce max 5 7
#reduce max 7 5

/-
We can also prove theorems about
our language in general. Here's a
proof that evaluation under a given
interpretation is "deterministic:: 
it always produces the same result.

This is really just a corollary of
the facts that (1) functions in Lean 
are single valued and (2) we defined 
the semantics of expressions with a
function. There's one and only one 
answer for the value of any given
expression.
-/

theorem pEval_deterministic :
∀ e : pExp, 
∀ i : pInterp,
∀ v1 v2 : bool,
v1 = pEval e i → v2 = pEval e i → v1 = v2 :=
begin
intros e i v1 v2 h_v1 h_v2,
rw h_v1, 
rw h_v2,
end


/-
We can also prove theorems ("reason
about") particular expressions, or
certain classes of expressions, in 
our language. For example, if X_exp 
is any variable expression, then the 
expression (X_exp ∧ (¬ X_exp)) is 
false under any interpretation. We
can easily prove this proposition.
-/

theorem contra :
∀ V : pVar,
∀ i : pInterp,
pEval 
    ((mk_var_pexp V) ∧ ¬ (mk_var_pexp V)) i = ff 
:=
begin
intros X i,
simp [pEval],
-- case analysis on result of function!
cases (i X),
left, apply rfl,
right, apply rfl,
end

/-
Note that it is quantified over all
possible interpretations: over all
possible functions from pVar → bool.
Lean supports what is called higher
order predicate logic. Quantifying
over functions and relations is ok
in a higher-order predicate logic. 
It is not allowed in the first-order
predicate logic of everyday math and
computer science. Here you can see
that it gives you great expressive
power to be able to quantify over
functions. It gives us a way to say,
"under any possible interpretation",
which is exactly what we need to be
able to say to define satisfiability,
validity, unsatisfiability, etc.
-/



/-
Exercise: Prove that for any 
variable, V, the logical expression
(mk_var_exp V) ∨ (¬ (mk_var_exp V))
always evaluates to true.
-/

def valid (e : pExp) : Prop :=
    ∀ i : pInterp, pEval e i = tt

/-
An expression in propositional logic
is unsatisfiable if it does'ot evaluate 
to true under any interpretation.
-/

def unsatisfiable (e : pExp) : Prop :=
    ∀ i, pEval e i = ff

/-
You could also have said there does not
exist an i that makes (pEval e i) = tt.
-/

/-
An interpretation that makes an
expression, e, evaluate to true,
is said to be a "model" of that
expression. Here's a predicate
asserting that i is a model of e.
-/

def isModel (i: pInterp) (e : pExp) :=
    pEval e i = tt

/-
An expression is said to be satisfiable 
if there is at least one interpretation 
under which it evaluates to true.
-/
def satisfiable (e : pExp) : Prop :=
    ∃ i, isModel i e

/-
Example: X ∧ ¬ X is unsatisfiable.
-/

example : unsatisfiable (X_exp ∧ (¬ (X_exp))) :=
begin
unfold unsatisfiable,
intro i,
rw pEval, -- you can do this
rw pEval, -- and do it again
cases (pEval X_exp i), -- cool!
trivial,
trivial,
end

/-
EXERCISE: Once you've extended
our logic with an or operator,
formulize and prove the proposition
that (our rendering of) X ∨ (¬ X)
is valid.

EXERCISE: Prove the proposition
that (X ∨ Y) ∧ Z is satisfiable.
Hint: You'll need a witness. There
is an element of search involved
in solving a problem like this.
-/

/-
EXERCISE: Write a SAT solver based
on what we've done here.
-/

-- m'th bit from right in binary rep of n
def mrbn: ℕ → ℕ → bool 
| 0 n := n % 2 = 1
| (nat.succ m') n := mrbn m' (n/2) 

/- smoke test
#reduce mrbn 0 15
#reduce mrbn 2 15
#reduce mrbn 2 15
#reduce mrbn 3 15
#reduce mrbn 4 15
#reduce mrbn 5 15
-/

/-
The mth canonical interpretation
among the 2^n-1 interpretations
for a set of variables of size n.

The values of the first n-indexed
variables in the mth interpretation
are determined by the bits in the 
binary representation of m. The
leftmost bit gives the value for 
the variable with index 0. Each
bit to the left gives the value of
the next indexed variable. All 
subsequent values are ff. m thus 
effectively enumerates the 2^n 
interpretations on the n first 
variables in the index set of all
variables. 
-/

def mthInterpOf2toN (m n: ℕ) : pInterp :=
    if (m >= 2^n)
    then falseInterp 
    else
    λ v : pVar, 
        match v with
        | (pVar.mk i) := 
        if i >= n then 
        ff 
        else 
        (mrbn i m)
        end

/-
Examples:
-/

#reduce pEval and_X_Y_exp (mthInterpOf2toN 3 3)

-- unincorporated

#reduce mthInterpOf2toN 3 5

def first_n_true_inter (n : ℕ) : pInterp :=
λ v, 
    match v with
    | (pVar.mk n') := if n' < n then tt else ff
    end

def all_models (e : pExp) :=
    { m | isModel m e}


def sat_solve (e : pExp) : option pInterp :=
none


