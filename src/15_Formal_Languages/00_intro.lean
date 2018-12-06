/-
A logic is a "formal language" that has
a mathematically defined syntax and a
mathematically defined semantics. The
semantics in turn depends on an intended
"real-world interpretation" of the basic
symbols in a given logical expression.

Consider for example this proposition
∀ p : Person, ∃ m: Person, motherOf p m. 
We could have written it in a logically
equivalent form: ∀ x : X, ∃ m : X, r p m.
The benefit of the first version is that
it *suggests* an intended interpretation.
We mean for p and m to represent people
(any human beings), and we intend the
motherOf predicate to represent the real
relationship connecting people to moms.

We now drill down on the notions of the
syntax and semantics of a formal language.
The syntax of a language defines the set
of valid expressions in the language. In
predicate logic, for example, ∀ p: Person,
∃ m : Person, motherOf p m is well formed.
However, the expression, ∀ ∃ r, is not.

The semantics of a language then assigns 
a meaning of some kind to each expression
in the language given an interpretation
of the basic elements of an expression.
When the formal language is a logic, the
syntax defines a language of propositions,
predicates, etc., while a semantics tells
us how to evaluate the truth of any such
expression.
-/

/-
In this unit we begin by formalizing the
syntax, interpretation, and semantics of
propositional logic. Proposition logic is
a very simple logic, one that essentially
mirrors (is "isomorphic to") the language
of Boolean expressions.

There are only a few kinds of expressions
in propositional logic. These constitute
the syntax of propositional logic.

* literal expressions for true and false
* variable expressions
* not expressions
* and expressions
* or expressions
* etc.

The semantics gives us a way to decide
what each expression in a language means.
In proposition logic and expression means
("is") either true or false. Here are the
rules.

* the literal true expression is true

* the literal false expression is false

* the value of an "and" expressions, e1 ∧ e2,
is the Boolean conjunction of the values 
of the expressions, e1 and e2, respectively

* the value of a "not" expression ¬ e, is
the Boolean negation of the value of e

* this leaves the question of the value of
a variable expression; for this we need an
additional idea: that of an interpretation.
An interpretation simply assigns a Boolean
value to each variable that might appear in
an expression. Now, to evaluate a variable 
expression, X, we just "look up" its value
in a given interpretation. A variable will
have different values under different
interpretations, and so expressions, in 
general (because they generally involve
variables) will have different values under
different interpretations.

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
| (mk_or_pexp e1 e2) i := 
    bor (pEval e1 i) (pEval e2 i)


notation (e1 ∧ e2) := mk_and_pexp e1 e2

def conjunct : pExp := X_exp ∧ Y_exp
/-
And now we have a formal language, with
a syntax, interpretations, and semantics.
Let's evaluate some of our expressions
under varying interpretations.
-/

-- literal expressions

#reduce pEval tt_exp falseInterp
#reduce pEval tt_exp trueInterp
#reduce pEval tt_exp anInterp

#reduce pEval ff_exp falseInterp
#reduce pEval ff_exp trueInterp
#reduce pEval ff_exp anInterp

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
A function that returns the set 
of variables in a given pExp.
-/

/-
Helper function that adds variables
in given expression to given set of
variables.
-/
def vars_in_exp_helper: 
    pExp → set pVar → set pVar
| (mk_lit_pexp _) s := s
| (mk_var_pexp v) s := s ∪ { v }
| (mk_not_pexp e) s := 
    s ∪ (vars_in_exp_helper e s)
| (mk_and_pexp e1 e2) s := 
    s ∪ 
    (vars_in_exp_helper e1 s) ∪ 
    (vars_in_exp_helper e2 s)

/-
Main function: add variables in given
expression to initially empty set and
return result.
-/
def vars_in_exp (e: pExp) : set pVar :=
    vars_in_exp_helper e ({}: set pVar)

#reduce vars_in_exp and_X_Y_exp
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
e2. You can use the Lean-provided max function in your answer.
-/

#reduce max 5 7
#reduce max 7 5

/-
We can also prove theorems about
our language in general. Here's a
proof that evaluation under a given
interpretation is deterministic. It
always produces the same result.
This is really just a corollary of
the fact that functions in Lean are
single valued and we've defined the
semantics of expressions with a
function.
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
We can also prove theorems about
particular expressions in our language.
For example, if X_exp is some variable
expression, then the expression 
X_exp ∧ (¬ X_exp) is false under *any*
interpretation.
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
EXERCISE: extend the syntax, surface
syntax, and semantics of the language
with an "or" operator. Use ∨ as surface
syntax.
-/

/-
Exercise: now prove that for any 
variable, V, the logical expression
(mk_var_exp V) ∨ (¬ (mk_var_exp V))
always evaluates to true.
-/