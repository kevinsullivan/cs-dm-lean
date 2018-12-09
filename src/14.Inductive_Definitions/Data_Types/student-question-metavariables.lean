
-- just an old factorial function

def fac : ℕ → ℕ 
| 0 := 1
| (nat.succ n') := 
    (nat.succ n') * (fac n')

/-
Let's look at proofs of (fac k = 0) in two
different styles. In one style we'll use
metavariables and axioms. In the other, it's
ordinary variables and constructive proofs.
-/

-- with metavariables and axioms

variable k : ℕ 
#check k
#reduce k    -- can't reduce a metavariable
axiom k0 : k = 0  -- omg, it's a real function
#check k0     -- wait, that's kind of weird
#check k0 k   -- we can create proofs of k = 0
variable l : ℕ -- for any k, let's try it on l
#check k0 l   -- here we have a proof of l = 0
#reduce k0 k  -- but again can't reduce metavar

-- that said, we can use the axiom in proofs
example : fac k = 1 :=
begin
    have keq0 := k0 k,
    rw keq0,
    trivial,
end

-- QED

/-
Now with ordinary variables: it's just rfl.
In a way, rfl causes (fac k) to compute, to
reduce, after which it's just reflexive eq.
-/

/-
Here's a zero-valued (non-meta) variable. It
thus has a definite value, which, in this case
is zero. There's a constructive proof, namely
0, of the type of k', i.e., ℕ.
-/

def k' := 0

/-
Now the proof is literally trivial. In this
case, the trivial tactic tries applying rfl 
and that is all it takes.
-/

example : fac k' = 1 :=
begin
    trivial,
end