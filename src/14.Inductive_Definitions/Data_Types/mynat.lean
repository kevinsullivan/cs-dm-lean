namespace my_nat

inductive mynat : Type 
| zero : mynat
| succ : mynat → mynat

def zero := mynat.zero
def one := mynat.succ zero
def two := mynat.succ one
def three := 
    mynat.succ 
        (mynat.succ 
            (mynat.succ 
                zero))

#reduce one
#reduce two
#reduce three

/-
Unary functions
-/

-- identity function on mynat
def id_mynat (n: mynat) := n

-- constant zero function
def zero_mynat (n: mynat) := zero

-- predecessor function
def pred (n : mynat) :=
    match n with
    | mynat.zero := zero
    | mynat.succ n' := n'
    end

/-
There are two new and important
concepts here. The first is a new
kind of matching. The second is
that we define the predecessor 
of zero to be zero. That's a bit
odd.

Look at the matching. The first
pattern is familar. The second,
though, it interesting. If we get
here, we know n isn't zero, so it
must by the successor of the next
smaller mynat. Here we give that
next smaller value the name n'.
And of course that's the number
we want to return as precessor!
-/

/- 
Now let's see binary operations
and recursive functions. To 
define a recursive function we
have a new syntax/
-/

def add_mynat: mynat → mynat → mynat
| mynat.zero m := m
| (mynat.succ n') m :=
    mynat.succ (add_mynat n' m)

/-
Syntax notes: use explicit function
type syntax. Omit any :=. Define how
the function works by cases. Each case
defines what the function does for the
specific kinds of arguments used in the
case. Omit commas between arguments
All cases may be covered
-/

-- It works!
#reduce add_mynat one two
#reduce add_mynat three three


/-
EXERCISES:

(1) We just implemented addition as
the recursive (iterated) application
of the successor function. Now you are
to implement multiplication as iterated
addition.

(2) Implement exponentiation as iterated
multiplication.

(3) Take this pattern one ste further.
What function did you implement? How
would you write it in regular math 
notation?
-/


end my_nat