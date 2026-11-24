/- To define the natural numbers we use inductive types. Natural numbers can be
    visualized as a long snake of numbers, beginning with zeroes with each number
    pointing to its successor. In this sense, there are two ways to construct a
    natural number, either make zero or take a natural number and get its
    successor. -/

inductive MyNat where
| zero : MyNat -- Our first constructor.
| succ : MyNat → MyNat -- THe successor takes in a natural number, and returns another.

/- Lean automatically prevents fun, by this I mean it stops zero from being
    the successor of any natural number. (independence of constructors) -/
theorem zero_ne_succ (n : MyNat) : MyNat.zero ≠ n.succ := nofun

/- It also stops a number from being the successor of two numbers. -/
theorem succ_inj (n m : MyNat) : n.succ = m.succ → n = m := by
    intro hsucc
    apply MyNat.noConfusion hsucc
    intro h
    exact h

/- No we define addition, this may be done inductively on the first variable. -/
def MyNat.Add : MyNat → MyNat → MyNat
| zero, n => n
| succ m, n => (Add m n).succ

namespace MyNat -- So that we don't have to keep writing `MyNat.Add` etc.

/- This holds definitionally, to clear this we use the `rfl` axioms,
     i.e. reflexivity of equality. -/
theorem zero_add (n : MyNat) : Add zero n = n := rfl

-- Again, definitional.
theorem succ_add (n m : MyNat) : Add m.succ n = (Add m n).succ := rfl

-- Our first nontrivial proof, use induction.
theorem add_zero (n : MyNat) : Add n zero = n := by
    induction n with
    | zero =>
        rw [zero_add]
    -- `k` is t.he inductive variable, and `hk` is the inductive hypothesis
    | succ k hk =>
        rw [succ_add, hk]

-- Try the following!
theorem add_succ (n m : MyNat) : Add m n.succ = (Add m n).succ := by
    sorry

theorem add_comm (n m : MyNat) : Add m n = Add n m := by
    sorry

theorem add_assoc (m n k : MyNat) : Add (Add m n) k = Add m (Add n k) := by
    sorry

theorem add_cancel (n m k : MyNat) (heq : Add n k = Add m k) : n = m := by
    sorry

def Mul : MyNat → MyNat → MyNat := sorry
