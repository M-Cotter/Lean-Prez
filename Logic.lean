/- This line of code introduces three proposition variables that we will
    be able to use in the rest of this file. -/
variable (P Q R : Prop)

-- # PROPOSITIONS

-- An `example` is just a theorem with no name, aptly used mostly for demonstration.

/- This next theorem is extremely trivial, it asks if we have a proof of `P`
    (i.e. `hp`) then can you prove `P`?.-/
example (hp : P) : P := by
    exact hp

-- The `exact` tactic is used to provide a proof which closes a goal.

-- Try it!
example (hp : P) (hq : Q) (hr : R) : Q := by
    sorry

-- # IMPLICATION

-- To type `→` write `\imp` or `\to`, both work.

/- When dealing with implications in our hypotheses, we use the `apply` tactic. This
    is going to allow us to apply an implication to a theorem to reduce our goal. -/
example (hp : P) (hpq : P → Q) : Q := by
    apply hpq
    exact hp

-- Try it!
example (hp : P) (hpq : P → Q) (hqr : Q → R) : R := by
    sorry

/- When dealing with implication in our *goal*, we want to use the `intro` tactic.
    This will add the proposition before the arrow to our hypotheses, and make
    the goal the proposition after the arrow. -/
example : P → P := by
    intro hp
    exact hp

-- Put it all together!
example (hpq : P → Q) (hqr : Q → R) : P → R := by
    sorry


-- # CONJUNCTION

-- We will now introduce the *logical and*, denoted `∧` (type `\and`).

/- If we see `∧` in our goal, we must apply `And.intro`, this is going to reduce our
    goal (which might be to prove `P ∧ Q`) to `P` and then `Q`. Literally, `And.intro`
    is a constructor, it constructs the proposition `P ∧ Q`. -/
example (hp : P) (hq : Q) : P ∧ Q := by
    apply And.intro
    -- To get these bullets type `\.`, these are almost purely cosmetic.
    · exact hp
    · exact hq

-- Parse what this is saying. Also, bracketing in Lean defaults to the right.
example : P → Q → P ∧ Q := by
    sorry

/- If we see `∧` in our hypotheses, e.g. `(hpq : P ∧ Q)`, simply write `hpq.left` to
    get a proof of `P` and `hpq.right` to get a proof of `Q`. -/

example (hpq : P ∧ Q) : P := by
    exact hpq.left

-- Try.
example (hpq : P ∧ Q) : Q ∧ P := by
    sorry

-- # LOGICAL EQUIVALENCE

/- The if and only if was touched on earlier, when I mentioned the propext axiom.
    It is remarkably simple, `↔` (type `\iff`) can be introducted using the
    `apply Iff.intro`, which takes and iff statement in our goal and reduces
    it to two implications.-/

example (hpq : P → Q) (hqp : Q → P) : P ↔ Q := by
    apply Iff.intro
    exact hpq
    exact hqp

#check Eq.mpr

/- When `↔` appears in the hypotheses, we can extract the implication or reverse
    implication using `.mp` or `.mpr` (read: *modus ponens* / *modus ponens reverse*)-/

example (hpq : P ↔ Q) (hq : Q) : P := by
    apply hpq.mpr
    exact hq

example (hpq : P ↔ Q) (hp : P) : Q := by
    apply hpq.mp
    exact hp

-- Try!
example (hpq : P ↔ Q) (hqr : Q ↔ R) (hr : R) : P := by
    sorry

/- We can also use a new tactic: `rw`. The two letters
    here stand for *rewrite*, mostly this tactic is used for proving identites.
    But for `↔`, as I touched on earlier, iff is the same as equality by the
    *propext* axiom. -/

example (hpq : P ↔ Q) (hq : Q) : P := by
    rw [hpq]
    exact hq

example (hpq : P ↔ Q) (hqr : Q ↔ R) (hr : R) : P := by
    rw [hpq, hqr]
    exact hr

-- What if our equality is backwards?
example (hpq : P ↔ Q) (hp : P) : Q := by
    rw [← hpq] -- write `\l` (for left arrow).
    exact hp

-- Try it! (If you're curious, I got the subscript `0` by typing `\0`)
theorem and_comm₀ : P ∧ Q ↔ Q ∧ P := by
    sorry

-- For the daring.
theorem and_assoc₀ : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) := by
    sorry

-- # DISJUNCTION

-- Last, and probably least, is disjunction (AKA logical `or`).

/- To prove an `Or` statement is simply, you just have to pick a side. Use the
    tactics `left` or `right` to choose which side you want to prove. -/

example (hp : P) : P ∨ Q := by
    left
    exact hp

#check Or.inl

/- Alternatively, you can use either `Or.inl`/`Or.inr` (read: 'Or intro left/right')
    to construct an or statement. -/

example (hp : P) : P ∨ Q := by
    apply Or.inl
    exact hp

/- Using or when its in your hypotheses is a little more involved, really
    there are two ways to get `Or`. So when we have a statement like `Or` in
    our hypotheses we should split into cases. This is done using the `Or.elim`
    constructor. -/

#check Or.elim

example (hporq : P ∨ P) : P := by
    apply Or.elim hporq
    · intro p
      exact p
    · intro p
      exact p

-- Let's try
theorem or_comm₀ : P ∨ Q ↔ Q ∨ P := sorry

-- For the daring.
theorem or_assoc₀ : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) := by
    sorry

-- # NEGATION

/- If `P` is a proposition then `¬P` is another name for the proposition `P → False`.
    The proposition `False` is very special, by the principle of explosion a falsehood
    implies anything. -/

example (hf : False) : P := by
    exfalso -- This tactic reduces any goal to `False`.
    exact hf

example (hp : P) : ¬¬P := by
    intro hnp
    apply hnp
    exact hp

example (hnp : ¬¬¬P) : ¬P := by
    sorry

example (hpq : P → Q) : ¬Q → ¬P := by sorry

/- As it turns out, we do not yet have enough power to prove `¬¬P ↔ P`, we need
    the axiom of choice (seriously). Luckily, we can just use a built in theorem. -/

example : ¬¬P ↔ P := by
    exact Classical.not_not

example : P ∨ ¬P := by
    exact Classical.em P

-- Try!
example : (P → Q) ↔ (¬Q → ¬P) := by
    sorry
