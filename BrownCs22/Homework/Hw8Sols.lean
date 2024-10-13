import BrownCs22.Library.Tactics
import BrownCs22.Library.Defs
import Mathlib.Mathport.Syntax
import Mathlib.Data.Nat.Parity

set_option pp.notation true
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.instances false
set_option pp.instanceTypes false
set_option pp.instantiateMVars false
set_option pp.privateNames false
set_option pp.universes false
set_option linter.unusedVariables false



/-

# Combinatorics!

In this homework, we'll be looking at some combinatorics problems formalized in
Lean. In doing so, we'll get to see how the same function can be defined in several
different ways in Lean, and how our choice of definition can affect the proofs we
write about that function.

Our proofs will also expose the many unspoken assumptions that often go unnoticed
when proving theorems in informal math. Those assumptions can lead to incorrect
proofs, if we use those theorems in situations where the assumptions are false!

As with last homework, much of this file is a demo. The problems for you to solve
start at line 253.





# How to define "n choose k" or, how to choose "choose"

Before we get to the function definitions, we need to go over some new notation.

In Lean, we calculate factorials with the `Nat.factorial` function. But that becomes
annoying to type out (and to read) when you're working with tons of factorial
expressions. It would be nice if we could use the exclamation point notation ordinarily
used in written math, where `n! = Nat.factorial n`.

But unfortunately, `!` is a somewhat special character in Lean (it means `not`),
so we had to get SUPER creative. So, for this homework only, we've introduced a
bit of special notation:

-/

notation:max n "¡" => Nat.factorial n

#eval 6¡

/-

We're using the UPSIDE-DOWN exclamation point! (¿?¡!?¿) You can type this character
by entering a backslash `\` and then a normal exclamation point.

Now, how should we define the combination, or "choose", function?

We could just directly steal the definition we used in lecture:

-/

def ChooseAttempt1 (n k : ℕ) := n¡ / (k¡ * (n-k)¡)

/-

But what does this actually mean? In lecture, we were implicitly working under the
assumption that `k` and `n` are natural numbers, and we've formalized that. But
we were also working under the assumption that `k ≤ n`, and that is no longer the
case here - our `ChooseAttempt1` function generalizes over all natural numbers.

That's a good thing, since we would like to be able to say `2 Choose 3 = 0`, for
a couple reasons. Firstly, it's impossible to choose 3 elements from a set of 2,
so it makes sense to say there are 0 ways of doing so. Secondly, this is required
to make Pascal's Rule (https://en.wikipedia.org/wiki/Pascal%27s_rule) work nicely.

(Consider applying Pascal's Rule when `n = k = 3`.)

However, this also means we have to deal with the thorny question of what `(n-k)¡`
means when `n < k`. The factorial function doesn't make much sense on negative
numbers, so it's a good thing the subtraction function on natural numbers bottoms
out at 0.

Well, when `n < k`, then `(n-k)¡ = 0¡ = 1`, and `n¡ < k¡`, and division of natural
numbers rounds down, so `ChooseAttempt1 n k = n¡ / (k¡ * 1) = n¡ / k¡ = 0`.

So this actually seems to work!

Except, wait, we lied. `n < k` USUALLY implies `n¡ < k¡`, with one exception:
when `n = 0` and `k = 1`.

-/

#eval ChooseAttempt1 0 1 -- WRONG

/-

So we need to amend our definition. Let's try again:

-/

def ChooseAttempt2 (n k : ℕ) := 
  match n, k with
  | 0, _ => 0
  | n, k => n¡ / (k¡ * (n-k)¡)

/-

This syntax means roughly the following:
"First check if `n = 0`. In this case return 0 (regardless of what `k` is).
Otherwise, return `n¡ / (k¡ * (n-k)¡)`."

This works, right? Nope.

-/

#eval ChooseAttempt2 0 0 -- WRONG

/-

It can seem funny to ask how many ways there are to choose 0 elements
from a set of 0. But another way of saying this is, how many 0-element
subsets of the empty set are there? There's one: the empty set itself!
So `0 choose 0` should be 1.

Last try.

-/

@[reducible] -- ignore this first line
def Choose (n k : ℕ) := 
  match n, k with
  | _, 0 => 1
  | 0, _ => 0
  | n, k => n¡ / (k¡ * (n-k)¡)

/-

Finally, this works. Notice how many assumptions, and how much nuance, went undetected
in this one little function. Notice also how this definition is NOT recursive - 
as a result, our proofs about it will not use induction.

We're introducing notation for this function as well.

`(n C k)` means `Choose n k`. The parentheses, and the spaces around the C, are
required. To use `simp` to break down a `Choose` expression, you still have to
refer to it by its proper name, e.g. `simp [Choose]`.

-/

notation:max "(" n " C " k ")" => Choose n k

#eval (4 C 2)

/-

Let's prove some stuff! You are free to use the theorems below however you want
in the following problems. You don't need to understand our Lean proofs of them.

-/

-- Every natural number is either 0, or the successor of another natural number.
lemma eq_zero_or_exists_succ (n : ℕ) :
  n = 0 ∨ ∃ (n0 : ℕ), n = n0 + 1 := by
  have hnzp : n = 0 ∨ n > 0 := Nat.eq_zero_or_pos n
  eliminate hnzp
  --  the previous two lines could have been written as one, `eliminate Nat.eq_zero_or_pos n`.
  {left; assumption}
  {
    right
    eliminate (Nat.exists_eq_succ_of_ne_zero (by linarith)) with w
    existsi w
    assumption
  }

-- If a number is more than another number, it must be a successor of some number.
lemma exists_succ_of_gt {x n : ℕ} :
  x < n → ∃ (n0 : ℕ), n = n0 + 1 := by
  intro h
  have hnzp : n = 0 ∨ ∃ n0, n = n0 + 1 := eq_zero_or_exists_succ n
  eliminate hnzp 
  -- again, the previous two lines could have been written as `eliminate eq_zero_or_exists_succ n`.
  linarith
  assumption

-- Any pair of natural numbers is equal or isn't.
lemma nat_eq_or_ne (n k : ℕ) : n = k ∨ n ≠ k := by
  exact Decidable.eq_or_ne n k

-- Every natural number is either equal to zero or not.
lemma eq_zero_or_ne_zero (n : ℕ) : n = 0 ∨ n ≠ 0 := by
  exact nat_eq_or_ne n 0 
  
-- As long as `n` and `k` are both positive, `Choose n k` is 
-- equivalent to `n¡ / (k¡ * (n-k)¡)`
@[simp] lemma Choose_expansion_of_pos_n_k (n k : ℕ) :
  0 < n → 0 < k → Choose n k = n¡ / (k¡ * (n-k)¡) := by
  intro hn hk
  rewrite [Nat.pos_iff_ne_zero] at *
  simp [Choose]

-- So `simp` will automatically clean up annoying bits of arithmetic that might
-- pop up in your problems. You shouldn't need to call these manually.
@[simp] lemma _112 : 1 + 1 = 2 := by numbers
@[simp] lemma _x112 (x : ℕ) : x + 1 + 1 = x + 2 := by rw [add_assoc];
@[simp] lemma _x11x (x : ℕ) : x + 1 - 1 = x := by simp
@[simp] lemma _011 : 0 + 1 = 1 := by simp
@[simp] lemma _s01 : Nat.succ 0 = 1 := by simp
@[simp] lemma Choose_zero_eq_one : ∀ n, (n C 0) = 1 := by simp [Choose]



/-

# Problem 1

Remember that you won't be able to break down an expression like `(n C k)` until
you know more about `n` or `k` (you can't break it down without knowing which arm
of the `Choose` function will match!) So, one trick that's helpful in most of
these proofs is breaking the problem into cases - for example, one case where
`n = 0`, and one case where `∃ n0, n = n0 + 1`. It will occasionally be necessary
to nest these cases.

If you're confused, take a closer look at the provided helper theorems, and make
sure you remember how to use existence and disjunction proofs. Also make sure you
know how to do the proof on paper, first.

For some of the trickier proofs, we've provided some of the proof structure for you.

If you're feeling particularly adventurous, you are also free to use any library 
theorems you find in Mathlib4
(https://leanprover-community.github.io/mathlib4_docs), but you may find the following
theorems particularly useful. These are the only outside theorems our solutions use.

One last pro tip: if you have a proof `h` in your context that you want to simplify,
you can call `simp` like this: `simp at h`.

-/

#check Nat.mul_div_cancel
#check Nat.factorial_pos
#check Nat.factorial_succ
#check Nat.div_self
#check Ne.symm
#check Nat.ne_of_lt
#check Nat.div_eq_zero
#check Nat.eq_zero_or_pos
#check Nat.factorial_lt
#check lt_mul_of_lt_of_one_le
#check Nat.sub_sub_self
#check mul_comm
#check lt_of_not_le
#check Nat.sub_eq_zero_iff_le
#check Nat.sub_add_comm



/- We do this one for you as a demo: -/
@[simp] lemma Choose_one_eq_self (n : ℕ) :
  (n C 1) = n := by
  /- The line below is more condensed notation than we are used to, but it functions
  to break down the proof into two cases:
    n = 0
    ∃ n0, n = n0 + 1 
    
  We could have instead done this with a `have` statement followed by `eliminate`:
  see lines 170 and 185 for similar syntax! 
  
  Since we use {} to partition our subgoals, we name both resulting hypotheses `h`:
  this is not necessary. -/
  eliminate (eq_zero_or_exists_succ n) with h h
  { -- Since n = 0, we know the result of the choose function by its definition.
    -- Therefore, we feed `h` to the simplifier.
    simp [h]}
  { -- Here, `h` is an existential, so we can use `eliminate` to extract a witness.
    eliminate h with n0 h
    -- Since n = n0 + 1, n can't be 0. This fact is important to make sure our reasoning
    -- about factorials is correct later (and so that we can `simp Choose`). Note that we don't give this statement a name,
    -- and it gets named `this`. This is fine, since we don't refer to it explicitly.
    have : n ≠ 0 := by linarith 
    simp [Choose]
    -- We unfold the definition of factorials for n ≠ 0
    -- (the nonzero assumption is hidden in the fact that the definition refers to `Nat.succ n`)
    rewrite [h, Nat.factorial_succ] 
    
    simp
    rewrite [Nat.mul_div_cancel] -- a very useful lemma :) This breaks our proof into 2 subgoals, since 
                                 -- we must justify that our denominator is not 0.
    {simp}
    {apply Nat.factorial_pos}
  }


-- Remember that `simp` can expand an expression `(n C k)` to the full factorial
-- fraction as long as it knows `n ≠ 0` and `k ≠ 0`, i.e., as long as you have
-- proofs of `n ≠ 0` and `k ≠ 0` in your context.

/- _ points -/
@[simp] lemma Choose_self_eq_one (n : ℕ) :
  (n C n) = 1 := by
  eliminate (eq_zero_or_exists_succ n) with h h
  {simp [h]}
  {
    eliminate h with n0 h
    have : n ≠ 0 := by linarith
    simp [Choose]
    apply Nat.div_self
    apply Nat.factorial_pos
  }




-- You don't have to do this one on your own -- we're going to talk through it
-- together in lecture on Friday, April 14!
lemma binomial_symmetry_helper (n k : ℕ) :
  n ≠ 0 → k ≠ 0 → (n - k) ≠ 0 → (n C k) = (n C n-k) := by
  intros hn hk hnk
  simp [Choose]
  rewrite [mul_comm]
  rewrite [Nat.sub_sub_self]
  { reflexivity }
  { have : k < n
    { apply lt_of_not_le
      rewrite [← Nat.sub_eq_zero_iff_le]
      assumption }
    { linarith }
  }

-- This next proof is basically about hunting down and proving all the possible
-- edge cases, and fiddling with arithmetic until you're in a position to call
-- `binomial_symmetry_helper`.

-- Hint: you'll probably have to do a few case splits on whether a natural number
-- is 0 or a successor, like `eliminate (eq_zero_or_ne_zero n) with hn hn`.

-- Also, consider: why would this be false without the `k ≤ n` hypothesis? Where
-- would the proof go wrong?


/- _ points -/
theorem binomial_symmetry (n k : ℕ) :
  k ≤ n → (n C k) = (n C n-k) := by
-- students are given the `intro` and 3 `eliminate` statements, as well as `apply binomial_symmetry_helper`.
-- These statements subdivide our proof into various cases where we assume certain numbers are zero or nonzero.
  intro hk_le_n
  eliminate (eq_zero_or_ne_zero n) with hn hn
  { -- In order to simplify our goal, we need to figure out if `k` and `n-k` are zero or nonzero. Luckily,
    -- since k ≤ n and n = 0, we can quickly conclude that k = 0.
    have : k = 0 := by linarith
    -- Now, we can use `simp` (making sure to give it the assumptions that `n` and `k` are 0)
    simp [hn, this]
  }
  {
    eliminate (eq_zero_or_ne_zero k) with hk hk
    { -- We already know the "zero-ness" of `n` and `k`, so we can call `simp` immediately.
      simp [hk]}
    {
      eliminate (eq_zero_or_ne_zero (n - k)) with hnk hnk
      { -- In order to call `simp` here, we need to show that `n = k`. Unfortunately, `n - k = 0`
        -- doesn't immediately imply this, due to how we defined subtraction on natural numbers
        -- (eg `1 - 3 = 0`). However, it allows us to conclude `n ≤ k` (using a handy dandy theorem)
        -- which we can combine with the pre-existing knowledge that `k ≤ n` to get what we need!
        have : n ≤ k := by apply Nat.le_of_sub_eq_zero; assumption
        have : n = k := by linarith
        simp [this]
      }
      {
        apply binomial_symmetry_helper
        -- Turns out all of these `sorry` blocks are goals that exactly match our context!
        -- Seeing a bunch of `assumption`s at the ends of proofs can feel unsatisfying, but
        -- it gets the job done :)
        {assumption}
        {assumption}
        {assumption}
      }
    }
  }



/-

# Alternative definition

Now we're going to explore an alternative way of defining the combination function,
using Pascal's Rule. This way, Pascal's Rule is true *by definition*, which is pretty
handy. This is the definition used by Mathlib!

-/

@[reducible] def AltChoose (n k : ℕ) := 
  match n, k with
  | _, 0 => 1
  | 0, _ => 0
  | n+1, k+1 => AltChoose n (k+1) + AltChoose n k

/-

Unlike our previous definition, `Choose`, this one is recursive. As a result, ALL
of our proofs in this section will need to be by induction. It's also a much
simpler definition in some ways - it doesn't use the factorial or division functions,
both of which can be very tricky to work with. So these proofs have the potential
to be much shorter.

However, it's not as immediately obvious that this definition does indeed calculate
the combination function we're aiming for. Also, proving its equivalence to our
previous `Choose` definition is surprisingly difficult, and beyond the scope of
this class. You should still be able to convince yourself that they're the same,
though (hint: induct on `n` and apply Pascal's Rule).

These kinds of trade-offs are inevitable in math, and it's good to be aware of them
when writing your own definitions.





# Problem 2

Now let's try proving the same theorems with this alternative definition. For your
convenience, we've again introduced some notation to avoid writing out `AltChoose`
every time. It just uses an `A` instead of a `C`.

-/

notation:max "(" n " A " k ")" => AltChoose n k

@[simp] lemma AltChoose_zero_eq_one : ∀ n, (n A 0) = 1 := by simp [AltChoose]
  
/- _ points -/
@[simp] lemma AltChoose_one_eq_self :
  ∀ n, (n A 1) = n := by
  basic_induction -- Induction time! 
  { -- by definition
   simp [AltChoose]}
  { -- Once we introduce our inductive hypothesis, proving the inductive step follows from the recursive definition of 
    -- `AltChoose`.
    intro n h
    simp [AltChoose]
    assumption
  }

-- In this problem, you might find the following lemma useful again:
#check exists_succ_of_gt


/-

In this problem, it can  be  tricky to think about what the induction predicate is!
We're doing induction on `n`, with the predicate `∀ k, n < k → (n A k) = 0`.
Take a look at what our induction hypothesis `ih` looks like in the inductive step.

-/
/- _ points -/
@[simp] lemma AltChoose_zero_of_k_gt_n :
  ∀ n k, n < k → (n A k) = 0 := by
  basic_induction
  {
    intro k h
    -- Because AltChoose is a recursive definition that relies on `_+1`,
    -- we need to show that `k` is the successor of something. Luckily,
    -- we have been given a lemma for that earlier!
    have : ∃ k0, k = k0 + 1 := exists_succ_of_gt h
    -- Eliminate the existential, then we can simplify!
    eliminate this with k0 h
    simp [h, AltChoose]
  }
  { -- Lots of `intro`s here - make sure you know which is which!
    intro n hind k hless
    -- Same trick as before
    have : ∃ k0, k = k0 + 1 := exists_succ_of_gt hless
    eliminate this with k0 h
    -- Due to our definitions, this `simp` gives us an AND statement in our goal, so we
    -- will need to `split` it.
    simp [h]
    split_goal
    -- Note that `hind` is a hypothesis that ends with `→ (n A k) = 0`. This matches our goal (replacing `k` with `k0+1`),
    -- so we can `apply` it to end up with the left side of the implication! In both cases, this results in a proof solvable
    -- by `linarith`.
    apply hind; linarith
    apply hind; linarith
  }

/- _ points -/
@[simp] lemma AltChoose_self_eq_one :
  ∀ n, (n A n) = 1 := by
  -- Because we have defined `AltChoose` inductively, this is super straightforward! `simp` does a lot of work here.
  basic_induction
  {simp [AltChoose]}
  {
    intro n h
    simp [AltChoose]
    assumption
  }



/-

# Bonus!

The AltChoose version of the proof of binomial symmetry is surprisingly difficult!

It can be done using only the tools you've been taught, but it's LONG, and it requires
a lot of fiddling around to get the arithmetic right.

Try it out if you're feeling confident... 👁️👄👁️

Hint: you may find the theorems below quite useful.


This problem is a doozy. No worries if it is confusing, but I highly recommend
hovering over some of the lemmas that appear below to get more of a sense for what
Lean can do, even if you're not sure of the overarching structure! 
Some of these lemmas (especially things like `add_comm`) come up a *lot*
when doing more in-depth mathematical work in Lean.
-/

#check nat_eq_or_ne
#check Nat.lt_of_le_of_ne
#check eq_zero_or_exists_succ
#check Nat.sub_add_comm
#check add_comm
#check congr_arg
#check congr_arg₂
#check Nat.sub_add_eq

/- _ points -/
theorem alt_binomial_symmetry :
  ∀ n k, k ≤ n → (n A k) = (n A n-k) := by
  basic_induction
  { -- Pretty straightforward base case - looks like what we've seen before.
    intro k h
    have : k = 0 := by linarith
    simp [this, AltChoose]
  }

  { intro n hind k hless
    -- The following lemma lets us split the proof into
    -- cases where `k=n+1` and `k≠n+1`.
    -- In general, a lot of proofs become much easier when you
    -- can reason out a way to break the problem into multiple
    -- cases and justify that they encompass all possibilities.
    eliminate nat_eq_or_ne k (n+1) with h h

    -- the equality case is, unsusprisingly, easily doable with `simp`.
    {simp [h, AltChoose]}

    { 
      -- Here's the fun part! We first jump through some hoops to show that 
      -- `k ≤ n`, using the facts that `k ≤ n + 1` and `k ≠ n + 1`.
      have hklt : k < n + 1 := by {
        apply Nat.lt_of_le_of_ne
        assumption
        assumption
      }

      have hkle : k ≤ n := by linarith

      -- Split into more cases! Either `k=0` or `k = k0+1`
      eliminate eq_zero_or_exists_succ k with hz hsucc
      
      {simp [hz, AltChoose]}
      
      {
        eliminate hsucc with k0 hk -- Eliminate existensial
        rewrite [Nat.sub_add_comm hkle] -- Some arithmetic rearrangement
        simp [hk, AltChoose]
        rewrite [add_comm] -- More rearrangement - Lean likes it when things are in *very specific* spots :)
        -- `congr_arg₂` looks very scary, in part because it is designed to be very general use. For our purposes,
        -- you can consider it to be saying something along the lines `a = c ∧ b = d → a + b = c + d`:
        apply congr_arg₂
        -- We now have two subgoals, asking us to show that various things are equal.
        { -- because `hind` has an implication, using it in a rewrite block adds a new subgoal, asking us
          -- to prove the left side of the implication.
          rewrite [hind]
          { -- Another (different) `congr_arg` here: this essentially allows us to get rid of `(n A ... )`, since that
            -- part is the same in each of our terms.
            apply congr_arg
            -- A bunch of arithmetic lemmas that come together to help us rearrange our math
            -- (note that `←Nat.sub_add_comm` adds a new subgoal)...
            rewrite [←Nat.sub_add_comm, add_comm k0 1, Nat.sub_add_eq]
            {simp} -- Now that we've arranged everything juuuuuust right, Lean will happily do the rest!
            {linarith}
          }
          {linarith} -- Remember that extra subgoal from `hind`? Here it is - and it turns out it's not too bad.
        }

        { -- We have finally made it to the second subgoal of `congr_arg₂`. If we try to use `hind` again, we discover
          -- that the rest is pretty straightforward.
          rewrite [hind]
          {apply refl} -- `refl` helps us prove equality goals where the two sides are already the same thing.
                       -- `linarith` would work just fine as well, but this provides more context for someone reading the proof.
          {linarith}
        }
      }
    }
  }
