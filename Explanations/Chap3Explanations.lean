import HTPILib.HTPIDefs
namespace HTPI


-- Let us begin introducing proofs in term mode

theorem extremely_easy (P : Prop) (h : P) : P := h

/-
Proof in term mode. We have one assumption P wihch we call h and claim P,
so proof follows from h.

When we write `h : P` we should not just think that h is a name for P,
but rather that h is a proof of P.
-/

theorem very_easy (P Q : Prop) (h1 : P → Q) (h2 : P) : Q := h1 h2

theorem easy (P Q R : Prop) (h1 : P → Q)
    (h2 : Q → R) (h3 : P) : R := h2 (h1 h3)


/-
`h2` will help us finish if we then add a proof of Q, which we can attain
by using `h1 h3`. The parentheses are needed for otherwise Lean would
interpret (h2 h1) h3, which makes no sense.
-/

-- Now we introduce proofs in tactic mode.

/-
Assume we want to prove `P → Q`. We can do so in one of two ways:
1. Assume `P` and prove `Q`.
2. Assume `Q` is false and prove that `P` is false. 

If our goal is `P → Q`, doing assume will change the goal to `Q` and
assume `P`. We make use of this in the next proof.
-/

theorem two_imp (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  contrapos
  assume h3 : P
  have h4 : Q := h1 h3
  show ¬R from h2 h4
  done

/-
We can clearly prove `P → ¬R` but we need to prove `R → ¬P` instead, so 
we use `contrapos` to get the contrapositive. This will immediately 
chance the goal to `P → ¬R`.

If we have `h`, we can also write `contrapos at h`.
-/

theorem two_imp₂ (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  contrapos at h1
  contrapos at h2
  assume h3 : R
  have h4 : ¬Q := h2 h3
  show ¬P from h1 h4 
  done

/-
We thus have a proof where we use the contrapositive of the hypotheses
instead of doing so in the goal.
-/

/- 
Since our goal is `R → ¬P`, we can also assume `R`, and then assume `P` 
and reach a contradiction.
-/

theorem two_imp₃ (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → ¬R) : R → ¬P := by
  assume h3 : R
  by_contra h4 -- The goal now changes to False, and h4 : P
  have h5 : Q := h1 h4
  have h6 : ¬R := h2 h5
  show False from h6 h3 -- One possible way of showing a contradiction
  done

/-
`¬Q` and `Q → False` are logically equivalent, and Lean uses the second
one. That means that if we have `h1 : ¬Q` and `h2 : Q`, `h1 h2` is a proof
of `False`. 
-/

/-
In a similar manner, we can use the following tactics:
* `contrapos`:       `P → Q` is changed to `¬Q → P`.
* `demorgan`:     `¬(P ∧ Q)` is changed to `¬P ∨ ¬Q`.
                  `¬(P ∨ Q)` is changed to `¬P ∧ ¬Q`.
                     `P ∧ Q` is changed to `¬(¬P ∨ ¬Q)`.
                     `P ∨ Q` is changed to `¬(¬P ∧ ¬Q)`.
* `conditional`:     `P → Q` is changed to `¬P ∨ Q`.
                  `¬(P → Q)` is changed to `¬P → Q`.
                     `P ∨ Q` is changed to `P ∧ ¬Q`.
                     `P ∧ Q` is changed to `¬(P → ¬Q)`.
* `double_neg`:        `¬¬P` is changed to `P`.
* `bicond_neg`:   `¬(P ↔ Q)` is changed to `¬P ↔ Q`.
                     `P ↔ Q` is changed to `¬(¬P ↔ Q)`.   
-/

-- All of these tactics can be used at a given proof by using `at h`.

/-
One note about types in Lean. It won't let you say `A : Set`, it needs
further specification. For example, you can say `A : Set Nat` if a set
`A` is subset of the naturals. You can also say `A : Set (Set Nat)`,
if `A` is a `Set` whose elements are sets of natural numbers.
-/

theorem Example_3_2_5_simple
    (B C : Set Nat) (a : Nat)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2
  conditional at h2
  show a ∈ C from h2 h1
  done

/-
The define tactic changes the sentence for the definition. In this case,
it changes `¬a ∈ B \ C` for `¬(a ∈ B ∧ ¬a ∈ C)`.
-/

/-
This proof does not use the fact that the sets are natural numbers. If
we want to make it fully general, Lean will ask us to still declare a \
`Type` in which elements in the set live. We can use a varialbe to 
stand for any type, like so.
-/

theorem Example_3_2_5_simple_general
    (U : Type) (B C : Set U) (a : U)
    (h1 : a ∈ B) (h2 : a ∉ B \ C) : a ∈ C := by
  define at h2
  demorgan at h2; conditional at h2
  exact h2 h1

theorem Example_3_2_4_v2 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4 -- The goal was ¬Q, so we assume Q and aim for contradiction
  have h5 : Q → R := h h3
  have h6 : R := h5 h4
  show False from h2 h6
  done

theorem Example_3_2_4_v3 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  by_contra h4
  contradict h2 -- We set the goal to contradict h2, that is, to `R`.
  show R from h h3 h4
  done

theorem Example_3_2_4_v4 (P Q R : Prop)
    (h : P → (Q → R)) : ¬R → (P → ¬Q) := by
  assume h2 : ¬R
  assume h3 : P
  contradict h2 with h4 -- Short form of `by_contra h4; contradict h2`
  show R from h h3 h4
  done

/- 
If we have a goal of `Q` and `h : P → Q`, we can use `apply h` and change
the goal to `P`. 
-/

theorem Like_Example_3_2_5
    (U : Type) (A B C : Set U) (a : U)
    (h1 : a ∈ A) (h2 : a ∉ A \ B)
    (h3 : a ∈ B → a ∈ C) : a ∈ C := by
  apply h3
  define at h2
  demorgan at h2; conditional at h2
  show a ∈ B from h2 h1
  done

/-
Now we start introducing (existential and universal) quantifiers. 

Lean has types of predicates. `Pred U` is the type of predicates that apply
to objects of type `U`. We may want to prove something like `∃x P(x)`, meaning
that there is an element `x` such that the predicate `P` applied to `x` holds.
`P x` is then an expression of type `Prop`, a proposition.

In Lean, quantifiers apply to as much as possible:
`∀ (x : U), P x ∧ Q x` means `∀ (x : U), (P x ∧ Q x)`.
If we want the quantifier to apply just to `P x`, we need to use parentheses:
`(∀ (x : U), P x) ∧ Q x`.
-/

/-
To prove a goal of form `∀ (x : U), P x`, we need to select a variable `x` that
can be any element of type `x`. This is done in Lean with `fix x : U`.
-/

/-
To use a given of form `∀ (x : U), P x`, we can plug any value of type `U` and
conclude that `P a` is true. If we have `h : ∀ (x : U), P x`, we can have
`have h' : P a := h a` for any `a : U`.
-/

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x → ¬Q x)
    (h2 : ∀ (x : U), Q x) :
    ¬∃ (x : U), P x := by
  quant_neg -- Negates quantification, we summarize that later
  fix x : U -- Fixes an element, changes goal to prove property for that element
  have h3 : P x → ¬ Q x := h1 x
  have h4 : Q x := h2 x
  contrapos at h3
  apply h3
  exact h4
  done

/-
The effect of `quant_neg` is it changes the goal (or hypothesis `h` if `at h`)
in the following ways, by negating:
* `¬∀ (x : U), P x` 	is changed to   `∃ (x : U), ¬P x`
* `¬∃ (x : U), P x` 	is changed to   `∀ (x : U), ¬P x`
*  `∀ (x : U), P x` 	is changed to  `¬∃ (x : U), ¬P x`
*  `∃ (x : U), P x` 	is changed to  `¬∀ (x : U), ¬P x`
-/

example (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ∀ (x : U), x ∈ A → x ∉ B) : A ⊆ C := by
  fix y : U -- goal changes to `y ∈ A → y ∈ C`  
  assume h3 : y ∈ A
  have h4 : ¬y ∈ B := h2 y h3
  define at h1 -- changes union for definition
  have h5 : y ∈ B ∪ C := h1 h3
  /-
  The double braces mean we don't need to use `y`; it is an implicit argument.
  If we wanted Lean to figure out the argument in the previous step, we
  could've written `h2 _ h3`.
  -/
  define at h5
  conditional at h5
  apply h5
  exact h4
  done

/-
To prove a goal of form `∃ (x : U), P x`, we need to find a value `a` for which
`P a` is true, and prove `P a`.

If we have `a : U` and `h : P a`, then we can infer `∃ (x : U), P x` by using
`Exists.intro a h`.
-/

/-
To use a given of form `h : ∃ (x : U), P x`, we use
`obtain (u : U) (h' P u) from h`. 
-/

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), ∃ (y : U), P x → ¬ Q y)
    (h2 : ∃ (x : U), ∀ (y : U), P x → Q y) :
    ∃ (x : U), ¬P x := by
  obtain (a : U)
    (h3 : ∀ (y : U), P a → Q y) from h2
  have h4 : ∃ (y : U), P a → ¬ Q y := h1 a
  obtain (b : U) (h5 : P a → ¬ Q b ) from h4
  have h6 : P a → Q b := h3 b
  apply Exists.intro a _
  by_contra h7 -- We have P a implies both Q b and ¬Q b
  show False from h5 h7 (h6 h7)
  done

theorem Example_3_3_5 (U : Type) (B : Set U)
    (F : Set (Set U)) : ⋃₀ F ⊆ B → F ⊆ 𝒫 B := by
  assume h1
  define
  fix x : Set U
  assume h2 : x ∈ F
  define
  fix y : U
  assume h3 : y ∈ x
  define at h1
  apply h1 _
  define
  apply Exists.intro x _
  exact And.intro h2 h3
  done

/-
We now move on to conjunctions and biconditionals. 
If `h1 : P` and `h2 : Q`, then `And.intro h1 h2 : P ∧ Q`. We can also write 
`⟨h1, h2⟩`. 

On the other hand, if we have `h : P ∧ Q`, we can get `h.left` as a proof of 
`P` and `h.right` as a proof of `Q`. If we have a goal like `P ∧ Q`, we can
write `apply And.intro` and we will split the goal in two. One goal will
be `P` and the other will be `Q`. We can now independently prove each of the
goals, which can potentially simplify the code if moving towards one
goal moves us away from the other.

We can also use this syntax for intersections. Namely, if `h : a ∈ A ∩ B`, 
`h.left : a ∈ A` and `h.right : a ∈ B`.
-/

theorem Like_Example_3_4_1 (U : Type)
    (A B C D : Set U) (h1 : A ⊆ B)
    (h2 : ¬∃ (c : U), c ∈ C ∩ D) :
    A ∩ C ⊆ B \ D := by
  define
  fix a : U
  assume h3 : a ∈ A ∩ C
  define
  apply And.intro -- we now have two goals: one per each element of the and
  · define at h1
    exact h1 h3.left -- this proves `a ∈ B`, closing the first subgoal
  · contradict h2 with h4
    apply Exists.intro a
    exact And.intro h3.right h4

/-
Remember that `P ↔ Q` is equivalent to `(P → Q) ∧ (Q → P)`. Thus, what 
we discussed so far can immediately be used to prove equivalences.

If `h1 : P → Q` and `h2 : Q → P`, then `Iff.intro h1 h2 : P ↔ Q`.
And conversely, `apply Iff.intro` will convert a goal of `P ↔ Q` into
two goals `P → Q` and `Q → P`. 

On the other hand, if `h : P ↔ Q`, then `h.ltr : P → Q` and `h.rtl : Q → P`.
Here, `ltr` is `left to right`; and `rtl` is `right to left`.
-/

example (U : Type) (P Q : Pred U)
    (h1 : ∀ (x : U), P x ↔ Q x) :
    (∃ (x : U), P x) ↔ ∃ (x : U), Q x := by
  apply Iff.intro
  · assume h2 : ∃ (x : U), P x
    obtain (u : U) (h3 : P u) from h2
    apply Exists.intro u
    exact (h1 u).ltr h3
  · assume h2 : ∃ (x : U), Q x
    obtain (u : U) (h3 : Q u) from h2
    show ∃ (x : U), P x from Exists.intro u ((h1 u).rtl h3)
    done 
  done

/-
We now introduce `calc`, calculational proofs. Calculational proofs consist
on a string of biconditional statements, each of which is provided with
a proof.
-/

theorem Example_3_4_5 (U : Type)
    (A B C : Set U) : A ∩ (B \ C) = (A ∩ B) \ C := by
  apply Set.ext -- set extensionality: two sets are equal iff they have the 
  -- same elements.
  fix x : U
  show x ∈ A ∩ (B \ C) ↔ x ∈ (A ∩ B) \ C from
    calc x ∈ A ∩ (B \ C)
      _ ↔ x ∈ A ∧ (x ∈ B ∧ x ∉ C) := Iff.refl _
      _ ↔ (x ∈ A ∧ x ∈ B) ∧ x ∉ C := and_assoc.symm
      _ ↔ x ∈ (A ∩ B) \ C := Iff.refl _
  done

#check Iff.refl 

/-
`Iff.refl` is just `(a : Prop) : a ↔ a`. However, Lean is smart enough to
expand definitions and still consider the proof valid if everything works out.
Using the underscore also gets Lean to try to find the proper variables. That's
why it works in the proof above, the expressions are definitionally equal and
the correct variables are inferred.

Inference of variables is also used in the remaining lines.
-/

/-
We move on to disjunctions. 

If we want to use `P ∨ Q` for a proof, one common way is to do so by 
cases. This means we first assume `P`, complete the proof, and we then do
the same assuming `Q`. This is done with the `by_cases` tactic.

If we have `h : P ∨ Q`, we do `by_cases on h`, which causes a new hypothesis
`h : P` as part of a new goal, and when completed moves on to `h : Q`.
If we want to retain the initial `h` we cando `by_cases on h with h1` and we 
will have `h1 : P` and later `h1 : Q`. Or we can even do 
`by_cases on h with h1, h2` and so we will first have `h1 : P` and later `h2 : Q`.

If the goal is of form `P ∨ Q`, it is enough to produce a proof of either
`P` or `Q`. If we have `h : P` we can finist the proof by using
`Or.intro_left Q h`, or just `Or.inl h`.
-/

theorem Example_3_5_2
    (U : Type) (A B C : Set U) :
    A \ (B \ C) ⊆ (A \ B) ∪ C := by
  define
  fix a : U
  assume h1 : a ∈ A \ (B \ C)
  define; define at h1
  have h2 : a ∈ A := h1.left
  have h3 : ¬a ∈ B \ C := h1.right
  define at h3; demorgan at h3
  by_cases on h3
  · apply Or.inl
    define
    exact ⟨h2, h3⟩
  · apply Or.inr h3 
  done

/-
Another way of proving a goal of form `P ∨ Q` is to assume `¬P` and 
prove `Q` or assume `¬Q` and prove `P`. 

This is done with `or_left with h` and `or_right with h`.
-/ 

example (U : Type) (A B C : Set U)
    (h1 : A \ B ⊆ C) : A ⊆ B ∪ C := by
  fix x : U
  assume h2 : x ∈ A
  define
  or_right with h3
  show x ∈ C from h1 (⟨h2, h3⟩)
  done

/-
Also note that `P ∨ Q` is equivalent to both `¬P → Q` and `¬Q → P`. Thus, 
if we are given `P ∨ Q` and prove `¬P`, we can prove `Q`; and if we have
`P ∨ Q` and `¬Q`, we can conclude `P`.

More concretely, if we have `h1 : P ∨ Q` and `h2 : ¬P`, `disj_syll h1 h2`
will change `h1` to `h1 : Q`. If we want to preserve the original we can
use `disj_syll h1 h2 with h3`.
-/

example
    (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B) : A ⊆ C := by
  fix a : U
  assume h3 : a ∈ A
  quant_neg at h2
  have h4 : a ∈ B ∪ C := h1 h3
  have h5 : a ∉ A ∩ B := h2 a
  define at h4
  define at h5; demorgan at h5
  disj_syll h5 h3
  disj_syll h4 h5
  exact h4
  done

/- 
Another way of proving this
-/

example
    (U : Type) (A B C : Set U) (h1 : A ⊆ B ∪ C)
    (h2 : ¬∃ (x : U), x ∈ A ∩ B) : A ⊆ C := by
  fix a : U
  assume h3 : a ∈ A
  have h4 : a ∈ B ∪ C := h1 h3
  define at h4
  have h5 : a ∉ B := by
    contradict h2 with h6
    apply Exists.intro a
    exact ⟨h3, h6⟩
  disj_syll h4 h5
  exact h4 
  done


/-
Now we review existence and uniqueness. Namely, assume that we have a 
goal `∃! (x : U), P x`.
* We can use `define` to rewrite it as 
    `∃ (x : U), P x ∧ ∀ (x_1 : U), P x_1 → x_1 = x`
  and use other techniques we've seen so far.
* Using that `P ∧ Q → R` is equivalent to `P → Q → R`, we can also prove
  `∃ (x : U), P x and ∀ (x_1 x_2 : U), P x_1 → P x_2 → x_1 = x_2`.
A exist unique goal can be split in these two goals by using the
`exists_unique` tactic.
-/

/-
We go towards the goal of proving that there is a unique set `A`
such that for every other `B`, `A ∪ B = B`. First, we show that the
empty set has this property.
-/

theorem empty_union {U : Type} (B : Set U) :
    ∅ ∪ B = B := by
  apply Set.ext
  fix x : U
  apply Iff.intro
  · assume h1
    define at h1
    have h2 : x ∉ ∅ := by
      by_contra h3
      define at h3
      exact h3
    disj_syll h1 h2
    exact h1
  · assume h1
    right
    exact h1
  done

/-
Another result we need is union commutativity
-/

theorem union_comm {U : Type} (X Y : Set U) :
    X ∪ Y = Y ∪ X := by
  ext x
  define : x ∈ X ∪ Y
  define : x ∈ Y ∪ X
  show x ∈ X ∨ x ∈ Y ↔ x ∈ Y ∪ X from or_comm
  done

/- 
Finally we prove the result.
-/

theorem Example_3_6_2 (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U),
    A ∪ B = B := by
  exists_unique
  . -- existence --
    apply Exists.intro ∅
    exact empty_union
  · -- uniqueness --
    fix C : Set U; fix D : Set U
    assume h1 : ∀ (B : Set U), C ∪ B = B
    assume h2 : ∀ (B : Set U), D ∪ B = B
    have h3 : C ∪ D = D := h1 D
    have h4 : D ∪ C = C := h2 C
    show C = D from
      calc C
        _ = D ∪ C := h4.symm 
        _ = C ∪ D := union_comm D C
        _ = D := h3
  done

/- 
Now, what if we want to use a uniqueness of existence result?
If we have `∃! (x : U), P x` we can assert the existence of an object
`a` for which `P a` is true, and also a proof of 
`∀ (x_1 x_2 : U), P x_1 → P x_2 → x_1 = x2`.

Particularly, from `h : ∃! (x : U), P x`, then the tactic 
`obtain (a : U) (h1 : P a) (h2 : ∀ (x_1 x_2 : U), P x_1 → P x_2 → x_1 = x_2) from h`.
This will introduce a new variable `a` of type `U` and new givens
`(h1 : P a)` and `(h2 : ∀ (x_1 x_2 : U), P x_1 → P x_2 → x_1 = x_2)`.
-/

theorem Example_3_6_4 (U : Type) (A B C : Set U)
    (h1 : ∃ (x : U), x ∈ A ∩ B)
    (h2 : ∃ (x : U), x ∈ A ∩ C)
    (h3 : ∃! (x : U), x ∈ A) :
    ∃ (x : U), x ∈ B ∩ C := by
  obtain (b : U) (h4 : b ∈ A ∩ B) from h1
  obtain (c : U) (h5 : c ∈ A ∩ C) from h2
  obtain (a : U) (h6 : a ∈ A) (h7 : ∀ (y z : U),
    y ∈ A → z ∈ A → y = z)  from h3
  define at h4; define at h5
  have h8 : b = c := h7 b c h4.left h5.left
  rewrite [h8] at h4 -- when provided an equivalence, Lean substitutes every
  -- ocurrence of the left side by the right side.
  show ∃ (x : U), x ∈ B ∩ C from
    Exists.intro c (And.intro h4.right h5.right)
  done


theorem union_comm₂ {U : Type} (X Y : Set U) :
    X ∪ Y = Y ∪ X := by
  apply Set.ext
  fix x : U
  define : x ∈ X ∪ Y
  define : x ∈ Y ∪ X
  -- apply? -- This makes Lean look for tactics that apply within its library.
  -- It can take a bit to process. The next line is the suggested result.
  exact Or.comm
  done

  /-
  We now get into more algebraic reasoning.

  Lean includes `Nat`, `Int`, `Rat`, `Real`, `Complex`, as well as many of the
  common symbols. For example, let us consider results on integer divisibility.
  -/

theorem Theorem_3_3_7 :
    ∀ (a b c : Int), a ∣ b → b ∣ c → a ∣ c := by
  fix a; fix b; fix c;
  assume h1 : a ∣ b; assume h2 : b ∣ c;
  define at h1; define at h2; define
  obtain (m : Int) (h3 : b = a * m) from h1
  obtain (n : Int) (h4 : c = b * n) from h2
  apply Exists.intro (m * n)
  rw [h3] at h4
  rw [mul_assoc a m n] at h4
  exact h4
  done

/-
`mul_assoc`, as expected, is a theorem stating multiplication associativity.
-/
#check mul_assoc
/-
Note that the statement is of the form `a * b * c = a * (b * c)`. We may have
expected to see `(a * b) * b` on the left hand side, but it is omitted because
that's how Lean reads it by default.
-/

theorem Theorem_3_4_7 :
    ∀ (n : Int), 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
  fix n : Int
  apply Iff.intro
  · -- (→)
    assume h1 : 6 ∣ n; define at h1
    obtain (k : Int) (h2 : n = 6 * k) from h1
    apply And.intro
    · define
      apply Exists.intro (3 * k)
      rw [← mul_assoc]
      exact h2
    · define
      apply Exists.intro (2 * k)
      rw [← mul_assoc]
      exact h2
  · -- (←)
    assume h1 : 2 ∣ n ∧ 3 ∣ n
    have h2 : 2 ∣ n := h1.left
    have h3 : 3 ∣ n := h1.right
    define at h2; define at h3; define
    obtain (j : Int) (h4 : n = 2 * j) from h2
    obtain (k : Int) (h5 : n = 3 * k) from h3
    have h6 : 6 * (j - k) = n :=
      calc 6 * (j - k)
        _ = 6 * j - 6 * k := mul_sub 6 j k
        _ = 3 * (2 * j) - 2 * (3 * k) := by
          repeat rw [← mul_assoc]
          rfl
        _ = 3 * n - 2 * n := by
          rw [← h4, ← h5]
        _ = (3 - 2) * n := (sub_mul 3 2 n).symm
        _ = n := Int.one_mul n
    apply Exists.intro (j - k)
    exact h6.symm
  done

  /-
  If a result is of the form `h : A ↔ B`, `rw [h]` will replace occurences of 
  `A` with `B`. If we want to do it the other way around (right to left), 
  we can do so by writting `rw [← h]`. This is what we are doing above with
  `rw [← mul_assoc]`. 
  -/

  /- The calc proof can be made significantly shorter by using the `ring`
  technique, which tries to prove equalities using ring properties. -/

  theorem Theorem_3_4_7₁ :
    ∀ (n : Int), 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
  fix n : Int
  apply Iff.intro
  · -- (→)
    assume h1 : 6 ∣ n; define at h1
    obtain (k : Int) (h2 : n = 6 * k) from h1
    apply And.intro
    · define
      apply Exists.intro (3 * k)
      rw [← mul_assoc]
      exact h2
    · define
      apply Exists.intro (2 * k)
      rw [← mul_assoc]
      exact h2
  · -- (←)
    assume h1 : 2 ∣ n ∧ 3 ∣ n
    have h2 : 2 ∣ n := h1.left
    have h3 : 3 ∣ n := h1.right
    define at h2; define at h3; define
    obtain (j : Int) (h4 : n = 2 * j) from h2
    obtain (k : Int) (h5 : n = 3 * k) from h3
    have h6 : 6 * (j - k) = n :=
      calc 6 * (j - k)
        _ = 3 * (2 * j) - 2 * (3 * k) := by ring
        _ = 3 * n - 2 * n := by rw [← h4, ← h5]
        _ = n := by ring
    apply Exists.intro (j - k)
    exact h6.symm
  done

/-
One last example.
-/

theorem Example_3_5_4 (x : Real) (h1 : x ≤ x ^ 2) : x ≤ 0 ∨ 1 ≤ x := by
  or_right with h2     --h2 : ¬x ≤ 0;  Goal : 1 ≤ x
  have h3 : 0 < x := lt_of_not_le h2
  have h4 : 1 * x ≤ x * x :=
    calc 1 * x
      _ = x := one_mul x
      _ ≤ x ^ 2 := h1
      _ = x * x := by ring
  show 1 ≤ x := le_of_mul_le_mul_right h4 h3
