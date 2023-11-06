import HTPILib.HTPIDefs
import HTPILib.Chap8Part1

namespace HTPI

-- Chapter ^: Mathematical induction --


-- Section 6.1. Proof by Mathematical Induction

/-
Mathematical induction is used to prove goals of the form
`∀ (n : Nat), P n`
by proving `P 0` and `∀ (n : Nat), P n → P (n + 1)`. These are respectively
called the "base step" and the "induction step".

Lean has the tactic `by_induc`. When used towards a goal of form `∀ (n : Nat), P n`,
the givens are unchanged, but the goal is replaced by two goals: the
base case goal and the induction step goal. We illustrate with an example.
-/

theorem Like_Example_6_1_2 :
    ∀ (n : Nat), 3 ∣ n ^ 3 + 2 * n := by
  by_induc
  · define
    apply Exists.intro 0
    rfl
  · fix n : ℕ
    assume ih : 3 ∣ n ^ 3 + 2 * n -- induction hypothesis
    define at ih
    obtain (k : ℕ) (h1 : n ^ 3 + 2 * n = 3 * k) from ih
    define
    apply Exists.intro (k + n ^ 2 + n + 1)
    show (n + 1) ^ 3 + 2 * (n + 1) = 3 * (k + n ^ 2 + n + 1) from
      calc (n + 1) ^ 3 + 2 * (n + 1)
        _ = n ^ 3 + 2 * n + 3 * n ^ 2 + 3 * n + 3 := by ring
        _ = 3 * k + 3 * n ^ 2 + 3 * n + 3 := by rw [h1]
        _ = 3 * (k + n ^ 2 + n + 1) := by ring
  done

/-
We now use an example which involves a sum over an index. In Lean, the
notation for that is `Sum i from k to n, f i`
-/

/-
To use induction to prove results involving sums, we can use the following:
-/

#check sum_base
/- @sum_base : ∀ {A : Type} [inst : AddZeroClass A] {k : ℕ} {f : ℕ → A},
            Sum i from k to k, f i = f k -/

#check sum_step
/-
@sum_step : ∀ {A : Type} [inst : AddZeroClass A] {k n : ℕ} {f : ℕ → A},
            k ≤ n → Sum i from k to n + 1, f i =
              (Sum i from k to n, f i) + f (n + 1) -/

#check sum_from_zero_step
/- ∀ {A : Type} [inst : AddZeroClass A] {n : ℕ} {f : ℕ → A},
            Sum i from 0 to n + 1, f i =
              (Sum i from 0 to n, f i) + f (n + 1) -/


theorem Like_Example_6_1_1 :
    ∀ (n : Nat), (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1) := by
  by_induc
  · -- Base case
    rw [sum_base]
    rfl
    done
  · -- Induction step
    fix n : ℕ
    assume ih : (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1)
    show (Sum i from 0 to n + 1, 2 ^ i) + 1 = 2 ^ (n + 1 + 1) from
      calc (Sum i from 0 to n + 1, 2 ^ i) + 1
        _ = (Sum i from 0 to n, 2 ^ i) + 2 ^ (n + 1) + 1 := by rw [sum_from_zero_step]
        _ = (Sum i from 0 to n, 2 ^ i) + 1 + 2 ^ (n + 1) := by ring
        _ = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [ih]
        _ = 2 ^ (n + 2) := by ring
  done

/-
One further example. The next example will use two tactics we have not yet
encountered.

* `norm_num`: evaluation of arithmetic expressions like *, +, -, ^, ≤.
* `linarith`: makes inferences that involve combining linear equations and inequalities.
-/
theorem Example_6_1_3 : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
  by_induc
  · -- Base case
    norm_num
  · -- Induction step
    fix n : ℕ
    assume h1 : n ≥ 5
    assume ih : 2 ^ n > n ^ 2
    have h2 : n * n ≥ n * 5 := ge_iff_le.mpr (Nat.mul_le_mul_left n h1)
    show 2 ^ (n + 1) > (n + 1) ^ 2 from
      calc 2 ^ (n + 1)
        _ = 2 * 2 ^ n := by ring
        _ > 2 * n ^ 2 := by linarith
        _ ≥ n ^ 2  + 5 * n := by linarith
        _ > n ^ 2 + 2 * n + 1 := by linarith
        _ = (n + 1) ^ 2 := by ring
  done

/-
Note that since we are using natural numbers, we need to avoid subtractions
that could be negative, as we will not get what we expect.
-/

#eval 2 - 3 -- returns 0

/-
We can avoid this problem by specifying that the used numbers are integers,
which we can do by using `(2 : Int)`. Substraction of integers behaves
as it should.
-/

#eval (2 : Int) - 3 -- returns -1

theorem Example_6_1_1 :
    ∀ (n : Nat), Sum i from 0 to n, (2 : Int) ^ i =
    (2 : Int) ^ (n + 1) - (1 : Int) := by
  by_induc
  · -- Base case
    rw [sum_base]
    rfl
  · -- Induction step
    fix n : ℕ
    assume ih : Sum i from 0 to n, (2 : Int) ^ i = (2 : Int) ^ (n + 1) - 1
    show Sum i from 0 to n + 1, (2 : Int) ^ i = (2 : Int) ^ (n + 1 + 1) - (1 : Int) from
      calc Sum i from 0 to n + 1, (2 : Int) ^ i
        _ = (Sum i from 0 to n, (2 : Int) ^ i) + (2 : Int) ^ (n + 1) := by rw [sum_from_zero_step]
        _ = (2 : Int) ^ (n + 1) - 1 + (2 : Int) ^ (n + 1) := by rw [ih]
        _ = (2 : Int) ^ (n + 1 + 1) - (1 : Int) := by ring
  done

/-
Without the Int typing, the result would be false.
-/


-- Section 6.2. More examples

/-
Mathematical induction is useful in many more settings, and not just in
proves involving calculatuions with natural numbers. We shall now see some
illustrations of that.

For example, we can prove that a property is verified for all finite sets
by using induction. We can prove it for sets of `0` or `1` elements as a
base case, and then assuming that the property holds for sets of `n`
elements, prove it for sets of `n + 1` elements. But what does it mean for
a set to have `n` elements?

We will explicitly prove theorems about it in Chapter 8, but for now here
are the theorems we will need for this section.
-/

-- The empty set is the only set with zero elements
#check zero_elts_iff_empty
    -- ∀ {U : Type} (A : Set U), numElts A 0 ↔ empty A

-- Only the singletons have one element
#check one_elt_iff_singleton
    -- ∀ {U : Type} (A : Set U), numElts A 1 ↔ ∃ (x : U), A = {x}

-- Nonempty sets have elements
#check nonempty_of_pos_numElts
    -- ∀ {U : Type} {A : Set U} {n : ℕ}, numElts A n → n > 0 → ∃ (x : U), x ∈ A

-- If you remove an element from a set with `n + 1` elements, you get a
-- set with `n` elements.
#check remove_one_numElts
    -- ∀ {U : Type} {A : Set U} {n : ℕ} {a : U}, numElts A (n + 1) → a ∈ A → numElts (A \ {a}) n

/-
Let us begin with an example: if `R` is a partial order on `A`, every
finite, nonempty subset of `A` has an `R`-minimal element.
-/

/-
We are going to need some lemmas to build up to the proof.
-/

/-
This first lemma says that if an element is below the minimal element of a
set, it is the minimal element of the set obtained by adding that element.
-/
lemma Lemma_6_2_1_1 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : R b c) : minimalElt R b B := by
  define at h3
  define
  apply And.intro h2
  contradict h3.right with h5
  obtain (x : A) (h6 : x ∈ B ∧ R x b ∧ x ≠ b) from h5
  apply Exists.intro x
  apply And.intro
  · exact And.intro h6.left h6.right.right
  · have Rtrans : transitive R := h1.right.left
    have h7 : R x c := Rtrans x b c h6.right.left h4
    apply And.intro h7
    by_contra h8
    rw [h8] at h6
    have Rantisymm : antisymmetric R := h1.right.right
    have h9 : c = b := Rantisymm c b h6.right.left h4
    show False from h6.right.right h9
  done

/-
We also need a lemma stating that if an element is not greater than
the minimal of a set, it is minimal in the union.
-/
lemma Lemma_6_2_1_2 {A : Type} {R : BinRel A} {B : Set A} {b c : A}
    (h1 : partial_order R) (h2 : b ∈ B) (h3 : minimalElt R c (B \ {b}))
    (h4 : ¬R b c) : minimalElt R c B := by
  define at h3
  define
  apply And.intro h3.left.left
  contradict h3.right with h5
  obtain (x : A) (h6 : x ∈ B ∧ R x c ∧ x ≠ c) from h5
  apply Exists.intro x
  apply And.intro
  · apply And.intro h6.left
    by_contra h7
    define at h7
    rw [h7] at h6
    show False from h4 h6.right.left
  · exact h6.right
  done

/-
Now we can finish proving the result.
-/

theorem Example_6_2_1 {A : Type} (R : BinRel A) (h : partial_order R) :
    ∀ n ≥ 1, ∀ (B : Set A), numElts B n →
      ∃ (x : A), minimalElt R x B := by
  by_induc
  · -- Base case
    fix B : Set A
    assume h1 : numElts B 1
    rw [one_elt_iff_singleton] at h1
    obtain (x : A) (h2 : B = {x}) from h1
    apply Exists.intro x
    define
    apply And.intro
    · rewrite [h2]; rfl
    · by_contra h3
      obtain (y : A) (h4 : y ∈ B ∧ R y x ∧ y ≠ x) from h3
      have h5 : y ∈ B := h4.left
      rw [h2] at h5
      show False from h4.right.right h5
  · -- Induction step
    fix n : ℕ
    assume h1 : n ≥ 1
    assume ih : ∀ (B : Set A), numElts B n → ∃ (x : A), minimalElt R x B
    fix B : Set A
    assume h2 : numElts B (n + 1)
    have h3 : n + 1 > 0 := by linarith
    obtain (b : A) (h4 : b ∈ B) from nonempty_of_pos_numElts h2 h3
    set B' : Set A := B \ {b}
    have h5 : numElts B' n := remove_one_numElts h2 h4
    have h6 : ∃ (x : A), minimalElt R x B' := ih B' h5
    obtain (c : A) (h7 : minimalElt R c B') from h6
    by_cases h8 : R b c
    · apply Exists.intro b; exact Lemma_6_2_1_1 h h4 h7 h8
    · apply Exists.intro c; exact Lemma_6_2_1_2 h h4 h7 h8
  done

/-
We now show a result stating that partial orders on a finite set can
be extended to total orders. We first need to introduce some additional
terminology.

Let `R` be a partial order relation. We say that `b` is R-comparable to
everything if `∀ (x : A), R b x ∨ R x b`. If `B` is a set of objects of `A`,
we say that `B` is R-comparable to everything if every element of `B` is
R-comparable to everything; that is, if `∀ b ∈ B, ∀ (x : A), R b x ∨ R x b`.

Finally, we say that another binary relation `T` extends `R` if
`∀ (x y : A), R x y → T x y`. We are going to prove that for every `R` and
every finite set `B` there exists a `T` that extends `R` and such that `B`
is T-comparable with everything.
-/

/-
Our first step will be proving it with `B` being a singleton, `B = {b}`.
We thus need that for all `a : A`, either `T a b` or `T b a`.

Since `T` has to be an extension of `R`, we know that `T x y` if `R x y`.
To this, we need to add the relations in which `b` will be involved.

Now, of course, if `R x b`, `T x b`. We could think of adding `T b x` if
`¬R x b`. However, `T` must be transitive, thus if we have `R x b` and
`¬R y b` we would have `T x b` and `T b y`, thus we have `T x y`. Let's
try to use this to define our extension.
-/

def extendPO {A : Type} (R : BinRel A) (b : A) (x y : A) : Prop :=
  R x y ∨ (R x b ∧ ¬R y b)

/-
We need to prove that it is a partial order.
-/

lemma extendPO_is_ref {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : reflexive (extendPO R b) := by
  define
  fix x : A
  define
  left
  exact h.left x
  done

lemma extendPO_is_trans {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : transitive (extendPO R b) := by
  define; fix x : A; fix y : A; fix z : A
  assume h1 : extendPO R b x y
  assume h2 : extendPO R b y z
  define at h1; define at h2; define; define at h
  have Rtrans : transitive R := h.right.left
  by_cases on h1
  · by_cases on h2
    · left
      exact Rtrans x y z h1 h2
    · right
      have h3 : R x b := Rtrans x y b h1 h2.left
      exact And.intro h3 h2.right
  · by_cases on h2
    · right
      apply And.intro h1.left
      by_contra h3
      have h4 : R y b := Rtrans y z b h2 h3
      show False from h1.right h4
    · right
      exact And.intro h1.left h2.right
  done

lemma extendPO_is_antisymm {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : antisymmetric (extendPO R b) := by
  define; fix x : A; fix y : A
  define at h; have Rantisymm : antisymmetric R := h.right.right
  have Rtrans : transitive R := h.right.left
  assume h1 : extendPO R b x y
  assume h2 : extendPO R b y x
  define at h1; define at h2
  by_cases on h1
  · by_cases on h2
    · exact Rantisymm x y h1 h2
    · have h3 : R x b := Rtrans x y b h1 h2.left
      by_contra; show False from h2.right h3
  · by_cases on h2
    · have h3 : R y b := Rtrans y x b h2 h1.left
      by_contra; show False from h1.right h3
    · by_contra; show False from h1.right h2.left
  done

/-
Of course, it is now immediate that we have a partial order.
-/

lemma extendPO_is_po {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : partial_order (extendPO R b) :=
  And.intro (extendPO_is_ref R b h)
    (And.intro (extendPO_is_trans R b h) (extendPO_is_antisymm R b h))

/-
And also that `extendPO R b` extends `R`.
-/
lemma extendPO_extends {A : Type} (R : BinRel A) (b : A) (x y : A) :
    R x y → extendPO R b x y := by
  assume h1 : R x y
  define
  left; exact h1
  done

/-
Finally, it makes `b` comparable with everything.
-/
lemma extendPO_all_comp {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) :
    ∀ (x : A), extendPO R b b x ∨ extendPO R b x b := by
  have Rref : reflexive R := h.left
  fix x : A
  or_left with h1
  define at h1; demorgan at h1
  define
  right
  exact And.intro (Rref b) h1.left
  done

/-
And now we can prove the actual result.
-/

theorem Exercise_6_2_2 {A : Type} (R : BinRel A) (h : partial_order R) :
    ∀ (n : Nat) (B : Set A), numElts B n → ∃ (T : BinRel A),
    partial_order T ∧ (∀ (x y : A), R x y → T x y) ∧
    ∀ x ∈ B, ∀ (y : A), T x y ∨ T y x := by
  by_induc
  · -- Base case
    fix B : Set A
    assume h1 : numElts B 0
    rewrite [zero_elts_iff_empty] at h1
    define at h1
    apply Exists.intro R
    apply And.intro h
    apply And.intro
    · fix x : A; fix y : A; assume h2 : R x y; exact h2
    · fix x : A; assume h2 : x ∈ B
      contradict h1
      apply Exists.intro x; exact h2
  · -- Induction step
    fix n : ℕ
    assume ih : ∀ (B : Set A), numElts B n → ∃ (T : BinRel A),
      partial_order T ∧ (∀ (x y : A), R x y → T x y) ∧
      ∀ (x : A), x ∈ B → ∀ (y : A), T x y ∨ T y x
    fix B : Set A
    assume h1 : numElts B (n + 1)
    have h2 : n + 1 > 0 := by linarith
    obtain (b : A) (h3 : b ∈ B) from nonempty_of_pos_numElts h1 h2
    set B' : Set A := B \ {b}
    have h4 : numElts B' n := remove_one_numElts h1 h3
    have h5 : ∃ (T : BinRel A), partial_order T
      ∧ (∀ (x y : A), R x y → T x y)
        ∧ ∀ (x : A), x ∈ B' → ∀ (y : A), T x y ∨ T y x := ih B' h4
    obtain (T' : BinRel A)
      (h6 : partial_order T' ∧ (∀ (x y : A), R x y → T' x y)
        ∧ ∀ (x : A), x ∈ B' → ∀ (y : A), T' x y ∨ T' y x) from h5
    have T'po : partial_order T' := h6.left
    have T'extR : ∀ (x y : A), R x y → T' x y := h6.right.left
    have T'compB' : ∀ (x : A), x ∈ B' → ∀ (y : A), T' x y ∨ T' y x := h6.right.right
    set T : BinRel A := extendPO T' b
    apply Exists.intro T
    apply And.intro (extendPO_is_po T' b T'po)
    apply And.intro
    · fix x : A; fix y : A
      assume h7 : R x y
      have h8 : T' x y := T'extR x y h7
      exact extendPO_extends T' b x y h8
    · fix x : A; assume h7 : x ∈ B
      by_cases h8 : x = b
      · rw [h8]
        exact extendPO_all_comp T' b T'po
      · have h9 : x ∈ B' := And.intro h7 h8
        fix y : A
        have h10 : T' x y ∨ T' y x := T'compB' x h9 y
        by_cases on h10
        · left; exact extendPO_extends T' b x y h10
        · right; exact extendPO_extends T' b y x h10
  done
