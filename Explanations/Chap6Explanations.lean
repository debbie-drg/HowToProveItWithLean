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


-- Section 6.3. Recursion

/-
Similarly to how we can use induction to prove a property for all natural
numbers, recursion let us define a function for all natural numbers.
Essentially, we specify the value of `f 0` and a way to determine the
value of `f (n + 1)` if we know `f n`. We can do so with match expressions.
-/

-- Factorial function
def fact (k : Nat) : Nat :=
  match k with
    | 0 => 1
    | n + 1 => (n + 1) * fact n

#eval fact 4 -- 24

/-
This is a recursive definition. When proving results about one such function,
it is quite common to use induction.
-/

theorem Example_6_3_1 : ∀ n ≥ 4, fact n > 2 ^ n := by
  by_induc
  · -- Base case
    norm_num
  · -- Induction step
    fix n : ℕ
    assume h1 : n ≥ 4
    have h2 : n + 1 > 0 := by linarith
    have h3 : 2 > 0 := by linarith
    have h4 : 2 ^ n > 0 := Nat.pos_pow_of_pos n h3
    have h5 : n + 1 > 2 := by linarith
    assume ih : fact n > 2 ^ n
    show fact (n + 1) > 2 ^ (n + 1) from
      calc fact (n + 1)
        _ = (n + 1) * fact n := by rfl
        _ > (n + 1) * 2 ^ n := Nat.mul_lt_mul_of_pos_left ih h2
        _ > 2 * 2 ^ n := Nat.mul_lt_mul_of_pos_right h5 h4
        _ = 2 ^ (n + 1) := by ring
  done

/-
This, however, can be made simpler. If `h` is a proof of a statement asserting
a relation between two tactics, `rel [h]` will attempt to prove any statement
obtained from that relationship by applying the same operation to both
sides. Note that this does not always succeed.
-/

theorem Example_6_3_1₁ : ∀ n ≥ 4, fact n > 2 ^ n := by
  by_induc
  · -- Base case
    norm_num
  · -- Induction step
    fix n : ℕ
    assume h1 : n ≥ 4
    assume ih : fact n > 2 ^ n
    have h2 : n + 1 > 2 := by linarith
    show fact (n + 1) > 2 ^ (n + 1) from
      calc fact (n + 1)
        _ = (n + 1) * fact n := by rfl
        _ > (n + 1) * 2 ^ n := by rel [ih]
        _ > 2 * 2 ^ n := by rel [h2]
        _ = 2 ^ (n + 1) := by ring
  done

/-
We now prove one of the lays of exponents: `a ^ (m + n) = a ^ m * a ^ n`.
Lean's definition is recursive, and uses different definitiosn depending on
the type of the base.
-/

--For natural numbers b and k, b ^ k = nat_pow b k:
def nat_pow (b k : Nat) : Nat :=
  match k with
    | 0 => 1
    | n + 1 => (nat_pow b n) * b

--For a real number b and a natural number k, b ^ k = real_pow b k:
def real_pow (b : Real) (k : Nat) : Real :=
  match k with
    | 0 => 1
    | n + 1 => b * (real_pow b n)

/-
Now note that the `ring` tactic can easilly solve our goal.
-/

theorem Example_6_3_2_cheating : ∀ (a : Real) (m n : Nat),
    a ^ (m + n) = a ^ m * a ^ n := by
  fix a : Real; fix m : Nat; fix n : Nat
  ring
  done

/-
However, to illustrate, let us do it using induction.
-/

theorem Example_6_3_2 : ∀ (a : Real) (m n : Nat),
    a ^ (m + n) = a ^ m * a ^ n := by
  fix a : ℝ; fix m : ℕ
  by_induc
  · -- Base case
    show a ^ (m + 0) = a ^ m * a ^ 0 from
      calc a ^ (m + 0)
        _ = a ^ m := by rfl
        _ = a ^ m * 1 := (mul_one (a ^ m)).symm
        _ = a ^ m * a ^ 0 := by rfl
  · -- Induction step
    fix n : ℕ
    assume ih : a ^ (m + n) = a ^ m * a ^ n
    show a ^ (m + (n + 1)) = a ^ m * a ^ (n + 1) from
      calc a ^ (m + (n + 1))
        _ = a ^ ((m + n) + 1) := by rw [add_assoc]
        _ = a * a ^ (m + n) := by rfl
        _ = a * (a ^ m * a ^ n) := by rw [ih]
        _ = a ^ m * (a * a ^ n) := by
          rw [← mul_assoc, mul_comm a, mul_assoc]
        _ = a ^ m * (a ^ (n + 1)) := by rfl
  done

/-
Let us prove one more theorem.

Now note that, quite often, Lean will coerce natural numbers to real
numbers in order to perform operations between naturals and reals. For
example, we can see notation such as `↑0`, denoting that `0` is coerced.
However, this should be equal to the real `0`, We have a result to do
that, called `Nat.cast_zero`.

Similarly, `Nat.cast_succ` proves that `↑(n + 1) = ↑n + 1`.
-/

theorem Example_6_3_4 : ∀ (x : Real), x > -1 →
    ∀ (n : Nat), (1 + x) ^ n ≥ 1 + n * x := by
  fix x : Real
  assume h1 : x > -1
  by_induc
  · -- Base case
    rw [Nat.cast_zero]
    linarith
  · -- Induction step
    fix n : ℕ
    assume ih : (1 + x) ^ n ≥ 1 + n * x
    have h2 : 0 ≤ 1 + x := by linarith -- Otherwise `rel [ih]` fails.
    have h3 : x ^ 2 ≥ 0 := sq_nonneg x
    have h4 : n * x ^ 2 ≥ 0 :=
      calc n * x ^ 2
        _ ≥ n * 0 := by rel [h3]
        _ = 0 := by ring
    rw [Nat.cast_succ]
    show (1 + x) ^ (n + 1) ≥ 1 + (n + 1) * x from
      calc (1 + x) ^ (n + 1)
        _ = (1 + x) * (1 + x) ^ n := by rfl
        _ ≥ (1 + x) * (1 + n * x) := by rel [ih]
        _ ≥ 1 + x + n * x + 0 := by linarith
        _ = 1 + (n + 1) * x := by ring
  done

/-
Note that `h2`, `h3`, and `h4` were added as needed when performing the
`calc` step.
-/

/-
Finally, let us briefly mention how `Sum i from k to n, f i` is defined.
The key is a function called `sum_seq`, defined by recursion.
-/

def sum_seq₁ {A : Type} [AddZeroClass A]
    (m k : Nat) (f : Nat → A) : A :=
  match m with
    | 0 => 0
    | n + 1 => sum_seq n k f + f (k + n)

/-
To ge an idea, we can evaluate `sum_seq 3 k f`.

sum_seq 3 k f = sum_seq 2 k f + f (k + 2)
              = sum_seq 1 k f + f (k + 1) + f (k + 2)
              = sum_seq 0 k f + f (k + 0) + f (k + 1) + f (k + 2)
              = 0 + f (k + 0) + f (k + 1) + f (k + 2)
              = f k + f (k + 1) + f (k + 2).
-/

/-
So we add three consecutive values of `f`, starting with `f k`. The
notation `Sum i from k to n, f i` is just defined to be
`sum_seq (n + 1 - k) k f`.
-/


-- Section 6.4. Strong induction

/-
In strong induction, instead of assuming a property for `n` and proving it
for `n + 1`, we assume it for every number up to and including `n`. Thus,
to prove a goal of form `∀ (n : ℕ), P n`, we prove
`∀ (n : ℕ), (∀ n_1 < n, P n_1) → P n`.

This can be done with the tactic `by_strong_induc`. Let us illustrate.

We prove the existence of divisor and remainder in the integer division.
-/

theorem Example_6_4_1 : ∀ m > 0, ∀ (n : Nat),
    ∃ (q r : Nat), n = m * q + r ∧ r < m := by
  fix m : ℕ; assume h1 : m > 0
  by_strong_induc
  fix n : ℕ; assume ih : ∀ (n_1 : ℕ), n_1 < n
    → ∃ (q : ℕ), ∃ (r : ℕ), n_1 = m * q + r ∧ r < m
  by_cases h2 : n < m
  · -- Case n < m
    apply Exists.intro 0
    apply Exists.intro n
    apply And.intro _ h2
    rw [mul_zero, zero_add]
  · -- Case ¬n < m
    have h3 : m ≤ n := by linarith
    obtain (k : Nat) (h4 : n = k + m) from Nat.exists_eq_add_of_le' h3
    have h5 : k < n := by linarith
    have h6 : ∃ (q r : Nat), k = m * q + r ∧ r < m := ih k h5
    obtain (q' : Nat)
      (h7 : ∃ (r : Nat), k = m * q' + r ∧ r < m) from h6
    obtain (r' : Nat) (h8 : k = m * q' + r' ∧ r' < m) from h7
    apply Exists.intro (q' + 1)
    apply Exists.intro r'     --Goal : n = m * (q' + 1) + r' ∧ r' < m
    apply And.intro _ h8.right
    show n = m * (q' + 1) + r' from
      calc n
        _ = k + m := h4
        _ = m * q' + r' + m := by rw [h8.left]
        _ = m * (q' + 1) + r' := by ring
  done

/-
Here, we are using the following results of the naturals.
-/

#check Nat.exists_eq_add_of_le
  -- ∀ {m n : ℕ}, m ≤ n → ∃ (k : ℕ), n = m + k

#check Nat.exists_eq_add_of_le'
  -- ∀ {m n : ℕ}, m ≤ n → ∃ (k : ℕ), n = k + m

/-
The integer division operator is just the integer quotient in Lean, `n / m`.
The remainder can be obtained by `n % m`.
Note that Lean already includes results on the properties of these numbers
-/

#check Nat.div_add_mod
  -- ∀ (m n : ℕ), n * (m / n) + m % n = m

#check Nat.mod_lt
  -- ∀ (x : ℕ) {y : ℕ}, y > 0 → x % y < y

/-
Note that Lean uses the definitions `n / 0 = 0` and `n % 0 = n`, which makes
adding additional requirements to the results above unnecessary.

If we instead want to obtain division of reals we instead explicitly
declare the types: `(5 : Real) / (2 : Real)` is `2.5`.
-/

/-
There is also a strong version of recursion. To show this, let us introduce
the definition for the Fibonacci sequence.
-/

def Fib (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 1
    | k + 2 => Fib k + Fib (k + 1)

/-
The induction is strong as we need the two previous terms, and not just
the last one. Let us prove that `Fib n < 2 ^ n` by strong induction.
To do so, we need to use the following pre-existing results.
-/

#check Nat.pos_of_ne_zero
  -- ∀ {n : ℕ}, n ≠ 0 → 0 < n

#check lt_of_le_of_ne
  -- ∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
                    -- a ≤ b → a ≠ b → a < b

#check lt_of_le_of_ne'
  -- ∀ {α : Type u_1} [inst : PartialOrder α] {a b : α},
                    -- a ≤ b → b ≠ a → a < b

/-
Note further that Lean treats `a < b` as meaning `a + 1 ≤ b`.
-/

lemma exists_eq_add_one_of_ne_zero {n : Nat}
    (h1 : n ≠ 0) : ∃ (k : Nat), n = k + 1 := by
  have h2 : 1 ≤ n := Nat.pos_of_ne_zero h1
  exact Nat.exists_eq_add_of_le' h2
  done

theorem exists_eq_add_two_of_ne_zero_one {n : Nat}
    (h1 : n ≠ 0) (h2 : n ≠ 1) : ∃ (k : Nat), n = k + 2 := by
  have h3 : 1 ≤ n := Nat.pos_of_ne_zero h1
  have h4 : 2 ≤ n := lt_of_le_of_ne' h3 h2
  exact Nat.exists_eq_add_of_le' h4
  done

/-
We can now proceed to proving the result.
-/

example : ∀ (n : Nat), Fib n < 2 ^ n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n₁ : ℕ), n₁ < n → Fib n₁ < 2 ^ n₁
  by_cases h1 : n = 0
  · -- Case n = 0
    rw [h1]; norm_num
  · -- Case ¬n = 0
    by_cases h2 : n = 1
    · -- Case n = 1
      rw [h2]; norm_num
    · -- Case ¬n = 1. We now have n ≥ 2
      obtain (k : Nat) (h3 : n = k + 2) from
        exists_eq_add_two_of_ne_zero_one h1 h2
      have h4 : k < n := by linarith
      have h5 : Fib k < 2 ^ k := ih k h4
      have h6 : k + 1 < n := by linarith
      have h7 : Fib (k + 1) < 2 ^ (k + 1) := ih (k + 1) h6
      rw [h3]
      show Fib (k + 2) < 2 ^ (k + 2) from
        calc Fib (k + 2)
          _ = Fib k + Fib (k + 1) := by rfl
          _ < 2 ^ k + Fib (k + 1) := by rel [h5]
          _ < 2 ^ k + 2 ^ (k + 1) := by rel [h7]
          _ ≤ 2 ^ k + 2 ^ (k + 1) + 2 ^ k := by linarith
          _ = 2 ^ (k + 2) := by ring
  done

/-
Strong induction can also be used to prove results that may not seem to
have form `∀ (n : Nat), ...` at first. We illustrate that by showing that
ℕ is well-ordered. That is, we show that if `S : Set Nat` is non-empty
it has a smallest element. We prove the contrapositive.
-/

theorem well_ord_princ (S : Set Nat) : (∃ (n : Nat), n ∈ S) →
    ∃ (n : Nat), n ∈ S ∧ ∀ (m : Nat), m ∈ S → n ≤ m := by
  contrapos
  assume h1 : ¬∃ (n : ℕ), n ∈ S ∧ ∀ (m : ℕ), m ∈ S → n ≤ m
  quant_neg
  by_strong_induc
  fix n : ℕ
  assume ih : ∀ (n_1 : ℕ), n_1 < n → ¬n_1 ∈ S
  contradict h1 with h2
  apply Exists.intro n
  apply And.intro h2
  fix m : ℕ
  assume h3 : m ∈ S
  have h4 : m < n → ¬m ∈ S := ih m
  contrapos at h4
  have h5 : ¬m < n := h4 h3
  linarith
  done

/-
Using the well ordering principle, we can show that the square root of
two is irrational. The procedure is as follows: if `√2` were rational,
there would exist `p` and `q` naturals such that `q ≠ 0` and `p / q = √2`.
Therefore, `p² = 2q²`. So we can prove that `√2` is irrational by proving
that two such naturals cannot exist.

We use the even definition, which was introduced in the exercises for
Section 6.1
-/

def nat_even (n : Nat) : Prop := ∃ (k : Nat), n = 2 * k

/-
We also use the following lemma, whose proof is in the exercises.
-/

lemma sq_even_iff_even (n : Nat) : nat_even (n * n) ↔ nat_even n := by
  sorry

/-
We also need the following theorem.
-/

#check mul_left_cancel_iff_of_pos
  -- ∀ {α : Type u_1} {a b c : α}
            --  [inst : MulZeroClass α] [inst_1 : PartialOrder α]
            --  [inst_2 : PosMulMonoRev α],
            --  0 < a → (a * b = a * c ↔ b = c)

/-
Proving that `√2` is irrational means proving that
`¬∃ (q p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0`
Equivalently, we can prove that the set
`S = { q : Nat | ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 }`
is empty. We can do so by contradiction. If we assumed that it was
non-empty, by the well-ordering principle it would have a smallest element.
We show that this leads to a contradiction.
-/

theorem Theorem_6_4_5 :
    ¬∃ (q p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 := by
  set S : Set Nat :=
    { q : Nat | ∃ (p : Nat), p * p = 2 * (q * q) ∧ q ≠ 0 }
  by_contra h1
  have h2 : ∃ (q : Nat), q ∈ S := h1
  have h3 : ∃ (q : Nat), q ∈ S ∧ ∀ (r : Nat), r ∈ S → q ≤ r :=
    well_ord_princ S h2
  obtain (q : Nat) (h4 : q ∈ S ∧ ∀ (r : Nat), r ∈ S → q ≤ r) from h3
  have qinS : q ∈ S := h4.left
  have qleast : ∀ (r : ℕ), r ∈ S → q ≤ r := h4.right
  define at qinS
  obtain (p : Nat) (h5 : p * p = 2 * (q * q) ∧ q ≠ 0) from qinS
  have pqsqrt2 : p * p = 2 * (q * q) := h5.left
  have qne0 : q ≠ 0 := h5.right
  have h6 : nat_even (p * p) := Exists.intro (q * q) pqsqrt2
  rw [sq_even_iff_even p] at h6
  obtain (p' : Nat) (p'halfp : p = 2 * p') from h6
  have h7 : 2 * (2 * (p' * p')) = 2 * (q * q) := by
    rw [←pqsqrt2, p'halfp]
    ring
  have h8 : 2 > 0 := by norm_num
  rw [mul_left_cancel_iff_of_pos h8] at h7
  have h9 : nat_even (q * q) := Exists.intro (p' * p') h7.symm
  rw [sq_even_iff_even q] at h9
  obtain (q' : Nat) (q'halfq : q = 2 * q') from h9
  have h10 : 2 * (p' * p') = 2 * (2 * (q' * q')) := by
    rw [h7, q'halfq]
    ring
  rw [mul_left_cancel_iff_of_pos h8] at h10
  have q'ne0 : q' ≠ 0 := by
    contradict qne0 with h11
    rw [q'halfq, h11]
  have q'inS : q' ∈ S := Exists.intro p' (And.intro h10 q'ne0)
  have qleq' : q ≤ q' := qleast q' q'inS
  rewrite [q'halfq] at qleq'
  contradict q'ne0
  linarith
  done
