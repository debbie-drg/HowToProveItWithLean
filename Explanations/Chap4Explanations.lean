import HTPILib.HTPIDefs
namespace HTPI


-- Chapter 4: Relations --

/-
If `A` and `B` are types, `A × B` is the type of ordered pairs `(a, b) : A × B`,
where `a : A` and `b : B`. If `p = (a, b)`, then `a = p.fst`, and `b = p.snd`.
We can also write `a = p.1`, `b = p.2`, and `p = (p.1, p.2)`.
-/

/-
A relation in `A × B` is just a subset `R ⊆ A × B`. If `(a, b) ∈ R` we denote
`a R b` and say that `a` and `b` are related. Note that `R` then has type
`Set (A × B)`. We introduce some common definitions.
-/


-- Let `R` be a relation.

-- * Domain: `Dom(R) = {a ∈ A | ∃b ∈ B ((a, b) ∈ R)}`

def Dom {A B : Type} (R : Set (A × B)) : Set A :=
  { a : A | ∃ (b : B), (a, b) ∈ R }

-- * Range: `Ran(R) = {b ∈ B | ∃a ∈ A ((a, b) ∈ R)}`

def Ran {A B : Type} (R : Set (A × B)) : Set B :=
  { b : B | ∃ (a : A), (a, b) ∈ R }

-- * Inverse: `R⁻¹ = {(b, a) ∈ B × A | (a, b) ∈ R}`

def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
  { (b, a) : B × A | (a, b) ∈ R }

-- * Composition of `R` and `S`:
    -- `S ∘ R = {(a, c) ∈ A × C | ∃b ∈ B ((a, b) ∈ R and (b, c) ∈ S)}`

def comp {A B C : Type}
    (S : Set (B × C)) (R : Set (A × B)) : Set (A × C) :=
  { (a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S }

/-
This also lets us get used to the syntax of definitions in Lean.

We now have a bunch of simple results that are immediate.
-/

theorem Theorem_4_2_5_1 {A B : Type}
    (R : Set (A × B)) : inv (inv R) = R := by rfl

theorem Theorem_4_2_5_2 {A B : Type}
    (R : Set (A × B)) : Dom (inv R) = Ran R := by rfl

theorem Theorem_4_2_5_3 {A B : Type}
    (R : Set (A × B)) : Ran (inv R) = Dom R := by rfl

/-
The following are not immediate.
-/

theorem Theorem_4_2_5_4 {A B C D : Type}
    (R : Set (A × B)) (S : Set (B × C)) (T : Set (C × D)) :
    comp T (comp S R) = comp (comp T S) R := by
  apply Set.ext
  fix (a, d) : A × D
  apply Iff.intro
  · -- (→)
    assume h1 : (a, d) ∈ comp T (comp S R)
    define
    define at h1
    obtain (c : C) (h2 : (a, c) ∈ comp S R ∧ (c, d) ∈ T) from h1
    have h3 : (a, c) ∈ comp S R := h2.left
    define at h3
    obtain (b : B) (h4 : (a, b) ∈ R ∧ (b, c) ∈ S) from h3
    apply Exists.intro b
    apply And.intro h4.left
    define
    apply Exists.intro c
    apply And.intro h4.right h2.right
  · -- (←)
    assume h1 : (a, d) ∈ comp (comp T S) R
    define; define at h1
    obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, d) ∈ comp T S) from h1
    have h3 : (b, d) ∈ comp T S := h2.right
    define at h3
    obtain (c : C) (h4 : (b, c) ∈ S ∧ (c, d) ∈ T) from h3
    apply Exists.intro c
    apply And.intro _ h4.right
    define
    apply Exists.intro b
    apply And.intro h2.left h4.left
  done

/-
For the next result we need a quick result.
-/

theorem inv_def {A B : Type} (R : Set (A × B)) (a : A) (b : B) :
    (b, a) ∈ inv R ↔ (a, b) ∈ R := by rfl

/-
We can now use this result to rewrite hypotheses and goals.
-/

theorem Theorem_4_2_5_5 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) :
    inv (comp S R) = comp (inv R) (inv S) := by
  apply Set.ext
  fix (c, a) : C × A
  apply Iff.intro
  · -- (→)
    assume h1 : (c, a) ∈ inv (comp S R)
    define at h1
    define
    obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ S) from h1
    apply Exists.intro b
    rw [inv_def, inv_def]
    exact And.intro h2.right h2.left
  · -- (←)
    assume h1 : (c, a) ∈ comp (inv R) (inv S)
    define at h1
    define
    obtain (b : B) (h2 : (c, b) ∈ inv S ∧ (b, a) ∈ inv R) from h1
    apply Exists.intro b
    rw [inv_def, inv_def] at h2
    exact And.intro h2.right h2.left
  done

/-
In Lean, instead of viewing relations as `Set (A × B)` we have a type `Rel A B`.
When using this type, we denote `R a b` when `a R b` in standard mathematical
notation; that is, when `a` and `b` are related through `R`.

As before, when looking at `R a b` think that we have a proof that `a R b`.
-/

/-
We now consider extensions, establishing a correspondence between `R A B` and
`Set (A × B)`. If `R a b`, we let `R'` denote the set of all pairs `(a, b) : A × B`
such that `R a b`. Then `R'` has type `Set (A × B)`, and `R a b` and `(a, b) ∈ R'`
are equivalent for all `a` and `b`.

We say that `R` is a relation from `A` to `B` and that `R'` is the extension of `R`.
-/

def extension {A B : Type} (R : Rel A B) : Set (A × B) :=
  { (a, b) : A × B | R a b }

theorem ext_def {A B : Type} (R : Rel A B) (a : A) (b : B) :
    (a, b) ∈ extension R ↔ R a b := by rfl

/-
We now focus on relations from a set to itself, `Rel A A`, or `BinRel A`.
Some key properties about one such relation.
-/

-- * Reflexive: `R` is reflexive if `R x x` is true for all `x : A`.

def reflexive {A : Type} (R : BinRel A) : Prop :=
  ∀ (x : A), R x x

-- * Symmetric: `R` is symmetric if `R x y` and `R y x` are equivalent.

def symmetric {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y : A), R x y → R y x

-- * Transitive: `R` is transitive if `R x y` and `R y z` implies `R x z`.

def transitive {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y z : A), R x y → R y z → R x z

/-
Let us prove some basic results about these properties.
-/

-- `R` is symmetric iff `R = R⁻¹`.
theorem Theorem_4_3_4_2 {A : Type} (R : BinRel A) :
    symmetric R ↔ extension R = inv (extension R) := by
  apply Iff.intro
  · -- (→)
    assume h1 : symmetric R
    define at h1
    apply Set.ext
    fix (a, b) : A × A
    show (a, b) ∈ extension R ↔ (a, b) ∈ inv (extension R) from
      calc (a, b) ∈ extension R
        _ ↔ R a b := by rfl
        _ ↔ R b a := Iff.intro (h1 a b) (h1 b a)
        _ ↔ (a, b) ∈ inv (extension R) := by rfl
    done
  · -- (←)
    assume h1 : extension R = inv (extension R)
    define
    fix a : A; fix b : A
    assume h2 : R a b
    rewrite [←ext_def R, h1, inv_def, ext_def] at h2
    show R b a from h2
    done
  done

/-
Note we are using rewrites with ext_def and inv_def in the second part.
-/

/-
For any types `A` and `B`, if we want to define `R` a relation from `A`
to `B`, we can do it by specifying, for any `a : A` and `b : B`, what
proposition is represented by `R a b`.

For example, if `A` is a set, we can define a relation `elementhood A`
from `A` to `Set A` as follows.
-/

def elementhood (A : Type) (a : A) (X : Set A) : Prop := a ∈ X

/-
We can also use this to define an operation that reverses the process of
forming the extension of a relation. If `R` has type `Set (A × B)`, then we
define `RelFromExt R` to be the relation whose extension is `R`. We have
the following simple theorems clarifying the meaining of this
-/

def RelFromExt {A B : Type}
    (R : Set (A × B)) (a : A) (b : B) : Prop := (a, b) ∈ R

theorem RelFromExt_def {A B : Type}
    (R : Set (A × B)) (a : A) (b : B) :
    RelFromExt R a b ↔ (a, b) ∈ R := by rfl

example {A B : Type} (R : Rel A B) :
    RelFromExt (extension R) = R := by rfl

example {A B : Type} (R : Set (A × B)) :
    extension (RelFromExt R) = R := by rfl
