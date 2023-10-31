import HTPILib.HTPIDefs
import HTPILib.Chap4
namespace HTPI



-- Chapter 5: Functions --

/-
One way of thinking about functions is to consider them as relations `F ⊆ A × B`
wheregiven `a ∈ A` there is exactly one `b ∈ B` such that `(a, b) ∈ F`. We
then introduce the notation `F(a) = b`. Functions are denoted `F : A → B`.

If we have `f : A → B`, we can think of it as an operation applied to objects
of type `A`, arriving at a type `B`. We say that `A` is the domain of `f`, and
`B` is its range. Note that `f` can be regarded as of type `A → B`, in which
case it is not a subset of `A × B`. We can still obtain the set again by
taking the `graph` of `f`, namely the ordered pairs `(a, b)` such that `f a = b`.
-/

def graph {A B : Type} (f : A → B) : Set (A × B) :=
  { (a, b) : A × B | f a = b }

theorem graph_def {A B : Type} (f : A → B) (a : A) (b : B) :
    (a, b) ∈ graph f ↔ f a = b := by rfl

/-
We can additionaly say that a relation `Set (A × B)` is the graph of a function
if and only if it has the definitional property we introduced above:
-/

def is_func_graph {A B : Type} (F : Set (A × B)) : Prop :=
  ∀ (x : A), ∃! (y : B), (x, y) ∈ F

theorem func_from_graph {A B : Type} (F : Set (A × B)) :
    (∃ (f : A → B), graph f = F) ↔ is_func_graph F := sorry

/-
The left-to-right direction is proven in the exercises. The right-to-left
requires concepts that won't be introduced until Chapter 8.
-/

/-
Using the axiom of set extensionality, it can be proven that two functions
are equal if they have equal images for all elements. However, in
Lean functions are not sets of ordered pairs, so we cannot do that.

Instead, Lean assumes the axiom of `functional extentionality` or `funext`.
Note that not every type theory has this axiom.
-/

theorem Theorem_5_1_4 {A B : Type} (f g : A → B) :
    (∀ (a : A), f a = g a) → f = g := funext

/-
Thus, if we want to prove that two sets are equal we can use `funext`
like we were using `ext` to prove equality of sets.
-/

example {A B : Type} (f g : A → B) :
    graph f = graph g → f = g := by
  assume h1 : graph f = graph g
  apply funext; fix x : A
  have h2 : (x, f x) ∈ graph f := by
    define; rfl
  rw [h1] at h2
  define at h2
  exact h2.symm
  done

/-
The axiom of extensionality for sets is that sets are completely determined
by their elements; this is what justifies our usual method of defining a set.
We can do so by specifying its elements or a rule to distinguish which elements
are in it.

Similarly, `funext` allows us to define functions by specifying the images of
every element. Here are two ways of defining a squaring function for naturals
in Lean.
-/

def square₁ (n : Nat) : Nat := n ^ 2

def square₂ : Nat → Nat := fun (n : Nat) => n ^ 2

/-
The furst expression says we have an argument of type `Nat` and an output of
type `Nat`. The second expression says we have an argument of type
`Nat → Nat` and we then define it using the `fun` keyword.
-/

example : square₁ = square₂ := by rfl

#eval square₁ 7

/-
As we had composition of relations, we have composition of functions and the
composition of two functions is again a function.
-/

theorem Theorem_5_1_5 {A B C : Type} (f : A → B) (g : B → C) :
    ∃ (h : A → C), graph h = comp (graph g) (graph f) := by
  set h : A → C := fun (x : A) => g (f x)
  -- the set keyworkd allows us to introduce new elements to the proof state.
  apply Exists.intro h
  apply Set.ext
  fix (a, c)
  apply Iff.intro
  · assume h1 : (a, c) ∈ graph h
    define at h1
    define
    apply Exists.intro (f a)
    apply And.intro
    · define; rfl
    · define
      exact h1
  · assume h1 : (a, c) ∈ comp (graph g) (graph f)
    define; define at h1
    obtain (b : B) (h2 : (a, b) ∈ graph f ∧ (b, c) ∈ graph g) from h1
    have h3 : (a, b) ∈ graph f := h2.left
    have h4 : (b, c) ∈ graph g := h2.right
    define at h3; define at h4
    rw [← h3] at h4
    exact h4
  done

/-
The composition of `f` and `g` is denoted `g ∘ f`. Composition is associative.
-/

example {A B C D : Type} (f : A → B) (g : B → C) (h : C → D) :
    h ∘ (g ∘ f) = (h ∘ g) ∘ f := by rfl

/-
We can always consider the idenitiy function `id` of a set to itself, with its
usual properties.
-/

example {A B : Type} (f : A → B) : f ∘ id = f := by rfl

example {A B : Type} (f : A → B) : id ∘ f = f := by rfl

/-
When using `id`, Lean will figure out to which type it corresponds. If we want
to specify the type we can write `@id A`.
-/

/-
Now remember that `f : A → B` is called onto if for every `b : B` there is
`a : A` with `f a = b`.
-/

def onto {A B : Type} (f : A → B) : Prop :=
  ∀ (y : B), ∃ (x : A), f x = y

/-
And, `f` is one-to-one if given `a1 a2 : A` with `f a1 = f a2` then `a1 = a2`.
-/

def one_to_one {A B : Type} (f : A → B) : Prop :=
  ∀ (x1 x2 : A), f x1 = f x2 → x1 = x2

/-
The composition of one-to-one functions is one-to-one and the composition of
onto functions is onto.
-/

theorem Theorem_5_2_5_1 {A B C : Type} (f : A → B) (g : B → C) :
    one_to_one f → one_to_one g → one_to_one (g ∘ f) := by
  assume f11 : one_to_one f
  assume g11 : one_to_one g
  define at f11; define at g11; define
  fix a₁; fix a₂; assume h : (g ∘ f) a₁ = (g ∘ f) a₂
  have h' : f a₁ = f a₂ := g11 (f a₁) (f a₂) h
  exact f11 a₁ a₂ h'
  done

/-
Sometimes we may want to rewrite `(g ∘ f) a` as `g (f a)`. For that we can
use the rewrite tactic together with the following lemma.
-/

lemma comp_def {A B C : Type} (f : A → B) (g : B → C) (x : A) :
    (g ∘ f) x = g (f x) := by rfl

/-
And now we show that the composition of onto functions is onto.
-/

theorem Theorem_5_2_5_2 {A B C : Type} (f : A → B) (g : B → C) :
    onto f → onto g → onto (g ∘ f) := by
  assume fonto : onto f
  assume gonto : onto g
  define at fonto; define at gonto; define
  fix c : C
  obtain (b : B) (h : g b = c) from gonto c
  obtain (a : A) (h' : f a = b) from fonto b
  apply Exists.intro a
  rw [comp_def, h', h]
  done
