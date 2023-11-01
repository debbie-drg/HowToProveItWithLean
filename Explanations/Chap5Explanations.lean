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

/-
We continue with inverses. Since functions are relations, we can always consider
the inverse relation. However, when can we ensure that such inverse is a
function? Remember that `inv` can be used to obtain the inverse of a relation.

We're gonna prove that if a function is onto and one-to-one, it's inverse is
a function. For that, we are going to use the `func_from_graph` result proved
in Section 5.1.
-/

#check @func_from_graph

theorem Theorem_5_3_1 {A B : Type}
    (f : A → B) (h1 : one_to_one f) (h2 : onto f) :
    ∃ (g : B → A), graph g = inv (graph f) := by
  rw [func_from_graph]
  define; fix b : B
  exists_unique
  · define at h2
    obtain (a : A) (h4 : f a = b) from h2 b
    apply Exists.intro a
    define; exact h4
  · fix a₁; fix a₂
    assume h3 : (b, a₁) ∈ inv (graph f)
    assume h4 : (b, a₂) ∈ inv (graph f)
    define at h3; define at h4
    rewrite [← h4] at h3
    define at h1
    exact h1 a₁ a₂ h3
  done

/-
Now, what is the relation between a function and its inverse? They should
compose to the identity, which as mention can be written as `id`.
-/

theorem Theorem_5_3_2_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : g ∘ f = id := by
  apply funext; fix a : A
  have h2 : (f a, a) ∈ graph g := by
    rw [h1]
    define
    rfl
  define at h2
  exact h2
  done

theorem Theorem_5_3_2_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : graph g = inv (graph f)) : f ∘ g = id := by
  have h2 : graph f = inv (graph g) := by
    apply Set.ext; fix (a, b)
    show (a, b) ∈ graph f ↔ (a, b) ∈ inv (graph g) from
      calc (a, b) ∈ graph f
        _ ↔ (b, a) ∈ inv (graph f) := by rfl
        _ ↔ (a, b) ∈ inv (inv (graph f)) := by rfl
        _ ↔ (a, b) ∈ inv (graph g) := by rw [h1]
  apply funext; fix b : B
  have h' : (g b, b) ∈ graph f := by
    rw [h2]
    define
    rfl
  define at h'
  exact h'
  done

/-
Using he results above, if `f` is one-to-one and onto, it has an inverse `g`.
The converse is true as well.
-/

theorem Theorem_5_3_3_1 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) : one_to_one f := by
  define; fix a₁; fix a₂
  assume h2 : f a₁ = f a₂
  show a₁ = a₂ from
    calc a₁
      _ = id a₁ := by rfl
      _ = (g ∘ f) a₁ := by rw [h1]
      _ = g (f a₁) := by rfl
      _ = g (f a₂) := by rw [h2]
      _ = (g ∘ f) a₂ := by rfl
      _ = id a₂ := by rw [← h1]
      _ = a₂ := by rfl
  done

theorem Theorem_5_3_3_2 {A B : Type} (f : A → B) (g : B → A)
    (h1 : f ∘ g = id) : onto f := by
  define; fix b : B
  apply Exists.intro (g b)
  show f (g b) = b from
    calc f (g b)
      _ = (f ∘ g) b := by rfl
      _ = id b := by rw [h1]
      _ = b := by rfl
  done

/-
And combining, we have the following.
-/

theorem Theorem_5_3_5 {A B : Type} (f : A → B) (g : B → A)
    (h1 : g ∘ f = id) (h2 : f ∘ g = id) : graph g = inv (graph f) := by
  have h3 : one_to_one f := Theorem_5_3_3_1 f g h1
  have h4 : onto f := Theorem_5_3_3_2 f g h2
  obtain (g' : B → A) (h5 : graph g' = inv (graph f))
    from Theorem_5_3_1 f h3 h4
  have h6 : g' ∘ f = id := Theorem_5_3_2_1 f g' h5
  have h7 : g = g' :=
    calc g
      _ = id ∘ g := by rfl
      _ = (g' ∘ f) ∘ g := by rw [h6]
      _ = g' ∘ (f ∘ g) := by rfl
      _ = g' ∘ id := by rw [h2]
      _ = g' := by rfl
  rw [h7]
  exact h5
  done

/-
Assume now that `f : A → A` and `C : Set A`. We say that `C` is closed under
`f` if the image by `f` of any element of `C` is again in `C`.
-/

def closed {A : Type} (f : A → A) (C : Set A) : Prop := ∀ x ∈ C, f x ∈ C

/-
If a set isn't closed, we can add elements until it is. The `closure` is the
smallest set verifying this, with respect to the relation `sub` that we already
worked with. Thus:
-/

def closure {A : Type} (f : A → A) (B C : Set A) : Prop :=
  smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed f D }

/-
We have already shown that if a smallest element exists, it is unique.
But does the closure of a set exists? We now prove it. The way to go is to
obtain it as the intersection of every clossed set verifying the proerty.
-/

theorem Theorem_5_4_5 {A : Type} (f : A → A) (B : Set A) :
    ∃ (C : Set A), closure f B C := by
  set F : Set (Set A) := { D : Set A | B ⊆ D ∧ closed f D }
  set C : Set A := ⋂₀ F
  apply Exists.intro C
  define
  apply And.intro
  · define
    apply And.intro
    · fix a : A; assume h1 : a ∈ B
      define; fix D : Set A; assume h2 : D ∈ F
      define at h2
      exact h2.left h1
    · define; fix a : A; assume h1 : a ∈ C
      define; fix D : Set A; assume h2 : D ∈ F
      define at h1
      have h3 : a ∈ D := h1 D h2
      define at h2
      exact h2.right a h3
  · fix D : Set A
    assume h1 : D ∈ {D : Set A | B ⊆ D ∧ closed f D}
    define; fix a : A; assume h2 : a ∈ C
    define at h2
    exact h2 D h1
  done

/-
Usually, closure is most desirable when having functions of two variables,
of type `(A × A) → A`, or equivalently, `A → A → A`. These are commonly
used when talking about algebraic substructures, as one of the requirements
is precisely that they're closed under the algebraic structure's different
operations. One such example is that of integer addition.
-/

def plus (m n : Int) : Int := m + n

def plus' : Int → Int → Int := fun (m n : Int) => m + n

def plus'' : Int → Int → Int := fun (m : Int) => (fun (n : Int) => m + n)

/-
The third way is perhaps the closest to the type. Namely, for every integer
we have a function from integers to integers.
-/

/-
If we have `f : A → A → A` and `a : A`, `f a : A → A`. We call this
partial application of `f`. Of course, if `b : A`, `f a b : A`, where this
can be thought of applying `f a` to `b`.
-/

/-
Now, remember that in Chapter 3 we introduced predicates, `Pred U`.
Internally, `Pred U` is defined to be the type `U → Prop`, so if `P : Pred U`
and `x : U`, `P x : Prop` is the proposition corresponding to applying `P`
to `u`.

Similarly, `Rel` stands for `A → B → Prop`, so if `R : Rel A B`, `R` is a
function of two variables: one of type `A` and one of type `B`.

Another already seen example is that of `closed f C`. Here, the second
argument is a function `f : A → A`. Functions can be used as arguments
for functions in Lean, as is common in functional programming paradigms.
-/

/-
Back to closures, this is how we can extend the idea of closures to
functions of two variables.
-/

def closed2 {A : Type} (f : A → A → A) (C : Set A) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, f x y ∈ C

def closure2 {A : Type} (f : A → A → A) (B C : Set A) : Prop :=
  smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed2 f D }

/-
Closures under functions of two variables also exist. The argument is
pretty similar.
-/

theorem Theorem_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := by
  set F : Set (Set A) := { D : Set A | B ⊆ D ∧ closed2 f D }
  set C : Set A := ⋂₀ F
  apply Exists.intro C
  define
  apply And.intro
  · define
    apply And.intro
    · fix b; assume h1 : b ∈ B
      define; fix D; assume h2 : D ∈ F
      define at h2
      exact h2.left h1
    · define; fix a : A; assume h1 : a ∈ C; fix b : A; assume h2 : b ∈ C
      define at h1; define at h2
      define; fix D; assume h3 : D ∈ F
      have h4 : a ∈ D := h1 D h3
      have h5 : b ∈ D := h2 D h3
      define at h3
      exact h3.right a h4 b h5
  · fix D : Set A
    assume h1 : D ∈ {D : Set A | B ⊆ D ∧ closed2 f D}
    define; fix a : A; assume h2 : a ∈ C
    define at h2
    have h3 : D ∈ F := h1
    exact h2 D h3
  done

/-
We also considered closed families and the closure of a family.
-/

def closed_family {A : Type} (F : Set (A → A)) (C : Set A) : Prop :=
  ∀ f ∈ F, closed f C

def closure_family {A : Type} (F : Set (A → A)) (B C : Set A) : Prop :=
  smallestElt (sub A) C { D : Set A | B ⊆ D ∧ closed_family F D }
