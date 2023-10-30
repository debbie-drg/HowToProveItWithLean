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

/-
We now introduce relations with additional properties.
-/

/-
Recall that a relation is an `order relation` if it is reflexive,
transitive and antisymmetric.
-/

def antisymmetric {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y : A), R x y → R y x → x = y

def partial_order {A : Type} (R : BinRel A) : Prop :=
  reflexive R ∧ transitive R ∧ antisymmetric R

def total_order {A : Type} (R : BinRel A) : Prop :=
  partial_order R ∧ ∀ (x y : A), R x y ∨ R y x

/-
Note that `partial_order` means `reflexive R ∧ (transitive R ∧ antisymmetric R)`
based on how Lean groups parenthesis. Therefore, if `h` is proof of partial
order:
* `h.left` is prove of reflexivity
* `h.right.left` is proof of transitity
* `h.right.right` is proof of antisymmetry.
-/

/-
An example of a partial order relation is the subset relation.
-/

def sub (A : Type) (X Y : Set A) : Prop := X ⊆ Y

/-
In order relations, we can talk about smallest elements, or minimums. Namely,
an element that is below (related to) every other element.
-/

def smallestElt {A : Type} (R : BinRel A) (b : A) (B : Set A) : Prop :=
  b ∈ B ∧ ∀ x ∈ B, R b x

/-
Smallest elements don't always exist, but `minimals` do. Namely, elements for
which we cannot find anything below (but there may be elements not related
to it in either direction).
-/

def minimalElt {A : Type} (R : BinRel A) (b : A) (B : Set A) : Prop :=
  b ∈ B ∧ ¬∃ x ∈ B, R x b ∧ x ≠ b

/-
If a minimum exists, it is a minimal element, and it is unique, as we prove now.
-/

theorem Theorem_4_4_6_2 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    minimalElt R b B ∧ ∀ (c : A), minimalElt R c B → b = c := by
  define at h1
  define at h2
  apply And.intro
  · define
    apply And.intro h2.left
    quant_neg; fix x : A
    demorgan
    or_right with h3
    demorgan
    or_right with h4
    have h5 : R b x := h2.right x h3
    exact h1.right.right x b h4 h5
  · fix x : A; assume h3 : minimalElt R x B
    define at h3
    contradict h3.right with h4
    apply Exists.intro b
    have h5 : R b x := h2.right x h3.left
    exact And.intro h2.left (And.intro h5 h4)
  done

/-
And, if we have a total order, any minimal element must also be a smallest
element.
-/

theorem Theorem_4_4_6_3 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : total_order R) (h2 : minimalElt R b B) : smallestElt R b B := by
  define
  define at h1
  define at h2
  apply And.intro h2.left
  fix x : A; assume h3 : x ∈ B
  by_cases h4 : x = b
  · -- Case x = b
    rw [h4]
    have h5 : partial_order R := h1.left
    define at h5
    exact h5.left b
  · -- Case x ≠ b
    have h5 : R x b ∨ R b x := h1.right x b
    have h6 : ¬R x b := by
      contradict h2.right with h8
      apply Exists.intro x
      exact And.intro h3 (And.intro h8 h4)
    disj_syll h5 h6
    exact h5
  done

/-
Maximal and maximum elements can be defined in an analogous manner.

We can also define upper bounds and least upper bounds.
-/

def upperBd {A : Type} (R : BinRel A) (a : A) (B : Set A) : Prop :=
  ∀ x ∈ B, R x a

def lub {A : Type} (R : BinRel A) (a : A) (B : Set A) : Prop :=
  smallestElt R a { c : A | upperBd R c B }

/-
Finally, we introduce equivalence relations; relations that are reflexive,
symmetric and transitive.
-/

def equiv_rel {A : Type} (R : BinRel A) : Prop :=
  reflexive R ∧ symmetric R ∧ transitive R

/-
An important concept related to equivalence relations is the equivalence class
of an element, namely the set of all elements related to it.
-/

def equivClass {A : Type} (R : BinRel A) (x : A) : Set A :=
  { y : A | R y x }

/-
Given an equivalence relation we can define a quotient, the set of all
equivalence classes of the relation.
-/

def mod (A : Type) (R : BinRel A) : Set (Set A) :=
  { equivClass R x | x : A }

/-
We are gonna prove some relations. Instead of using the notation `X = ∅`,
it may be more useful to use a `empty` property stating that the set has no
elements. Similarly, we introduce a pairwise disjoint property for two
sets with empty intersection.
-/

def empty {A : Type} (X : Set A) : Prop := ¬∃ (x : A), x ∈ X

def pairwise_disjoint {A : Type} (F : Set (Set A)) : Prop :=
  ∀ X ∈ F, ∀ Y ∈ F, X ≠ Y → empty (X ∩ Y)

/-
Now, one key property of equivalence relations is that the equivalence classes
form a `partition`, namely, a set of sets which are pairwise disjoint and
whose union is the total set.
-/

def partition {A : Type} (F : Set (Set A)) : Prop :=
  (∀ (x : A), x ∈ ⋃₀ F) ∧ pairwise_disjoint F ∧ ∀ X ∈ F, ¬empty X

/-
Let us prove what we just claimed about equivalence classes being a partition.
-/

-- Every element is in an equivalence class
lemma Lemma_4_5_5_1 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x : A), x ∈ equivClass R x := by
  fix x : A
  define
  define at h
  have Rref : reflexive R := h.left
  show R x x from Rref x
  done


lemma Lemma_4_5_5_2 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x y : A), y ∈ equivClass R x ↔
      equivClass R y = equivClass R x := by
  have Rsymm : symmetric R := h.right.left
  have Rtrans : transitive R := h.right.right
  fix x : A; fix y : A
  apply Iff.intro
  · -- (→)
    assume h2 :
      y ∈ equivClass R x
    define at h2
    apply Set.ext
    fix z : A
    apply Iff.intro
    · -- Proof that z ∈ equivClass R y → z ∈ equivClass R x
      assume h3 : z ∈ equivClass R y
      define
      define at h3
      show R z x from Rtrans z y x h3 h2
      done
    · -- Proof that z ∈ equivClass R x → z ∈ equivClass R y
      assume h3 : z ∈ equivClass R x
      define
      define at h3
      have h4 : R x y := Rsymm y x h2
      show R z y from Rtrans z x y h3 h4
      done
    done
  · -- (←)
    assume h2 :
      equivClass R y = equivClass R x
    rw [←h2]
    show y ∈ equivClass R y from Lemma_4_5_5_1 R h y
    done
  done

/-
We prove the three needed statements separately.
-/

lemma Theorem_4_5_4_part_1 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ (x : A), x ∈ ⋃₀ (mod A R) := by
  fix x : A
  define        --Goal : ∃ (t : Set A), t ∈ mod A R ∧ x ∈ t
  apply Exists.intro (equivClass R x)
  apply And.intro _ (Lemma_4_5_5_1 R h x)
                --Goal : equivClass R x ∈ mod A R
  define        --Goal : ∃ (x_1 : A), equivClass R x_1 = equivClass R x
  apply Exists.intro x
  rfl
  done

lemma Theorem_4_5_4_part_2 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    pairwise_disjoint (mod A R) := by
  define
  fix X : Set A
  assume h2 : X ∈ mod A R
  fix Y : Set A
  assume h3 : Y ∈ mod A R           --Goal : X ≠ Y → empty (X ∩ Y)
  define at h2; define at h3
  obtain (x : A) (h4 : equivClass R x = X) from h2
  obtain (y : A) (h5 : equivClass R y = Y) from h3
  contrapos
  assume h6 : ∃ (x : A), x ∈ X ∩ Y  --Goal : X = Y
  obtain (z : A) (h7 : z ∈ X ∩ Y) from h6
  define at h7
  rewrite [←h4, ←h5] at h7 --h7 : z ∈ equivClass R x ∧ z ∈ equivClass R y
  have h8 : equivClass R z = equivClass R x :=
    (Lemma_4_5_5_2 R h x z).ltr h7.left
  have h9 : equivClass R z = equivClass R y :=
    (Lemma_4_5_5_2 R h y z).ltr h7.right
  show X = Y from
    calc X
      _ = equivClass R x := h4.symm
      _ = equivClass R z := h8.symm
      _ = equivClass R y := h9
      _ = Y              := h5
  done

lemma Theorem_4_5_4_part_3 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ¬empty X := by
  fix X : Set A
  assume h2 : X ∈ mod A R  --Goal : ¬empty X
  define; double_neg       --Goal : ∃ (x : A), x ∈ X
  define at h2             --h2 : ∃ (x : A), equivClass R x = X
  obtain (x : A) (h3 : equivClass R x = X) from h2
  rewrite [←h3]
  show ∃ (x_1 : A), x_1 ∈ equivClass R x from
    Exists.intro x (Lemma_4_5_5_1 R h x)
  done

/-
And we now put everything together.
-/

theorem Theorem_4_5_4 {A : Type} (R : BinRel A) (h : equiv_rel R) :
    partition (mod A R) := And.intro (Theorem_4_5_4_part_1 R h)
      (And.intro (Theorem_4_5_4_part_2 R h) (Theorem_4_5_4_part_3 R h))

/-
Conversely, we now show that every partition arises as the set of equivalence
classes of an equivalence relation. We define thef ollowing relation.
-/

def EqRelFromPart {A : Type} (F : Set (Set A)) (x y : A) : Prop :=
  ∃ X ∈ F, x ∈ X ∧ y ∈ X

/-
We then have the following results.
-/

lemma overlap_implies_equal {A : Type}
    (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ Y ∈ F, ∀ (x : A), x ∈ X → x ∈ Y → X = Y := by
  fix X : Set A; assume h1 : X ∈ F
  fix Y : Set A; assume h2 : Y ∈ F
  fix x; assume h3 : x ∈ X; assume h4 : x ∈ Y
  define at h
  by_contra h5
  have h6 : pairwise_disjoint F := h.right.left
  define at h6
  have h7 : empty (X ∩ Y) := h6 X h1 Y h2 h5
  define at h7
  have h8 : x ∈ X ∩ Y := And.intro h3 h4
  quant_neg at h7
  have h9 : ¬x ∈ X ∩ Y := h7 x
  show False from h9 h8
  done

lemma Lemma_4_5_7_ref {A : Type} (F : Set (Set A)) (h : partition F):
    reflexive (EqRelFromPart F) := by
  define; fix a : A
  define; define at h
  have h1 : a ∈ ⋃₀ F := h.left a
  define at h1; obtain (B : Set A) (h2 : B ∈ F ∧ a ∈ B) from h1
  apply Exists.intro B
  exact And.intro h2.left (And.intro h2.right h2.right)
  done

lemma Lemma_4_5_7_symm {A : Type} (F : Set (Set A)) (h : partition F):
    symmetric (EqRelFromPart F) := by
  define; fix x; fix y; assume h1 : EqRelFromPart F x y
  define at h1; define
  obtain (X : Set A) (h2 : X ∈ F ∧ x ∈ X ∧ y ∈ X) from h1
  apply Exists.intro X
  exact And.intro h2.left (And.intro h2.right.right h2.right.left)
  done

lemma Lemma_4_5_7_trans {A : Type} (F : Set (Set A)) (h : partition F):
    transitive (EqRelFromPart F) := by
  define; fix x; fix y; fix z
  assume h1 : EqRelFromPart F x y; assume h2 : EqRelFromPart F y z
  define; define at h1; define at h2
  obtain (X1 : Set A) (h3 : X1 ∈ F ∧ x ∈ X1 ∧ y ∈ X1) from h1
  obtain (X2 : Set A) (h4 : X2 ∈ F ∧ y ∈ X2 ∧ z ∈ X2) from h2
  have h5 : X1 = X2 := overlap_implies_equal F h X1 h3.left X2 h4.left y h3.right.right h4.right.left
  rw [h5] at h3
  apply Exists.intro X2
  exact And.intro h3.left (And.intro h3.right.left h4.right.right)
  done

/-
We now put them together.
-/

lemma Lemma_4_5_7 {A : Type} (F : Set (Set A)) (h : partition F) :
    equiv_rel (EqRelFromPart F) := And.intro (Lemma_4_5_7_ref F h)
      (And.intro (Lemma_4_5_7_symm F h) (Lemma_4_5_7_trans F h))

/-
The next result is also needed.
-/

lemma Lemma_4_5_8 {A : Type} (F : Set (Set A)) (h : partition F) :
    ∀ X ∈ F, ∀ x ∈ X, equivClass (EqRelFromPart F) x = X := by
  fix X; assume hX : X ∈ F; fix x; assume hx : x ∈ X
  ext a
  apply Iff.intro
  · assume ha: a ∈ equivClass (EqRelFromPart F) x
    define at ha
    obtain (Y : Set A) (hY : Y ∈ F ∧ a ∈ Y ∧ x ∈ Y) from ha
    have hXeqY : X = Y := overlap_implies_equal F h X hX Y hY.left x hx hY.right.right
    rw [hXeqY]
    exact hY.right.left
  · assume haX : a ∈ X
    define; apply Exists.intro X
    exact And.intro hX (And.intro haX hx)
  done

/-
And now we can finally prove the result.
-/

theorem Theorem_4_5_6 {A : Type} (F : Set (Set A)) (h: partition F) :
    ∃ (R : BinRel A), equiv_rel R ∧ mod A R = F := by
  set R : BinRel A := EqRelFromPart F
  apply Exists.intro R
  apply And.intro (Lemma_4_5_7 F h)
  apply Set.ext
  fix X : Set A
  apply Iff.intro
  · -- (→)
    assume h2 : X ∈ mod A R
    define at h2
    obtain (x : A) (h3 : equivClass R x = X) from h2
    have h4 : x ∈ ⋃₀ F := h.left x
    define at h4
    obtain (Y : Set A) (h5 : Y ∈ F ∧ x ∈ Y) from h4
    have h6 : equivClass R x = Y :=
      Lemma_4_5_8 F h Y h5.left x h5.right
    rewrite [←h3, h6]
    show Y ∈ F from h5.left
    done
  · -- (←)
    assume h2 : X ∈ F
    have h3 : ¬empty X := h.right.right X h2
    define at h3; double_neg at h3
    obtain (x : A) (h4 : x ∈ X) from h3
    define
    show ∃ (x : A), equivClass R x = X from
      Exists.intro x (Lemma_4_5_8 F h X h2 x h4)
    done
  done
