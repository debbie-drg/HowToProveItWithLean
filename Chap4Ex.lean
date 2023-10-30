import HTPILib.Chap4
namespace HTPI.Exercises

/- Section 4.2 -/
-- 1.
theorem Exercise_4_2_9a {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Dom (comp S R) ⊆ Dom R := by
  define
  fix a : A
  assume h1 : a ∈ Dom (comp S R)
  define at h1
  obtain (c : C) (h2 : (a, c) ∈ comp S R) from h1
  define at h2
  obtain (b : B) (h3 : (a, b) ∈ R ∧ (b, c) ∈ S) from h2
  define
  apply Exists.intro b
  exact h3.left
  done

-- 2.
theorem Exercise_4_2_9b {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Ran R ⊆ Dom S → Dom (comp S R) = Dom R := by
  assume h1 : Ran R ⊆ Dom S
  ext a
  apply Iff.intro
  · assume h2 : a ∈ Dom (comp S R)
    define at h2; obtain (c : C) (h3 : (a, c) ∈ comp S R) from h2
    define at h3; obtain (b : B) (h4 : (a, b) ∈ R ∧ (b, c) ∈ S) from h3
    define
    apply Exists.intro b
    exact h4.left
  · assume h2 : a ∈ Dom R
    define at h2
    obtain (b : B) (h3 : (a, b) ∈ R) from h2
    define at h1
    have h4 : b ∈ Ran R := by
      define; apply Exists.intro a; exact h3
    have h5 : b ∈ Dom S := h1 h4
    define at h5
    obtain (c : C) (h6 : (b, c) ∈ S) from h5
    define
    apply Exists.intro c
    define
    apply Exists.intro b
    exact And.intro h3 h6
  done

-- 3.
--Fill in the blank to get a correct theorem and then prove the theorem
theorem Exercise_4_2_9c {A B C : Type} (R : Set (A × B))
    (S : Set (B × C)) : Ran R = Dom S → Ran (comp S R) = Ran S := by
  assume h1 : Ran R = Dom S
  ext c
  apply Iff.intro
  · assume h2 : c ∈ Ran (comp S R)
    define at h2
    obtain (a : A) (h3 : (a, c) ∈ comp S R) from h2
    define at h3
    obtain (b : B) (h4 : (a, b) ∈ R ∧ (b, c) ∈ S) from h3
    define
    apply Exists.intro b
    exact h4.right
  · assume h2 : c ∈ Ran S
    define at h2
    obtain (b : B) (h3 : (b, c) ∈ S) from h2
    have h4 : b ∈ Dom S := by
      define; apply Exists.intro c; exact h3
    rw [← h1] at h4
    define at h4
    obtain (a : A) (h5 : (a, b) ∈ R) from h4
    define
    apply Exists.intro a
    define
    apply Exists.intro b
    exact And.intro h5 h3
  done

-- 4.
theorem Exercise_4_2_12a {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    (comp S R) \ (comp T R) ⊆ comp (S \ T) R := by
  define; fix (a, c); assume h1 : (a, c) ∈ comp S R \ comp T R
  define at h1
  have h2 : (a, c) ∈ comp S R := h1.left
  have h3 : ¬(a, c) ∈ comp T R := h1.right
  define at h2
  obtain (b : B) (h4 : (a, b) ∈ R ∧ (b, c) ∈ S) from h2
  define at h3
  quant_neg at h3
  have h5 : ¬((a, b) ∈ R ∧ (b, c) ∈ T) := h3 b
  demorgan at h5
  disj_syll h5 h4.left
  define
  apply Exists.intro b
  exact And.intro h4.left (And.intro h4.right h5)
  done

-- 5.
--You won't be able to complete this proof
theorem Exercise_4_2_12b {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S \ T) R ⊆ (comp S R) \ (comp T R) := by
  define
  fix (a, c)
  assume h1 : (a, c) ∈ comp (S \ T) R
  define at h1
  obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ S \ T) from h1
  have h3 : (a, b) ∈ R := h2.left
  have h4 : (b, c) ∈ S \ T := h2.right
  have h5 : (b, c) ∈ S := h4.left
  have h6 : (a, c) ∈ comp S R := by
    define
    apply Exists.intro b; exact And.intro h3 h5
  have h7 : ¬(a, c) ∈ comp T R := by
    define
    quant_neg
    fix b'
    demorgan
    sorry
  sorry
  -- The mistake in the proof is that knowing that `(b, c) ∉ T` is not
  -- enough to show that `(a, c) ∉ T ∘ R`. There could be a different `b' : B`
  -- verifying that property.

-- 6.
-- This result is false, although one of the directions is true. We change it
-- and prove it.
theorem Exercise_4_2_14c {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∩ T) R ⊆ (comp S R) ∩ (comp T R) := by
  define; fix (a, c); assume h1 : (a, c) ∈ comp (S ∩ T) R
  define at h1
  obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ S ∩ T) from h1
  apply And.intro
  · define
    apply Exists.intro b
    exact And.intro h2.left h2.right.left
  · define
    apply Exists.intro b
    exact And.intro h2.left h2.right.right
  done
/-
To show that the other direction is false, have:
`R = {(a, b₁), (a, b₂)}`
`S = {(b₁, c)}`
`T = {(b₂,c)}`
Then `S ∩ T = ∅`, so `(S ∩ T) ∘ R = ∅`. However, `(a, c) ∈ S ∘ R` using
`b₁` as witness, and `(a, c) ∈ T ∘ R` using `b₂` as witness.
-/

-- 7.
--You might not be able to complete this proof
theorem Exercise_4_2_14d {A B C : Type}
    (R : Set (A × B)) (S T : Set (B × C)) :
    comp (S ∪ T) R = (comp S R) ∪ (comp T R) := by
  apply Set.ext; fix (a, c)
  apply Iff.intro
  · assume h1 : (a, c) ∈ comp (S ∪ T) R
    define at h1
    obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ S ∪ T) from h1
    have h3 : (b, c) ∈ S ∪ T := h2.right
    by_cases on h3
    · have h4 : (a, c) ∈ comp S R := by
        define; apply Exists.intro b; exact And.intro h2.left h3
      left; exact h4
    · have h4 : (a, c) ∈ comp T R := by
        define; apply Exists.intro b; exact And.intro h2.left h3
      right; exact h4
  · assume h1 : (a, c) ∈ comp S R ∪ comp T R
    by_cases on h1
    · define at h1; obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ S) from h1
      define; apply Exists.intro b
      apply And.intro h2.left; left; exact h2.right
    · define at h1; obtain (b : B) (h2 : (a, b) ∈ R ∧ (b, c) ∈ T) from h1
      define; apply Exists.intro b
      apply And.intro h2.left; right; exact h2.right
  done

/- Section 4.3 -/
-- 1.
example :
    elementhood Int 6 { n : Int | ∃ (k : Int), n = 2 * k } := by
  apply Exists.intro 3
  ring
  done

-- 2.
theorem Theorem_4_3_4_1 {A : Type} (R : BinRel A) :
    reflexive R ↔ { (x, y) : A × A | x = y } ⊆ extension R := by
  apply Iff.intro
  · assume h1 : reflexive R
    define at h1
    define
    fix (a, a'); assume h2 : (a, a') ∈ { (a, a') : A × A | a = a'}
    define at h2
    rw [← h2]
    exact h1 a
  · assume h1 : { (x, y) : A × A | x = y } ⊆ extension R
    define at h1
    define; fix a
    have h2 : (a, a) ∈ { (x, y) : A × A | x = y } := by rfl
    have h3 : (a, a) ∈ extension R := h1 h2
    exact h3
  done

-- 3.
theorem Theorem_4_3_4_3 {A : Type} (R : BinRel A) :
    transitive R ↔
      comp (extension R) (extension R) ⊆ extension R := by
  apply Iff.intro
  · assume h1 : transitive R
    define at h1
    define
    fix (a, a')
    assume h2 : (a, a') ∈ comp (extension R) (extension R)
    define at h2
    obtain (a'' : A) (h3 :  (a, a'') ∈ extension R ∧ (a'', a') ∈ extension R) from h2
    have h4 : R a a'' := h3.left
    have h5 : R a'' a' := h3.right
    exact h1 a a'' a' h4 h5
  · assume h1 : comp (extension R) (extension R) ⊆ extension R
    define
    fix x; fix y; fix z
    assume h2 : R x y
    assume h3 : R y z
    define at h1
    have h4 : (x, z) ∈ comp (extension R) (extension R) := by
      define; apply Exists.intro y
      exact And.intro h2 h3
    exact h1 h4
  done

-- 4.
theorem Exercise_4_3_12a {A : Type} (R : BinRel A) (h1 : reflexive R) :
    reflexive (RelFromExt (inv (extension R))) := by
  define; fix a
  define
  exact h1 a
  done

-- 5.
theorem Exercise_4_3_12c {A : Type} (R : BinRel A) (h1 : transitive R) :
    transitive (RelFromExt (inv (extension R))) := by
  define; fix x; fix y; fix z
  assume h2 : RelFromExt (inv (extension R)) x y; define at h2
  assume h3 : RelFromExt (inv (extension R)) y z; define at h3
  define; define at h1
  exact h1 z y x h3 h2
  done

-- 6.
theorem Exercise_4_3_18 {A : Type}
    (R S : BinRel A) (h1 : transitive R) (h2 : transitive S)
    (h3 : comp (extension S) (extension R) ⊆
      comp (extension R) (extension S)) :
    transitive (RelFromExt (comp (extension R) (extension S))) := by
  define; fix x; fix y; fix z
  assume h4 : RelFromExt (comp (extension R) (extension S)) x y; define at h4
  obtain (xy : A) (h5 : (x, xy) ∈ extension S ∧ (xy, y) ∈ extension R) from h4
  assume h6 : RelFromExt (comp (extension R) (extension S)) y z; define at h6
  obtain (yz : A) (h7 : (y, yz) ∈ extension S ∧ (yz, z) ∈ extension R) from h6
  have h8 : (xy, yz) ∈ comp (extension S) (extension R) := by
    define; apply Exists.intro y; exact And.intro h5.right h7.left
  have h9 : (xy, yz) ∈ comp (extension R) (extension S) := h3 h8
  define at h9; obtain (xyz : A) (h10 : (xy, xyz) ∈ extension S ∧ (xyz, yz) ∈ extension R) from h9
  apply Exists.intro xyz
  apply And.intro
  · exact h2 x xy xyz h5.left h10.left
  · exact h1 xyz yz z h10.right h7.right
  done

-- 7.
theorem Exercise_4_3_20 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ X ≠ ∅ ∧ Y ≠ ∅ ∧
    ∀ (x y : A), x ∈ X → y ∈ Y → R x y) :
    transitive R → transitive S := by
  assume h1 : transitive R
  define; fix X; fix Y; fix Z
  assume h2 : S X Y; assume h3 : S Y Z
  rw [h] at h2
  rw [h] at h3
  have h5 : Y ≠ ∅ := h2.right.left
  rw [← Set.nonempty_iff_ne_empty] at h5
  define at h5; obtain (y : A) (h6 : y ∈ Y) from h5
  rw [h]
  apply And.intro h2.left
  apply And.intro h3.right.left
  fix x; fix z; assume h7 : x ∈ X; assume h8 : z ∈ Z
  have h9 : R x y := h2.right.right x y h7 h6
  have h10 : R y z := h3.right.right y z h6 h8
  exact h1 x y z h9 h10
  done

-- 8.
--You might not be able to complete this proof
theorem Exercise_4_3_13b {A : Type}
    (R1 R2 : BinRel A) (h1 : symmetric R1) (h2 : symmetric R2) :
    symmetric (RelFromExt ((extension R1) ∪ (extension R2))) := by
  define; fix x; fix y
  assume h3 : RelFromExt (extension R1 ∪ extension R2) x y
  define at h3
  by_cases on h3
  · have h4 : (y, x) ∈ extension R1 := h1 x y h3
    define; left; exact h4
  · have h4 : (y, x) ∈ extension R2 := h2 x y h3
    define; right; exact h4
  done

-- 9.
--You might not be able to complete this proof
theorem Exercise_4_3_13c {A : Type}
    (R1 R2 : BinRel A) (h1 : transitive R1) (h2 : transitive R2) :
    transitive (RelFromExt ((extension R1) ∪ (extension R2))) := sorry
/-
This result is false. Imagine we have a set of three elements
`{x, y, z}`, `R1` only relating `x` and `y`, and `R2` only relating `y` and `z`.
Then `R1 ∪ R2` relates `x` with `y` and `y` with `z` but does not relate `x`
with `z`.
-/

-- 10.
--You might not be able to complete this proof
theorem Exercise_4_3_19 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ ∃ (x y : A), x ∈ X ∧ y ∈ Y ∧ R x y) :
    transitive R → transitive S := sorry
/-
Also false. The elements in `Y` can be different between different sets,
thus transitivity cannot be applied. In fact, the same relation as before with
`X = {x}`, `Y = {y}` and `Z = {z}` works here.
-/

/- Section 4.4 -/
-- 1.
theorem Example_4_4_3_1 {A : Type} : partial_order (sub A) := by
  define
  apply And.intro
  · define
    fix X
    define; fix a; assume h; exact h
  · apply And.intro
    · define; fix X; fix Y; fix Z
      assume h1 : sub A X Y
      assume h2 : sub A Y Z
      define at h1
      define at h2
      define; fix a; assume h3 : a ∈ X
      have h4 : a ∈ Y := h1 h3
      exact h2 h4
    · define; fix X; fix Y
      assume h1 : sub A X Y
      assume h2 : sub A Y X
      ext x; apply Iff.intro
      · assume h3 : x ∈ X
        exact h1 h3
      · assume h3 : x ∈ Y
        exact h2 h3
  done

-- 2.
theorem Theorem_4_4_6_1 {A : Type} (R : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    ∀ (c : A), smallestElt R c B → b = c := by
  fix a : A; assume h3 : smallestElt R a B
  define at h1; define at h2; define at h3
  have h4 : R a b := h3.right b h2.left
  have h5 : R b a := h2.right a h3.left
  exact h1.right.right b a h5 h4
  done

-- 3.
--If F is a set of sets, then ⋃₀ F is the lub of F in the subset ordering
theorem Theorem_4_4_11 {A : Type} (F : Set (Set A)) :
    lub (sub A) (⋃₀ F) F := by
  define
  apply And.intro
  · define; fix X; assume h1 : X ∈ F
    define; fix a; assume h2 : a ∈ X
    define; apply Exists.intro X; exact And.intro h1 h2
  · fix X; assume h1 : X ∈ {c : Set A | upperBd (sub A) c F}
    define at h1
    define; fix a; assume h2 : a ∈ ⋃₀ F
    define at h2; obtain (B : Set A) (h3 : B ∈ F ∧ a ∈ B) from h2
    have h4 : sub A B X := h1 B h3.left
    define at h4
    exact h4 h3.right
  done

-- 4.
theorem Exercise_4_4_8 {A B : Type} (R : BinRel A) (S : BinRel B)
    (T : BinRel (A × B)) (h1 : partial_order R) (h2 : partial_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      T (a, b) (a', b') ↔ R a a' ∧ S b b') :
    partial_order T := by
  define; apply And.intro
  · define; fix (a, b)
    rw [h3]
    apply And.intro (h1.left a) (h2.left b)
  · apply And.intro
    · define; fix (a₁, b₁); fix (a₂, b₂); fix (a₃, b₃)
      assume h4 : T (a₁, b₁) (a₂, b₂)
      assume h5 : T (a₂, b₂) (a₃, b₃)
      rw [h3] at h4; rw [h3] at h5; rw [h3]
      apply And.intro
      · exact h1.right.left a₁ a₂ a₃ h4.left h5.left
      · exact h2.right.left b₁ b₂ b₃ h4.right h5.right
    · define; fix (a, b); fix (a', b')
      assume h4 : T (a, b) (a', b')
      assume h5 : T (a', b') (a, b)
      rw [h3] at h4; rw [h3] at h5
      have h6 : a = a' := h1.right.right a a' h4.left h5.left
      have h7 : b = b' := h2.right.right b b' h4.right h5.right
      ext; exact h6; exact h7
  done

-- 5.
theorem Exercise_4_4_9_part {A B : Type} (R : BinRel A) (S : BinRel B)
    (L : BinRel (A × B)) (h1 : total_order R) (h2 : total_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ↔ R a a' ∧ (a = a' → S b b')) :
    ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ∨ L (a', b') (a, b) := by
  fix a; fix a'; fix b; fix b'
  define at h1; define at h2
  have h4: R a a' ∨ R a' a := h1.right a a'
  have h5 : S b b' ∨ S b' b := h2.right b b'
  have h6 : a = a' ∨ a ≠ a' := eq_or_ne a a'
  by_cases on h6
  · have h7 : R a a := h1.left.left a
    by_cases on h5
    · left; rw [h3]
      apply And.intro
      · rw [← h6]; exact h7
      · assume h; exact h5
    · right; rw [h3]
      apply And.intro
      · rw [← h6]; exact h7
      · assume h; exact h5
  · by_cases on h4
    · left; rw [h3]
      apply And.intro h4
      assume h; by_contra; show False from h6 h
    · right; rw [h3]
      apply And.intro h4
      assume h; by_contra; show False from h6 h.symm
  done

-- 6.
theorem Exercise_4_4_15a {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    smallestElt R1 b B → smallestElt R2 b B := by
  assume h4 : smallestElt R1 b B
  define at h4; define
  apply And.intro h4.left; fix a : A; assume h5 : a ∈ B
  have h6 : (b, a) ∈ extension R1 := by
    define; exact h4.right a h5
  have h7 : (b, a) ∈ extension R2 := h3 h6
  define at h7; exact h7
  done

-- 7.
theorem Exercise_4_4_15b {A : Type}
    (R1 R2 : BinRel A) (B : Set A) (b : A)
    (h1 : partial_order R1) (h2 : partial_order R2)
    (h3 : extension R1 ⊆ extension R2) :
    minimalElt R2 b B → minimalElt R1 b B := by
  assume h4 : minimalElt R2 b B
  define at h4; define
  apply And.intro h4.left; quant_neg; fix a : A; demorgan
  have h5 : ¬∃ (x : A), x ∈ B ∧ R2 x b ∧ x ≠ b := h4.right
  quant_neg at h5
  have h6 : ¬(a ∈ B ∧ R2 a b ∧ a ≠ b) := h5 a
  demorgan at h6; by_cases on h6
  · left; exact h6
  · demorgan at h6
    by_cases on h6
    · right; demorgan; left
      by_contra h7
      have h8 : R2 a b := by
        have h9 : (a, b) ∈ extension R1 := by
          define; exact h7
        have h10 : (a, b) ∈ extension R2 := h3 h9
        define at h10; exact h10
      show False from h6 h8
    · right; demorgan; right; exact h6
  done

-- 8.
theorem Exercise_4_4_18a {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (h1 : partial_order R)
    (h2 : ∀ x ∈ B1, ∃ y ∈ B2, R x y) (h3 : ∀ x ∈ B2, ∃ y ∈ B1, R x y) :
    ∀ (x : A), upperBd R x B1 ↔ upperBd R x B2 := by
  fix a : A
  apply Iff.intro
  · assume h4 : upperBd R a B1
    define at h4; define; fix b; assume h5 : b ∈ B2
    have h6 : ∃ (y : A), y ∈ B1 ∧ R b y := h3 b h5
    obtain (y : A) (h7 : y ∈ B1 ∧ R b y) from h6
    have h8 : R y a := h4 y h7.left
    exact h1.right.left b y a h7.right h8
  · assume h4 : upperBd R a B2
    define at h4; define; fix b; assume h5 : b ∈ B1
    have h6 : ∃ (y : A), y ∈ B2 ∧ R b y := h2 b h5
    obtain (y : A) (h7 : y ∈ B2 ∧ R b y) from h6
    have h8 : R y a := h4 y h7.left
    exact h1.right.left b y a h7.right h8
  done

-- 9.
theorem Exercise_4_4_22 {A : Type}
    (R : BinRel A) (B1 B2 : Set A) (x1 x2 : A)
    (h1 : partial_order R) (h2 : lub R x1 B1) (h3 : lub R x2 B2) :
    B1 ⊆ B2 → R x1 x2 := by
  assume h4 : B1 ⊆ B2
  define at h2; define at h3
  have h5 : x2 ∈ {c : A | upperBd R c B1} := by
    define; fix x; assume h5 : x ∈ B1
    have h6 : x ∈ B2 := h4 h5
    have h7 : x2 ∈ {c : A | upperBd R c B2} := h3.left
    define at h7
    exact h7 x h6
  exact h2.right x2 h5
  done

-- 10.
theorem Exercise_4_4_24 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (R ∪ (inv R))
    { T : Set (A × A) | R ⊆ T ∧ symmetric (RelFromExt T) } := by
  define
  apply And.intro
  · define
    apply And.intro
    · define; fix a; assume h; left; exact h
    · define; fix x; fix y; assume h : RelFromExt (R ∪ inv R) x y
      define; define at h
      by_cases on h
      · right; define; exact h
      · left; define at h; exact h
  · fix F; assume h
    define at h; define; fix (a, a'); assume h1
    by_cases on h1
    · exact h.left h1
    · define at h1
      have h2 : RelFromExt F a' a := by
        define; exact h.left h1
      have h3 : symmetric (RelFromExt F) := h.right
      define at h3
      exact h3 a' a h2
  done

/- Section 4.5 -/
-- 1.
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

-- 2.
lemma Lemma_4_5_7_ref {A : Type} (F : Set (Set A)) (h : partition F):
    reflexive (EqRelFromPart F) := by
  define; fix a : A
  define; define at h
  have h1 : a ∈ ⋃₀ F := h.left a
  define at h1; obtain (B : Set A) (h2 : B ∈ F ∧ a ∈ B) from h1
  apply Exists.intro B
  exact And.intro h2.left (And.intro h2.right h2.right)
  done

-- 3.
lemma Lemma_4_5_7_symm {A : Type} (F : Set (Set A)) (h : partition F):
    symmetric (EqRelFromPart F) := by
  define; fix x; fix y; assume h1 : EqRelFromPart F x y
  define at h1; define
  obtain (X : Set A) (h2 : X ∈ F ∧ x ∈ X ∧ y ∈ X) from h1
  apply Exists.intro X
  exact And.intro h2.left (And.intro h2.right.right h2.right.left)
  done

-- 4.
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

-- 5.
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

-- 6.
lemma elt_mod_equiv_class_of_elt
    {A : Type} (R : BinRel A) (h : equiv_rel R) :
    ∀ X ∈ mod A R, ∀ x ∈ X, equivClass R x = X := by
  fix X; assume h1 : X ∈ mod A R
  fix x; assume hxX : x ∈ X
  define at h1
  obtain (x' : A) (hx' : equivClass R x' = X) from h1
  have hxRx' : x ∈ equivClass R x' := by
    rw [hx']; exact hxX
  have hRxRx' : equivClass R x = equivClass R x' := (Lemma_4_5_5_2 R h x' x).mp hxRx'
  rw [hRxRx']; exact hx'
  done

-- Definitions for next three exercises:
def dot {A : Type} (F G : Set (Set A)) : Set (Set A) :=
    { Z : Set A | ¬empty Z ∧ ∃ X ∈ F, ∃ Y ∈ G, Z = X ∩ Y }

def conj {A : Type} (R S : BinRel A) (x y : A) : Prop :=
    R x y ∧ S x y

-- 7.
theorem Exercise_4_5_20a {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    equiv_rel (conj R S) := by
  define at h1; define at h2; define
  apply And.intro
  · define; fix a; define
    apply And.intro (h1.left a) (h2.left a)
  · apply And.intro
    · define; fix x; fix y; assume h : conj R S x y
      define at h; define
      exact And.intro (h1.right.left x y h.left) (h2.right.left x y h.right)
    · define; fix x; fix y; fix z
      assume hxy : conj R S x y
      assume hyz : conj R S y z
      define at hxy; define at hyz; define
      apply And.intro
      · exact h1.right.right x y z hxy.left hyz.left
      · exact h2.right.right x y z hxy.right hyz.right
  done

-- 8.
theorem Exercise_4_5_20b {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    ∀ (x : A), equivClass (conj R S) x =
      equivClass R x ∩ equivClass S x := by
  fix a; ext x; apply Iff.intro
  · assume h : x ∈ equivClass (conj R S) a
    define at h; exact h
  · assume h : x ∈ equivClass R a ∩ equivClass S a
    define; exact h
  done

-- 9.
theorem Exercise_4_5_20c {A : Type} (R S : BinRel A)
    (h1 : equiv_rel R) (h2 : equiv_rel S) :
    mod A (conj R S) = dot (mod A R) (mod A S) := by
  ext X; apply Iff.intro
  · assume h : X ∈ mod A (conj R S)
    define at h; obtain (a : A) (ha : equivClass (conj R S) a = X) from h
    define
    apply And.intro
    · have haclass : a ∈ equivClass (conj R S) a := by
        define; exact And.intro (h1.left a) (h2.left a)
      have haX : a ∈ X := by
        rw [← ha]; exact haclass
      by_contra hX; define at hX; quant_neg at hX
      have haXneg : ¬a ∈ X := hX a
      show False from haXneg haX
    · apply Exists.intro (equivClass R a)
      apply And.intro
      · define; apply Exists.intro a; rfl
      · apply Exists.intro (equivClass S a)
        apply And.intro
        · define; apply Exists.intro a; rfl
        · rw [← ha]
          exact Exercise_4_5_20b R S h1 h2 a
  · assume h : X ∈ dot (mod A R) (mod A S)
    define at h
    have hXnempty := h.left; define at hXnempty; double_neg at hXnempty
    obtain (x : A) (hxX : x ∈ X) from hXnempty
    have h' : ∃ (X_1 : Set A), X_1 ∈ mod A R ∧ ∃ (Y : Set A), Y ∈ mod A S ∧ X = X_1 ∩ Y := h.right
    obtain (X1 : Set A) (hX1 : X1 ∈ mod A R ∧ ∃ (Y : Set A), Y ∈ mod A S ∧ X = X1 ∩ Y) from h'
    have h'' : ∃ (Y : Set A), Y ∈ mod A S ∧ X = X1 ∩ Y := hX1.right
    obtain (X2 : Set A) (hX2 : X2 ∈ mod A S ∧ X = X1 ∩ X2) from h''
    have hX1mod : X1 ∈ mod A R := hX1.left
    have hX2mod : X2 ∈ mod A S := hX2.left
    define at hX1mod; define at hX2mod
    obtain (a1 : A) (ha1 : equivClass R a1 = X1) from hX1mod
    obtain (a2 : A) (ha2 : equivClass S a2 = X2) from hX2mod
    have hxinter : x ∈ X1 ∩ X2 := by
      rw [← hX2.right]; exact hxX
    have hxX1 : x ∈ X1 := Set.mem_of_mem_inter_left hxinter
    have hxX2 : x ∈ X2 := Set.mem_of_mem_inter_right hxinter
    have hxX1 : equivClass R x = X1 := elt_mod_equiv_class_of_elt R h1 X1 hX1.left x hxX1
    have hxX2 : equivClass S x = X2 := elt_mod_equiv_class_of_elt S h2 X2 hX2.left x hxX2
    define; apply Exists.intro x
    rw [Exercise_4_5_20b R S h1 h2 x, hxX1, hxX2]
    exact hX2.right.symm
  done

-- 10.
def equiv_mod (m x y : Int) : Prop := m ∣ (x - y)

theorem Theorem_4_5_10 : ∀ (m : Int), equiv_rel (equiv_mod m) := by
  fix m : ℤ
  define
  apply And.intro
  · define; fix x
    define; apply Exists.intro 0
    ring
  · apply And.intro
    · define; fix y; fix z; assume h : equiv_mod m y z
      define at h; define
      obtain (c : ℤ) (h' : y - z = m * c) from h
      apply Exists.intro (-1 * c)
      simp; rw [← h']; ring
    · define; fix x; fix y; fix z
      assume h1 : equiv_mod m x y; assume h2 : equiv_mod m y z
      define at h1; define at h2; define
      obtain (c₁ : ℤ) (hc₁ : x - y = m * c₁) from h1
      obtain (c₂ : ℤ) (hc₂ : y - z = m * c₂) from h2
      apply Exists.intro (c₁ + c₂)
      rw [mul_add, ← hc₁, ← hc₂]
      ring
  done
