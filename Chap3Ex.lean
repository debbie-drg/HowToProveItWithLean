import HTPILib.Chap3
namespace HTPI.Exercises

/- Sections 3.1 and 3.2 -/
-- 1.
theorem Exercise_3_2_1a (P Q R : Prop)
    (h1 : P → Q) (h2 : Q → R) : P → R := by
  assume h : P
  apply h2
  apply h1
  exact h
  done

-- 2.
theorem Exercise_3_2_1b (P Q R : Prop)
    (h1 : ¬R → (P → ¬Q)) : P → (Q → R) := by
  assume h2 : P
  assume h3 : Q
  by_contra h4 -- The goal was `R`, so now we assume `¬R` and need to show `False`
  have h5 : ¬Q := (h1 h4) h2
  exact h5 h3

-- 3.
theorem Exercise_3_2_2a (P Q R : Prop)
    (h1 : P → Q) (h2 : R → ¬Q) : P → ¬R := by
  assume h3 : P
  by_contra h4
  have h5 : Q := h1 h3
  have h6 : ¬Q := h2 h4
  show False from h6 h5
  done

-- 4.
theorem Exercise_3_2_2b (P Q : Prop)
    (h1 : P) : Q → ¬(Q → ¬P) := by
  assume h2 : Q
  by_contra h3
  have h4 : ¬P := h3 h2
  show False from h4 h1
  done

/- Section 3.3 -/
-- 1.
theorem Exercise_3_3_1
    (U : Type) (P Q : Pred U) (h1 : ∃ (x : U), P x → Q x) :
    (∀ (x : U), P x) → ∃ (x : U), Q x := by
  intro h2
  obtain (x : U) (h3 : P x → Q x) from h1
  have h4 : P x := h2 x
  have h5 : Q x := h3 h4
  apply Exists.intro x h5
  done

-- 2.
theorem Exercise_3_3_8 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : A ⊆ ⋃₀ F := by
  define
  fix a : U
  assume h2 : a ∈ A
  define
  apply Exists.intro A _
  exact And.intro h1 h2
  done

-- 3.
theorem Exercise_3_3_9 (U : Type) (F : Set (Set U)) (A : Set U)
    (h1 : A ∈ F) : ⋂₀ F ⊆ A := by
  define
  fix a : U
  assume h2 : a ∈ ⋂₀ F
  define at h2
  exact h2 A h1
  done

-- 4.
theorem Exercise_3_3_10 (U : Type) (B : Set U) (F : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → B ⊆ A) : B ⊆ ⋂₀ F := by
  define
  fix a : U
  assume h2 : a ∈ B
  define
  fix C : Set U
  assume h3 : C ∈ F
  have h4 : B ⊆ C := h1 C h3
  define at h4
  exact h4 h2
  done

-- 5.
theorem Exercise_3_3_13 (U : Type)
    (F G : Set (Set U)) : F ⊆ G → ⋂₀ G ⊆ ⋂₀ F := by
  assume h1 : F ⊆ G
  define
  fix a : U
  assume h2 : a ∈ ⋂₀ G
  define
  fix t : Set U
  assume h3 : t ∈ F
  define at h1
  have h4 : t ∈ G := h1 h3
  define at h2
  exact h2 t h4
  done

/- Section 3.4 -/
-- 1.
theorem Exercise_3_4_2 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊆ C) : A ⊆ B ∩ C := by
  define
  fix a : U
  assume h3 : a ∈ A
  apply And.intro
  · exact h1 h3
  · exact h2 h3
  done

-- 2.
theorem Exercise_3_4_4 (U : Type) (A B C : Set U)
    (h1 : A ⊆ B) (h2 : A ⊈ C) : B ⊈ C := by
  define
  define at h2
  quant_neg at h2
  obtain (a : U) (h3 : ¬(a ∈ A → a ∈ C)) from h2
  conditional at h3
  quant_neg
  apply Exists.intro a
  conditional
  exact ⟨h1 h3.left, h3.right⟩
  done

-- 3.
theorem Exercise_3_3_16 (U : Type) (B : Set U)
    (F : Set (Set U)) : F ⊆ 𝒫 B → ⋃₀ F ⊆ B := by
  assume h1 : F ⊆ 𝒫 B
  define at h1
  define
  fix a : U
  assume h2 : a ∈ ⋃₀ F
  define at h2
  obtain (t : Set U) (h3 : t ∈ F ∧ a ∈ t) from h2
  have h4 : t ∈ 𝒫 B := h1 h3.left
  define at h4
  exact h4 h3.right
  done

-- 4.
theorem Exercise_3_3_17 (U : Type) (F G : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ⊆ B) :
    ⋃₀ F ⊆ ⋂₀ G := by
  define
  fix a : U
  assume h2 : a ∈ ⋃₀ F
  define at h2
  obtain (t : Set U) (h3 : t ∈ F ∧ a ∈ t) from h2
  have h4 : ∀ (B : Set U), B ∈ G → t ⊆ B := h1 t h3.left
  define
  fix p : Set U
  assume h5 : p ∈ G
  have h6 : t ⊆ p := h4 p h5
  exact h6 h3.right
  done

-- 5.
theorem Exercise_3_4_7 (U : Type) (A B : Set U) :
    𝒫 (A ∩ B) = 𝒫 A ∩ 𝒫 B := by
  ext c
  apply Iff.intro
  · assume h1 : c ∈ 𝒫(A ∩ B)
    define at h1
    define
    apply And.intro
    · define
      fix a
      assume h2 : a ∈ c
      exact (h1 h2).left
    · define
      fix a
      assume h2 : a ∈ c
      exact (h1 h2).right
  · assume h1 : c ∈ 𝒫 A ∩ 𝒫 B
    define
    fix a
    assume h2 : a ∈ c
    define at h1
    apply And.intro
    · have h3 : c ∈ 𝒫 A := h1.left
      define at h3
      exact h3 h2
    · have h3 : c ∈ 𝒫 B := h1.right
      define at h3
      exact h3 h2
  done

-- 6.
theorem Exercise_3_4_17 (U : Type) (A : Set U) : A = ⋃₀ (𝒫 A) := by
  ext x
  apply Iff.intro
  · assume h1 : x ∈ A
    define
    apply Exists.intro A
    apply And.intro
    · define
      fix a : U
      assume h2 : a ∈ A
      exact h2
    exact h1
  · assume h1 : x ∈ ⋃₀ (𝒫 A)
    define at h1
    obtain (t : Set U) (h2 : t ∈ 𝒫 A ∧ x ∈ t) from h1
    have h3 : t ∈ 𝒫 A := h2.left
    define at h3
    exact h3 h2.right
  done

-- 7.
theorem Exercise_3_4_18a (U : Type) (F G : Set (Set U)) :
    ⋃₀ (F ∩ G) ⊆ (⋃₀ F) ∩ (⋃₀ G) := by
  define
  fix a : U
  assume h1 : a ∈ ⋃₀ (F ∩ G)
  define at h1
  obtain (t : Set U) (h2 : t ∈ F ∩ G ∧ a ∈ t) from h1
  have h3 : a ∈ t := h2.right
  have h4 : t ∈ F ∩ G := h2.left
  apply And.intro
  · define
    use t
    exact ⟨h4.left, h3⟩
  · define
    use t
    exact ⟨h4.right, h3⟩
  done

-- 8.
theorem aux (U : Type) (F : Set (Set U)) (A : Set U) (t : U) :
    (t ∈ A) → (A ∈ F) → (t ∈ ⋃₀ F) := by
  assume h1 : t ∈ A
  assume h2 : A ∈ F
  define
  apply Exists.intro A
  exact ⟨h2, h1⟩


theorem Exercise_3_4_19 (U : Type) (F G : Set (Set U)) :
    (⋃₀ F) ∩ (⋃₀ G) ⊆ ⋃₀ (F ∩ G) ↔
      ∀ (A B : Set U), A ∈ F → B ∈ G → A ∩ B ⊆ ⋃₀ (F ∩ G) := by
  apply Iff.intro
  · assume h1 : ⋃₀ F ∩ ⋃₀ G ⊆ ⋃₀ (F ∩ G)
    fix A : Set U
    fix B : Set U
    assume h2 : A ∈ F
    assume h3 : B ∈ G
    define
    fix a : U
    assume h4 : a ∈ A ∩ B
    define at h1
    have h5 : a ∈ ⋃₀ F := aux U F A a h4.left h2
    have h6 : a ∈ ⋃₀ G := aux U G B a h4.right h3
    exact h1 ⟨h5, h6⟩
  · intro h1
    define
    intro a
    assume h2 : a ∈ ⋃₀ F ∩ ⋃₀ G
    have h3 : a ∈ ⋃₀ F := h2.left
    define at h3
    obtain (C : Set U) (h4 : C ∈ F ∧ a ∈ C) from h3
    have h5 : a ∈ ⋃₀ G := h2.right
    define at h5
    obtain (D : Set U) (h6 : D ∈ G ∧ a ∈ D) from h5
    have h7 : a ∈ C ∩ D := ⟨h4.right, h6.right⟩
    have h8 : C ∩ D ⊆ ⋃₀ (F ∩ G) := h1 C D h4.left h6.left
    exact h8 h7
  done

/- Section 3.5 -/
-- 1.
theorem Exercise_3_5_2 (U : Type) (A B C : Set U) :
    (A ∪ B) \ C ⊆ A ∪ (B \ C) := by
  intro x
  assume h1 : x ∈ (A ∪ B) \ C
  define at h1
  have h2 : x ∈ A ∪ B := h1.left
  have h3 : ¬x ∈ C := h1.right
  define at h2
  by_cases on h2
  · left
    exact h2
  · right
    define
    exact ⟨h2, h3⟩
  done

-- 2.
theorem Exercise_3_5_5 (U : Type) (A B C : Set U)
    (h1 : A ∩ C ⊆ B ∩ C) (h2 : A ∪ C ⊆ B ∪ C) : A ⊆ B := by
  intro x
  assume h3 : x ∈ A
  have h4 : x ∈ A ∪ C := by
    left; exact h3
  have h5 : x ∈ B ∪ C := h2 h4
  by_cases on h5
  · exact h5
  · have h6 : x ∈ B ∩ C := h1 ⟨h3, h5⟩
    exact h6.left
  done

-- 3.
theorem Exercise_3_5_7 (U : Type) (A B C : Set U) :
    A ∪ C ⊆ B ∪ C ↔ A \ C ⊆ B \ C := by
  apply Iff.intro
  · assume h1 : A ∪ C ⊆ B ∪ C
    intro x
    assume h2 : x ∈ A \ C
    define at h2
    have h3 : x ∈ A ∪ C := by
      left; exact h2.left
    have h4 : x ∈ B ∪ C := h1 h3
    define
    by_cases on h4
    · exact ⟨h4, h2.right⟩
    · by_contra
      show False from h2.right h4
  · assume h1 : A \ C ⊆ B \ C
    intro x
    assume h2 : x ∈ A ∪ C
    or_left with h3
    by_cases on h2
    · have h4 : x ∈ B \ C := h1 ⟨h2, h3⟩
      exact h4.left
    by_contra
    show False from h3 h2
  done

-- 4.
theorem Exercise_3_5_8 (U : Type) (A B : Set U) :
    𝒫 A ∪ 𝒫 B ⊆ 𝒫 (A ∪ B) := by
  define
  fix X
  assume h1 : X ∈ 𝒫 A ∪ 𝒫 B
  define
  fix a
  assume h2 : a ∈ X
  by_cases on h1
  · define at h1
    have h3 : a ∈ A := h1 h2
    left; exact h3
  · define at h1
    have h3 : a ∈ B := h1 h2
    right; exact h3
  done

-- 5.
theorem Exercise_3_5_17b (U : Type) (F : Set (Set U)) (B : Set U) :
    B ∪ (⋂₀ F) = { x : U | ∀ (A : Set U), A ∈ F → x ∈ B ∪ A } := by
  ext x
  apply Iff.intro
  · assume h1
    define
    fix A : Set U
    assume h2 : A ∈ F
    by_cases on h1
    · left; exact h1
    · define at h1
      have h3 : x ∈ A := h1 A h2
      right; exact h3
  · assume h1
    define at h1
    define
    or_right with h2
    define
    fix A : Set U; assume h3 : A ∈ F
    have h4 : x ∈ B ∪ A := h1 A h3
    disj_syll h4 h2
    exact h4
  done

-- 6.
theorem Exercise_3_5_18 (U : Type) (F G H : Set (Set U))
    (h1 : ∀ (A : Set U), A ∈ F → ∀ (B : Set U), B ∈ G → A ∪ B ∈ H) :
    ⋂₀ H ⊆ (⋂₀ F) ∪ (⋂₀ G) := by
  intro x; assume h2 : x ∈ ⋂₀ H
  define at h2
  define
  or_right with h3
  define at h3
  quant_neg at h3
  obtain (C : Set U) (h4 : ¬(C ∈ F → x ∈ C)) from h3
  conditional at h4
  define
  fix D; assume h5 : D ∈ G
  have h6 : C ∪ D ∈ H := h1 C h4.left D h5
  have h7 : x ∈ C ∪ D := h2 (C ∪ D) h6
  disj_syll h7 h4.right
  exact h7
  done

-- 7.
theorem Exercise_3_5_24a (U : Type) (A B C : Set U) :
    (A ∪ B) △ C ⊆ (A △ C) ∪ (B △ C) := by
  define
  fix x; assume h1 : x ∈ (A ∪ B) △ C
  define at h1
  define
  by_cases on h1
  · define at h1
    have h2 : x ∈ A ∪ B := h1.left
    by_cases on h2
    · left
      have h3 : x ∈ A \ C := ⟨h2, h1.right⟩
      define; left; exact h3
    · right
      have h3 : x ∈ B \ C := ⟨h2, h1.right⟩
      define; left; exact h3
  · define at h1
    have h2 : ¬x ∈ A ∪ B := h1.right
    define at h2; demorgan at h2
    have h3 : x ∈ C \ A := ⟨h1.left, h2.left⟩
    left; right; exact h3
  done

/- Section 3.6 -/
-- 1.
theorem Exercise_3_4_15 (U : Type) (B : Set U) (F : Set (Set U)) :
    ⋃₀ { X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B }
      ⊆ ⋃₀ (F \ 𝒫 B) := by
  define; fix a : U; assume h1
  define at h1
  obtain (C : Set U) (h2 : C ∈ {X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B} ∧ a ∈ C) from h1
  have h3 : a ∈ C := h2.right
  have h4 : C ∈ {X : Set U | ∃ (A : Set U), A ∈ F ∧ X = A \ B} := h2.left
  define at h4
  obtain (D : Set U) (h5 : D ∈ F ∧ C = D \ B) from h4
  define
  apply Exists.intro D
  apply And.intro
  · define
    apply And.intro
    · exact h5.left
    · define
      quant_neg
      apply Exists.intro a
      conditional
      have h6 : C = D \ B := h5.right
      rw [h6] at h3
      exact h3
  have h6 : C = D \ B := h5.right
  rw [h6] at h3
  exact h3.left
  done

-- 2.
theorem Exercise_3_5_9 (U : Type) (A B : Set U)
    (h1 : 𝒫 (A ∪ B) = 𝒫 A ∪ 𝒫 B) : A ⊆ B ∨ B ⊆ A := by
  --Hint:  Start like this:
  have h2 : A ∪ B ∈ 𝒫 (A ∪ B) := by
    define; intro a; assume h3; exact h3
  rw [h1] at h2
  by_cases on h2
  · define at h2
    right
    define; fix b; assume h3 : b ∈ B
    have h4 : b ∈ A ∪ B := by
      right; exact h3
    exact h2 h4
  · define at h2
    left
    define; fix a; assume h3 : a ∈ A
    have h4 : a ∈ A ∪ B := by
      left; exact h3
    exact h2 h4
  done

-- 3.
theorem Exercise_3_6_6b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∪ B = A := by
  exists_unique
  · apply Exists.intro Set.univ
    fix B; exact Set.univ_union
  · fix A; fix B; assume h1; assume h2
    have h3 : A ∪ B = A := h1 B
    have h4 : B ∪ A = B := h2 A
    show A = B := by
      calc A
        _ = A ∪ B := h3.symm
        _ = B ∪ A := Set.union_comm A B
        _ = B := h4
      done
  done

-- 4.
theorem Exercise_3_6_7b (U : Type) :
    ∃! (A : Set U), ∀ (B : Set U), A ∩ B = A := by
  exists_unique
  · apply Exists.intro ∅
    exact Set.empty_inter
  · fix A; fix B; assume h1
    assume h2
    have h3 : A ∩ B = A := h1 B
    have h4 : B ∩ A = B := h2 A
    show A = B := by
      calc A
        _ = A ∩ B := h3.symm
        _ = B ∩ A := Set.inter_comm A B
        _ = B := h4
      done
    done

-- 5.
theorem minus_complement (U : Type) : ∀ (A : Set U), Aᶜ \ A = Aᶜ := by
  fix A; ext x; apply Iff.intro
  · assume h
    define at h
    exact h.left
  · assume h1
    have h2 : ¬x ∈ A := by
      define at h1
      exact h1
    exact ⟨h1, h2⟩
  done

theorem all_set_or_compl (U : Type) (x : U): ∀ (A : Set U), x ∈ A ∨ x ∈ Aᶜ := by
  fix A
  or_left with h
  define at h
  double_neg at h
  exact h

theorem Exercise_3_6_8a (U : Type) : ∀ (A : Set U),
    ∃! (B : Set U), ∀ (C : Set U), C \ A = C ∩ B := by
  fix A; exists_unique
  · apply Exists.intro Aᶜ
    fix C; ext x; apply Iff.intro
    · assume h1 : x ∈ C \ A
      define at h1
      exact h1
    · assume h1 : x ∈ C ∩ Aᶜ
      define at h1
      exact h1
  · fix C; fix D; assume h1; assume h2
    have h3 : A ∩ C = ∅ := by
      have h3 : A \ A = A ∩ C := h1 A
      rw [Set.diff_self] at h3
      exact h3.symm
    have h4 : A ∩ D = ∅ := by
      have h3 : A \ A = A ∩ D := h2 A
      rw [Set.diff_self] at h3
      exact h3.symm
    ext x
    have h : x ∈ A ∨ x ∈ Aᶜ := all_set_or_compl U x A
    by_cases on h
    · have h5 : ¬x ∈ C := by
        by_contra h5
        have h6 : x ∈ A ∩ C := ⟨h, h5⟩
        rw [h3] at h6
        show False from h6
      have h6 : ¬x ∈ D := by
        by_contra h6
        have h7 : x ∈ A ∩ D := ⟨h, h6⟩
        rw [h4] at h7
        show False from h7
      by_contra h8
      bicond_neg at h8
      rw [h8] at h5
      show False from h6 h5
    · have h5 : D \ A = D ∩ C := h1 D
      have h6 : C \ A = C ∩ D := h2 C
      define at h
      apply Iff.intro
      · assume h7 : x ∈ C
        have h8 : x ∈ C \ A := ⟨h7, h⟩
        rw [h6] at h8
        exact h8.right
      · assume h7 : x ∈ D
        have h8 : x ∈ D \ A := ⟨h7, h⟩
        rw [h5] at h8
        exact h8.right
  done

-- 6.
theorem Exercise_3_6_10 (U : Type) (A : Set U)
    (h1 : ∀ (F : Set (Set U)), ⋃₀ F = A → A ∈ F) :
    ∃! (x : U), x ∈ A := by
  --Hint:  Start like this:
  set F0 : Set (Set U) := { X : Set U | X ⊆ A ∧ ∃! (x : U), x ∈ X }
  --Now F0 is in the tactic state, with the definition above
  have h2 : ⋃₀ F0 = A := by
    ext x
    apply Iff.intro;
    · assume h3; define at h3
      obtain (B : Set U) (h4 : B ∈ F0 ∧ x ∈ B) from h3
      have h5 : B ∈ F0 := h4.left
      define at h5
      exact h5.left h4.right
    · assume h2 : x ∈ A
      set Fx : Set U := {x}
      have h3 : Fx ⊆ A := by
        define
        fix a; assume h3 : a ∈ Fx
        have h4 : a = x := Set.eq_of_mem_singleton h3
        rw [← h4] at h2
        exact h2
      have h4 : ∃! (x : U), x ∈ Fx := by
        exists_unique
        · apply Exists.intro x
          rfl
        · fix y; fix z; assume h4; assume h5
          have h6 : y = x := Set.eq_of_mem_singleton h4
          have h7 : z = x := Set.eq_of_mem_singleton h5
          rw [h6, h7]
      define; apply Exists.intro Fx
      apply And.intro
      · define
        exact ⟨h3, h4⟩
      rfl
  have h3 : A ∈ F0 := h1 F0 h2
  define at h3
  exact h3.right
  done

/- Section 3.7 -/
-- 1.
theorem Exercise_3_3_18a (a b c : Int)
    (h1 : a ∣ b) (h2 : a ∣ c) : a ∣ (b + c) := by
  define; define at h1; define at h2
  obtain (d : ℤ) (h3 : b = a * d) from h1
  obtain (e : ℤ) (h4 : c = a * e) from h2
  apply Exists.intro (d + e)
  rw [mul_add, ← h3, ← h4]
  done

#check and_or_left

-- 2.
theorem Exercise_3_4_6 (U : Type) (A B C : Set U) :
    A \ (B ∩ C) = (A \ B) ∪ (A \ C) := by
  apply Set.ext
  fix x : U
  show x ∈ A \ (B ∩ C) ↔ x ∈ A \ B ∪ A \ C from
    calc x ∈ A \ (B ∩ C)
      _ ↔ x ∈ A ∧ ¬(x ∈ B ∧ x ∈ C) := by rfl
      _ ↔ x ∈ A ∧ (¬x ∈ B ∨ ¬x ∈ C) := by
        have h3 : ¬(x ∈ B ∧ x ∈ C) ↔ (¬x ∈ B ∨ ¬x ∈ C) := by
          demorgan; rfl
        rw [h3]
      _ ↔ (x ∈ A ∧ ¬x ∈ B) ∨ (x ∈ A ∧ ¬x ∈ C) := by apply and_or_left
      _ ↔ x ∈ (A \ B) ∪ (A \ C) := by rfl
  done

-- 3.
theorem Exercise_3_4_10 (x y : Int)
    (h1 : odd x) (h2 : odd y) : even (x - y) := by
  define at h1; define at h2; define
  obtain (k₁ : ℤ) (h3 : x = 2 * k₁ + 1) from h1
  obtain (k₂ : ℤ) (h4 : y = 2 * k₂ + 1) from h2
  apply Exists.intro (k₁ - k₂)
  rw [h3, h4]
  ring

-- 4.
theorem Exercise_3_4_27a :
    ∀ (n : Int), 15 ∣ n ↔ 3 ∣ n ∧ 5 ∣ n := by
  fix n
  apply Iff.intro
  · -- (→)
    assume h1 : 15 ∣ n
    define at h1
    obtain (c : ℤ) (h2 : n = 15 * c) from h1
    apply And.intro
    · define
      apply Exists.intro (5 * c)
      rw [h2]; ring
    · define
      apply Exists.intro (3 * c)
      rw [h2]; ring
  · -- (←)
    assume h : 3 ∣ n ∧ 5 ∣ n
    have h1 : 3 ∣ n := h.left
    have h2 : 5 ∣ n := h.right
    define at h1; define at h2
    obtain (c₁ : ℤ) (h3 : n = 3 * c₁) from h1
    obtain (c₂ : ℤ) (h4 : n = 5 * c₂) from h2
    define
    have h5 : 15 * (2 * c₂ - c₁) = n :=
      calc 15 * (2 * c₂ - c₁)
        _ = 6 * (5 * c₂) - 5 * (3 * c₁) := by ring
        _ = 6 * n - 5 * n := by rw [← h3, ← h4]
        _ = n := by ring
    apply Exists.intro (2 * c₂ - c₁)
    exact h5.symm
  done

-- 5.
theorem Like_Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ { 𝒫 A | A ∈ F }) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := by
  have h2 : ⋃₀ F ∈ 𝒫 (⋃₀ F) := by
    have h3 : ⋃₀ F ⊆ ⋃₀ F := by rfl
    exact Set.mem_powerset h3
  have h3 :  ⋃₀ F ∈ ⋃₀ { 𝒫 A | A ∈ F } := h1 h2
  define at h3
  obtain (B : Set (Set U)) (h4 : B ∈ {x : Set (Set U) | ∃ (A : Set U), A ∈ F ∧ 𝒫 A = x} ∧ ⋃₀ F ∈ B) from h3
  have h5 : B ∈ {x : Set (Set U) | ∃ (A : Set U), A ∈ F ∧ 𝒫 A = x} := h4.left
  define at h5
  obtain (A : Set U) (h6 : A ∈ F ∧ 𝒫 A = B) from h5
  apply Exists.intro A
  apply And.intro
  · exact h6.left
  · fix C; assume h7 : C ∈ F
    have h8 : 𝒫 A = B := h6.right
    have h9 : ⋃₀ F ∈ B := h4.right
    rw [← h8] at h9
    define at h9
    define; fix a
    assume h10 : a ∈ C
    have h11 : a ∈ ⋃₀ F := by
      define
      apply Exists.intro C
      exact ⟨h7, h10⟩
    exact h9 h11
