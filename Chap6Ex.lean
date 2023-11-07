import HTPILib.Chap6
namespace HTPI.Exercises

/- Section 6.1 -/
-- 1.
theorem Like_Exercise_6_1_1 :
    ∀ (n : Nat), 2 * Sum i from 0 to n, i = n * (n + 1) := by
  by_induc
  · rw [sum_base]
  · fix n : ℕ
    assume ih : 2 * Sum i from 0 to n, i = n * (n + 1)
    show 2 * Sum i from 0 to n + 1, i = (n + 1) * (n + 1 + 1) from
      calc 2 * Sum i from 0 to n + 1, i
        _ = 2 * ((Sum i from 0 to n, i) + (n + 1)) := by rw [sum_from_zero_step]
        _ = 2 * (Sum i from 0 to n, i) + 2 * (n + 1) := by ring
        _ = n * (n + 1) + 2 * (n + 1) := by rw [ih]
        _ = (n + 1) * (n + 1 + 1) := by ring
  done

-- 2.
theorem Like_Exercise_6_1_4 :
    ∀ (n : Nat), Sum i from 0 to n, 2 * i + 1 = (n + 1) ^ 2 := by
  by_induc
  · rw [sum_base]
    rfl
  · fix n : ℕ
    assume ih : Sum i from 0 to n, 2 * i + 1 = (n + 1) ^ 2
    show Sum i from 0 to n + 1, 2 * i + 1 = (n + 1 + 1) ^ 2 from
      calc Sum i from 0 to n + 1, 2 * i + 1
        _ = (Sum i from 0 to n, 2 * i + 1) + (2 * (n + 1) + 1) := by rw [sum_from_zero_step]
        _ = (n + 1) ^ 2 + (2 * (n + 1) + 1) := by rw [ih]
        _ = (n + 1 + 1) ^ 2 := by ring
  done

-- 3.
theorem Exercise_6_1_9a : ∀ (n : Nat), 2 ∣ n ^ 2 + n := by
  by_induc
  · define
    apply Exists.intro 0
    rfl
  · fix n : ℕ
    assume ih : 2 ∣ n ^ 2 + n
    define at ih
    obtain (c : ℕ) (h1 : n ^ 2 + n = 2 * c) from ih
    define
    apply Exists.intro (c + n + 1)
    show (n + 1) ^ 2 + (n + 1) = 2 * (c + n + 1) from
      calc (n + 1) ^ 2 + (n + 1)
        _ = (n ^ 2 + n) + 2 * (n + 1) := by ring
        _ = 2 * c + 2 * (n + 1) := by rw [h1]
        _ = 2 * (c + n + 1) := by ring
  done

-- 4.
theorem Exercise_6_1_13 :
    ∀ (a b : Int) (n : Nat), (a - b) ∣ (a ^ n - b ^ n) := by
  fix a : ℤ; fix b : ℤ
  by_induc
  · -- Base case
    define; apply Exists.intro 0; ring
  · -- Inductive case
    fix n : ℕ
    assume ih : a - b ∣ a ^ n - b ^ n
    define at ih
    obtain (c : ℤ) (h1 : a ^ n - b ^ n = (a - b) * c) from ih
    define
    apply Exists.intro (a * c + b ^ n)
    show a ^ (n + 1) - b ^ (n + 1) = (a - b) * (a * c + b ^ n) from
      calc a ^ (n + 1) - b ^ (n + 1)
        _ = a * (a ^ n - b ^ n) + b ^ n * (a - b) := by ring
        _ = a * ((a - b) * c) + b ^ n * (a - b) := by rw [h1]
        _ = (a - b) * (a * c + b ^ n) := by ring
  done

-- 5.
theorem Exercise_6_1_15 : ∀ n ≥ 10, 2 ^ n > n ^ 3 := by
  by_induc
  · linarith
  · fix n; assume h1 : n ≥ 10
    assume ih : 2 ^ n > n ^ 3
    have h2 : n * n ≥ n * 10 := ge_iff_le.mpr (Nat.mul_le_mul_left n h1)
    have h3 : n * (n * n) ≥ n * (n * 10) := ge_iff_le.mpr (Nat.mul_le_mul_left n h2)
    show 2 ^ (n + 1) > (n + 1) ^ 3 from
      calc 2 ^ (n + 1)
        _ = 2 * 2 ^ n := by ring
        _ > 2 * n ^ 3 := by linarith
        _ ≥ n ^ 3 + 10 * n ^ 2 := by linarith
        _ ≥ n ^ 3 + 3 * n ^ 2 + 3 * n + 1 := by linarith
        _ = (n + 1) ^ 3 := by ring
  done

-- 6.
lemma nonzero_is_successor :
    ∀ (n : Nat), n ≠ 0 → ∃ (m : Nat), n = m + 1 := by
  by_induc
  · assume h1 : 0 ≠ 0
    by_contra h2
    apply h1
    rfl
  · fix n
    assume ih : n ≠ 0 → ∃ (m : ℕ), n = m + 1
    assume h2 : n + 1 ≠ 0
    apply Exists.intro n
    rfl
  done

-- 7.
theorem Exercise_6_1_16a1 :
    ∀ (n : Nat), nat_even n ∨ nat_odd n := by
  by_induc
  · left
    define
    apply Exists.intro 0
    rfl
  · fix n
    assume ih : nat_even n ∨ nat_odd n
    by_cases on ih
    · define at ih
      obtain (k : ℕ) (h1 : n = 2 * k) from ih
      right; define; apply Exists.intro k
      rw [h1]
    · define at ih
      obtain (k : ℕ) (h1 : n = 2 * k + 1) from ih
      left; define; apply Exists.intro (k + 1)
      show n + 1 = 2 * (k + 1) from
        calc n + 1
          _ = 2 * k + 1 + 1 := by rw [h1]
          _ = 2 * (k + 1) := by ring
  done

-- 8.
--Hint:  You may find the lemma nonzero_is_successor
--from a previous exercise useful, as well as Nat.add_right_cancel.
theorem Exercise_6_1_16a2 :
    ∀ (n : Nat), ¬(nat_even n ∧ nat_odd n) := by
  by_induc
  · demorgan; right; define; quant_neg
    fix k
    linarith
  · fix n; assume h1 : ¬(nat_even n ∧ nat_odd n)
    demorgan at h1
    demorgan
    by_cases on h1
    · right
      define; quant_neg; fix k
      by_contra h2
      have h3 : n  = 2 * k := Nat.add_right_cancel h2
      apply h1; define; apply Exists.intro k; exact h3
    · left
      define; quant_neg; fix k
      by_contra h2
      apply h1
      have h3 : ¬k = 0 := by
        by_contra h3
        rw [h3] at h2
        linarith
      obtain (k' : ℕ) (h4 : k = k' + 1) from nonzero_is_successor k h3
      define
      apply Exists.intro k'
      linarith
  done

/- Section 6.2 -/
-- 1.
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

-- 2.
lemma extendPO_is_ref {A : Type} (R : BinRel A) (b : A)
    (h : partial_order R) : reflexive (extendPO R b) := by
  define
  fix x : A
  define
  left
  exact h.left x
  done

-- 3.
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

-- 4.
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

-- 5.
theorem Exercise_6_2_3 (A : Type) (R : BinRel A)
    (h : total_order R) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ (b : A), smallestElt R b B := by
  define at h
  have Rpart_ord : partial_order R := h.left
  define at Rpart_ord
  by_induc
  · fix B : Set A
    assume h1 : numElts B 1
    rw [one_elt_iff_singleton] at h1
    obtain (x : A) (h2 : B = {x}) from h1
    apply Exists.intro x
    define
    apply And.intro
    · rw [h2]; rfl
    · fix y : A; assume h3 : y ∈ B
      have h3 : y = x := by
        rw [h2] at h3
        define at h3
        exact h3
      rw [h3]
      exact Rpart_ord.left x
  · fix n : ℕ; assume h1 : n ≥ 1
    assume ih : ∀ (B : Set A), numElts B n → ∃ (b : A), smallestElt R b B
    fix B : Set A; assume h2 : numElts B (n + 1)
    have h3 : n + 1 > 0 := by linarith
    have h4 : ∃ (x : A), x ∈ B := nonempty_of_pos_numElts h2 h3
    obtain (b : A) (h5 : b ∈ B) from h4
    set B' : Set A := B \ {b}
    have h6 : numElts B' n := remove_one_numElts h2 h5
    have h7 : ∃ (b : A), smallestElt R b B' := ih B' h6
    obtain (b' : A) (h8 : smallestElt R b' B') from h7
    by_cases h9 : R b b'
    · apply Exists.intro b
      define; apply And.intro h5
      fix x : A; assume h10 : x ∈ B
      by_cases h11 : x = b
      · rw [h11]; exact Rpart_ord.left b
      · have h12 : x ∈ B' := And.intro h10 h11
        have h13 : R b' x := h8.right x h12
        exact Rpart_ord.right.left b b' x h9 h13
    · apply Exists.intro b'
      disj_syll (h.right b b') h9 with h10
      define; apply And.intro h8.left.left
      fix x : A; assume h12 : x ∈ B
      by_cases h11 : x = b
      · rw [h11]; exact h10
      · have h13 : x ∈ B' := And.intro h12 h11
        exact h8.right x h13
  done

-- 6.
--Hint:  First prove that R is reflexive
theorem Exercise_6_2_4a {A : Type} (R : BinRel A)
    (h : ∀ (x y : A), R x y ∨ R y x) : ∀ n ≥ 1, ∀ (B : Set A),
    numElts B n → ∃ x ∈ B, ∀ y ∈ B, ∃ (z : A), R x z ∧ R z y := by
  have Rrefl : reflexive R := by
    define; fix x; have h1 : R x x ∨ R x x := h x x
    by_cases on h1; exact h1; exact h1
  by_induc
  · fix B : Set A; assume h1 : numElts B 1
    rw [one_elt_iff_singleton] at h1
    obtain (x : A) (h2 : B = {x}) from h1
    apply Exists.intro x
    apply And.intro
    · rw [h2]; rfl
    · fix y; assume h3 : y ∈ B
      have h4 : y = x := by
        rw [h2] at h3; define at h3; exact h3
      rw [h4]
      apply Exists.intro x
      exact And.intro (Rrefl x) (Rrefl x)
  · fix n : ℕ
    assume h1 : n ≥ 1
    assume ih : ∀ (B : Set A), numElts B n →
      ∃ (x : A), x ∈ B ∧ ∀ (y : A), y ∈ B → ∃ (z : A), R x z ∧ R z y
    fix B : Set A; assume h2 : numElts B (n + 1)
    have h3 : n + 1 > 0 := by linarith
    have h4 : ∃ (x : A), x ∈ B := nonempty_of_pos_numElts h2 h3
    obtain (b : A) (h5 : b ∈ B) from h4
    set B' : Set A := B \ {b}
    have h6 : numElts B' n := remove_one_numElts h2 h5
    have h7 : ∃ (x : A), x ∈ B' ∧ ∀ (y : A), y ∈ B' → ∃ (z : A),
      R x z ∧ R z y := ih B' h6
    obtain (x : A) (h8 : x ∈ B' ∧ ∀ (y : A), y ∈ B' → ∃ (z : A),
      R x z ∧ R z y) from h7
    by_cases h9 : ∃ (z : A), R x z ∧ R z b
    · apply Exists.intro x
      apply And.intro h8.left.left
      fix y : A; assume h10 : y ∈ B
      by_cases h11 : y = b
      · rw [h11]; exact h9
      · have h12 : y ∈ B' := And.intro h10 h11
        exact h8.right y h12
    · apply Exists.intro b
      apply And.intro h5
      fix y : A; assume h10 : y ∈ B
      by_cases h11 : y = b
      · rw [h11]
        apply Exists.intro b
        exact And.intro (Rrefl b) (Rrefl b)
      · have h12 : y ∈ B' := And.intro h10 h11
        obtain (z : A) (h13 : R x z ∧ R z y) from h8.right y h12
        have h14 : R b z := by
          by_contra h14
          disj_syll (h b z) h14 with h15
          apply h9; apply Exists.intro z
          exact And.intro h13.left h15
        apply Exists.intro z
        exact And.intro h14 h13.right
  done

-- 7.
theorem Like_Exercise_6_2_16 {A : Type} (f : A → A)
    (h : one_to_one f) : ∀ (n : Nat) (B : Set A), numElts B n →
    closed f B → ∀ y ∈ B, ∃ x ∈ B, f x = y := by
  by_induc
  · fix B : Set A; assume h1 : numElts B 0
    assume h2 : closed f B
    fix y : A; assume h3 : y ∈ B
    by_contra
    rw [zero_elts_iff_empty] at h1
    define at h1
    quant_neg at h1
    show False from h1 y h3
  · fix n : ℕ
    assume ih : ∀ (B : Set A), numElts B n → closed f B →
      ∀ (y : A), y ∈ B → ∃ (x : A), x ∈ B ∧ f x = y
    fix B : Set A; assume h1 : numElts B (n + 1)
    assume h2 : closed f B
    fix y : A; assume h3 : y ∈ B
    by_contra h4
    set B' : Set A := B \ {y}
    have h5 : closed f B' := by
      define
      fix x : A; assume h5 : x ∈ B'
      have h6 : x ∈ B := h5.left
      have h7 : f x ∈ B := h2 x h6
      have h8 : ¬f x = y := by
        by_contra h8
        apply h4
        apply Exists.intro x
        exact And.intro h6 h8
      exact And.intro h7 h8
    have h6 : n + 1 > 0 := by linarith
    have h7 : numElts B' n := remove_one_numElts h1 h3
    have h8 : ∀ (y : A), y ∈ B' → ∃ (x : A), x ∈ B' ∧ f x = y := ih B' h7 h5
    have h9 : f y ∈ B := h2 y h3
    have h10 : ¬f y = y := by
      by_contra h10
      apply h4
      apply Exists.intro y
      exact And.intro h3 h10
    have h11 : f y ∈ B' := And.intro h9 h10
    obtain (x : A) (h12 : x ∈ B' ∧ f x = f y) from h8 (f y) h11
    have h13 : x = y := h x y h12.right
    have h14 : ¬y ∈ B' := by
      define; demorgan; right; rfl
    apply h14; rw [← h13]; exact h12.left
  done

-- 8.
--Hint:  Use Exercise_6_2_2
theorem Example_6_2_2 {A : Type} (R : BinRel A)
    (h1 : ∃ (n : Nat), numElts { x : A | x = x } n)
    (h2 : partial_order R) : ∃ (T : BinRel A),
      total_order T ∧ ∀ (x y : A), R x y → T x y := by
  set B : Set A := {x : A | x = x}
  obtain (n : ℕ) (h3 : numElts B n) from h1
  obtain (T : BinRel A)
    (h4 : partial_order T ∧ (∀ (x y : A), R x y → T x y) ∧
    ∀ x ∈ B, ∀ (y : A), T x y ∨ T y x) from Exercise_6_2_2 R h2 n B h3
  apply Exists.intro T
  apply And.intro
  · define
    apply And.intro h4.left
    fix x; fix y
    have h5 : x ∈ B := rfl
    exact h4.right.right x h5 y
  · exact h4.right.left
  done

/- Section 6.3 -/
-- 1.
theorem Exercise_6_3_4 : ∀ (n : Nat),
    3 * (Sum i from 0 to n, (2 * i + 1) ^ 2) =
    (n + 1) * (2 * n + 1) * (2 * n + 3) := by
  by_induc
  · -- Base case
    rw [sum_base]
    linarith
  · -- Induction step
    fix n : ℕ
    assume ih : 3 * Sum i from 0 to n, (2 * i + 1) ^ 2
      = (n + 1) * (2 * n + 1) * (2 * n + 3)
    rw [sum_from_zero_step, mul_add, ih]
    linarith
  done

-- 2.
theorem Exercise_6_3_7b (f : Nat → Real) (c : Real) : ∀ (n : Nat),
    Sum i from 0 to n, c * f i = c * Sum i from 0 to n, f i := by
  by_induc
  · rw [sum_base, sum_base]
  · fix n : ℕ
    assume ih : Sum i from 0 to n, c * f i = c * Sum i from 0 to n, f i
    rw [sum_from_zero_step, ih, sum_from_zero_step]
    linarith
  done

-- 3.
theorem fact_pos : ∀ (n : Nat), fact n ≥ 1 := by
  by_induc
  · norm_num
  · fix n : ℕ
    assume ih : fact n ≥ 1
    show fact (n + 1) ≥ 1 from
      calc fact (n + 1)
        _ = (n + 1) * fact n := by rfl
        _ ≥ (n + 1) * 1 := by rel [ih]
        _ = n + 1 := by rw [mul_one]
        _ ≥ 1 := by linarith
  done

-- 4.
theorem power_law_nat : ∀ (a : Nat) (m n : Nat),
    a ^ (m + n) = a ^ m * a ^ n := by
  fix a : Nat; fix m : Nat; fix n : Nat
  ring
  done

--Hint:  Use the theorem fact_pos from the previous exercise
theorem Exercise_6_3_13a (k : Nat) : ∀ (n : Nat),
    fact (k ^ 2 + n) ≥ k ^ (2 * n) := by
  by_induc
  · -- Base case
    have h : k ^ (2 * 0) = 1 := by
      rw [mul_zero, pow_zero]
    rw [h]
    exact fact_pos (k ^ 2 + 0)
  · -- Induction step
    fix n : ℕ
    assume ih : fact (k ^ 2 + n) ≥ k ^ (2 * n)
    have h1 : k ≥ 0 := by linarith
    have h2 : k ^ (2 * n) ≥ 0 := pow_nonneg h1 (2 * n)
    have h3 : n + 1 ≥ 0 := by linarith
    have h4 : (n + 1) * k ^ (2 * n) ≥ 0 := mul_nonneg h3 h2
    have h5 : 2 + 2 * n = 2 * (n + 1) := by linarith
    show fact (k ^ 2 + (n + 1)) ≥ k ^ (2 * (n + 1)) from
      calc fact (k ^ 2 + (n + 1))
        _ = (k ^ 2 + (n + 1)) * fact (k ^ 2 + n) := by rfl
        _ ≥ (k ^ 2 + (n + 1)) * k ^ (2 * n) := by rel [ih]
        _ = (n + 1) * k ^ (2 * n) + (k ^ 2) * (k ^ (2 * n)) := by linarith
        _ ≥ (k ^ 2) * (k ^ (2 * n)) := by linarith
        _ = k ^ (2 + 2 * n) := (power_law_nat k 2 (2 * n)).symm
        _ = k ^ (2 * (n + 1)) := by rw [h5]
  done

-- 5.
--Hint:  Use the theorem in the previous exercise.
--You may find it useful to first prove a lemma:
--∀ (k : Nat), 2 * k ^ 2 + 1 ≥ k
lemma for_Exercise_6_3_13b : ∀ (k : Nat), 2 * k ^ 2 + 1 ≥ k := by
  by_induc
  · linarith
  · fix k : ℕ
    assume ih : 2 * k ^ 2 + 1 ≥ k
    have h1 : k ≥ 0 := by linarith
    have h2 : 4 * k + 1 ≥ 0 := by linarith
    show 2 * (k + 1) ^ 2 + 1 ≥ k + 1 from
      calc 2 * (k + 1) ^ 2 + 1
        _ = 2 * k ^ 2 + 4 * k + 2 + 1 := by linarith
        _ = (2 * k ^ 2 + 2) + (4 * k + 1) := by linarith
        _ ≥ (2 * k ^ 2 + 2) + 0 := by linarith
        _ = 2 * k ^ 2 + 2 := by rw [add_zero]
        _ ≥ (2 * k ^ 2 + 1) + 1 := by linarith
        _ ≥ k + 1 := by rel [ih]
  done

theorem Exercise_6_3_13b (k : Nat) : ∀ n ≥ 2 * k ^ 2,
    fact n ≥ k ^ n := by
  by_induc
  · -- Base case: just apply Exercise_6_3_13a
    have h1 : fact (k ^ 2 + k ^ 2) ≥ k ^ (2 * k ^ 2) := Exercise_6_3_13a k (k ^ 2)
    have h2 : k ^ 2 + k ^ 2 = 2 * k ^ 2 := by linarith
    rw [h2] at h1
    exact h1
  · -- Induction step
    fix n : ℕ
    assume h1 : n ≥ 2 * k ^ 2
    have h2 : n + 1 ≥ k := by
      have h3 : n + 1 ≥ 2 * k ^ 2 + 1 := by linarith
      have h4 : 2 * k ^ 2 + 1 ≥ k := for_Exercise_6_3_13b k
      linarith
    assume ih : fact n ≥ k ^ n
    show fact (n + 1) ≥ k ^ (n + 1) from
      calc fact (n + 1)
        _ = (n + 1) * fact n := by rfl
        _ ≥ (n + 1) * k ^ n := by rel [ih]
        _ ≥ k * k ^ n := by rel [h2]
        _ = k ^ 1 * k ^ n := by linarith
        _ = k ^ (1 + n) := (power_law_nat k 1 n).symm
        _ = k ^ (n + 1) := by rw [add_comm n 1]
  done

-- 6.
def seq_6_3_15 (k : Nat) : Int :=
    match k with
      | 0 => 0
      | n + 1 => 2 * seq_6_3_15 n + n

theorem Exercise_6_3_15 : ∀ (n : Nat),
    seq_6_3_15 n = 2 ^ n - n - 1 := by
  by_induc
  · rw [Nat.cast_zero]
    have h1 : seq_6_3_15 0 = 0 := by rfl
    rw [h1]
    linarith
  · fix n : ℕ
    assume ih : seq_6_3_15 n = 2 ^ n - n - 1
    have h1 : 2 * 2 ^ n = 2 ^ (n + 1) := by calc 2 * 2 ^ n
      _ = 2 ^ 1 * 2 ^ n := by rfl
      _ = 2 ^ (1 + n) := (power_law_nat 2 1 n).symm
      _ = 2 ^ (n + 1) := by rw [add_comm 1 n]
    rw [Nat.cast_succ]
    show seq_6_3_15 (n + 1) = 2 ^ (n + 1) - (n + 1) - 1 from
      calc seq_6_3_15 (n + 1)
        _ = 2 * seq_6_3_15 n + n := by rfl
        _ = 2 * (2 ^ n - n - 1) + n := by rw [ih]
        _ = 2 * 2 ^ n - (n + 1) - 1 := by linarith
        _ = 2 ^ (n + 1) - (n + 1) - 1 := by linarith
  done

-- 7.
def seq_6_3_16 (k : Nat) : Nat :=
    match k with
      | 0 => 2
      | n + 1 => (seq_6_3_16 n) ^ 2

theorem Exercise_6_3_16 : ∀ (n : Nat),
    seq_6_3_16 n = 2 ^ (2 ^ n) := by
  by_induc
  · have h1 : seq_6_3_16 0 = 2 := by rfl
    rw [h1]
    rw [pow_zero, pow_one]
  · fix n : ℕ
    assume ih : seq_6_3_16 n = 2 ^ 2 ^ n
    have h1 : 2 * 2 ^ n = 2 ^ (n + 1) := by calc 2 * 2 ^ n
      _ = 2 ^ 1 * 2 ^ n := by rfl
      _ = 2 ^ (1 + n) := (power_law_nat 2 1 n).symm
      _ = 2 ^ (n + 1) := by rw [add_comm 1 n]
    show seq_6_3_16 (n + 1) = 2 ^ 2 ^ (n + 1) from
      calc seq_6_3_16 (n + 1)
        _ = (seq_6_3_16 n) ^ 2 := by rfl
        _ = (2 ^ 2 ^ n) ^ 2 := by rw [ih]
        _ = 2 ^ (2 * 2 ^ n) := by
          rw [← pow_mul 2 (2 ^ n) 2, mul_comm (2 ^ n) 2]
        _ = 2 ^ (2 ^ (n + 1)) := by rw [h1]
  done

/- Section 6.4 -/
-- 1.
--Hint: Use Exercise_6_1_16a1 and Exercise_6_1_16a2
lemma sq_even_iff_even (n : Nat) :
    nat_even (n * n) ↔ nat_even n := sorry

-- 2.
--This theorem proves that the square root of 6 is irrational
theorem Exercise_6_4_4a :
    ¬∃ (q p : Nat), p * p = 6 * (q * q) ∧ q ≠ 0 := sorry

-- 3.
theorem Exercise_6_4_5 :
    ∀ n ≥ 12, ∃ (a b : Nat), 3 * a + 7 * b = n := sorry

-- 4.
theorem Exercise_6_4_7a : ∀ (n : Nat),
    (Sum i from 0 to n, Fib i) + 1 = Fib (n + 2) := sorry

-- 5.
theorem Exercise_6_4_7c : ∀ (n : Nat),
    Sum i from 0 to n, Fib (2 * i + 1) = Fib (2 * n + 2) := sorry

-- 6.
theorem Exercise_6_4_8a : ∀ (m n : Nat),
    Fib (m + n + 1) = Fib m * Fib n + Fib (m + 1) * Fib (n + 1) := sorry

-- 7.
theorem Exercise_6_4_8d : ∀ (m k : Nat), Fib m ∣ Fib (m * k) := sorry

-- 8.
def Fib_like (n : Nat) : Nat :=
  match n with
    | 0 => 1
    | 1 => 2
    | k + 2 => 2 * (Fib_like k) + Fib_like (k + 1)

theorem Fib_like_formula : ∀ (n : Nat), Fib_like n = 2 ^ n := sorry

-- 9.
def triple_rec (n : Nat) : Nat :=
  match n with
    | 0 => 0
    | 1 => 2
    | 2 => 4
    | k + 3 => 4 * triple_rec k +
                6 * triple_rec (k + 1) + triple_rec (k + 2)

theorem triple_rec_formula :
    ∀ (n : Nat), triple_rec n = 2 ^ n * Fib n := sorry

-- 10.
lemma quot_rem_unique_lemma {m q r q' r' : Nat}
    (h1 : m * q + r = m * q' + r') (h2 : r' < m) : q ≤ q' := sorry

theorem quot_rem_unique (m q r q' r' : Nat)
    (h1 : m * q + r = m * q' + r') (h2 : r < m) (h3 : r' < m) :
    q = q' ∧ r = r' := sorry

-- 11.
theorem div_mod_char (m n q r : Nat)
    (h1 : n = m * q + r) (h2 : r < m) : q = n / m ∧ r = n % m := sorry

/- Section 6.5 -/
-- Definitions for next three exercises
def rep_image_family {A : Type}
    (F : Set (A → A)) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => { x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F k B) }

def cumul_image_family {A : Type}
    (F : Set (A → A)) (B : Set A) : Set A :=
  { x : A | ∃ (n : Nat), x ∈ rep_image_family F n B }

def image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  { z : A | ∃ (x y : A), x ∈ B ∧ y ∈ B ∧ z = f x y }

def rep_image2 {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => image2 f (rep_image2 f k B)

def cumul_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  { x : A | ∃ (n : Nat), x ∈ rep_image2 f n B }

def un_image2 {A : Type} (f : A → A → A) (B : Set A) : Set A :=
  B ∪ (image2 f B)

def rep_un_image2 {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) : Set A :=
  match n with
    | 0 => B
    | k + 1 => un_image2 f (rep_un_image2 f k B)

def cumul_un_image2 {A : Type}
    (f : A → A → A) (B : Set A) : Set A :=
  { x : A | ∃ (n : Nat), x ∈ rep_un_image2 f n B }

-- 1.
theorem rep_image_family_base {A : Type}
    (F : Set (A → A)) (B : Set A) : rep_image_family F 0 B = B := by rfl

theorem rep_image_family_step {A : Type}
    (F : Set (A → A)) (n : Nat) (B : Set A) :
    rep_image_family F (n + 1) B =
    { x : A | ∃ f ∈ F, x ∈ image f (rep_image_family F n B) } := by rfl

lemma rep_image_family_sub_closed {A : Type}
    (F : Set (A → A)) (B D : Set A)
    (h1 : B ⊆ D) (h2 : closed_family F D) :
    ∀ (n : Nat), rep_image_family F n B ⊆ D := sorry

theorem Exercise_6_5_3 {A : Type} (F : Set (A → A)) (B : Set A) :
    closure_family F B (cumul_image_family F B) := sorry

-- 2.
theorem rep_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_image2 f 0 B = B := by rfl

theorem rep_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_image2 f (n + 1) B = image2 f (rep_image2 f n B) := by rfl

--You won't be able to complete this proof
theorem Exercise_6_5_6 {A : Type} (f : A → A → A) (B : Set A) :
    closed2 f (cumul_image2 f B) := sorry

-- 3.
theorem rep_un_image2_base {A : Type} (f : A → A → A) (B : Set A) :
    rep_un_image2 f 0 B = B := by rfl

theorem rep_un_image2_step {A : Type}
    (f : A → A → A) (n : Nat) (B : Set A) :
    rep_un_image2 f (n + 1) B =
    un_image2 f (rep_un_image2 f n B) := by rfl

theorem Exercise_6_5_8a {A : Type} (f : A → A → A) (B : Set A) :
    ∀ (m n : Nat), m ≤ n →
    rep_un_image2 f m B ⊆ rep_un_image2 f n B := sorry

lemma rep_un_image2_sub_closed {A : Type} {f : A → A → A} {B D : Set A}
    (h1 : B ⊆ D) (h2 : closed2 f D) :
    ∀ (n : Nat), rep_un_image2 f n B ⊆ D := sorry

lemma closed_lemma
    {A : Type} {f : A → A → A} {B : Set A} {x y : A} {nx ny n : Nat}
    (h1 : x ∈ rep_un_image2 f nx B) (h2 : y ∈ rep_un_image2 f ny B)
    (h3 : nx ≤ n) (h4 : ny ≤ n) :
    f x y ∈ cumul_un_image2 f B := sorry

theorem Exercise_6_5_8b {A : Type} (f : A → A → A) (B : Set A) :
    closure2 f B (cumul_un_image2 f B) := sorry

-- Definitions for next four exercises
def idExt (A : Type) : Set (A × A) := { (x, y) : A × A | x = y }

def rep_comp {A : Type} (R : Set (A × A)) (n : Nat) : Set (A × A) :=
  match n with
    | 0 => idExt A
    | k + 1 => comp (rep_comp R k) R

def cumul_comp {A : Type} (R : Set (A × A)) : Set (A × A) :=
  { (x, y) : A × A | ∃ n ≥ 1, (x, y) ∈ rep_comp R n }
-- 4.
theorem rep_comp_one {A : Type} (R : Set (A × A)) :
    rep_comp R 1 = R := sorry

-- 5.
theorem Exercise_6_5_11 {A : Type} (R : Set (A × A)) :
    ∀ (m n : Nat), rep_comp R (m + n) =
    comp (rep_comp R m) (rep_comp R n) := sorry

-- 6.
lemma rep_comp_sub_trans {A : Type} {R S : Set (A × A)}
    (h1 : R ⊆ S) (h2 : transitive (RelFromExt S)) :
    ∀ n ≥ 1, rep_comp R n ⊆ S := sorry

-- 7.
theorem Exercise_6_5_14 {A : Type} (R : Set (A × A)) :
    smallestElt (sub (A × A)) (cumul_comp R)
    { S : Set (A × A) | R ⊆ S ∧ transitive (RelFromExt S) } := sorry
