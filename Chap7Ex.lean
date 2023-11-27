import HTPILib.Chap7
namespace HTPI.Exercises

/- Section 7.1 -/
-- 1.
theorem dvd_a_of_dvd_b_mod {a b d : Nat}
    (h1 : d ∣ b) (h2 : d ∣ (a % b)) : d ∣ a := by
  set q : Nat := a / b
  have h3 : b * q + a % b = a := Nat.div_add_mod a b
  define at h1; obtain (j : ℕ) (h4 : b = d * j) from h1
  define at h2; obtain (k : ℕ) (h5 : a % b = d * k) from h2
  define; apply Exists.intro (j * q + k)
  show a = d * (j * q + k) from
    calc a
      _ = b * q + a % b := h3.symm
      _ = (d * j) * q + a % b := by rw [h4]
      _ = (d * j) * q + d * k := by rw [h5]
      _ = d * (j * q + k) := by ring_nf
  done

-- 2.
lemma gcd_comm_lt {a b : Nat} (h : a < b) : gcd a b = gcd b a := by
  have h1 : b ≠ 0 := by linarith
  have h2 : a % b = a := Nat.mod_eq_of_lt h
  rw [gcd_nonzero a h1, h2]
  done

theorem gcd_comm (a b : Nat) : gcd a b = gcd b a := by
  by_cases h1 : a < b
  · exact gcd_comm_lt h1
  · by_cases h2 : b = a
    · rw [h2]
    · have h3 : a ≥ b := Nat.ge_of_not_lt h1
      have h4 : a > b := lt_of_le_of_ne h3 h2
      have h5 : b < a := gt_iff_lt.mp h4
      have h6 : gcd b a = gcd a b := gcd_comm_lt h5
      exact h6.symm
  done

-- 3.
theorem Exercise_7_1_5 (a b : Nat) (n : Int) :
    (∃ (s t : Int), s * a + t * b = n) ↔ (↑(gcd a b) : Int) ∣ n := by
  apply Iff.intro
  · -- →
    assume h1 : ∃ (s : ℤ), ∃ (t : ℤ), s * ↑a + t * ↑b = n
    obtain (s : ℤ) (h2 : ∃ (t : ℤ), s * ↑a + t * ↑b = n) from h1
    obtain (t : ℤ) (h3 : s * ↑a + t * ↑b = n) from h2
    have h4 : (gcd a b) ∣ a := gcd_dvd_left a b
    have h5 : (gcd a b) ∣ b := gcd_dvd_right a b
    define at h4; obtain (c : ℕ) (h6 : a = gcd a b * c) from h4
    define at h5; obtain (d : ℕ) (h7 : b = gcd a b * d) from h5
    have h8 : n = s * ↑(gcd a b * c) + t * ↑(gcd a b * d) := by
      calc n
        _ = s * ↑a + t * ↑b := h3.symm
        _ = s * ↑(gcd a b * c) + t * ↑b := by rw [← h6]
        _ = s * ↑(gcd a b * c) + t * ↑(gcd a b * d) := by rw [← h7]
    rw [Nat.cast_mul, Nat.cast_mul] at h8
    define
    apply Exists.intro (s * ↑c + t * ↑d)
    show n = ↑(gcd a b) * (s * ↑c + t * ↑d) from
      calc n
        _ = s * (↑(gcd a b) * ↑c) + t * (↑(gcd a b) * ↑d) := h8
        _ = ↑(gcd a b) * (s * ↑c) + ↑(gcd a b) * (t * ↑d) := by ring
        _ = ↑(gcd a b) * (s * ↑c + t * ↑d) := by ring
  · assume h1 : ↑(gcd a b) ∣ n
    define at h1
    obtain (c : ℤ) (h2 : n = ↑(gcd a b) * c) from h1
    have h3 : (gcd_c1 a b) * ↑a + (gcd_c2 a b) * ↑b = ↑(gcd a b) := gcd_lin_comb b a
    apply Exists.intro ((gcd_c1 a b) * c)
    apply Exists.intro ((gcd_c2 a b) * c)
    rw [h2]
    show gcd_c1 a b * c * ↑a + gcd_c2 a b * c * ↑b = ↑(gcd a b) * c from
      calc gcd_c1 a b * c * ↑a + gcd_c2 a b * c * ↑b
        _ = c * (gcd_c1 a b * ↑a + gcd_c2 a b * ↑b) := by ring
        _ = c * ↑(gcd a b) := by rw [h3]
        _ = ↑(gcd a b) * c := by ring
  done

-- 4.
theorem Exercise_7_1_6 (a b c : Nat) :
    gcd a b = gcd (a + b * c) b := by
  have h1 : gcd a b ∣ gcd (a + b * c) b := by
    set s : ℤ := gcd_c1 (a + b * c) b
    set t : ℤ := gcd_c2 (a + b * c) b
    have h1 : s * ↑(a + b * c) + t * ↑b = ↑(gcd (a + b * c) b)
      := gcd_lin_comb b (a + b * c)
    have h2 : s * ↑a + (s * ↑c + t) * ↑b = ↑(gcd (a + b * c) b) := by
      calc s * ↑a + (s * ↑c + t) * ↑b
        _ = s * (↑a + ↑b * ↑c) + t * ↑b := by ring
        _ = s * (↑a + ↑(b * c)) + t * ↑b := by rw [Nat.cast_mul]
        _ = s * ↑(a + b * c) + t * ↑b := by rw [Nat.cast_add]
        _ = ↑(gcd (a + b * c) b) := by rw [h1]
    have h3 : (∃ (s t : Int), s * a + t * b = ↑(gcd (a + b * c) b)) := by
      apply Exists.intro s; apply Exists.intro (s * ↑c + t); exact h2
    have h4 : (↑(gcd a b) : Int) ∣ ↑(gcd (a + b * c) b)
      := (Exercise_7_1_5 a b (↑(gcd (a + b * c) b))).mp h3
    exact Int.coe_nat_dvd.mp h4
  have h2 : gcd (a + b * c) b ∣ gcd a b := by
    set s : ℤ := gcd_c1 a b
    set t : ℤ := gcd_c2 a b
    have h2 : s * ↑a + t * ↑b = ↑(gcd a b) := gcd_lin_comb b a
    have h3 : s * ↑(a + b * c) + (t - s * ↑c) * ↑b = ↑(gcd a b) := by
      calc s * ↑(a + b * c) + (t - s * ↑c) * ↑b
        _ = s * (↑a + ↑(b * c)) + (t - s * ↑c) * ↑b := by rw [Nat.cast_add]
        _ = s * (↑a + ↑b * ↑c) + (t - s * ↑c) * ↑b := by rw [Nat.cast_mul]
        _ = s * ↑a + t * ↑b := by ring
        _ = ↑(gcd a b) := by rw [h2]
    have h4 : (∃ (s t : Int), s * (a + b * c) + t * b = ↑(gcd a b)) := by
      apply Exists.intro s; apply Exists.intro (t - s * ↑c); exact h3
    have h5 : (↑(gcd (a + b * c) b) : Int) ∣ ↑(gcd a b)
      := (Exercise_7_1_5 (a + b * c) b (↑(gcd a b))).mp h4
    exact Int.coe_nat_dvd.mp h5
  exact Nat.dvd_antisymm h1 h2
  done

-- 5.
theorem gcd_is_nonzero {a b : Nat} (h : a ≠ 0 ∨ b ≠ 0) :
    gcd a b ≠ 0 := by
  by_contra h1
  have h2 : gcd a b ∣ a := gcd_dvd_left a b
  rw [h1] at h2
  have h3 : gcd a b ∣ b := gcd_dvd_right a b
  rw [h1] at h3
  have h4 : a = 0 := Nat.eq_zero_of_zero_dvd h2
  have h5 : b = 0 := Nat.eq_zero_of_zero_dvd h3
  demorgan at h
  have h6 : a = 0 ∧ b = 0 := And.intro h4 h5
  show False from h h6
  done

-- 6.
theorem gcd_greatest {a b d : Nat} (h1 : gcd a b ≠ 0)
    (h2 : d ∣ a) (h3 : d ∣ b) : d ≤ gcd a b := by
  have h4 : d ∣ gcd a b := Theorem_7_1_6 h2 h3
  define at h4
  obtain (c : Nat) (h5 : gcd a b = d * c) from h4
  by_cases h6 : c = 0
  · by_contra h7
    rw [h6, mul_zero] at h5
    show False from h1 h5
  · have h7 : c > 0 := Nat.pos_of_ne_zero h6
    have h8 : c ≥ 1 := by linarith
    have h9 : 1 * d ≤ c * d := Nat.mul_le_mul_right d h8
    rw [one_mul, mul_comm c d, ← h5] at h9
    exact h9

-- 7.
lemma Lemma_7_1_10a {a b : Nat}
    (n : Nat) (h : a ∣ b) : (n * a) ∣ (n * b) := by
  define at h; obtain (c : ℕ) (h1 : b = a * c) from h
  define; apply Exists.intro c
  rw [h1, ← mul_assoc]
  done

lemma Lemma_7_1_10b {a b n : Nat}
    (h1 : n ≠ 0) (h2 : (n * a) ∣ (n * b)) : a ∣ b := by
  have h' : n > 0 := Nat.pos_of_ne_zero h1
  define at h2; obtain (c : ℕ) (h3 : n * b = n * a * c) from h2
  rw [mul_assoc, mul_left_cancel_iff_of_pos h'] at h3
  define; apply Exists.intro c; exact h3
  done

lemma Lemma_7_1_10c {a b : Nat}
    (h1 : a ∣ b) (h2 : b ∣ a) : a = b := by
  define at h1; obtain (c : ℕ) (h3 : b = a * c) from h1
  define at h2; obtain (d : ℕ) (h4 : a = b * d) from h2
  by_cases h : a = 0
  · rw [h, zero_mul] at h3
    rw [h, h3]
  · have h' : a > 0 := Nat.pos_of_ne_zero h
    have h5 : 1 = c * d := by
      rw [h3, mul_assoc] at h4
      nth_rewrite 1 [← mul_one a] at h4
      rw [mul_left_cancel_iff_of_pos h'] at h4
      exact h4
    have h6 : c = 1 ∧ d = 1 := mul_eq_one.mp h5.symm
    rw [h4, h6.right, mul_one]
    done

theorem Exercise_7_1_10 (a b n : Nat) :
    gcd (n * a) (n * b) = n * gcd a b := by
  by_cases h0 : n = 0
  · rw [h0, zero_mul, zero_mul, gcd_base, zero_mul]
  · have h1 : gcd a b ∣ a := gcd_dvd_left a b
    have h2 : n * gcd a b ∣ n * a := Lemma_7_1_10a n h1
    have h3 : gcd a b ∣ b := gcd_dvd_right a b
    have h4 : n * gcd a b ∣ n * b := Lemma_7_1_10a n h3
    have h5 : n * gcd a b ∣ gcd (n * a) (n * b) := Theorem_7_1_6 h2 h4
    have h6 : n ∣ n * a := by
      define; apply Exists.intro a; rfl
    have h7 : n ∣ n * b := by
      define; apply Exists.intro b; rfl
    have h8 : n ∣ gcd (n * a) (n * b) := Theorem_7_1_6 h6 h7
    obtain (c : Nat) (h9 : gcd (n * a) (n * b) = n * c) from h8
    have h10: n * c ∣ gcd (n * a) (n * b) := by
      define; apply Exists.intro 1; rw [mul_one]; exact h9
    have h11 : n * c ∣ n * a := dvd_gcd_dvd_left h10
    have h12 : c ∣ a := Lemma_7_1_10b h0 h11
    have h13 : n * c ∣ n * b := dvd_gcd_dvd_right h10
    have h14 : c ∣ b := Lemma_7_1_10b h0 h13
    have h15 : c ∣ gcd a b := Theorem_7_1_6 h12 h14
    have h16 : n * c ∣ n * gcd a b := Lemma_7_1_10a n h15
    rw [← h9] at h16
    exact Lemma_7_1_10c h16 h5
  done

/- Section 7.2 -/
-- 1.
lemma dvd_prime {a p : Nat}
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := by
  by_cases h3 : a = 1
  · left; exact h3
  · right
    define at h1
    have two_le_p : 2 ≤ p := h1.left
    have p_prime_cond : ¬∃ (a : ℕ), ∃ (b : ℕ), a * b = p ∧ a < p ∧ b < p := h1.right
    obtain (b : Nat) (h4 : p = a * b) from h2
    have h5 : a ≠ 0 := by
      by_contra h5
      rw [h5, zero_mul] at h4
      linarith
    have h6 : a ≥ p := by
      by_contra h6
      apply p_prime_cond
      apply Exists.intro a; apply Exists.intro b
      apply And.intro h4.symm
      have h7 : a < p := by linarith
      apply And.intro h7
      by_contra h8
      have h9 : b ≥ p := by linarith
      have h10 : a > 1 := by
        have h10 : a ≥ 1 := Nat.pos_of_ne_zero h5
        exact lt_of_le_of_ne' h10 h3
      have h10 : p < p := by
        calc p
          _ = a * b := by rw [h4]
          _ ≥ a * p := by rel [h9]
          _ > 1 * p := by rel [h10]
          _ = p := by ring
      linarith
    have h7 : b ≥ 1 := by
      by_contra h7
      have h8 : b = 0 := by linarith
      rw [h8, mul_zero] at h4
      linarith
    have h8 : a ≤ p := by
      calc a
        _ = a * 1 := by rw [mul_one]
        _ ≤ a * b := by rel [h7]
        _ = p := by rw [h4]
    linarith
  done

-- 2.
-- Hints:  Start with apply List.rec.  You may find mul_ne_zero useful
theorem prod_nonzero_nonzero : ∀ (l : List Nat),
    (∀ (a : Nat), a ∈ l → a ≠ 0) → prod l ≠ 0 := by
  apply List.rec
  · -- Base case
    assume h : ∀ (a : ℕ), a ∈ [] → a ≠ 0
    have h1 : prod [] = 1 := by rfl
    linarith
  · -- Induction step
    fix p : Nat; fix l : List Nat
    assume ih : (∀ (a : ℕ), a ∈ l → a ≠ 0) → prod l ≠ 0
    assume h1 : ∀ (a : ℕ), a ∈ p :: l → a ≠ 0
    rw [prod_cons]
    have h2 : p ≠ 0 := by
      have h : p ∈ p :: l := List.mem_cons_self p l
      exact h1 p h
    have h3 : ∀ (a : ℕ), a ∈ l → a ≠ 0 := by
      fix a : Nat
      assume h : a ∈ l
      have h' : a ∈ p :: l := List.mem_cons_of_mem p h
      exact h1 a h'
    have h4 : prod l ≠ 0 := ih h3
    exact Nat.mul_ne_zero h2 h4
  done

-- 3.
lemma two_prime : prime 2 := by
  define
  apply And.intro
  · linarith
  · by_contra h
    obtain (a : Nat) (h1 : ∃ (b : ℕ), a * b = 2 ∧ a < 2 ∧ b < 2) from h
    obtain (b : Nat) (h2 : a * b = 2 ∧ a < 2 ∧ b < 2) from h1
    have h3 : a ≤ 1 := by linarith
    have h4 : b ≤ 1 := by linarith
    have h5 : a * b ≤ 1 := by
      calc a * b
        _ ≤ a * 1 := by rel [h4]
        _ ≤ 1 * 1 := by rel [h3]
        _ = 1 := by rw [mul_one]
    linarith
  done

theorem rel_prime_iff_no_common_factor (a b : Nat) :
    rel_prime a b ↔ ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := by
  apply Iff.intro
  · assume h : rel_prime a b
    define at h
    by_contra h1
    obtain (p : Nat) (h2 : prime p ∧ p ∣ a ∧ p ∣ b) from h1
    have h3 : p ∣ gcd a b := Theorem_7_1_6 h2.right.left h2.right.right
    rw [h] at h3
    have h4 : p = 1 := eq_one_of_dvd_one h3
    have h5 : p ≠ 1 := prime_not_one h2.left
    apply h5; exact h4
  · assume h : ¬∃ (p : ℕ), prime p ∧ p ∣ a ∧ p ∣ b
    define
    by_contra h1
    by_cases h2 : gcd a b = 0
    · have h3 : a = 0 := by
        have h4 : gcd a b ∣ a := gcd_dvd_left a b
        rw [h2] at h4
        exact Nat.eq_zero_of_zero_dvd h4
      rw [h3, gcd_comm, gcd_base] at h2
      apply h
      apply Exists.intro 2
      apply And.intro two_prime
      apply And.intro
      · define; apply Exists.intro 0; rw [h3]
      · define; apply Exists.intro 0; rw [h2]
    have h3 : gcd a b ≥ 1 := by
      have h : gcd a b > 0 := Nat.pos_of_ne_zero h2
      linarith
    have h4 : gcd a b ≥ 2 := by
      have h : gcd a b > 1 := lt_of_le_of_ne' h3 h1
      linarith
    have h5 : ∃ (p : Nat), prime_factor p (gcd a b) := exists_prime_factor (gcd a b) h4
    obtain (p : Nat) (h6 : prime_factor p (gcd a b)) from h5
    define at h6
    have h7 : p ∣ a := dvd_gcd_dvd_left h6.right
    have h8 : p ∣ b := dvd_gcd_dvd_right h6.right
    apply h; apply Exists.intro p
    exact And.intro h6.left (And.intro h7 h8)
  done

-- 4.
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := by
  define
  rw [gcd_comm]
  define at h; exact h
  done

-- 5.
lemma in_prime_factorization_iff_prime_factor {a : Nat} {l : List Nat}
    (h1 : prime_factorization a l) (p : Nat) :
    p ∈ l ↔ prime_factor p a := by
  apply Iff.intro
  · -- (→)
    assume h2 : p ∈ l
    define
    define at h1
    have h3 : nondec_prime_list l := h1.left
    define at h3
    apply And.intro (h3.left p h2)
    rw [← h1.right]
    exact list_elt_dvd_prod h2
  · -- (←)
    assume h2 : prime_factor p a
    define at h2
    define at h1
    have h3 : all_prime l := h1.left.left
    rw [← h1.right] at h2
    exact prime_in_list h2.left h3 h2.right
  done

-- 6.
theorem Exercise_7_2_5 {a b : Nat} {l m : List Nat}
    (h1 : prime_factorization a l) (h2 : prime_factorization b m) :
    rel_prime a b ↔ (¬∃ (p : Nat), p ∈ l ∧ p ∈ m) := by
  apply Iff.intro
  · -- (→)
    assume h3 : rel_prime a b
    by_contra h4
    obtain (p : Nat) (h5 : p ∈ l ∧ p ∈ m) from h4
    have h6 : ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := (rel_prime_iff_no_common_factor a b).mp h3
    apply h6
    apply Exists.intro p
    have h7 : prime p := h1.left.left p h5.left
    apply And.intro h7
    rw [← h1.right, ← h2.right]
    exact And.intro (list_elt_dvd_prod h5.left) (list_elt_dvd_prod h5.right)
  · -- (←)
    assume h3 : ¬∃ (p : ℕ), p ∈ l ∧ p ∈ m
    by_contra h4
    rw [rel_prime_iff_no_common_factor] at h4
    double_neg at h4
    obtain (p : Nat) (h5 : prime p ∧ p ∣ a ∧ p ∣ b) from h4
    apply h3
    apply Exists.intro p
    have h6 : prime_factor p a := And.intro h5.left h5.right.left
    have h7 : prime_factor p b := And.intro h5.left h5.right.right
    apply And.intro
    · exact (in_prime_factorization_iff_prime_factor h1 p).mpr h6
    · exact (in_prime_factorization_iff_prime_factor h2 p).mpr h7
  done

-- 7.
theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := by
  apply Iff.intro
  · assume h : rel_prime a b
    apply Exists.intro (gcd_c1 a b)
    apply Exists.intro (gcd_c2 a b)
    rw [← Nat.cast_one, ← h]
    exact gcd_lin_comb b a
  · assume h1 : ∃ (s : ℤ), ∃ (t : ℤ), s * ↑a + t * ↑b = 1
    have h2 : (↑(gcd a b) : Int) ∣ 1 := (Exercise_7_1_5 a b (1 : Int)).mp h1
    rw [← Nat.cast_one, Int.coe_nat_dvd] at h2
    exact eq_one_of_dvd_one h2
  done

-- 8.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := by
  rw [rel_prime_iff_no_common_factor]
  rw [rel_prime_iff_no_common_factor] at h1
  by_contra h4
  obtain (p : Nat) (h5 : prime p ∧ p ∣ a' ∧ p ∣ b') from h4
  apply h1
  apply Exists.intro p
  apply And.intro h5.left
  apply And.intro
  · exact dvd_trans h5.right.left h2
  · exact dvd_trans h5.right.right h3
  done

-- 9.
theorem Exercise_7_2_9 {a b j k : Nat}
    (h1 : gcd a b ≠ 0) (h2 : a = j * gcd a b) (h3 : b = k * gcd a b) :
    rel_prime j k := by
  set s : Int := gcd_c1 a b
  set t : Int := gcd_c2 a b
  have h4 : s * ↑a + t * ↑b = ↑(gcd a b) := gcd_lin_comb b a
  nth_rewrite 1 [h3, h2] at h4
  rw [Nat.cast_mul, Nat.cast_mul] at h4
  have h5 : ↑(gcd a b) = (s * ↑j + t * ↑k) * ↑(gcd a b) := by
    calc ↑(gcd a b)
      _ = s * (↑j * ↑(gcd a b)) + t * (↑k * ↑(gcd a b)) := by rw [h4]
      _ = (s * ↑j) * ↑(gcd a b) + (t * ↑k) * ↑(gcd a b) := by ring
      _ = (s * ↑j + t * ↑k) * ↑(gcd a b) := by ring
  have h6 : (↑(gcd a b) : Int) ≠ ↑0 := by
    by_contra h6
    rw [← Nat.cast_zero, Int.cast_eq_cast_iff_Nat] at h6
    show False from h1 h6
  nth_rewrite 1 [← Int.one_mul ↑(gcd a b)] at h5
  have h7 : 1 = (s * ↑j + t * ↑k) := Int.eq_of_mul_eq_mul_right h6 h5
  have h8 : ∃ (s t : Int), s * j + t * k = 1 := by
    apply Exists.intro s; apply Exists.intro t; exact h7.symm
  exact (Exercise_7_2_6 j k).mpr h8
  done

-- 10.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := by
  set s : Int := gcd_c1 a b
  set t : Int := gcd_c2 a b
  set u : Int := gcd_c1 a c
  set v : Int := gcd_c2 a c
  have h1 : s * ↑a + t * ↑b = ↑(gcd a b) := gcd_lin_comb b a
  have h2 : u * ↑a + v * ↑c = ↑(gcd a c) := gcd_lin_comb c a
  have h3 : ↑(gcd a b * gcd a c) =
    (s * u * ↑a + s * v * ↑c + t * ↑b * u) * ↑a + (t * v) * ↑(b * c) := by
    calc ↑(gcd a b * gcd a c)
      _ = ↑(gcd a b) * ↑(gcd a c) := by rw [Nat.cast_mul]
      _ = (s * ↑a + t * ↑b) * (u * ↑a + v * ↑c) := by rw [h1, h2]
      _ = s * ↑a * u * ↑a + s * ↑a * v * ↑c + t * ↑b * u * ↑a + t * ↑b * v * ↑c := by ring
      _ = s * u * ↑a * ↑a + s * v * ↑c * ↑a +  t * ↑b * u * ↑a + t * v * (↑b * ↑c) := by ring
      _ = s * u * ↑a * ↑a + s * v * ↑c * ↑a +  t * ↑b * u * ↑a + t * v * ↑(b * c) := by rw [← Nat.cast_mul b c]
      _ = (s * u * ↑a + s * v * ↑c + t * ↑b * u) * ↑a + (t * v) * ↑(b * c) := by ring
  have h4 : ∃ (s t : Int),  s * ↑a + t * ↑(b * c) = ↑(gcd a b * gcd a c) := by
    apply Exists.intro (s * u * ↑a + s * v * ↑c + t * ↑b * u)
    apply Exists.intro (t * v)
    exact h3.symm
  have h5 : ↑(gcd a (b * c)) ∣ (↑(gcd a b * gcd a c) : Int) :=
    (Exercise_7_1_5 a (b * c) ↑(gcd a b * gcd a c)).mp h4
  rw [Int.coe_nat_dvd] at h5
  exact h5
  done

/- Section 7.3 -/
-- 1.
theorem congr_trans' {m : Nat} : ∀ {a b c : Int},
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := by
  fix a : Int; fix b : Int; fix c : Int
  assume h1 : a ≡ b (MOD m)
  assume h2 : b ≡ c (MOD m)
  define at h1; define at h2
  obtain (d : Int) (h3 : a - b = m * d) from h1
  obtain (e : Int) (h4 : b - c = m * e) from h2
  define
  apply Exists.intro (d + e)
  show a - c = m * (d + e) from
    calc a - c
      _ = (a - b) + (b - c) := by ring
      _ = m * d + m * e := by rw [h3, h4]
      _ = m * (d + e) := by ring
  done

-- 2.
theorem Theorem_7_3_6_3 {m : Nat} (X : ZMod m) : X + [0]_m = X := by
  obtain (a : Int) (h1 : X = [a]_m) from cc_rep X
  rw [h1, add_class, add_zero]
  done

-- 3.
theorem Theorem_7_3_6_4 {m : Nat} (X : ZMod m) :
    ∃ (Y : ZMod m), X + Y = [0]_m := by
  obtain (a : Int) (h1 : X = [a]_m) from cc_rep X
  apply Exists.intro [m - a]_m
  rw [h1, add_class]
  have h2 : [m]_m = [0]_m := by
    rw [cc_eq_iff_congr]
    define
    apply Exists.intro 1
    ring
  show [a + (m - a)]_m = [0]_m by
    calc [a + (m - a)]_m
      _ = [m]_m := by ring_nf
      _ = [0]_m := by rw [h2]
  done

-- 4.
theorem Exercise_7_3_4a {m : Nat} (Z1 Z2 : ZMod m)
    (h1 : ∀ (X : ZMod m), X + Z1 = X)
    (h2 : ∀ (X : ZMod m), X + Z2 = X) : Z1 = Z2 := by
  obtain (a1 : Int) (h4 : Z1 = [a1]_m) from cc_rep Z1
  obtain (a2 : Int) (h5 : Z2 = [a2]_m) from cc_rep Z2
  have h6 : Z1 = [0]_m := by
    have h6 : [0]_m + Z1 = [0]_m := h1 [0]_m
    rw [h4, add_class, zero_add] at h6
    rw [h4, h6]
  have h7 : Z2 = [0]_m := by
    have h7 : [0]_m + Z2 = [0]_m := h2 [0]_m
    rw [h5, add_class, zero_add] at h7
    rw [h5, h7]
  rw [h6, h7]
  done

-- 5.
theorem Exercise_7_3_4b {m : Nat} (X Y1 Y2 : ZMod m)
    (h1 : X + Y1 = [0]_m) (h2 : X + Y2 = [0]_m) : Y1 = Y2 := by
  obtain (a : Int) (h3 : X = [a]_m) from cc_rep X
  obtain (b1 : Int) (h4 : Y1 = [b1]_m) from cc_rep Y1
  obtain (b2 : Int) (h5 : Y2 = [b2]_m) from cc_rep Y2
  have h6 : [a + b1]_m = [a + b2]_m := by
    calc [a + b1]_m
      _ = [a]_m + [b1]_m := by rw [← add_class]
      _ = X + Y1 := by rw [h3, h4]
      _ = [0]_m := by rw [h1]
      _ = X + Y2 := by rw [h2]
      _ = [a]_m + [b2]_m := by rw [h3, h5]
      _ = [a + b2]_m := by rw [add_class]
  rw [cc_eq_iff_congr] at h6
  define at h6
  obtain (c : Int) (h7 : a + b1 - (a + b2) = ↑m * c) from h6
  have h8 : b1 - b2 = ↑m * c := by
    calc b1 - b2
      _ = (a - a) + b1 - b2 := by ring
      _ = a + b1 - (a + b2) := by ring
      _ = ↑m * c:= by rw [h7]
  have h9 : [b1]_m = [b2]_m := by
    rw [cc_eq_iff_congr]
    define
    apply Exists.intro c
    exact h8
  rw [h4, h5]
  exact h9
  done

-- 6.
theorem Theorem_7_3_10 (m a : Nat) (b : Int) :
    ¬(↑(gcd m a) : Int) ∣ b → ¬∃ (x : Int), a * x ≡ b (MOD m) := by
  contrapose
  assume h1 : ¬¬∃ (x : ℤ), ↑a * x ≡ b (MOD m)
  double_neg; double_neg at h1
  obtain (x : Int) (h2 : ↑a * x ≡ b (MOD m)) from h1
  define at h2
  obtain (c : Int) (h3 : ↑a * x - b = ↑m * c) from h2
  have h4 : b = (-c) * ↑m + x * ↑a := by
    calc b
      _ = -(-b) := by ring
      _ = -(↑a * x - b - ↑a * x) := by ring
      _ = -(↑m * c - ↑a * x) := by rw [h3]
      _ = ↑a * x - ↑m * c := by ring
      _ = (-c) * ↑m + x * ↑a := by ring
  have h5 : ∃ (s t : Int), s * m + t * a = b := by
    apply Exists.intro (-c)
    apply Exists.intro x
    exact h4.symm
  exact (Exercise_7_1_5 m a b).ltr h5
  done

-- 7.
theorem Theorem_7_3_11 (m n : Nat) (a b : Int) (h1 : n ≠ 0) :
    n * a ≡ n * b (MOD n * m) ↔ a ≡ b (MOD m) := by
  apply Iff.intro
  · assume h2 : ↑n * a ≡ ↑n * b (MOD n * m)
    define at h2
    obtain (c : Int) (h3 : ↑n * a - ↑n * b = ↑(n * m) * c) from h2
    define
    apply Exists.intro c
    have h4 : ↑n * (a - b) = ↑n * (↑m * c) := by
      calc ↑n * (a - b)
        _ = ↑n * a - ↑n * b := by ring
        _ = ↑(n * m) * c := by rw [h3]
        _ = (↑n * ↑m) * c := by rw [Nat.cast_mul]
        _ = ↑n * (↑m * c) := by ring
    exact Int.eq_of_mul_eq_mul_left (Int.ofNat_ne_zero.rtl h1) h4
  · assume h2 : a ≡ b (MOD m)
    define at h2
    obtain (c : Int) (h3 : a - b = ↑m * c) from h2
    apply Exists.intro c
    show ↑n * a - ↑n * b = ↑(n * m) * c from
      calc ↑n * a - ↑n * b
        _ = ↑n * (a - b) := by ring
        _ = ↑n * (↑m * c) := by rw [h3]
        _ = (↑n * ↑m) * c := by ring
        _ = ↑(n * m) * c := by rw [Nat.cast_mul]
  done

-- 8.
theorem Exercise_7_3_16 {m : Nat} {a b : Int} (h : a ≡ b (MOD m)) :
    ∀ (n : Nat), a ^ n ≡ b ^ n (MOD m) := by
  by_induc
  · -- Base case
    define; apply Exists.intro 0; ring
  · -- Induction step
    fix n : Nat
    assume ih : a ^ n ≡ b ^ n (MOD m)
    rw [← cc_eq_iff_congr]
    rw [← cc_eq_iff_congr] at ih
    rw [← cc_eq_iff_congr] at h
    have h1 : a ^ (n + 1) = a ^ n * a := by ring
    have h2 : b ^ (n + 1) = b ^ n * b := by ring
    rw [h1, h2]
    show [a ^ n * a]_m = [b ^ n * b]_m from
      calc [a ^ n * a]_m
        _ = [a ^ n]_m * [a]_m := by rw [mul_class]
        _ = [b ^ n]_m * [b]_m := by rw [h, ih]
        _ = [b ^ n * b]_m := by rw [mul_class]
  done

-- 9.
example {m : Nat} [NeZero m] (X : ZMod m) :
    ∃! (a : Int), 0 ≤ a ∧ a < m ∧ X = [a]_m := by
  obtain (a : Int) (h1 : X = [a]_m) from cc_rep X
  exists_unique
  · apply Exists.intro (a % m)
    rw [h1, cc_eq_iff_congr]
    exact mod_cmpl_res m a
  · fix a1 : Int; fix a2 : Int
    assume h2 : 0 ≤ a1 ∧ a1 < ↑m ∧ X = [a1]_m
    assume h3 : 0 ≤ a2 ∧ a2 < ↑m ∧ X = [a2]_m
    rw [h1, cc_eq_iff_congr] at h2
    rw [h1, cc_eq_iff_congr] at h3
    exact (Theorem_7_3_1 m a).unique h2 h3
  done

-- 10.
lemma congr_rel_prime_lr {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a → rel_prime m b := by
  assume h2 : rel_prime m a
  define at h1
  obtain (c : Int) (h3 : ↑a - ↑b = ↑m * c) from h1
  define at h2
  set s : Int := gcd_c1 m a
  set t : Int := gcd_c2 m a
  have h4 : s * ↑m + t * ↑a = ↑(gcd m a) := gcd_lin_comb a m
  rw [h2] at h4
  have h5 : ↑a = ↑m * c + ↑b := by
    calc ↑a
      _ = ↑a - ↑b + ↑b := by ring
      _ = ↑m * c + ↑b := by rw [h3]
  have h6 : (s + t * c) * m + t * b = s * m + t * a := by
    calc (s + t * c) * m + t * b
      _ = s * m + t * (m * c + b) := by ring
      _ = s * m + t * a := by rw [h5]
  rw [h4] at h6
  have h7 : ∃ (s t : Int), s * m + t * b = (↑1 : Int) := by
    apply Exists.intro (s + t * c)
    apply Exists.intro t
    exact h6
  exact (Exercise_7_2_6 m b).rtl h7

theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := by
  apply Iff.intro
  · exact congr_rel_prime_lr h1
  · have h2 : ↑b ≡ ↑a (MOD m) := congr_symm h1
    exact congr_rel_prime_lr h2
  done

-- 11.
--Hint: You may find the theorem Int.ofNat_mod_ofNat useful.
theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := by
  apply Iff.intro
  · assume h1 : rel_prime m (a % m)
    define at h1
    set s : Int := gcd_c1 m (a % m)
    set t : Int := gcd_c2 m (a % m)
    have h2 : s * ↑m + t * ↑(a % m) = ↑(gcd m (a % m))
      := gcd_lin_comb (a % m) m
    rw [h1, ← Int.ofNat_mod_ofNat, Nat.cast_one] at h2
    have h3 : m * (a / m) + a % m = a := Nat.div_add_mod a m
    have h4 : (↑(a % m) : Int) = ↑a - ↑m * ↑(a / m) := by
      calc (↑(a % m) : Int)
        _ = ↑(m * (a / m)) + ↑(a % m) - ↑(m * (a / m)) := by ring
        _ = ↑((m * (a / m)) + (a % m)) - ↑(m * (a / m)) := by rw [Nat.cast_add]
        _ = ↑a - ↑(m * (a / m)) := by rw [h3]
        _ = ↑a - ↑m * ↑(a / m) := by rw [Nat.cast_mul]
    rw [← Int.ofNat_mod_ofNat] at h4
    rw [h4] at h2
    have h5 : ∃ (s t : Int), s * ↑m + t * ↑a = 1 := by
      apply Exists.intro (s - t * ↑(a / m))
      apply Exists.intro t
      show (s - t * ↑(a / m)) * ↑m + t * ↑a = 1 from
        calc (s - t * ↑(a / m)) * ↑m + t * ↑a
          _ = s * ↑m + t * (↑a - ↑m * ↑(a / m)) := by ring
          _ = 1 := by rw [h2]
    exact (Exercise_7_2_6 m a).rtl h5
  · assume h1 : rel_prime m a
    define at h1
    set s : Int := gcd_c1 m a
    set t : Int := gcd_c2 m a
    have h2 : s * ↑m + t * ↑a = ↑(gcd m a)
      := gcd_lin_comb a m
    rw [h1, Nat.cast_one] at h2
    have h3 : m * (a / m) + a % m = a := Nat.div_add_mod a m
    rw [← h3, Nat.cast_add, Nat.cast_mul] at h2
    have h4 : ∃ (s t : Int), s * ↑m + t * ↑(a % m) = 1 := by
      apply Exists.intro (s + t * ↑(a / m))
      apply Exists.intro t
      show (s + t * ↑(a / m)) * ↑m + t * ↑(a % m) = 1 from
        calc (s + t * ↑(a / m)) * ↑m + t * ↑(a % m)
          _ = s * ↑m + t * (↑m * ↑(a / m) + ↑(a % m)) := by ring
          _ = 1 := by rw [h2]
    exact (Exercise_7_2_6 m (a % m)).rtl h4
  done

-- 12.
lemma congr_iff_mod_eq_Int (m : Nat) (a b : Int) [NeZero m] :
    a ≡ b (MOD m) ↔ a % ↑m = b % ↑m := by
  apply Iff.intro
  · assume h1 : a ≡ b (MOD m)
    have h2 : 0 ≤ a % ↑m ∧ a % ↑m < m ∧ a ≡ a % m (MOD m) := mod_cmpl_res m a
    have h3 : 0 ≤ b % ↑m ∧ b % ↑m < m ∧ b ≡ b % m (MOD m) := mod_cmpl_res m b
    have h4 : a ≡ b % ↑m (MOD m) := congr_trans h1 h3.right.right
    have h5 : 0 ≤ b % ↑m ∧ b % ↑m < m ∧ a ≡ b % m (MOD m) := by
      apply And.intro h3.left
      exact And.intro h3.right.left h4
    exact (Theorem_7_3_1 m a).unique h2 h5
  · assume h1 : a % ↑m = b % ↑m
    rw [← cc_eq_iff_congr, cc_eq_mod, cc_eq_mod m b]
    rw [h1]
  done

--Hint for next theorem: Use the lemma above,
--together with the theorems Int.ofNat_mod_ofNat and Nat.cast_inj.
theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := by
  apply Iff.intro
  · assume h1 : ↑a ≡ ↑b (MOD m)
    have h2 : (↑a % ↑m : Int) = ↑b % ↑m
      := (congr_iff_mod_eq_Int m ↑a ↑b).ltr h1
    rw [Int.ofNat_mod_ofNat, Int.ofNat_mod_ofNat] at h2
    exact Nat.cast_inj.ltr h2
  · assume h1 : a % m = b % m
    have h2 : (↑(a % m) : Int) = ↑(b % m) := Nat.cast_inj.rtl h1
    repeat rw [← Int.ofNat_mod_ofNat] at h2
    exact (congr_iff_mod_eq_Int m ↑a ↑b).rtl h2
  done

/- Section 7.4 -/
-- 1.
--Hint:  Use induction.
--For the base case, compute [a]_m ^ 0 * [1]_m in two ways:
--by Theorem_7_3_6_7, [a] ^ 0 * [1]_m = [a]_m ^ 0
--by ring, [a]_m ^ 0 * [1]_m = [1]_m.
lemma Exercise_7_4_5_Int (m : Nat) (a : Int) :
    ∀ (n : Nat), [a]_m ^ n = [a ^ n]_m := sorry

-- 2.
lemma left_inv_one_one_below {n : Nat} {g g' : Nat → Nat}
    (h1 : ∀ i < n, g' (g i) = i) : one_one_below n g := sorry

-- 3.
lemma comp_perm_below {n : Nat} {f g : Nat → Nat}
    (h1 : perm_below n f) (h2 : perm_below n g) :
    perm_below n (f ∘ g) := sorry

-- 4.
lemma perm_below_fixed {n : Nat} {g : Nat → Nat}
    (h1 : perm_below (n + 1) g) (h2 : g n = n) : perm_below n g := sorry

-- 5.
lemma Lemma_7_4_6 {a b c : Nat} :
    rel_prime (a * b) c ↔ rel_prime a c ∧ rel_prime b c := sorry

-- 6.
example {m a : Nat} [NeZero m] (h1 : rel_prime m a) :
    a ^ (phi m + 1) ≡ a (MOD m) := sorry

-- 7.
theorem Like_Exercise_7_4_11 {m a p : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p + 1 = phi m) :
    [a]_m * [a ^ p]_m = [1]_m := sorry

-- 8.
theorem Like_Exercise_7_4_12 {m a p q k : Nat} [NeZero m]
    (h1 : rel_prime m a) (h2 : p = q + (phi m) * k) :
    a ^ p ≡ a ^ q (MOD m) := sorry

/- Section 7.5 -/
-- 1.
--Hint:  Use induction.
lemma num_rp_prime {p : Nat} (h1 : prime p) :
    ∀ (k : Nat), k < p → num_rp_below p (k + 1) = k := sorry

-- 2.
lemma three_prime : prime 3 := sorry

-- 3.
--Hint:  Use the previous exercise, Exercise_7_2_7, and Theorem_7_4_2.
theorem Exercise_7_5_13a (a : Nat) (h1 : rel_prime 561 a) :
    ↑(a ^ 560) ≡ 1 (MOD 3) := sorry

-- 4.
--Hint:  Imitate the way Theorem_7_2_2_Int was proven from Theorem_7_2_2.
lemma Theorem_7_2_3_Int {p : Nat} {a b : Int}
    (h1 : prime p) (h2 : ↑p ∣ a * b) : ↑p ∣ a ∨ ↑p ∣ b := sorry

-- 5.
--Hint:  Use the previous exercise.
theorem Exercise_7_5_14b (n : Nat) (b : Int)
    (h1 : prime n) (h2 : b ^ 2 ≡ 1 (MOD n)) :
    b ≡ 1 (MOD n) ∨ b ≡ -1 (MOD n) := sorry
