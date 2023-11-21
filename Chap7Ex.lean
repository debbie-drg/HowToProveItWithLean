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

lemma dvd_gcd_dvd_left {n a b : Nat} (h : n ∣ gcd a b) : n ∣ a := by
  define at h
  obtain (c : Nat) (h1 : gcd a b = n * c) from h
  have h2 : gcd a b ∣ a := gcd_dvd_left a b
  define at h2
  obtain (d : Nat) (h3 : a = gcd a b * d) from h2
  define
  apply Exists.intro (c * d)
  rw [← mul_assoc, ← h1]
  exact h3

lemma dvd_gcd_dvd_right {n a b : Nat} (h : n ∣ gcd a b) : n ∣ b := by
  rw [gcd_comm] at h
  exact dvd_gcd_dvd_left h

theorem Exercise_7_1_10₁ (a b n : Nat) :
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
    (h1 : prime p) (h2 : a ∣ p) : a = 1 ∨ a = p := sorry

-- 2.
-- Hints:  Start with apply List.rec.  You may find mul_ne_zero useful
theorem prod_nonzero_nonzero : ∀ (l : List Nat),
    (∀ (a : Nat), a ∈ l → a ≠ 0) → prod l ≠ 0 := sorry

-- 3.
theorem rel_prime_iff_no_common_factor (a b : Nat) :
    rel_prime a b ↔ ¬∃ (p : Nat), prime p ∧ p ∣ a ∧ p ∣ b := sorry

-- 4.
theorem rel_prime_symm {a b : Nat} (h : rel_prime a b) :
    rel_prime b a := sorry

-- 5.
lemma in_prime_factorization_iff_prime_factor {a : Nat} {l : List Nat}
    (h1 : prime_factorization a l) (p : Nat) :
    p ∈ l ↔ prime_factor p a := sorry

-- 6.
theorem Exercise_7_2_5 {a b : Nat} {l m : List Nat}
    (h1 : prime_factorization a l) (h2 : prime_factorization b m) :
    rel_prime a b ↔ (¬∃ (p : Nat), p ∈ l ∧ p ∈ m) := sorry

-- 7.
theorem Exercise_7_2_6 (a b : Nat) :
    rel_prime a b ↔ ∃ (s t : Int), s * a + t * b = 1 := sorry

-- 8.
theorem Exercise_7_2_7 {a b a' b' : Nat}
    (h1 : rel_prime a b) (h2 : a' ∣ a) (h3 : b' ∣ b) :
    rel_prime a' b' := sorry

-- 9.
theorem Exercise_7_2_9 {a b j k : Nat}
    (h1 : gcd a b ≠ 0) (h2 : a = j * gcd a b) (h3 : b = k * gcd a b) :
    rel_prime j k := sorry

-- 10.
theorem Exercise_7_2_17a (a b c : Nat) :
    gcd a (b * c) ∣ gcd a b * gcd a c := sorry

/- Section 7.3 -/
-- 1.
theorem congr_trans {m : Nat} : ∀ {a b c : Int},
    a ≡ b (MOD m) → b ≡ c (MOD m) → a ≡ c (MOD m) := sorry

-- 2.
theorem Theorem_7_3_6_3 {m : Nat} (X : ZMod m) : X + [0]_m = X := sorry

-- 3.
theorem Theorem_7_3_6_4 {m : Nat} (X : ZMod m) :
    ∃ (Y : ZMod m), X + Y = [0]_m := sorry

-- 4.
theorem Exercise_7_3_4a {m : Nat} (Z1 Z2 : ZMod m)
    (h1 : ∀ (X : ZMod m), X + Z1 = X)
    (h2 : ∀ (X : ZMod m), X + Z2 = X) : Z1 = Z2 := sorry

-- 5.
theorem Exercise_7_3_4b {m : Nat} (X Y1 Y2 : ZMod m)
    (h1 : X + Y1 = [0]_m) (h2 : X + Y2 = [0]_m) : Y1 = Y2 := sorry

-- 6.
theorem Theorem_7_3_10 (m a : Nat) (b : Int) :
    ¬(↑(gcd m a) : Int) ∣ b → ¬∃ (x : Int), a * x ≡ b (MOD m) := sorry

-- 7.
theorem Theorem_7_3_11 (m n : Nat) (a b : Int) (h1 : n ≠ 0) :
    n * a ≡ n * b (MOD n * m) ↔ a ≡ b (MOD m) := sorry

-- 8.
theorem Exercise_7_3_16 {m : Nat} {a b : Int} (h : a ≡ b (MOD m)) :
    ∀ (n : Nat), a ^ n ≡ b ^ n (MOD m) := sorry

-- 9.
example {m : Nat} [NeZero m] (X : ZMod m) :
    ∃! (a : Int), 0 ≤ a ∧ a < m ∧ X = [a]_m := sorry

-- 10.
theorem congr_rel_prime {m a b : Nat} (h1 : a ≡ b (MOD m)) :
    rel_prime m a ↔ rel_prime m b := sorry

-- 11.
--Hint: You may find the theorem Int.ofNat_mod_ofNat useful.
theorem rel_prime_mod (m a : Nat) :
    rel_prime m (a % m) ↔ rel_prime m a := sorry

-- 12.
lemma congr_iff_mod_eq_Int (m : Nat) (a b : Int) [NeZero m] :
    a ≡ b (MOD m) ↔ a % ↑m = b % ↑m := sorry

--Hint for next theorem: Use the lemma above,
--together with the theorems Int.ofNat_mod_ofNat and Nat.cast_inj.
theorem congr_iff_mod_eq_Nat (m a b : Nat) [NeZero m] :
    ↑a ≡ ↑b (MOD m) ↔ a % m = b % m := sorry

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
