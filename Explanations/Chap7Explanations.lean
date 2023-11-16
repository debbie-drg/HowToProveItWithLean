import HTPILib.HTPIDefs
import HTPILib.Chap6

namespace HTPI


-- Chapter 7. Number Theory

-- Section 7.1 Greatest Common Divisors

/-
The explanations here are going to be more succint. In this section we
introduce the Euclidean Algorithm to compute the gcd of two numbers.
Recall that the remainder operation was denoted `a % b`.

The main ingredient of the algorithm lies in the next two results.
-/

theorem dvd_mod_of_dvd_a_b {a b d : Nat}
    (h1 : d ∣ a) (h2 : d ∣ b) : d ∣ (a % b) := by
  set q : Nat := a / b
  have h3 : b * q + a % b = a := Nat.div_add_mod a b
  obtain (j : Nat) (h4 : a = d * j) from h1
  obtain (k : Nat) (h5 : b = d * k) from h2
  define
  apply Exists.intro (j - k * q)
  show a % b = d * (j - k * q) from
    calc a % b
      _ = b * q + a % b - b * q := (Nat.add_sub_cancel_left _ _).symm
      _ = a - b * q := by rw [h3]
      _ = d * j - d * (k * q) := by rw [h4, h5, mul_assoc]
      _ = d * (j - k * q) := (Nat.mul_sub_left_distrib _ _ _).symm
  done

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

/-
These theorems tell us that the gcd of `a` and `b` is the same as that of
`b` and `a % b`; thus we can iterate:
-/

def gcd₁ (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 => gcd₁ (n + 1) (a % (n + 1))

/-
Unfortunately, Lean cannot determine that this terminates, so it shows
an error. Recursive functions don't necessarily need to end.

Consider the following more obvious example.
-/

def loop (n : Nat) : Nat := loop (n + 1)

/-
Again, the lack of guarantee of termination means this definition fails.
It does not provide us with a function from Nat to Nat.
-/

/-
While the `loop` function does not terminate, gcd should. We just need
to show it to Lean.

The function `gcd` has two arguments: `a` and `b`. When `b = n + 1`, we
have to compute `gcd (n + 1) (a % (n + 1))`. The first argument here
could be larger than the first argument in the value we are trying to
compute, but no matter, because the second will always be smaller.
This suffices to show that the computation must terminate. We can tell
Lean to focus on the second argument by adding a `termination_by`.
-/

def gcd₂ (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 => gcd₂ (n + 1) (a % (n + 1))
  termination_by gcd₂ a b => b

/-
Lean is still not satisfied, but the error is more helpful now. Namely,
it claims to have proven that `a % (n + 1) < Nat.succ n`. where
`Nat.succ n` is `n + 1`. We need to produce a proof of this fact.
-/

lemma mod_succ_lt (a n : Nat) : a % (n + 1) < n + 1 := by
  have h : n + 1 > 0 := Nat.succ_pos n
  show a % (n + 1) < n + 1 from Nat.mod_lt a h
  done

/-
With this, and using a `have` expression as suggested by the error, we
can finally successfully define the function.
-/

def gcd (a b : Nat) : Nat :=
  match b with
    | 0 => a
    | n + 1 =>
      have : a % (n + 1) < n + 1 := mod_succ_lt a n
      gcd (n + 1) (a % (n + 1))
  termination_by gcd a b => b

/-
And now we can compute stuff!
-/

#eval gcd 672 161    --Answer: 7.  Note 672 = 7 * 96 and 161 = 7 * 23.

/-
We now move to establishing the main properties of gcd.
-/

lemma gcd_base (a : Nat) : gcd a 0 = a := by rfl

lemma gcd_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd a b = gcd b (a % b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
  rewrite [h2]
  rfl
  done

lemma mod_nonzero_lt (a : Nat) {b : Nat} (h : b ≠ 0) : a % b < b := by
  have h1 : b > 0 := Nat.pos_of_ne_zero h
  show a % b < b from Nat.mod_lt a h1
  done

lemma dvd_self (n : Nat) : n ∣ n := by
  apply Exists.intro 1
  rw [mul_one]
  done

/-
One important result is that `gcd a b` divices both `a` and `b`. We prove it by strong
induction.
-/

theorem gcd_dvd : ∀ (b a : Nat), (gcd a b) ∣ a ∧ (gcd a b) ∣ b := by
  by_strong_induc
  fix b : ℕ
  assume ih : ∀ (b' : ℕ), b' < b → ∀ (a : ℕ), gcd a b' ∣ a ∧ gcd a b' ∣ b'
  fix a : ℕ
  by_cases h1 : b = 0
  · -- Case b = 0
    rw [h1, gcd_base]
    apply And.intro (dvd_self a)
    define; apply Exists.intro 0
    rfl
  · -- Case b ≠ 0
    rw [gcd_nonzero a h1]
    have h2 : a % b < b := mod_nonzero_lt a h1
    have h3 : (gcd b (a % b)) ∣ b ∧ (gcd b (a % b)) ∣ (a % b) :=
      ih (a % b) h2 b
    apply And.intro _ h3.left
    exact dvd_a_of_dvd_b_mod h3.left h3.right
  done

/-
Note that we would not be able to prove the result fixing a and then doing strong
induction, because of how the `gcd` function is defined.

We can now get two different theorems stating this relation for both left and right.
-/

theorem gcd_dvd_left (a b : Nat) : (gcd a b) ∣ a := (gcd_dvd b a).left

theorem gcd_dvd_right (a b : Nat) : (gcd a b) ∣ b := (gcd_dvd b a).right

/-
Euclid's algorithm to compute thet `gcd` can be extended to show constructively
that we can obtain integers `t` and `s` such that `gcd(a, b) = s * a + t * b`.
Note that we need to use integers, as it is possible that `t` and `s` cannot be
positive at the same time. Here, we will use a slightly different technique to
prove this result and obtain the integers.
-/

/-
If `b = 0`, we have that `gcd(a,b) = a = 1 * a + 0 * b`, so we can use `s = 1` and
`t = 0`. Otherwise, let `q` and `r` be the quotient and remainder of dividing `a` by
`b`, hence `a = b * q + r`. Furthermore, `gcd(a,b) = gcd(b,r)`. Now, if we have
already computed `s'` and `t'` such that `gcd(b,r) = s' * b + t' * r`, then
`gcd(a,b) = gcd(b,r) = s' * b + t' * r = s' * b + t' * (a - b * q)`
        ` = t' * a + (s' - t' * q) * b`
Therefore, to write `gcd(a,b) = a * s + t * b` we use `s = t'` and `t = s' - t' * q`.
If we need to continue computations we can keep doing it recursively.
-/

/-
This provides us with a basis to define two recursive functions: `gcd_c1` and `gcd_c2`,
with `s = gcd_c1 a b` and `t = gcd_c2 a b`. These two functions will be mutually
recursive: each is defined not only in terms of them but in terms of the other as well.
Lean allows for this, as we now show.

One further note: since `s` and `t` can be negative, we need to work with integers, so
type coercion will be used.
-/

mutual
  def gcd_c1 (a b : Nat) : Int :=
    match b with
      | 0 => 1
      | n + 1 =>
        have : a % (n + 1) < n + 1 := mod_succ_lt a n
        gcd_c2 (n + 1) (a % (n + 1))
          --Corresponds to s = t' in (*)

  def gcd_c2 (a b : Nat) : Int :=
    match b with
      | 0 => 0
      | n + 1 =>
        have : a % (n + 1) < n + 1 := mod_succ_lt a n
        gcd_c1 (n + 1) (a % (n + 1)) -
          (gcd_c2 (n + 1) (a % (n + 1))) * ↑(a / (n + 1))
          --Corresponds to t = s' - t'q in (*)
end
  termination_by
    gcd_c1 a b => b
    gcd_c2 a b => b

/-
We now prove the desired result: that this function provides the coefficients to write
the gcd. Let us begin with some lemmas.
-/

lemma gcd_c1_base (a : Nat) : gcd_c1 a 0 = 1 := by rfl

lemma gcd_c1_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c1 a b = gcd_c2 b (a % b) := by
  obtain (n : ℕ) (h1 : b = n + 1) from exists_eq_add_one_of_ne_zero h
  rw [h1]
  rfl
  done

lemma gcd_c2_base (a : Nat) : gcd_c2 a 0 = 0 := by rfl

lemma gcd_c2_nonzero (a : Nat) {b : Nat} (h : b ≠ 0) :
    gcd_c2 a b = gcd_c1 b (a % b) - (gcd_c2 b (a % b)) * ↑(a / b) := by
  obtain (n : Nat) (h2 : b = n + 1) from exists_eq_add_one_of_ne_zero h
  rw [h2]
  rfl
  done

/-
And now we can prove the result.
-/

theorem gcd_lin_comb : ∀ (b a : Nat),
    (gcd_c1 a b) * ↑a + (gcd_c2 a b) * ↑b = ↑(gcd a b) := by
  by_strong_induc
  fix b : ℕ
  assume ih : ∀ (b_1 : ℕ), b_1 < b → ∀ (a : ℕ),
      gcd_c1 a b_1 * ↑a + gcd_c2 a b_1 * ↑b_1 = ↑(gcd a b_1)
  fix a : ℕ
  by_cases h1 : b = 0
  · -- Case b = 0
    rw [h1, gcd_c1_base, gcd_c2_base, gcd_base]
    norm_num
  · -- Case b ≠ 0
    rw [gcd_c1_nonzero a h1, gcd_c2_nonzero a h1, gcd_nonzero a h1]
    -- We introduce some variables to simplify the notation
    set r : Nat := a % b
    set q : Nat := a / b
    set s : Int := gcd_c1 b r
    set t : Int := gcd_c2 b r
    have h2 : r < b := mod_nonzero_lt a h1
    have h3 : s * ↑b + t * ↑r = ↑(gcd b r) := ih r h2 b
    have h4 : b * q + r = a := Nat.div_add_mod a b
    rewrite [←h3, ←h4]
    rewrite [Nat.cast_add, Nat.cast_mul]
    ring
  done

/-
The use of the cast is necessary in order for `ring` to be able to complete the proof.
It makes the remaining naturals in the expression into integers.
-/

#eval gcd_c1 672 161  --Answer: 6
#eval gcd_c2 672 161  --Answer: -25
  --Note 6 * 672 - 25 * 161 = 4032 - 4025 = 7 = gcd 672 161

/-
We finish this section with another result.
-/

theorem Theorem_7_1_6 {d a b : Nat} (h1 : d ∣ a) (h2 : d ∣ b) :
    d ∣ gcd a b := by
  rewrite [←Int.coe_nat_dvd]
  set s : Int := gcd_c1 a b
  set t : Int := gcd_c2 a b
  have h3 : s * ↑a + t * ↑b = ↑(gcd a b) := gcd_lin_comb b a
  rewrite [←h3]
  obtain (j : Nat) (h4 : a = d * j) from h1
  obtain (k : Nat) (h5 : b = d * k) from h2
  rewrite [h4, h5, Nat.cast_mul, Nat.cast_mul]
  define
  apply Exists.intro (s * ↑j + t * ↑k)
  ring
  done

/-
`Int.coe_nat_dvd` establishes that divisibility is equivalent over the integers and
naturals, when both numbers are natural.
-/
