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


-- Section 7.2. Prime factorization

def prime (n : Nat) : Prop :=
  2 ≤ n ∧ ¬∃ (a b : Nat), a * b = n ∧ a < n ∧ b < n

/-
The main goal of this section is to prove that every integer has a unique factorization.
Let us first prove that every natural number greater or equal than 2 has a prime factor.
-/

def prime_factor (p n : Nat) : Prop := prime p ∧ p ∣ n

lemma dvd_trans {a b c : Nat} (h1 : a ∣ b) (h2 : b ∣ c) : a ∣ c := by
  define at h1
  obtain (c₁ : Nat) (h3 : b = a * c₁) from h1
  define at h2
  obtain (c₂ : Nat) (h4 : c = b * c₂) from h2
  define
  apply Exists.intro (c₁ * c₂)
  rw [← mul_assoc, ← h3, ← h4]
  done

lemma exists_prime_factor : ∀ (n : Nat), 2 ≤ n →
    ∃ (p : Nat), prime_factor p n := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ (n₁ : ℕ), n₁ < n → 2 ≤ n₁ → ∃ (p : ℕ), prime_factor p n₁
  assume h1 : 2 ≤ n
  by_cases h2 : prime n
  · -- If `n` is already prime, it's pretty obvious
    apply Exists.intro n
    define
    exact And.intro h2 (dvd_self n)
  · -- If `n` is not prime
    define at h2
    demorgan at h2
    disj_syll h2 h1
    obtain (a : Nat) (h3 : ∃ (b : Nat), a * b = n ∧ a < n ∧ b < n) from h2
    obtain (b : Nat) (h4 : a * b = n ∧ a < n ∧ b < n) from h3
    have h5 : 2 ≤ a := by
      by_contra h6
      have h7 : a ≤ 1 := by linarith
      have h8 : n ≤ b :=
        calc n
          _ = a * b := h4.left.symm
          _ ≤ 1 * b := by rel [h7]
          _ = b := by ring
      linarith -- n ≤ b contradicts b < n
    have h6 : ∃ (p : Nat), prime_factor p a := ih a h4.right.left h5
    obtain (p : Nat) (h7 : prime_factor p a) from h6
    apply Exists.intro p
    define
    define at h7
    apply And.intro h7.left
    have h8 : a ∣ n := by
      apply Exists.intro b
      exact h4.left.symm
    exact dvd_trans h7.right h8
  done

/-
By the well ordering principle, every number greater to or equal than 2 must
have a smallest prime factor.
-/

lemma exists_least_prime_factor {n : Nat} (h : 2 ≤ n) :
    ∃ (p : Nat), prime_factor p n ∧
    ∀ (q : Nat), prime_factor q n → p ≤ q := by
  set S : Set Nat := { p : Nat | prime_factor p n }
  have h2 : ∃ (p : Nat), p ∈ S := exists_prime_factor n h
  show ∃ (p : Nat), prime_factor p n ∧
    ∀ (q : Nat), prime_factor q n → p ≤ q from well_ord_princ S h2
  done

/-
We now introduce a new type: Lists. If `U` is a type, then `List U` is the type
of lists of objects of type `U`. They are denoted using brackets, so `[3, 7, 1]`
is of type `List Nat`.

`[]` denotes the empty list, also called `nil`.

If `a : U` and `l : List U`, `a :: l` denotes the list consisting of `a`
followed by the items of `l`. This is the `cons` operator, and every lsit can be
constructed by applying the `cons` operation repeatedly.

If `l : List U` and `a : U`, then `a ∈ l` denotes that `a` is one of the entries
in the list `l`. For example, `7 ∈ [3, 7, 1]`.

Here are some basic results about the `cons` operator.
-/

#check List.not_mem_nil
-- ∀ {α : Type u_1} (a : α), a ∉ []

#check List.mem_cons
-- ∀ {α : Type u_1} {a b : α} {l : List α}, a ∈ b :: l ↔ a = b ∨ a ∈ l

#check List.mem_cons_self
-- ∀ {α : Type u_1} (a : α) (l : List α), a ∈ a :: l

#check List.mem_cons_of_mem
-- ∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈ l → a ∈ y :: l

/-
Let us define some properties that we need towards our goals.
-/

def all_prime (l : List Nat) : Prop := ∀ p ∈ l, prime p
-- Every member of the list is prime

def nondec (l : List Nat) : Prop :=
  match l with
    | [] => True   -- True is a proposition that is always true
    | n :: L => (∀ m ∈ L, n ≤ m) ∧ nondec L
-- Every member of the list is less than or equal to all later members

def nondec_prime_list (l : List Nat) : Prop := all_prime l ∧ nondec l

def prod (l : List Nat) : Nat :=
  match l with
    | [] => 1
    | n :: L => n * (prod L)
-- The product of all members of l

def prime_factorization (n : Nat) (l : List Nat) : Prop :=
  nondec_prime_list l ∧ prod l = n
-- l is a non-decerasing list of prime numbers whose product is n.

/-
Let us prove some results
-/

lemma all_prime_nil : all_prime [] := by
  define
  fix p : Nat
  contrapos
  assume h1 : ¬prime p
  show p ∉ [] from List.not_mem_nil p
  done

lemma all_prime_cons (n : Nat) (L : List Nat) :
    all_prime (n :: L) ↔ prime n ∧ all_prime L := by
  apply Iff.intro
  · -- (→)
    assume h1 : all_prime (n :: L)
    define at h1
    apply And.intro (h1 n (List.mem_cons_self n L))
    define
    fix p : Nat; assume h2 : p ∈ L
    exact h1 p (List.mem_cons_of_mem n h2)
  · -- (←)
    assume h1 : prime n ∧ all_prime L
    define : all_prime L at h1
    define
    fix p : Nat; assume h2 : p ∈ n :: L
    rw [List.mem_cons] at h2
    by_cases on h2
    · rw [h2]; exact h1.left
    · exact h1.right p h2
  done

lemma nondec_nil : nondec [] := by
  define
  trivial -- Proves some obviously true statements
  done

lemma nondec_cons (n : Nat) (L : List Nat) :
    nondec (n :: L) ↔ (∀ m ∈ L, n ≤ m) ∧ nondec L := by rfl

lemma prod_nil : prod [] = 1 := by rfl

lemma prod_cons : prod (n :: L) = n * (prod L) := by rfl

/-
We now quickly review some other statements about lists.
If `l` is a list, we can get its length as `List.length l` or `l.length`.
-/

#check List.length_eq_zero
-- ∀ {α : Type u_1} {l : List α}, List.length l = 0 ↔ l = []

#check List.length_cons
-- ∀ {α : Type u_1} (a : α) (as : List α), List.length (a :: as) = Nat.succ (List.length as)

#check List.exists_cons_of_ne_nil
-- ∀ {α : Type u_1} {l : List α}, l ≠ [] → ∃ (b : α), ∃ (L : List α), l = b :: L

/- And one last lemma -/

lemma exists_cons_of_length_eq_succ {A : Type}
    {l : List A} {n : Nat} (h : l.length = n + 1) :
    ∃ (a : A) (L : List A), l = a :: L ∧ L.length = n := by
  have h1 : l ≠ [] := by
    by_contra h1
    have h2 : l.length = 0 := List.length_eq_zero.mpr h1
    linarith
  obtain (a : A) (h2 :  ∃ (L : List A), l = a :: L) from List.exists_cons_of_ne_nil h1
  obtain (L : List A) (h3 : l = a :: L) from h2
  apply Exists.intro a; apply Exists.intro L
  apply And.intro h3
  have h4 : List.length (a :: L) = List.length L + 1 := List.length_cons a L
  rw [← h3, h] at h4
  linarith
  done

/-
We can now prove that every member of a list of natural numbers divides
the product of the list.
-/

lemma list_elt_dvd_prod_by_length (a : Nat) : ∀ (n : Nat),
    ∀ (l : List Nat), l.length = n → a ∈ l → a ∣ prod l := by
  by_induc
  · fix l : List Nat; assume h1 : l.length = 0
    rw [List.length_eq_zero] at h1
    rw [h1]
    contrapos
    assume h2 : ¬a ∣ prod []
    exact List.not_mem_nil a
  · fix n : Nat
    assume ih : ∀ (l : List Nat), List.length l = n → a ∈ l → a ∣ prod l
    fix l : List Nat
    assume h1 : l.length = n + 1
    obtain (b : Nat) (h2 : ∃ (L : List Nat),
      l = b :: L ∧ L.length = n) from exists_cons_of_length_eq_succ h1
    obtain (L : List Nat) (h3 : l = b :: L ∧ L.length = n) from h2
    have h4 : a ∈ L → a ∣ prod L := ih L h3.right
    assume h5 : a ∈ l
    rw [h3.left, prod_cons]
    rw [h3.left, List.mem_cons] at h5
    by_cases on h5
    · apply Exists.intro (prod L)
      rw [h5]
    · have h6 : a ∣ prod L := h4 h5
      have h7 : prod L ∣ b * prod L := by
        apply Exists.intro b; ring
      exact dvd_trans h6 h7
  done

lemma list_elt_dvd_prod {a : Nat} {l : List Nat}
    (h : a ∈ l) : a ∣ prod l := by
  set n : Nat := l.length
  have h1 : l.length = n := by rfl
  show a ∣ prod l from list_elt_dvd_prod_by_length a n l h1 h
  done

/-
We can now prove that every natural has a prime factorization.
-/

lemma exists_prime_factorization : ∀ (n : Nat), n ≥ 1 →
    ∃ (l : List Nat), prime_factorization n l := by
  by_strong_induc
  fix n : Nat
  assume ih : ∀ n_1 < n, n_1 ≥ 1 →
    ∃ (l : List Nat), prime_factorization n_1 l
  assume h1 : n ≥ 1
  by_cases h2 : n = 1
  · -- Case n = 1
    apply Exists.intro []
    define
    apply And.intro
    · define
      exact And.intro all_prime_nil nondec_nil
    · rw [prod_nil, h2]
  · -- Case n > 1
    have h3 : n ≥ 2 := lt_of_le_of_ne' h1 h2
    obtain (p : Nat) (h4 : prime_factor p n ∧ ∀ (q : Nat),
      prime_factor q n → p ≤ q) from exists_least_prime_factor h3
    have p_prime_factor : prime_factor p n := h4.left
    define at p_prime_factor
    have p_prime : prime p := p_prime_factor.left
    have p_dvd_n : p ∣ n := p_prime_factor.right
    have p_least : ∀ (q : Nat), prime_factor q n → p ≤ q := h4.right
    obtain (m : Nat) (n_eq_pm : n = p * m) from p_dvd_n
    have h5 : m ≠ 0 := by
      contradict h1 with h6
      have h7 : n = 0 :=
        calc n
          _ = p * m := n_eq_pm
          _ = p * 0 := by rw [h6]
          _ = 0 := by ring
      rw [h7]
      norm_num
    have m_pos : 0 < m := Nat.pos_of_ne_zero h5
    have m_lt_n : m < n := by
      define at p_prime
      show m < n from
        calc m
          _ < m + m := by linarith
          _ = 2 * m := by ring
          _ ≤ p * m := by rel [p_prime.left]
          _ = n := n_eq_pm.symm
    obtain (L : List Nat) (h6 : prime_factorization m L)
      from ih m m_lt_n m_pos
    define at h6
    have ndpl_L : nondec_prime_list L := h6.left
    define at ndpl_L
    apply Exists.intro (p :: L)
    define
    apply And.intro
    · -- Proof of nondec_prime_list (p :: L)
      define
      apply And.intro
      · -- Proof of all_prime (p :: L)
        rw [all_prime_cons]
        exact And.intro p_prime ndpl_L.left
      · -- Proof of nondec (p :: L)
        rw [nondec_cons]
        apply And.intro _ ndpl_L.right
        fix q : Nat
        assume q_in_L : q ∈ L
        have h7 : q ∣ prod L := list_elt_dvd_prod q_in_L
        rw [h6.right] at h7
        have h8 : m ∣ n := by
          apply Exists.intro p
          rewrite [n_eq_pm]
          ring
        have q_dvd_n : q ∣ n := dvd_trans h7 h8
        have ap_L : all_prime L := ndpl_L.left
        define at ap_L
        have q_prime_factor : prime_factor q n :=
          And.intro (ap_L q q_in_L) q_dvd_n
        show p ≤ q from p_least q q_prime_factor
    · -- Proof of prod (p :: L) = n
      rewrite [prod_cons, h6.right, n_eq_pm]
      rfl
  done

/-
We now turn to uniqueness. We first need the concept of relative primes.
-/

def rel_prime (a b : Nat) : Prop := gcd a b = 1

theorem Theorem_7_2_2 {a b c : Nat}
    (h1 : c ∣ a * b) (h2 : rel_prime a c) : c ∣ b := by
  rw [←Int.coe_nat_dvd]
  define at h1; define at h2; define
  obtain (j : Nat) (h3 : a * b = c * j) from h1
  set s : Int := gcd_c1 a c
  set t : Int := gcd_c2 a c
  have h4 : s * ↑a + t * ↑c = ↑(gcd a c) := gcd_lin_comb c a
  rw [h2, Nat.cast_one] at h4
  apply Exists.intro (s * ↑j + t * ↑b)
  show ↑b = ↑c * (s * ↑j + t * ↑b) from
    calc ↑b
      _ = (1 : Int) * ↑b := (one_mul _).symm
      _ = (s * ↑a + t * ↑c) * ↑b := by rw [h4]
      _ = s * (↑a * ↑b) + t * ↑c * ↑b := by ring
      _ = s * (↑c * ↑j) + t * ↑c * ↑b := by
            rw [←Nat.cast_mul a b, h3, Nat.cast_mul c j]
      _ = ↑c * (s * ↑j + t * ↑b) := by ring
  done

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

lemma rel_prime_of_prime_not_dvd {a p : Nat}
    (h1 : prime p) (h2 : ¬p ∣ a) : rel_prime a p := by
  have h3 : gcd a p ∣ a := gcd_dvd_left a p
  have h4 : gcd a p ∣ p := gcd_dvd_right a p
  have h5 : gcd a p = 1 ∨ gcd a p = p := dvd_prime h1 h4
  have h6 : gcd a p ≠ p := by
    contradict h2 with h6
    rewrite [h6] at h3
    show p ∣ a from h3
    done
  disj_syll h5 h6
  show rel_prime a p from h5
  done

theorem Theorem_7_2_3 {a b p : Nat}
    (h1 : prime p) (h2 : p ∣ a * b) : p ∣ a ∨ p ∣ b := by
  or_right with h3
  have h4 : rel_prime a p := rel_prime_of_prime_not_dvd h1 h3
  show p ∣ b from Theorem_7_2_2 h2 h4
  done

/-
Before we move on, we mention that Lean has a theorem called `List.rec`
to justify induction on lists, which is more convenient than doing
induction on the length of a list.
-/

lemma eq_one_of_dvd_one {n : Nat} (h : n ∣ 1) : n = 1 := by
  define at h
  obtain (c : Nat) (h1 : 1 = n * c) from h
  by_contra h2
  by_cases h3 : n = 0
  · rw [h3, zero_mul] at h1
    trivial
  · have h4 : n > 1 := by
      have h5 : n ≥ 1 := Nat.pos_of_ne_zero h3
      exact lt_of_le_of_ne' h5 h2
    have h5 : c ≠ 0 := by
      by_contra h5
      rw [h5, mul_zero] at h1
      trivial
    have h5 : c ≥ 1 := Nat.pos_of_ne_zero h5
    have h6 : 1 > 1 := by
      calc 1
        _ = n * c := by rw [h1]
        _ > 1 * c := by rel [h4]
        _ = c := by rw [one_mul]
        _ ≥ 1 := h5
    trivial
  done

lemma prime_not_one {p : Nat} (h : prime p) : p ≠ 1 := by
  define at h
  have h1 : 2 ≤ p := h.left
  linarith

theorem Theorem_7_2_4 {p : Nat} (h1 : prime p) :
    ∀ (l : List Nat), p ∣ prod l → ∃ a ∈ l, p ∣ a := by
  apply List.rec
  · -- Base case
    rw [prod_nil]
    assume h2 : p ∣ 1
    have h3 : p = 1 := eq_one_of_dvd_one h2
    by_contra
    exact (prime_not_one h1) h3
  · -- Induction step
    fix b : Nat
    fix L : List Nat
    assume ih : p ∣ prod L → ∃ a ∈ L, p ∣ a
    assume h2 : p ∣ prod (b :: L)
    rw [prod_cons] at h2
    have h3 : p ∣ b ∨ p ∣ prod L := Theorem_7_2_3 h1 h2
    by_cases on h3
    · -- Case p ∣ b
      apply Exists.intro b
      exact And.intro (List.mem_cons_self b L) h3
    · -- Case p ∣ prod L
      obtain (a : Nat) (h4 : a ∈ L ∧ p ∣ a) from ih h3
      apply Exists.intro a
      exact And.intro (List.mem_cons_of_mem b h4.left) h4.right
  done

lemma prime_in_list {p : Nat} {l : List Nat}
    (h1 : prime p) (h2 : all_prime l) (h3 : p ∣ prod l) : p ∈ l := by
  obtain (a : Nat) (h4 : a ∈ l ∧ p ∣ a) from Theorem_7_2_4 h1 l h3
  define at h2
  have h5 : prime a := h2 a h4.left
  have h6 : p = 1 ∨ p = a := dvd_prime h5 h4.right
  disj_syll h6 (prime_not_one h1)
  rw [h6]
  show a ∈ l from h4.left
  done

lemma first_le_first {p q : Nat} {l m : List Nat}
    (h1 : nondec_prime_list (p :: l)) (h2 : nondec_prime_list (q :: m))
    (h3 : prod (p :: l) = prod (q :: m)) : p ≤ q := by
  define at h1; define at h2
  have h4 : q ∣ prod (p :: l) := by
    define
    apply Exists.intro (prod m)
    rw [←prod_cons]
    show prod (p :: l) = prod (q :: m) from h3
    done
  have h5 : all_prime (q :: m) := h2.left
  rw [all_prime_cons] at h5
  have h6 : q ∈ p :: l := prime_in_list h5.left h1.left h4
  have h7 : nondec (p :: l) := h1.right
  rw [nondec_cons] at h7
  rw [List.mem_cons] at h6
  by_cases on h6
  · -- Case 1. h6 : q = p
    linarith
    done
  · -- Case 2. h6 : q ∈ l
    have h8 : ∀ m ∈ l, p ≤ m := h7.left
    show p ≤ q from h8 q h6
    done
  done

lemma nondec_prime_list_tail {p : Nat} {l : List Nat}
    (h : nondec_prime_list (p :: l)) : nondec_prime_list l := by
  define at h
  define
  apply And.intro
  · have h1 : all_prime (p :: l) := h.left
    define at h1
    define; fix p' : Nat; assume h2 : p' ∈ l
    have h3 : p' ∈ p :: l := List.mem_cons_of_mem p h2
    exact h1 p' h3
  · have h2 : nondec (p :: l) := h.right
    define at h2
    exact h2.right
  done

lemma cons_prod_not_one {p : Nat} {l : List Nat}
    (h : nondec_prime_list (p :: l)) : prod (p :: l) ≠ 1 := by
  define at h
  have h1 : all_prime (p :: l) := h.left
  define at h1
  have h2 : p ∈ p :: l :=  List.mem_cons_self p l
  have h3 : prime p := h1 p h2
  have h4 : p ∣ prod (p :: l) := list_elt_dvd_prod h2
  have h5 : p ≠ 1 := prime_not_one h3
  by_contra h6
  rw [h6] at h4
  have h7 : p = 1 := eq_one_of_dvd_one h4
  apply h5; exact h7
  done

lemma list_nil_iff_prod_one {l : List Nat} (h : nondec_prime_list l) :
    l = [] ↔ prod l = 1 := by
  apply Iff.intro
  · assume h1 : l = []
    rw [h1]
    rfl
  · assume h1 : prod l = 1
    by_contra h2
    obtain (p : Nat) (h3 : exists L : List Nat, l = p :: L) from List.exists_cons_of_ne_nil h2
    obtain (L : List Nat) (h4 : l = p :: L) from h3
    rw [h4] at h
    have h5 : prod (p :: L) ≠ 1 := cons_prod_not_one h
    apply h5
    rw [h4] at h1
    exact h1
  done

lemma prime_pos {p : Nat} (h : prime p) : p > 0 := by
  define at h
  have h1 : 2 ≤ p := h.left
  linarith
  done

theorem Theorem_7_2_5 : ∀ (l1 l2 : List Nat),
    nondec_prime_list l1 → nondec_prime_list l2 →
    prod l1 = prod l2 → l1 = l2 := by
  apply List.rec
  · -- Base case
    fix l2 : List Nat
    assume h1 : nondec_prime_list []
    assume h2 : nondec_prime_list l2
    assume h3 : prod [] = prod l2
    rw [prod_nil, eq_comm, ← list_nil_iff_prod_one h2] at h3
    exact h3.symm
  · -- Induction step
    fix p : Nat
    fix L1 : List Nat
    assume ih : ∀ (l2 : List Nat), nondec_prime_list L1 →
        nondec_prime_list l2 → prod L1 = prod l2 → L1 = l2
    fix l2 : List Nat
    assume h1 : nondec_prime_list (p :: L1)
    assume h2 : nondec_prime_list l2
    assume h3 : prod (p :: L1) = prod l2
    have h4 : ¬prod (p :: L1) = 1 := cons_prod_not_one h1
    rw [h3, ←list_nil_iff_prod_one h2] at h4
    obtain (q : Nat) (h5 : ∃ (L : List Nat), l2 = q :: L) from
      List.exists_cons_of_ne_nil h4
    obtain (L2 : List Nat) (h6 : l2 = q :: L2) from h5
    rw [h6] at h2
    rw [h6] at h3
    have h7 : p ≤ q := first_le_first h1 h2 h3
    have h8 : q ≤ p := first_le_first h2 h1 h3.symm
    have h9 : p = q := by linarith
    rewrite [h9, prod_cons, prod_cons] at h3
    have h10 : nondec_prime_list L1 := nondec_prime_list_tail h1
    have h11 : nondec_prime_list L2 := nondec_prime_list_tail h2
    define at h2
    have h12 : all_prime (q :: L2) := h2.left
    rewrite [all_prime_cons] at h12
    have h13 : q > 0 := prime_pos h12.left
    have h14 : prod L1 = prod L2 := Nat.eq_of_mul_eq_mul_left h13 h3
    have h15 : L1 = L2 := ih L2 h10 h11 h14
    rw [h6, h9, h15]
  done

/-
Finally, we can prove the fundamental theorem of arithmetic
-/

theorem fund_thm_arith (n : Nat) (h : n ≥ 1) :
    ∃! (l : List Nat), prime_factorization n l := by
  exists_unique
  · -- Existence
    exact exists_prime_factorization n h
  · -- Uniqueness
    fix l1 : List Nat; fix l2 : List Nat
    assume h1 : prime_factorization n l1; define at h1
    assume h2 : prime_factorization n l2; define at h2
    have h3 : prod l1 = n := h1.right
    rw [← h2.right] at h3
    exact Theorem_7_2_5 l1 l2 h1.left h2.left h3
  done
