import HTPILib.HTPIDefs
namespace HTPI


-- Chapter ^: Mathematical induction --


-- Section 6.1. Proof by Mathematical Induction

/-
Mathematical induction is used to prove goals of the form
`∀ (n : Nat), P n`
by proving `P 0` and `∀ (n : Nat), P n → P (n + 1)`. These are respectively
called the "base step" and the "induction step".

Lean has the tactic `by_induc`. When used towards a goal of form `∀ (n : Nat), P n`,
the givens are unchanged, but the goal is replaced by two goals: the
base case goal and the induction step goal. We illustrate with an example.
-/

theorem Like_Example_6_1_2 :
    ∀ (n : Nat), 3 ∣ n ^ 3 + 2 * n := by
  by_induc
  · define
    apply Exists.intro 0
    rfl
  · fix n : ℕ
    assume ih : 3 ∣ n ^ 3 + 2 * n -- induction hypothesis
    define at ih
    obtain (k : ℕ) (h1 : n ^ 3 + 2 * n = 3 * k) from ih
    define
    apply Exists.intro (k + n ^ 2 + n + 1)
    show (n + 1) ^ 3 + 2 * (n + 1) = 3 * (k + n ^ 2 + n + 1) from
      calc (n + 1) ^ 3 + 2 * (n + 1)
        _ = n ^ 3 + 2 * n + 3 * n ^ 2 + 3 * n + 3 := by ring
        _ = 3 * k + 3 * n ^ 2 + 3 * n + 3 := by rw [h1]
        _ = 3 * (k + n ^ 2 + n + 1) := by ring
  done

/-
We now use an example which involves a sum over an index. In Lean, the
notation for that is `Sum i from k to n, f i`
-/

/-
To use induction to prove results involving sums, we can use the following:
-/

#check sum_base
/- @sum_base : ∀ {A : Type} [inst : AddZeroClass A] {k : ℕ} {f : ℕ → A},
            Sum i from k to k, f i = f k -/

#check sum_step
/-
@sum_step : ∀ {A : Type} [inst : AddZeroClass A] {k n : ℕ} {f : ℕ → A},
            k ≤ n → Sum i from k to n + 1, f i =
              (Sum i from k to n, f i) + f (n + 1) -/

#check sum_from_zero_step
/- ∀ {A : Type} [inst : AddZeroClass A] {n : ℕ} {f : ℕ → A},
            Sum i from 0 to n + 1, f i =
              (Sum i from 0 to n, f i) + f (n + 1) -/


theorem Like_Example_6_1_1 :
    ∀ (n : Nat), (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1) := by
  by_induc
  · -- Base case
    rw [sum_base]
    rfl
    done
  · -- Induction step
    fix n : ℕ
    assume ih : (Sum i from 0 to n, 2 ^ i) + 1 = 2 ^ (n + 1)
    show (Sum i from 0 to n + 1, 2 ^ i) + 1 = 2 ^ (n + 1 + 1) from
      calc (Sum i from 0 to n + 1, 2 ^ i) + 1
        _ = (Sum i from 0 to n, 2 ^ i) + 2 ^ (n + 1) + 1 := by rw [sum_from_zero_step]
        _ = (Sum i from 0 to n, 2 ^ i) + 1 + 2 ^ (n + 1) := by ring
        _ = 2 ^ (n + 1) + 2 ^ (n + 1) := by rw [ih]
        _ = 2 ^ (n + 2) := by ring
  done

/-
One further example. The next example will use two tactics we have not yet
encountered.

* `norm_num`: evaluation of arithmetic expressions like *, +, -, ^, ≤.
* `linarith`: makes inferences that involve combining linear equations and inequalities.
-/
theorem Example_6_1_3 : ∀ n ≥ 5, 2 ^ n > n ^ 2 := by
  by_induc
  · -- Base case
    norm_num
  · -- Induction step
    fix n : ℕ
    assume h1 : n ≥ 5
    assume ih : 2 ^ n > n ^ 2
    have h2 : n * n ≥ n * 5 := ge_iff_le.mpr (Nat.mul_le_mul_left n h1)
    show 2 ^ (n + 1) > (n + 1) ^ 2 from
      calc 2 ^ (n + 1)
        _ = 2 * 2 ^ n := by ring
        _ > 2 * n ^ 2 := by linarith
        _ ≥ n ^ 2  + 5 * n := by linarith
        _ > n ^ 2 + 2 * n + 1 := by linarith
        _ = (n + 1) ^ 2 := by ring
  done

/-
Note that since we are using natural numbers, we need to avoid subtractions
that could be negative, as we will not get what we expect.
-/

#eval 2 - 3 -- returns 0

/-
We can avoid this problem by specifying that the used numbers are integers,
which we can do by using `(2 : Int)`. Substraction of integers behaves
as it should.
-/

#eval (2 : Int) - 3 -- returns -1

theorem Example_6_1_1 :
    ∀ (n : Nat), Sum i from 0 to n, (2 : Int) ^ i =
    (2 : Int) ^ (n + 1) - (1 : Int) := by
  by_induc
  · -- Base case
    rw [sum_base]
    rfl
  · -- Induction step
    fix n : ℕ
    assume ih : Sum i from 0 to n, (2 : Int) ^ i = (2 : Int) ^ (n + 1) - 1
    show Sum i from 0 to n + 1, (2 : Int) ^ i = (2 : Int) ^ (n + 1 + 1) - (1 : Int) from
      calc Sum i from 0 to n + 1, (2 : Int) ^ i
        _ = (Sum i from 0 to n, (2 : Int) ^ i) + (2 : Int) ^ (n + 1) := by rw [sum_from_zero_step]
        _ = (2 : Int) ^ (n + 1) - 1 + (2 : Int) ^ (n + 1) := by rw [ih]
        _ = (2 : Int) ^ (n + 1 + 1) - (1 : Int) := by ring
  done

/-
Without the Int typing, the result would be false.
-/
