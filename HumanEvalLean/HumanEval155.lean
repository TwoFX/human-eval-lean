-- https://github.com/leanprover-community/batteries/pull/1267
theorem Nat.isDigit_digitChar_iff_lt : n.digitChar.isDigit ↔ (n < 10) := sorry
theorem Nat.mem_toDigits_base_10_isDigit (h : c ∈ toDigits 10 n) : c.isDigit := sorry

abbrev Digit := { c : Char // c.isDigit }

def Int.digits (i : Int) : List Digit :=
  i.natAbs
    |>.toDigits (base := 10)
    |>.attach
    |>.map fun ⟨j, h⟩ => ⟨j, Nat.mem_toDigits_base_10_isDigit h⟩

structure Tally where
  even : Nat
  odd  : Nat
deriving Inhabited

namespace Tally

instance : Add Tally where
  add t₁ t₂ := { even := t₁.even + t₂.even, odd := t₁.odd + t₂.odd }

def total (t : Tally) : Nat :=
  t.even + t.odd

def log (t : Tally) (d : Digit) : Tally :=
  match d.val with
  | '0' | '2' | '4' | '6' | '8' => { t with even := t.even + 1 }
  | _                           => { t with odd  := t.odd  + 1 }

-- Applying `log` increases a tally's total by `1`.
theorem log_total (d : Digit) (t : Tally) : (t.log d).total = t.total + 1 := by
  rw [log]
  split <;> simp +arith [total]

-- Folding `log` over a given tally `init` produces the same total digit count as folding `log` over
-- `⟨0, 0⟩` and adding that to `init`.
theorem log_total_foldl {ds : List Digit} (init : Tally) :
    (ds.foldl log init).total = (ds.foldl log ⟨0, 0⟩).total + init.total := by
  induction ds generalizing init
  case' cons hd _ ih => simp +arith only [List.foldl_cons, ih (log _ hd), log_total]
  all_goals simp [total]

def count (i : Int) : Tally :=
  i.digits.foldl log ⟨0, 0⟩

example : count (-12) = ⟨1, 1⟩     := rfl
example : count 123 = ⟨1, 2⟩       := rfl
example : count 7 = ⟨0, 1⟩         := rfl
example : count (-78) = ⟨1, 1⟩     := rfl
example : count 3452 = ⟨2, 2⟩      := rfl
example : count 346211 = ⟨3, 3⟩    := rfl
example : count (-345821) = ⟨3, 3⟩ := rfl
example : count (-2) = ⟨1, 0⟩      := rfl
example : count (-45347) = ⟨2, 3⟩  := rfl
example : count 0 = ⟨1, 0⟩         := rfl

-- The tally total produced by `count` matches the number of digits in the input.
theorem count_total_eq_length : (count i).total = i.digits.length := by
  rw [count]
  generalize i.digits = ds
  induction ds
  case nil     => rfl
  case cons ih => rw [List.foldl_cons, List.length_cons, log_total_foldl, ih, log_total]; rfl

theorem count_decompose {d : Nat} (hd : d < 10) :
    count (10 * n + d) = count n + ⟨d % 2, 1 - d % 2⟩ := by
  sorry

/-!
## Prompt

```python3

def even_odd_count(num):
    """Given an integer. return a tuple that has the number of even and odd digits respectively.

     Example:
        even_odd_count(-12) ==> (1, 1)
        even_odd_count(123) ==> (1, 2)
    """
```

## Canonical solution

```python3
    even_count = 0
    odd_count = 0
    for i in str(abs(num)):
        if int(i)%2==0:
            even_count +=1
        else:
            odd_count +=1
    return (even_count, odd_count)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(7) == (0, 1)
    assert candidate(-78) == (1, 1)
    assert candidate(3452) == (2, 2)
    assert candidate(346211) == (3, 3)
    assert candidate(-345821) == (3, 3)
    assert candidate(-2) == (1, 0)
    assert candidate(-45347) == (2, 3)
    assert candidate(0) == (1, 0)


    # Check some edge cases that are easy to work out by hand.
    assert True

```
-/
