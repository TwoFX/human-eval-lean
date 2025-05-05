def Int.toDigits (i : Int) : List Char :=
  i.natAbs.toDigits (base := 10)

def evenOddCount (num : Int) : Nat × Nat :=
  num.toDigits.foldl countDigit (0, 0)
where
  countDigit (evenOdd : Nat × Nat) : Char → Nat × Nat
    | '0' | '2' | '4' | '6' | '8' => (evenOdd.fst + 1, evenOdd.snd)
    | _                           => (evenOdd.fst, evenOdd.snd + 1)

example : evenOddCount (-12) = (1, 1)     := rfl
example : evenOddCount 123 = (1, 2)       := rfl
example : evenOddCount 7 = (0, 1)         := rfl
example : evenOddCount (-78) = (1, 1)     := rfl
example : evenOddCount 3452 = (2, 2)      := rfl
example : evenOddCount 346211 = (3, 3)    := rfl
example : evenOddCount (-345821) = (3, 3) := rfl
example : evenOddCount (-2) = (1, 0)      := rfl
example : evenOddCount (-45347) = (2, 3)  := rfl
example : evenOddCount 0 = (1, 0)         := rfl

def Prod.sum : Nat × Nat → Nat
  | (n₁, n₂) => n₁ + n₂

-- Applying `evenOddCount.countDigit` increases the total digit count by `1`.
theorem evenOddCount.countDigit_sum (evenOdd : Nat × Nat) (d : Char) :
    (evenOddCount.countDigit evenOdd d).sum = evenOdd.sum + 1 := by
  unfold evenOddCount.countDigit
  split <;> simp +arith [Prod.sum]

-- Folding `evenOddCount.countDigit` over a given digit count `init` produces the same total digit
-- count as folding `evenOddCount.countDigit` over `(0, 0)` and adding that to `init`.
theorem evenOddCount.countDigit_sum_foldl (ds : List Char) (init : Nat × Nat) :
    (ds.foldl evenOddCount.countDigit init).sum =
    (ds.foldl evenOddCount.countDigit (0, 0)).sum + init.sum := by
  induction ds generalizing init
  case nil     => simp [Prod.sum]
  case cons ih => simp +arith only [List.foldl_cons, ih (countDigit _ _), countDigit_sum]; rfl

-- The total digit count produced by `evenOddCount` matches the number of digits in the input.
theorem evenOddCount_sum_eq_length : (evenOddCount i).sum = i.toDigits.length := by
  rw [evenOddCount]
  generalize i.toDigits = ds
  induction ds
  case nil => rfl
  case cons ih => rw [List.foldl_cons, List.length_cons, evenOddCount.countDigit_sum_foldl, ih,
                      evenOddCount.countDigit_sum, Prod.sum]

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
