import Std.Tactic.Do

def isPrime (n : Nat) : Bool := Id.run do
  let mut i := 2
  while i * i ≤ n do
    if i ∣ n then
      return false
    else
      i := i + 1
  return 1 < n

def isMultipleOf2Primes (a : Nat) : Bool := Id.run do
  let mut i := 2
  while i * i ≤ a do
    if i ∣ a then
      return isPrime (a / i)
    else
      i := i + 1
  return false

def isMultipleOf3Primes (a : Nat) : Bool := Id.run do
  let mut i := 2
  while i * i * i ≤ a do
    if i ∣ a then
      return isMultipleOf2Primes (a / i)
    else
      i := i + 1
  return false

def isMultiplyPrime (a : Nat) : Bool :=
  isMultipleOf3Primes a

example : isMultiplyPrime 5 = false := by native_decide
example : isMultiplyPrime 30 = true := by native_decide
example : isMultiplyPrime 8 = true := by native_decide
example : isMultiplyPrime 10 = false := by native_decide
example : isMultiplyPrime 125 = true := by native_decide
example : isMultiplyPrime (3 * 5 * 7) = true := by native_decide
example : isMultiplyPrime (3 * 6 * 7) = false := by native_decide
example : isMultiplyPrime (9 * 9 * 9) = false := by native_decide

def Nat.IsPrime (n : Nat) : Prop :=
  n > 1 ∧ ∀ m, m ∣ n → m = 1 ∨ m = n

theorem isPrime_is_correct (n : Nat) : isPrime n ↔ Nat.IsPrime n := by sorry

def IsMultiplyPrimeIff (solution : Nat → Bool) : Prop :=
  (a : Nat) → solution a ↔ ∃ (p₁ p₂ p₃ : Nat), p₁ * p₂ * p₃ = a ∧ Nat.IsPrime p₁ ∧ Nat.IsPrime p₂ ∧ Nat.IsPrime p₃

theorem isMultiplyPrime_is_correct : IsMultiplyPrimeIff isMultiplyPrime := by
  sorry

/-!
## Prompt

```python3

def is_multiply_prime(a):
    """Write a function that returns true if the given number is the multiplication of 3 prime numbers
    and false otherwise.
    Knowing that (a) is less then 100.
    Example:
    is_multiply_prime(30) == True
    30 = 2 * 3 * 5
    """
```

## Canonical solution

```python3
    def is_prime(n):
        for j in range(2,n):
            if n%j == 0:
                return False
        return True

    for i in range(2,101):
        if not is_prime(i): continue
        for j in range(2,101):
            if not is_prime(j): continue
            for k in range(2,101):
                if not is_prime(k): continue
                if i*j*k == a: return True
    return False
```

## Tests

```python3
def check(candidate):

    assert candidate(5) == False
    assert candidate(30) == True
    assert candidate(8) == True
    assert candidate(10) == False
    assert candidate(125) == True
    assert candidate(3 * 5 * 7) == True
    assert candidate(3 * 6 * 7) == False
    assert candidate(9 * 9 * 9) == False
    assert candidate(11 * 9 * 9) == False
    assert candidate(11 * 13 * 7) == True

```
-/
