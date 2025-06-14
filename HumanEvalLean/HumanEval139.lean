-- from Mathlib
def Nat.factorial : Nat → Nat
  | 0 => 1
  | .succ n => Nat.succ n * factorial n

notation:10000 n "!" => Nat.factorial n

def Nat.brazilianFactorial : Nat → Nat
  | .zero => 1
  | .succ n => (Nat.succ n)! * brazilianFactorial n

def special_factorial (n : Nat) : Nat :=
  special_factorial.go n 1 1 0
  where

  go (n fact brazilFact curr : Nat) : Nat :=
    if _h: curr >= n
    then brazilFact
    else
      let fact' := (curr + 1) * fact
      let brazilFact' := brazilFact * fact'
      special_factorial.go n fact' brazilFact' (Nat.succ curr)
  termination_by n - curr

theorem special_factorial_func_correct {n : Nat} :
    special_factorial n = n.brazilianFactorial := by
  simp [special_factorial]
  suffices ∀ (curr fact brazilFact : Nat), fact = curr ! → brazilFact = curr.brazilianFactorial →
    curr ≤ n → special_factorial.go n fact brazilFact curr = n.brazilianFactorial by
      apply this
      · simp [Nat.factorial]
      · simp [Nat.brazilianFactorial]
      · simp
  intro curr
  induction h: n - curr generalizing curr with
  | zero =>
    intro _ brazil _ hbrazil hcurr
    rw [Nat.sub_eq_zero_iff_le] at h
    have : n = curr := by omega
    simp [special_factorial.go, h, this, hbrazil]
  | succ m ih =>
    intro fact brazilFact hfact hbrazil hcurr
    have : ¬ curr ≥ n := by omega
    unfold special_factorial.go
    simp only [ge_iff_le, this, ↓reduceDIte, Nat.succ_eq_add_one]
    have : n - (curr + 1) = m := by omega
    specialize ih (curr + 1) this ((curr + 1) * fact) (brazilFact * ((curr + 1) * fact))
    simp only [hfact, Nat.factorial, Nat.succ_eq_add_one, hbrazil, Nat.brazilianFactorial,
      forall_const] at ih
    simp only [hfact, hbrazil]
    apply ih
    · ac_rfl
    · omega

theorem test1 : special_factorial 4 = 288 := by native_decide
theorem test2 : special_factorial 5 = 34560 := by native_decide
theorem test3 : special_factorial 7 = 125411328000 := by native_decide
theorem test4 : special_factorial 1 = 1 := by native_decide

/-!
## Prompt

```python3

def special_factorial(n):
    """The Brazilian factorial is defined as:
    brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
    where n > 0

    For example:
    >>> special_factorial(4)
    288

    The function will receive an integer as input and should return the special
    factorial of this integer.
    """
```

## Canonical solution

```python3
    fact_i = 1
    special_fact = 1
    for i in range(1, n+1):
        fact_i *= i
        special_fact *= fact_i
    return special_fact
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(4) == 288, "Test 4"
    assert candidate(5) == 34560, "Test 5"
    assert candidate(7) == 125411328000, "Test 7"

    # Check some edge cases that are easy to work out by hand.
    assert candidate(1) == 1, "Test 1"

```
-/
