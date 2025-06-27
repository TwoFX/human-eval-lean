/-- Computes the largest divisor in O(sqrt n) via trial divison. -/
def largestDivisor (n : Nat) : Nat :=
  go 2
where
  go (i : Nat) : Nat :=
    if h : n < i * i then
      1
    else if n % i = 0 then
      n / i
    else go (i + 1)
  termination_by n - i
  decreasing_by
    have : i < n := by
      match i with
      | 0 => omega
      | 1 => omega
      | i + 2 => exact Nat.lt_of_lt_of_le (Nat.lt_mul_self_iff.2 (by omega)) (Nat.not_lt.1 h)
    omega

example : largestDivisor 3 = 1 := by native_decide
example : largestDivisor 7 = 1 := by native_decide
example : largestDivisor 10 = 5 := by native_decide
example : largestDivisor 100 = 50 := by native_decide
example : largestDivisor 49 = 7 := by native_decide

inductive LargestDivisorSpec (n : Nat) : Nat → Prop
  | one : (∀ j, 2 ≤ j → j * j ≤ n → n % j ≠ 0) → LargestDivisorSpec n 1
  | div {i} : (∀ j, 2 ≤ j → j < i → n % j ≠ 0) → 2 ≤ i → n % i = 0 → LargestDivisorSpec n (n / i)

theorem largestDivisorSpec_go {n i : Nat} (hi : 2 ≤ i)
    (hi' : ∀ j, 2 ≤ j → j < i → n % j ≠ 0) : LargestDivisorSpec n (largestDivisor.go n i) := by
  fun_induction largestDivisor.go n i
  case case1 i hni =>
    apply LargestDivisorSpec.one
    intro j hj hj'
    apply hi' _ hj
    exact Nat.mul_self_lt_mul_self_iff.1 (Nat.lt_of_le_of_lt hj' hni)
  case case2 i hni hni' =>
    exact LargestDivisorSpec.div hi' hi hni'
  case case3 i hni hni' ih =>
    apply ih (by omega)
    intro j hj hij
    by_cases hij' : j = i
    · exact hij' ▸ hni'
    · exact hi' _ hj (by omega)

theorem largestDivisorSpec_largestDivisor {n : Nat} :
    LargestDivisorSpec n (largestDivisor n) := by
  rw [largestDivisor]
  exact largestDivisorSpec_go (Nat.le_refl _) (by omega)

theorem Nat.lt_mul_iff {a b : Nat} : a < a * b ↔ 0 < a ∧ 1 < b := by
  obtain (rfl|ha) := Nat.eq_zero_or_pos a
  · simp
  · simp [ha]

theorem mod_ne_zero_of_forall_of_div_lt {n i : Nat} (hn : 1 < n)
    (h : ∀ j, 2 ≤ j → j < i → n % j ≠ 0) (hi : n % i = 0) (k : Nat) (hk : n / i < k) (hk₁ : k < n) :
    n % k ≠ 0 := by
  intro hk₂
  obtain ⟨d, rfl⟩ := Nat.dvd_of_mod_eq_zero hk₂
  rw [Nat.lt_mul_iff] at hk₁
  have hi₀ : 0 < i := by
    apply Nat.pos_iff_ne_zero.2
    rintro rfl
    simp only [Nat.mod_zero] at hi
    omega
  refine h d ?_ ?_ (by simp)
  · omega
  · rw [Nat.div_lt_iff_lt_mul hi₀] at hk
    exact Nat.lt_of_mul_lt_mul_left hk

theorem mod_ne_zero_of_forall_of_lt_mul_self {n : Nat} (hn : 1 < n)
    (h : ∀ j, 2 ≤ j → j * j ≤ n → n % j ≠ 0) (k : Nat) (hk : n < k * k) (hk₁ : k < n) :
    n % k ≠ 0 := by
  intro hk₂
  obtain ⟨d, rfl⟩ := Nat.dvd_of_mod_eq_zero hk₂
  rw [Nat.lt_mul_iff] at hk₁
  refine h d ?_ ?_ (by simp)
  · omega
  · refine Nat.mul_le_mul_right _ (Nat.le_of_lt ?_)
    exact Nat.lt_of_mul_lt_mul_left hk

theorem largestDivisorSpec.out {n i : Nat} (hn : 1 < n) :
    LargestDivisorSpec n i → i < n ∧ n % i = 0 ∧ ∀ j, j < n → n % j = 0 → j ≤ i := by
  rintro (h|h)
  · refine ⟨hn, Nat.mod_one _, fun j hj hj₁ => Nat.not_lt.1 (fun hj₂ => ?_)⟩
    by_cases hj₃ : j * j ≤ n
    · exact h j (by omega) hj₃ hj₁
    · exact mod_ne_zero_of_forall_of_lt_mul_self hn h j (by omega) hj hj₁
  · rename_i i hi hi'
    refine ⟨?_, ?_, fun j hj hj₁ => ?_⟩
    · apply Nat.div_lt_self <;> omega
    · exact Nat.mod_eq_zero_of_dvd (Nat.div_dvd_of_dvd (Nat.dvd_of_mod_eq_zero hi'))
    · exact Nat.not_lt.1 (fun hj₂ => mod_ne_zero_of_forall_of_div_lt hn h hi' j hj₂ hj hj₁)

theorem largestDivisor_eq_iff {n i : Nat} (hn : 1 < n) :
    largestDivisor n = i ↔ i < n ∧ n % i = 0 ∧ ∀ j, j < n → n % j = 0 → j ≤ i := by
  have h := largestDivisorSpec.out hn (by exact largestDivisorSpec_largestDivisor)
  exact ⟨fun h' => h' ▸ h, fun hi => Nat.le_antisymm (hi.2.2 _ h.1 h.2.1) (h.2.2 _ hi.1 hi.2.1)⟩

/-!
## Prompt

```python3


def largest_divisor(n: int) -> int:
    """ For a given number n, find the largest number that divides n evenly, smaller than n
    >>> largest_divisor(15)
    5
    """
```

## Canonical solution

```python3
    for i in reversed(range(n)):
        if n % i == 0:
            return i
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate(3) == 1
    assert candidate(7) == 1
    assert candidate(10) == 5
    assert candidate(100) == 50
    assert candidate(49) == 7
```
-/
