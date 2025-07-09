import Std.Tactic.Do

def belowZero (l : List Int) : Bool :=
  go 0 l
where
  go (cur : Int) (remaining : List Int) : Bool :=
    if cur < 0 then
      true
    else
      match remaining with
      | [] => false
      | l::rem => go (cur + l) rem

theorem belowZero_iff {l : List Int} : belowZero l ↔ ∃ n, (l.take n).sum < 0 := by
  suffices ∀ c, belowZero.go c l ↔ ∃ n, c + (l.take n).sum < 0 by simpa using this 0
  intro c
  induction l generalizing c with
  | nil => simp [belowZero.go]
  | cons h t ih =>
    simp only [belowZero.go, Bool.if_true_left, Bool.or_eq_true, decide_eq_true_eq, ih]
    refine ⟨?_, ?_⟩
    · rintro (hc|⟨n, hn⟩)
      · exact ⟨0, by simpa⟩
      · exact ⟨n + 1, by simpa [← Int.add_assoc]⟩
    · rintro ⟨n, hn⟩
      rcases n with (_|n)
      · exact Or.inl (by simpa using hn)
      · exact Or.inr ⟨n, by simpa [Int.add_assoc] using hn⟩

def doBelowZero (operations : List Int) : Bool := Id.run do
  let mut balance := 0
  for op in operations do
    balance := balance + op
    if balance < 0 then
      return true
  return false

open Std.Do
set_option mvcgen.warning false

attribute [simp] Std.List.Zipper.pref

@[grind]
theorem List.sum_append_singleton {x : Int} {l : List Int} : (l ++ [x]).sum = l.sum + x := by
  simp [List.sum, ← List.foldr_assoc]

attribute [grind =] List.take_append List.take_left' List.take_length List.take_of_length_le

abbrev InvWithEarlyReturn
  (onContinue : PostCond (β × Std.List.Zipper l) ps)
  (onReturn : ρ → β → Assertion ps) :
    PostCond (MProd (Option ρ) β × Std.List.Zipper l) ps :=
  ⟨fun (⟨x, b⟩, xs) => spred(
        (⌜x = none⌝ ∧ onContinue.1 ⟨b, xs⟩)
      ∨ (∃ r, ⌜x = some r⌝ ∧ ⌜l = xs.pref⌝ ∧ onReturn r b)),
   onContinue.2⟩

theorem doBelowZero_iff {l : List Int} : doBelowZero l ↔ ∃ n, (l.take n).sum < 0 := by
  generalize h : doBelowZero l = res
  apply Id.by_wp h
  mvcgen
--  case inv => exact ⇓ (⟨r, bal⟩, xs) =>
--      (r = none ∧ bal = xs.pref.sum ∧ ∀ n, (xs.pref.take n).sum ≥ 0)
--    ∨ (r = some true ∧ l = xs.pref ∧ ∃ n, (l.take n).sum < 0)
  case inv =>
    exact InvWithEarlyReturn
      (⇓ (bal, xs) => bal = xs.pref.sum ∧ ∀ n, (xs.pref.take n).sum ≥ 0)
      (fun r bal => r = true ∧ ∃ n, (l.take n).sum < 0)
  all_goals simp_all
  all_goals try grind
  · exists rpref.reverse.length + 1
    simp_all only [List.sum, List.take_length_add_append, List.take_succ_cons, List.take_zero, List.foldr_append,
      List.foldr_cons, List.foldr_nil, Int.add_zero, ← List.foldr_assoc (α:=Int) (op:=(·+·)), Int.zero_add]
  · refine ⟨by grind, ?_⟩
    intro n
    have := h.2.2 n
    by_cases rpref.reverse.length + 1 ≤ n
    · grind
    · have : n - rpref.length = 0 := by grind
      grind

/-!
## Prompt

```python3
from typing import List


def below_zero(operations: List[int]) -> bool:
    """ You're given a list of deposit and withdrawal operations on a bank account that starts with
    zero balance. Your task is to detect if at any point the balance of account fallls below zero, and
    at that point function should return True. Otherwise it should return False.
    >>> below_zero([1, 2, 3])
    False
    >>> below_zero([1, 2, -4, 5])
    True
    """
```

## Canonical solution

```python3
    balance = 0

    for op in operations:
        balance += op
        if balance < 0:
            return True

    return False
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate([]) == False
    assert candidate([1, 2, -3, 1, 2, -3]) == False
    assert candidate([1, 2, -4, 5, 6]) == True
    assert candidate([1, -1, 2, -2, 5, -5, 4, -4]) == False
    assert candidate([1, -1, 2, -2, 5, -5, 4, -5]) == True
    assert candidate([1, -2, 2, -2, 5, -5, 4, -4]) == True
```
-/
