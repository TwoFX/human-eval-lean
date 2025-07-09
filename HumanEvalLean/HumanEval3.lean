import Std.Tactic.Do

namespace List

structure HasPrefix (P : List α → Prop) (l : List α) : Prop where
  exists_take : ∃ n, P (l.take n)

theorem hasPrefix_iff {P : List α → Prop} {l : List α} :
    l.HasPrefix P ↔ ∃ n, P (l.take n) := by
  grind [HasPrefix]

@[simp, grind]
theorem hasPrefix_nil {P : List α → Prop} : [].HasPrefix P ↔ P [] := by
  simp [hasPrefix_iff]

@[simp, grind]
theorem hasPrefix_of_nil {P : List α → Prop} {l : List α} (h : P []) : l.HasPrefix P :=
  ⟨⟨0, by simpa⟩⟩

@[simp, grind]
theorem hasPrefix_of_all {P : List α → Prop} {l : List α} (h : P l) : l.HasPrefix P :=
  ⟨⟨l.length, by simpa⟩⟩

@[grind]
theorem hasPrefix_cons {P : List α → Prop} {a : α} {l : List α} :
    (a :: l).HasPrefix P ↔ P [] ∨ l.HasPrefix (fun l' => P (a :: l')) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨n, hn⟩⟩
    refine (Nat.eq_zero_or_pos n).elim (by rintro rfl; simp_all) (fun hnp => Or.inr ⟨⟨n - 1, ?_⟩⟩)
    rwa [take_cons hnp] at hn
  · rintro (h|⟨⟨n, hn⟩⟩)
    · exact hasPrefix_of_nil h
    · exact ⟨n + 1, by simpa⟩

@[grind]
theorem hasPrefix_append {P : List α → Prop} {l l' : List α} :
    (l ++ l').HasPrefix P ↔ l.HasPrefix P ∨ l'.HasPrefix (fun l'' => P (l ++ l'')) := by
  induction l generalizing P with grind

end List

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
  rw [← List.hasPrefix_iff (P := fun l => c + l.sum < 0)]
  fun_induction belowZero.go with grind

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

@[simp, grind]
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
  rw [← List.hasPrefix_iff (P := fun l => l.sum < 0)]

  generalize h : doBelowZero l = res
  apply Id.by_wp h
  mvcgen
--  case inv => exact ⇓ (⟨r, bal⟩, xs) =>
--      (r = none ∧ bal = xs.pref.sum ∧ ∀ n, (xs.pref.take n).sum ≥ 0)
--    ∨ (r = some true ∧ l = xs.pref ∧ ∃ n, (l.take n).sum < 0)
  case inv =>
    exact InvWithEarlyReturn
      (⇓ (bal, xs) => bal = xs.pref.sum ∧ ¬ xs.pref.HasPrefix (fun l => l.sum < 0))
      (fun r bal => r = true ∧ l.HasPrefix (fun l => l.sum < 0))

  all_goals simp_all [List.hasPrefix_cons, List.hasPrefix_append]
  all_goals try grind

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
