import Std.Data.HashSet.Lemmas
import Std.Tactic.Do

open Std Do

theorem List.exists_mem_iff_exists_getElem (P : α → Prop) (l : List α) :
    (∃ x ∈ l, P x) ↔ ∃ (i : Nat), ∃ hi, P (l[i]'hi) := by
  grind [mem_iff_getElem]

structure List.Any₂ (P : α → α → Prop) (l : List α) where
  not_pairwise : ¬ l.Pairwise (fun x y => ¬P x y)

theorem List.any₂_iff_not_pairwise {P : α → α → Prop} {l : List α} :
    l.Any₂ P ↔ ¬l.Pairwise (fun x y => ¬P x y) := by
  grind [List.Any₂]

@[simp, grind]
theorem not_any₂_nil {P : α → α → Prop} : ¬List.Any₂ P [] := by
  simp [List.any₂_iff_not_pairwise]

@[simp, grind]
theorem List.any₂_cons {P : α → α → Prop} {x : α} {xs : List α} :
    List.Any₂ P (x::xs) ↔ (∃ y ∈ xs, P x y) ∨ List.Any₂ P xs := by
  grind [List.any₂_iff_not_pairwise]

@[grind]
theorem List.any₂_append {P : α → α → Prop} {xs ys : List α} :
    List.Any₂ P (xs ++ ys) ↔ List.Any₂ P xs ∨ List.Any₂ P ys ∨ (∃ x ∈ xs, ∃ y ∈ ys, P x y) := by
  grind [List.any₂_iff_not_pairwise]

def pairsSumToZero (l : List Int) : Bool :=
  go l ∅
where
  go (m : List Int) (seen : HashSet Int) : Bool :=
    match m with
    | [] => false
    | x::xs => if -x ∈ seen then true else go xs (seen.insert x)

example : pairsSumToZero [1, 3, 5, 0] = false := by native_decide
example : pairsSumToZero [1, 3, -2, 1] = false := by native_decide
example : pairsSumToZero [1, 2, 3, 7] = false := by native_decide
example : pairsSumToZero [2, 4, -5, 3, 5, 7] = true := by native_decide
example : pairsSumToZero [1] = false := by native_decide

-- `simp` does not solve this!!
example {x : Int} : -x + x = 0 := by omega

theorem pairsSumToZero_go_iff (l : List Int) (seen : HashSet Int) :
    pairsSumToZero.go l seen = true ↔
      l.Any₂ (fun a b => a + b = 0) ∨ ∃ a ∈ seen, ∃ b ∈ l, a + b = 0 := by
  fun_induction pairsSumToZero.go <;> simp <;> grind

theorem pairsSumToZero_iff (l : List Int) :
    pairsSumToZero l = true ↔ l.Any₂ (fun a b => a + b = 0) := by
  simp [pairsSumToZero, pairsSumToZero_go_iff]

def pairsSumToZero' (l : List Int) : Id Bool := do
  let mut seen : HashSet Int := ∅
  for x in l do
    if -x ∈ seen then
      return true
    seen := seen.insert x
  return false

-- Pain: I have no idea what the system wants from me when building an invariant.
-- What is a PostCond? What does the function I'm returning mean? How are early returns
-- and things like that represented?

-- Pain: The need to have the `l = z.pref` trick in the loop invariant. If you don't know this
-- it's hard to make progress. It would be really cool if there was some kind of "interactive"
-- way to build the loop invariant in multiple steps where I only have to input the
-- `(∀ x, x ∈ s ↔ x ∈ z.rpref) ∧ ¬ z.pref.Any₂ (fun a b => a + b = 0)` and
-- `l.Any₂ (fun a b => a + b = 0)` parts and the `o = none/some` and `l = z.pref` gadgets are
-- added automatically.

-- Pain: `refine` does not play well with `⇓` it seems

-- Pain: mvcgen generated multiple assumptions named `h`, leading to inaccessible names
-- Pain: mvcgen generally creates inaccessible names

@[simp]
theorem List.Zipper.pref_mk {l : List α} {rpref suff h} :
    (List.Zipper.mk rpref suff h : List.Zipper l).pref = rpref.reverse := rfl

set_option mvcgen.warning false

theorem pairsSumToZero'_spec (l : List Int) :
    ⦃⌜True⌝⦄ pairsSumToZero' l ⦃⇓r => r = true ↔ l.Any₂ (fun a b => a + b = 0)⦄ := by
  mvcgen [pairsSumToZero']

  case inv =>
    exact (fun (⟨o, s⟩, z) =>
      (o = none ∧ (∀ x, x ∈ s ↔ x ∈ z.rpref) ∧ ¬ z.pref.Any₂ (fun a b => a + b = 0)) ∨
      (o = some true ∧ l.Any₂ (fun a b => a + b = 0) ∧ l = z.pref), ())

  all_goals simp_all [List.any₂_append] <;> grind

/-!
## Prompt

```python3


def pairs_sum_to_zero(l):
    """
    pairs_sum_to_zero takes a list of integers as an input.
    it returns True if there are two distinct elements in the list that
    sum to zero, and False otherwise.
    >>> pairs_sum_to_zero([1, 3, 5, 0])
    False
    >>> pairs_sum_to_zero([1, 3, -2, 1])
    False
    >>> pairs_sum_to_zero([1, 2, 3, 7])
    False
    >>> pairs_sum_to_zero([2, 4, -5, 3, 5, 7])
    True
    >>> pairs_sum_to_zero([1])
    False
    """
```

## Canonical solution

```python3
    for i, l1 in enumerate(l):
        for j in range(i + 1, len(l)):
            if l1 + l[j] == 0:
                return True
    return False
```

## Tests

```python3


METADATA = {}


def check(candidate):
    assert candidate([1, 3, 5, 0]) == False
    assert candidate([1, 3, -2, 1]) == False
    assert candidate([1, 2, 3, 7]) == False
    assert candidate([2, 4, -5, 3, 5, 7]) == True
    assert candidate([1]) == False

    assert candidate([-3, 9, -1, 3, 2, 30]) == True
    assert candidate([-3, 9, -1, 3, 2, 31]) == True
    assert candidate([-3, 9, -1, 4, 2, 30]) == False
    assert candidate([-3, 9, -1, 4, 2, 31]) == False

```
-/

/-! Bonus material -/

theorem List.exists_append (l : List α) (n : Nat) (h : n ≤ l.length) : ∃ xs ys, ys.length = n ∧ l = xs ++ ys :=
  ⟨l.take (l.length - n), l.drop (l.length - n), by grind, by simp⟩

@[simp]
theorem Std.HashSet.toList_emptyWithCapacity {α : Type u} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] {n : Nat} :
    (HashSet.emptyWithCapacity n : HashSet α).toList = [] := by
  simp [← List.isEmpty_iff]

@[simp]
theorem Std.HashSet.toList_empty {α : Type u} [BEq α] [Hashable α]
    [EquivBEq α] [LawfulHashable α] : (∅ : HashSet α).toList = [] := by
  simp [← List.isEmpty_iff]

theorem List.Any₂.append_left {P : α → α → Prop} (xs : List α) {ys : List α} (h : ys.Any₂ P) : (xs ++ ys).Any₂ P :=
  List.any₂_append.2 (by simp [h])

theorem List.Any₂.append_right {P : α → α → Prop} {xs : List α} (ys : List α) (h : xs.Any₂ P) : (xs ++ ys).Any₂ P :=
  List.any₂_append.2 (by simp [h])

theorem List.any₂_append_left_right {P : α → α → Prop} (xs ys : List α) (h : ∃ x ∈ xs, ∃ y ∈ ys, P x y) :
    (xs ++ ys).Any₂ P :=
  List.any₂_append.2 (by simp [h])

theorem List.any₂_iff_exists (P : α → α → Prop) (l : List α) :
    List.Any₂ P l ↔ ∃ xs x ys, l = xs ++ x :: ys ∧ ∃ y ∈ ys, P x y := by
  constructor
  · rintro ⟨h⟩
    induction l with
    | nil => grind
    | cons x xs ih =>
      rw [List.pairwise_cons, Classical.not_and_iff_not_or_not] at h
      simp only [Classical.not_forall, Classical.not_not] at h
      rcases h with (⟨y, hy, hxy⟩|h)
      · exact ⟨[], by grind⟩
      · grind
  · grind

theorem List.any₂_iff_exists_getElem (P : α → α → Prop) (l : List α) :
    List.Any₂ P l ↔ ∃ (i j : Nat), ∃ hi hj, i < j ∧ P (l[i]'hi) (l[j]'hj) := by
  rw [List.any₂_iff_exists]
  constructor
  · rintro ⟨xs, x, ys, ⟨rfl, h⟩⟩
    obtain ⟨j₀, hj₀, hj₀'⟩ := (List.exists_mem_iff_exists_getElem _ _).1 h
    exact ⟨xs.length, xs.length + 1 + j₀, by grind⟩
  · rintro ⟨i, j, hi, hj, hij, h⟩
    exact ⟨l.take i, l[i], l.drop (i + 1), by simp,
      (List.exists_mem_iff_exists_getElem _ _).2 ⟨j - i - 1, by grind, by grind⟩⟩

@[simp, grind]
theorem List.any₂_append_singleton {P : α → α → Prop} {xs : List α} {x : α} :
    List.Any₂ P (xs ++ [x]) ↔ List.Any₂ P xs ∨ ∃ y ∈ xs, P y x := by
  grind [List.any₂_iff_not_pairwise]

@[simp, grind]
theorem not_any₂_singleton {P : α → α → Prop} {x : α} : ¬List.Any₂ P [x] := by
  simp [List.any₂_iff_not_pairwise]
