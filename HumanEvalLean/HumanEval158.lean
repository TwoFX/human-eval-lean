import Lean
open Std

def String.numUniqueChars (str : String) : Nat :=
  str.foldl (·.insert) (∅ : HashSet _) |>.size

def findMax (strs : List String) : Option String :=
  strs.foldl (max? · ·) none
where
  max? : Option String → String → String
  | none,      str  => str
  | some str₁, str₂ => max str₁ str₂
  max (str₁ str₂ : String) : String :=
    match compare str₁.numUniqueChars str₂.numUniqueChars with
    | .gt => str₁
    | .lt => str₂
    | .eq => if str₁ < str₂ then str₁ else str₂

example : findMax ["name", "of", "string"] = "string"                    := by native_decide
example : findMax ["name", "enam", "game"] = "enam"                      := by native_decide
example : findMax ["aaaaaaa", "bb" ,"cc"] = "aaaaaaa"                    := by native_decide
example : findMax ["name", "of", "string"] = "string"                    := by native_decide
example : findMax ["name", "enam", "game"] = "enam"                      := by native_decide
example : findMax ["aaaaaaa", "bb", "cc"] = "aaaaaaa"                    := by native_decide
example : findMax ["abc", "cba"] = "abc"                                 := by native_decide
example : findMax ["play", "this", "game", "of","footbott"] = "footbott" := by native_decide
example : findMax ["we", "are", "gonna", "rock"] = "gonna"               := by native_decide
example : findMax ["we", "are", "a", "mad", "nation"] = "nation"         := by native_decide
example : findMax ["this", "is", "a", "prrk"] = "this"                   := by native_decide
example : findMax ["b"] = "b"                                            := by native_decide
example : findMax ["play", "play", "play"] = "play"                      := by native_decide

theorem findMax_mem (h : findMax strs = some m) : m ∈ strs := by
  induction strs generalizing m <;> rw [findMax] at h
  case nil => contradiction
  case cons ih =>
    simp [findMax.max?] at h
    sorry -- Problem: We can't use IH again, cause we haven't generalized over the fold's init.
          -- Can we use `List.foldl_hom`?

theorem findMax_cons : findMax (hd :: tl) = findMax.max? (findMax tl) hd := by
  sorry

-- TODO: Does this actually hold? If not, use some sort of lex compare function instead of `<`.
theorem String.le_of_lt {s₁ s₂ : String} (h : s₁ < s₂) : s₁ ≤ s₂ :=
  sorry

structure UniqueMax (max : String) (strs : List String) : Prop where
  mem        : max ∈ strs
  max_unique : ∀ str ∈ strs, str.numUniqueChars ≤ max.numUniqueChars
  min_lex    : ∀ str ∈ strs, str.numUniqueChars = max.numUniqueChars → max ≤ str

namespace UniqueMax

theorem tail (h : UniqueMax m (hd :: tl)) (hm : m ∈ tl) : UniqueMax m tl where
  mem             := hm
  max_unique _ hm := h.max_unique _ (.tail _ hm)
  min_lex _ hm    := h.min_lex _ (.tail _ hm)

theorem to_findMax_max (h : UniqueMax m strs) (hm : str ∈ strs) : findMax.max m str = m := by
  rw [findMax.max]
  split <;> (try split) <;> try rfl
  next hc =>
    rw [Nat.compare_eq_lt] at hc
    have := h.max_unique _ hm
    omega
  next hc hl =>
    rw [Nat.compare_eq_eq] at hc
    have := h.min_lex _ hm hc.symm
    exact String.le_antisymm hl this

theorem to_findMax (h : UniqueMax m strs) : findMax strs = m := by
  induction strs <;> cases h.mem
  case cons.tail ih hm => simp [findMax_cons, ih (h.tail hm), findMax.max?, h.to_findMax_max]
  case cons.head tl ih =>
    simp only [findMax_cons, findMax.max?, findMax.max]
    split <;> (try split) <;> (try split) <;> try rfl
    next hf _ hc =>
      rw [Nat.compare_eq_gt] at hc
      have := h.max_unique _ (.tail _ <| findMax_mem hf)
      omega
    next hf _ hc hl =>
      rw [Nat.compare_eq_eq] at hc
      have := h.min_lex _ (.tail _ <| findMax_mem hf) hc
      simp [String.le_antisymm (String.le_of_lt hl) this]

theorem of_findMax (h : findMax strs = some m) : UniqueMax m strs where
  mem := findMax_mem h
  max_unique str hm := by
    induction strs
    case nil     => sorry
    case cons ih => sorry -- Same problem in IH as with `findMax_mem` above.
  min_lex := sorry -- Probably by induction with the same problem as commented on above.

theorem iff_findMax : (UniqueMax m strs) ↔ (findMax strs = m) where
  mp  := to_findMax
  mpr := of_findMax

end UniqueMax

/-!
## Prompt

```python3

def find_max(words):
    """Write a function that accepts a list of strings.
    The list contains different words. Return the word with maximum number
    of unique characters. If multiple strings have maximum number of unique
    characters, return the one which comes first in lexicographical order.

    find_max(["name", "of", "string"]) == "string"
    find_max(["name", "enam", "game"]) == "enam"
    find_max(["aaaaaaa", "bb" ,"cc"]) == ""aaaaaaa"
    """
```

## Canonical solution

```python3
    return sorted(words, key = lambda x: (-len(set(x)), x))[0]
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert (candidate(["name", "of", "string"]) == "string"), "t1"
    assert (candidate(["name", "enam", "game"]) == "enam"), 't2'
    assert (candidate(["aaaaaaa", "bb", "cc"]) == "aaaaaaa"), 't3'
    assert (candidate(["abc", "cba"]) == "abc"), 't4'
    assert (candidate(["play", "this", "game", "of","footbott"]) == "footbott"), 't5'
    assert (candidate(["we", "are", "gonna", "rock"]) == "gonna"), 't6'
    assert (candidate(["we", "are", "a", "mad", "nation"]) == "nation"), 't7'
    assert (candidate(["this", "is", "a", "prrk"]) == "this"), 't8'

    # Check some edge cases that are easy to work out by hand.
    assert (candidate(["b"]) == "b"), 't9'
    assert (candidate(["play", "play", "play"]) == "play"), 't10'

```
-/
