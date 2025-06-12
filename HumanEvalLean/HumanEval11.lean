import Std.Data.Iterators

def stringXor (a b : List Bool) : List Bool :=
  ((a.iter).zip b.iter)
    |>.map (fun p => Bool.xor p.1 p.2)
    |>.toList

@[simp, grind]
theorem length_stringXor {a b : List Bool} : (stringXor a b).length = min a.length b.length := by
  simp [stringXor]

theorem getElem_stringXor {a b : List Bool} {i : Nat} {hia : i < a.length} {hib : i < b.length} :
    (stringXor a b)[i]'(by grind) = Bool.xor a[i] b[i] := by
  simp [stringXor]

/-!
## Prompt

```python3
from typing import List


def string_xor(a: str, b: str) -> str:
    """ Input are two strings a and b consisting only of 1s and 0s.
    Perform binary XOR on these inputs and return result also as a string.
    >>> string_xor('010', '110')
    '100'
    """
```

## Canonical solution

```python3
    def xor(i, j):
        if i == j:
            return '0'
        else:
            return '1'

    return ''.join(xor(x, y) for x, y in zip(a, b))
```

## Tests

```python3


METADATA = {
    'author': 'jt',
    'dataset': 'test'
}


def check(candidate):
    assert candidate('111000', '101010') == '010010'
    assert candidate('1', '1') == '0'
    assert candidate('0101', '0000') == '0101'
```
-/
