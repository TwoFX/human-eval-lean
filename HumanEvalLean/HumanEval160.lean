inductive Op where
  | add
  | sub
  | mul
  | div
  | pow

namespace Op

instance : ToString Op where
  toString
    | add => "+"
    | sub => "-"
    | mul => "*"
    | div => "/"
    | pow => "^"

def prio : Op → Nat
  | add | sub => 1
  | mul | div => 2
  | pow       => 3

def leftAssoc : Op → Bool
  | add | sub => true
  | mul | div => true
  | pow       => false

def interpret : Op → (Nat → Nat → Nat)
  | add => (· + ·)
  | sub => (· - ·)
  | mul => (· * ·)
  | div => (· / ·)
  | pow => (· ^ ·)

end Op

inductive Expr where
  | lit (n : Nat)
  | app (op : Op) (arg₁ arg₂ : Expr)
  deriving Inhabited

namespace Expr

instance : ToString Expr where
  toString :=
    let rec go
      | .lit n            => s!"{n}"
      | .app op arg₁ arg₂ => s!"({go arg₁} {op} {go arg₂})"
    go

def eval : Expr → Nat
  | lit n            => n
  | app op arg₁ arg₂ => op.interpret arg₁.eval arg₂.eval

def lits : Expr → List Nat
  | lit n           => [n]
  | app _ arg₁ arg₂ => arg₁.lits ++ arg₂.lits

def apps : Expr → List Op
  | lit _            => []
  | app op arg₁ arg₂ => arg₁.apps ++ op :: arg₂.apps

structure ParseState where
  ops    : List Op   := []
  args   : List Nat  := []
  hold   : List Op   := []
  output : List Expr := []
  deriving Inhabited

namespace ParseState

def pushArg (σ : ParseState) (arg : Nat) : ParseState :=
  { σ with output := (lit arg) :: σ.output }

@[simp]
theorem pushArg_ops (σ : ParseState) : (σ.pushArg arg).ops = σ.ops := rfl

def pushOp? (σ : ParseState) (op : Op) : Option ParseState :=
  match σ.hold with
  | [] => some { σ with hold := [op] }
  | top :: hold =>
    match compare top.prio op.prio, top.leftAssoc with
    | .lt, _ | .eq, false => some { σ with hold := op :: top :: hold }
    | .gt, _ | .eq, true =>
      match σ.output with
      | arg₂ :: arg₁ :: out => some { σ with hold := op :: hold, output := .app top arg₁ arg₂ :: out }
      | _                   => none

@[simp]
theorem pushOp?_ops {σ : ParseState} (h : σ.pushOp? op = some σ') : σ'.ops = σ.ops := by
  rw [pushOp?] at h
  repeat' split at h
  all_goals
    first
    | injection h with h; rw [←h]
    | contradiction

def finalize (σ : ParseState) : ParseState :=
  match _ : σ.hold, σ.output with
  | op :: hold, arg₂ :: arg₁ :: out => finalize { σ with hold, output := .app op arg₁ arg₂ :: out }
  | _, _                            => σ
  termination_by σ.hold
  decreasing_by simp_all +arith

end ParseState

-- Parses an expression based on the "shunting yard algorithm".
def parse? (ops : List Op) (args : List Nat) : Option Expr :=
  go { ops, args } >>= (·.output[0]?)
where
  go (σ : ParseState) : Option ParseState :=
    match _ : σ.ops, σ.args with
    | op :: ops, arg :: args =>
      match _ : { σ with ops, args } |>.pushArg arg |>.pushOp? op with
      | none   => none
      | some σ => go σ
    | [], [arg] => { σ with args := [] } |>.pushArg arg |>.finalize
    | _, _  => none
  termination_by σ.ops
  decreasing_by simp_all +arith [ParseState.pushOp?_ops ‹_›]

theorem parse?.some_iff : (parse? ops args = some e) ↔ (args.length = ops.length + 1) := by
  sorry

theorem parse?.lits_eq_args (h : parse? ops args = some e) : e.lits = args := by
  sorry

theorem parse?.apps_eq_ops (h : parse? ops args = some e) : e.apps = ops := by
  sorry

end Expr

def doAlgebra (ops : List Op) (args : List Nat) : Option Nat :=
  Expr.eval <$> Expr.parse? ops args

example : doAlgebra [.add, .mul, .sub] [2, 3, 4, 5] = some 9  := by native_decide
example : doAlgebra [.pow, .mul, .add] [2, 3, 4, 5] = some 37 := by native_decide
example : doAlgebra [.add, .mul, .sub] [2, 3, 4, 5] = some 9  := by native_decide
example : doAlgebra [.div, .mul]       [7, 3, 4]    = some 8  := by native_decide

/-!
## Prompt

```python3

def do_algebra(operator, operand):
    """
    Given two lists operator, and operand. The first list has basic algebra operations, and
    the second list is a list of integers. Use the two given lists to build the algebric
    expression and return the evaluation of this expression.

    The basic algebra operations:
    Addition ( + )
    Subtraction ( - )
    Multiplication ( * )
    Floor division ( // )
    Exponentiation ( ** )

    Example:
    operator['+', '*', '-']
    array = [2, 3, 4, 5]
    result = 2 + 3 * 4 - 5
    => result = 9

    Note:
        The length of operator list is equal to the length of operand list minus one.
        Operand is a list of of non-negative integers.
        Operator list has at least one operator, and operand list has at least two operands.

    """
```

## Canonical solution

```python3
    expression = str(operand[0])
    for oprt, oprn in zip(operator, operand[1:]):
        expression+= oprt + str(oprn)
    return eval(expression)
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate(['**', '*', '+'], [2, 3, 4, 5]) == 37
    assert candidate(['+', '*', '-'], [2, 3, 4, 5]) == 9
    assert candidate(['//', '*'], [7, 3, 4]) == 8, "This prints if this assert fails 1 (good for debugging!)"

    # Check some edge cases that are easy to work out by hand.
    assert True, "This prints if this assert fails 2 (also good for debugging!)"

```
-/
