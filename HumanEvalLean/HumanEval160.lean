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

@[simp]
def pushArg (σ : ParseState) (arg : Nat) : ParseState :=
  { σ with output := (lit arg) :: σ.output }

def pushOp? (σ : ParseState) (op : Op) : Option ParseState :=
  match _ : σ.hold with
  | [] => some { σ with hold := [op] }
  | top :: hold =>
    match compare top.prio op.prio, top.leftAssoc with
    | .lt, _ | .eq, false => some { σ with hold := op :: top :: hold }
    | .gt, _ | .eq, true =>
      match σ.output with
      | arg₂ :: arg₁ :: out => pushOp? { σ with hold, output := app top arg₁ arg₂ :: out } op
      | _                   => none
termination_by σ.hold.length
decreasing_by all_goals simp +arith [*]

@[simp]
theorem pushOp?_ops {σ₁ : ParseState} (h : σ₁.pushOp? op = some σ₂) : σ₁.ops = σ₂.ops := by
  rw [pushOp?] at h
  repeat' split at h
  all_goals
    first
    | injection h with h; rw [←h]
    | rw [pushOp?_ops h]
    | contradiction
termination_by σ₁.hold
decreasing_by all_goals simp +arith [*]

theorem pushOp?_output_hold_length
    {σ₁ : ParseState} (hp : σ₁.pushOp? op = some σ₂) (hl : σ₁.hold.length < σ₁.output.length) :
    σ₂.output.length - σ₂.hold.length = σ₁.output.length - σ₁.hold.length - 1 := by
  rw [pushOp?] at hp
  repeat' split at hp <;> try contradiction
  all_goals
    first
      | injection hp with hp
      | have hp := pushOp?_output_hold_length hp
    simp_all only [List.length_cons, ←hp]
    omega
termination_by σ₁.hold
decreasing_by all_goals simp +arith [*]

theorem pushOp?_hold_length_le_output_length
    {σ₁ : ParseState} (hp : σ₁.pushOp? op = some σ₂) (hl : σ₁.hold.length < σ₁.output.length) :
    σ₂.hold.length ≤ σ₂.output.length := by
  rw [pushOp?] at hp
  repeat' split at hp
  all_goals
    first
      | contradiction
      | injection hp with hp; simp_all +arith [←hp]
      | exact pushOp?_hold_length_le_output_length hp (by simp_all)
termination_by σ₁.hold
decreasing_by all_goals simp +arith [*]

def push? (σ : ParseState) (arg : Nat) (op : Op) : Option ParseState :=
  σ.pushArg arg |>.pushOp? op

@[simp]
theorem push?_ops {σ₁ : ParseState} (h : σ₁.push? arg op = some σ₂) : σ₁.ops = σ₂.ops := by
  rw [push?, pushArg] at h
  have := pushOp?_ops h
  repeat simp_all only

theorem push?_output_hold_length
    {σ₁ : ParseState} (hp : σ₁.push? arg op = some σ₂) (hl : σ₁.hold.length ≤ σ₁.output.length) :
    σ₁.output.length - σ₁.hold.length = σ₂.output.length - σ₂.hold.length := by
  rw [push?, pushArg] at hp
  have hh : σ₁.hold.length < σ₁.output.length + 1 := by omega
  simp only [pushOp?_output_hold_length hp hh, List.length_cons]
  omega

theorem push?_output_length_eq_hold_length
    {σ₁ : ParseState} (hp : σ₁.push? arg op = some σ₂) (he : σ₁.hold.length = σ₁.output.length) :
    σ₂.output.length = σ₂.hold.length := by
  sorry -- TODO: Not sure if this is actually provable.

def finalize (σ : ParseState) : ParseState :=
  match _ : σ.hold, σ.output with
  | op :: hold, arg₂ :: arg₁ :: out => finalize { σ with hold, output := app op arg₁ arg₂ :: out }
  | _, _                            => σ
  termination_by σ.hold
  decreasing_by simp_all +arith

theorem finalize_output_length {σ : ParseState} (h : σ.hold.length < σ.output.length) :
    σ.finalize.output.length = σ.output.length - σ.hold.length := by
  replace ⟨ops, args, hold, output⟩ := σ
  induction hold generalizing output <;> cases output <;> rw [finalize]
  case cons.cons out => cases out <;> simp_all
  all_goals simp_all

def run? (σ : ParseState) : Option ParseState :=
  match _ : σ.ops, σ.args with
  | op :: ops, arg :: args =>
    match _ : { σ with ops, args }.push? arg op with
    | none   => none
    | some σ => run? σ
  | [], [arg] => { σ with args := [] } |>.pushArg arg |>.finalize
  | _, _  => none
termination_by σ.ops
decreasing_by have := push?_ops ‹_›; simp_all +arith

theorem run?_output_length
    {σ₁ : ParseState} (hr : σ₁.run? = some σ₂) (hl : σ₁.hold.length ≤ σ₁.output.length) :
    σ₂.output.length = σ₁.output.length + 1 - σ₁.hold.length := by
  rw [run?] at hr
  repeat' split at hr
  · contradiction
  next σ' h =>
    have : σ'.ops.length < σ₁.ops.length := by have := push?_ops h; simp_all
    have hl' := pushOp?_hold_length_le_output_length h <| by simp_all +arith
    have := push?_output_hold_length h hl
    simp only [run?_output_length hr hl', pushArg, List.length_cons] at *
    omega
  · injection hr with hr
    rw [←hr, finalize_output_length]
    repeat simp only [pushArg, List.length_cons]
    omega
  · contradiction
termination_by σ₁.ops.length

-- This implies that `parse?` either fails, or returns precisely a single output element.
theorem run?_output_singleton {ops args} (h : run? { ops, args } = some σ) : σ.output.length = 1 :=
  run?_output_length h .refl

end ParseState

-- Parses an expression based on the "shunting yard algorithm".
def parse? (ops : List Op) (args : List Nat) : Option Expr :=
  match h : { ops, args : ParseState }.run? with
  | none   => none
  | some σ => σ.output[0]'(by simp [ParseState.run?_output_singleton h])

theorem parse?_isSome_iff : (parse? ops args).isSome ↔ (args.length = ops.length + 1) where
  mp  := sorry
  mpr := sorry

theorem parse?_lits_eq_args (h : parse? ops args = some e) : e.lits = args := by
  sorry

theorem parse?_apps_eq_ops (h : parse? ops args = some e) : e.apps = ops := by
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
