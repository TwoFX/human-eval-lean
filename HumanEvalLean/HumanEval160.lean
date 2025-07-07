theorem List.length_one_eq_getElem_zero {l : List α} (h : l.length = 1) : l = [l[0]] := by
  cases l <;> try cases ‹List _›
  all_goals simp at h ⊢

inductive Op where
  | add
  | sub
  | mul
  | div
  | pow

namespace Op

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

namespace Expr

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

namespace ParseState

def lits (σ : ParseState) : List Nat :=
  go σ.output
where
  go : List Expr → List Nat
  | []       => []
  | e :: out => go out ++ e.lits

theorem output_eq_lits_eq {σ₁ σ₂ : ParseState} (h : σ₁.output = σ₂.output) : σ₁.lits = σ₂.lits := by
  simp only [lits, h]

macro_rules
  | `(tactic| decreasing_tactic) => `(tactic| simp +arith [*])

structure Wellformed (σ : ParseState) where
  external : σ.args.length = σ.ops.length + 1
  internal : σ.hold.length = σ.output.length

theorem Wellformed.of_external_cons
    (wf : Wellformed σ) (ho : σ.ops = op :: os) (ha : σ.args = arg :: as) :
    Wellformed { σ with ops := os, args := as } where
  external := have ⟨_, _⟩ := wf; by simp_all
  internal := wf.internal

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

macro "pushOp?_cases " h:ident : tactic => `(tactic|(
  rw [pushOp?] at $h:ident
  repeat' split at $h:ident
  all_goals try contradiction
  all_goals try injection $h with $h
  all_goals try rw [← $h]
))

theorem pushOp?_args {σ₁ : ParseState} (h : σ₁.pushOp? op = some σ₂) : σ₁.args = σ₂.args := by
  pushOp?_cases h <;> rw [pushOp?_args h]
termination_by σ₁.hold

theorem pushOp?_ops {σ₁ : ParseState} (h : σ₁.pushOp? op = some σ₂) : σ₁.ops = σ₂.ops := by
  pushOp?_cases h <;> rw [pushOp?_ops h]
termination_by σ₁.hold

theorem pushOp?_lits {σ₁ : ParseState} (h : σ₁.pushOp? op = some σ₂) : σ₁.lits = σ₂.lits := by
  pushOp?_cases h
  all_goals
    first
    | have : σ₁.lits = σ₂.lits := output_eq_lits_eq (h ▸ rfl); simp_all only
    | rw [← pushOp?_lits h]; simp_all [Expr.lits, lits, lits.go]
termination_by σ₁.hold

theorem pushOp?_output_hold_length
    {σ₁ : ParseState} (hp : σ₁.pushOp? op = some σ₂) (hl : σ₁.hold.length < σ₁.output.length) :
    σ₂.output.length - σ₂.hold.length = σ₁.output.length - σ₁.hold.length - 1 := by
  pushOp?_cases hp
  all_goals
    try have hp := pushOp?_output_hold_length hp
    simp_all only [List.length_cons, ← hp]
    omega
termination_by σ₁.hold

theorem pushOp?_hold_length_le_output_length
    {σ₁ : ParseState} (hp : σ₁.pushOp? op = some σ₂) (hl : σ₁.hold.length < σ₁.output.length) :
    σ₂.hold.length ≤ σ₂.output.length := by
  pushOp?_cases hp
  all_goals
    first
      | exact pushOp?_hold_length_le_output_length hp (by simp_all)
      | simp_all +arith [← hp]
termination_by σ₁.hold

theorem pushOp?_some {σ₁ : ParseState} (h : σ₁.hold.length < σ₁.output.length) :
    ∃ σ₂, σ₁.pushOp? op = some σ₂ := by
  rw [pushOp?]
  repeat' split
  all_goals try apply pushOp?_some
  all_goals try cases _ : σ₁.output <;> cases ‹List Expr›
  all_goals simp_all
termination_by σ₁.hold

def push? (σ : ParseState) (arg : Nat) (op : Op) : Option ParseState :=
  σ.pushArg arg |>.pushOp? op

theorem push?_args {σ₁ : ParseState} (h : σ₁.push? arg op = some σ₂) : σ₁.args = σ₂.args := by
  rw [push?, pushArg] at h
  have := pushOp?_args h
  repeat simp_all only

theorem push?_ops {σ₁ : ParseState} (h : σ₁.push? arg op = some σ₂) : σ₁.ops = σ₂.ops := by
  rw [push?, pushArg] at h
  have := pushOp?_ops h
  repeat simp_all only

macro_rules
  | `(tactic| decreasing_tactic) => `(tactic| have := push?_ops ‹_›; simp_all +arith)

theorem push?_lits {σ₁ : ParseState} (h : σ₁.push? arg op = some σ₂) : σ₂.lits = σ₁.lits ++ [arg] :=
  pushOp?_lits h |>.symm

theorem push?_output_hold_length
    {σ₁ : ParseState} (hp : σ₁.push? arg op = some σ₂) (hl : σ₁.hold.length ≤ σ₁.output.length) :
    σ₁.output.length - σ₁.hold.length = σ₂.output.length - σ₂.hold.length := by
  rw [push?, pushArg] at hp
  have hh : σ₁.hold.length < σ₁.output.length + 1 := by omega
  simp only [pushOp?_output_hold_length hp hh, List.length_cons]
  omega

theorem push?_output_length_eq_hold_length
    {σ₁ : ParseState} (hp : σ₁.push? arg op = some σ₂) (he : σ₁.hold.length = σ₁.output.length) :
    σ₂.hold.length = σ₂.output.length := by
  simp only [push?, pushArg] at hp
  have := push?_output_hold_length hp (Nat.le_of_eq he)
  have := pushOp?_hold_length_le_output_length hp (by simp_all)
  omega

theorem push?_wf (wf : Wellformed σ₁) (arg op) : ∃ σ₂, σ₁.push? arg op = some σ₂ :=
  pushOp?_some <| by simp [wf.internal]

theorem Wellformed.push? (hp : σ₁.push? arg op = some σ₂) (wf : Wellformed σ₁) : Wellformed σ₂ where
  external := push?_args hp ▸ push?_ops hp ▸ wf.external
  internal := push?_output_length_eq_hold_length hp wf.internal

def finalize (σ : ParseState) : ParseState :=
  match _ : σ.hold, σ.output with
  | op :: hold, arg₂ :: arg₁ :: out => finalize { σ with hold, output := app op arg₁ arg₂ :: out }
  | _, _                            => σ
termination_by σ.hold

@[simp]
theorem finalize_lits (σ : ParseState) : σ.finalize.lits = σ.lits := by
  rw [finalize]
  split
  · rw [finalize_lits]
    simp_all [Expr.lits, lits, lits.go]
  · rfl
termination_by σ.hold

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

macro "run?_cases " h:ident : tactic => `(tactic|(
  rw [run?] at $h:ident
  repeat' split at $h:ident
  all_goals try contradiction
))

theorem run?_lits {σ₁ : ParseState} (hr : σ₁.run? = some σ₂) : σ₂.lits = σ₁.lits ++ σ₁.args := by
  run?_cases hr
  next h =>
    rw [run?_lits hr]
    have := push?_lits h
    have := push?_args h
    simp_all [lits]
  · injection hr with hr
    rw [← hr, finalize_lits]
    simp_all [Expr.lits, lits, lits.go]
termination_by σ₁.ops.length

theorem run?_output_length
    {σ₁ : ParseState} (hr : σ₁.run? = some σ₂) (hl : σ₁.hold.length ≤ σ₁.output.length) :
    σ₂.output.length = σ₁.output.length + 1 - σ₁.hold.length := by
  run?_cases hr
  next ops₁ _ _ _ _  σ' h =>
    have hl' := pushOp?_hold_length_le_output_length h <| by simp_all +arith
    have := push?_output_hold_length h hl
    simp only [run?_output_length hr hl', pushArg, List.length_cons] at *
    omega
  · injection hr with hr
    rw [← hr, finalize_output_length]
    repeat simp only [pushArg, List.length_cons]
    omega
termination_by σ₁.ops.length

-- This implies that `parse?` either fails, or returns precisely a single output element.
theorem run?_output_singleton {ops args} (h : run? { ops, args } = some σ) : σ.output.length = 1 :=
  run?_output_length h .refl

theorem run?_wf (wf : Wellformed σ₁) : ∃ σ₂, σ₁.run? = some σ₂ := by
  rw [run?]
  repeat split
  next op _ arg _ ho ha _ =>
    have := push?_wf (wf.of_external_cons ho ha) arg op
    simp_all
  next ho ha _ h =>
    exact run?_wf <| (wf.of_external_cons ho ha).push? h
  · simp
  next h _ =>
    have ⟨_, _⟩ := wf
    cases ho : σ₁.ops <;> cases ha : σ₁.args <;> try specialize h _ _ _ _ ho ha
    all_goals simp_all
termination_by σ₁.ops.length

theorem run?_some {σ₁ : ParseState} (hr : σ₁.run? = some σ₂) :
    σ₁.args.length = σ₁.ops.length + 1 := by
  run?_cases hr
  next ops _ _ _ _ σ₂ h =>
    have := run?_some hr
    have := push?_args h
    have := push?_ops h
    simp_all
  · simp_all
termination_by σ₁.ops.length

end ParseState

-- Parses an expression based on the "shunting yard algorithm".
def parse? (ops : List Op) (args : List Nat) : Option Expr :=
  match h : { ops, args : ParseState }.run? with
  | none   => none
  | some σ => σ.output[0]'(by simp [ParseState.run?_output_singleton h])

theorem parse?_some_to_run?_some (h : parse? ops args = some e) :
    ∃ σ, { ops, args : ParseState }.run? = some σ := by
  rw [parse?] at h
  split at h <;> simp_all

theorem parse?_some_iff : (∃ e, parse? ops args = some e) ↔ (args.length = ops.length + 1) where
  mp h := parse?_some_to_run?_some h.choose_spec |>.choose_spec |> ParseState.run?_some
  mpr h := by
    have := ParseState.run?_wf (σ₁ := { ops, args }) ⟨h, rfl⟩
    rw [parse?]
    split <;> simp_all

theorem parse?_lits_eq_args (h : parse? ops args = some e) : e.lits = args := by
  rw [parse?] at h
  split at h
  · contradiction
  next σ hr =>
    injection h with h
    have hs := ParseState.run?_output_singleton hr
    have : σ.output = [e] := h ▸ List.length_one_eq_getElem_zero hs
    have := ParseState.run?_lits hr
    simp_all [ParseState.lits, ParseState.lits.go]

theorem parse?_apps_eq_ops (h : parse? ops args = some e) : e.apps = ops := by
  sorry

def parse (ops : List Op) (args : List Nat) (h : args.length = ops.length + 1) : Expr :=
  (parse? ops args).get <| Option.isSome_iff_exists.mpr <| parse?_some_iff.mpr h

theorem parse?_eq_parse (h : parse? ops args = some e) :
    e = parse ops args (parse?_some_iff.mp ⟨e, h⟩) := by
  simp [parse, h]

end Expr

def doAlgebra (ops : List Op) (args : List Nat) (h : args.length = ops.length + 1 := by decide) :=
  Expr.parse ops args h |>.eval

example : doAlgebra [.add, .mul, .sub] [2, 3, 4, 5] = 9  := by native_decide
example : doAlgebra [.pow, .mul, .add] [2, 3, 4, 5] = 37 := by native_decide
example : doAlgebra [.add, .mul, .sub] [2, 3, 4, 5] = 9  := by native_decide
example : doAlgebra [.div, .mul]       [7, 3, 4]    = 8  := by native_decide

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
