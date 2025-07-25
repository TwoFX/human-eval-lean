import Init.Data.Nat.Dvd
import Init.Data.Nat.Gcd

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html#Nat.minFac
def Nat.minFac (n : Nat) : Nat :=
  go 2
where
  go (i : Nat) : Nat :=
    if h : n < i * i then
      n
    else if h2 : i ∣ n then
      i
    else
      go (i + 1)
  termination_by n - i
  decreasing_by
    have : i < n := by
      match i with
      | 0 => omega
      | 1 => omega
      | i + 2 => exact Nat.lt_of_lt_of_le (Nat.lt_mul_self_iff.2 (by omega)) (Nat.not_lt.1 h)
    omega

def isMultipleOfKPrimes (n : Nat) (k : Nat) : Bool :=
  if hn₀ : n = 0 then
    false
  else if hk : k = 0 then
      n = 1
  else if hn₁ : n = 1 then
    false
  else
    let p := n.minFac
    isMultipleOfKPrimes (n / p) (k - 1)
  termination_by k
  decreasing_by
    omega

def isMultiplyPrime (n : Nat) : Bool := isMultipleOfKPrimes n 3

example : isMultiplyPrime 0 = false := by native_decide
example : isMultiplyPrime 1 = false := by native_decide
example : isMultiplyPrime 5 = false := by native_decide
example : isMultiplyPrime 30 = true := by native_decide
example : isMultiplyPrime 8 = true := by native_decide
example : isMultiplyPrime 10 = false := by native_decide
example : isMultiplyPrime 125 = true := by native_decide
example : isMultiplyPrime (3 * 5 * 7) = true := by native_decide
example : isMultiplyPrime (3 * 6 * 7) = false := by native_decide
example : isMultiplyPrime (9 * 9 * 9) = false := by native_decide
example : isMultiplyPrime (11 * 9 * 9) = false := by native_decide
example : isMultiplyPrime (11 * 13 * 7) = true := by native_decide

-- Section: Logic

theorem by_contra {p : Prop} (h : ¬p → False) : p := by
  if h1 : p then
    exact h1
  else
    simp [h1, h]
    exact h h1

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Bool/Basic.html#Bool.not_eq_true_eq_eq_false
theorem Bool.not_eq_true_eq_eq_false {b : Bool} : ¬b = true ↔ b = false := by simp

-- Section: Nat

theorem Nat.mul_lt_sq_imp_lt {a b : Nat} (h : a * b < d * d) : a < d ∨ b < d := by
  if hn : a < d then
    simp [hn]
  else
    simp at hn
    right
    suffices d * b ≤ a * b by
      exact Nat.lt_of_mul_lt_mul_left (Nat.lt_of_le_of_lt this h)
    exact mul_le_mul_right b hn

-- Section: Prime

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html#Nat.Prime
def Nat.Prime (n : Nat) : Prop :=
  1 < n ∧ ∀ {a b}, n ∣ a * b → n ∣ a ∨ n ∣ b

theorem Nat.Prime.one_lt (hp : Prime p) : 1 < p := hp.left

theorem Nat.Prime.zero_lt (hp : Prime p) : 0 < p := Nat.lt_trans (by simp) (hp.one_lt)

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Prime/Defs.html#Prime.ne_zero
theorem Nat.Prime.ne_zero (hp : Prime p) : p ≠ 0 := Ne.symm (Nat.ne_of_lt hp.zero_lt)

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Prime/Defs.html#Prime.ne_one
theorem Nat.Prime.ne_one (hp : Prime p) : p ≠ 1 := Ne.symm (Nat.ne_of_lt hp.one_lt)

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html#Nat.Prime.two_le
theorem Nat.Prime.two_le (hp : Prime p) : 2 ≤ p := by
  match p with
  | 0 => simp [Prime] at hp
  | 1 => simp [Prime] at hp
  | n + 2 => simp

theorem Nat.Prime.eq_one_or_self_of_dvd {p : Nat} (hb : Prime p) (a : Nat) (h : a ∣ p) : a = 1 ∨ a = p := by
  let ⟨u, hu⟩ := h
  have hd : p ∣ a * u := by simp [hu]
  apply Or.elim (hb.right hd)
  · intro hr; simp [Nat.dvd_antisymm h hr]
  · intro huu
    suffices a = 1 by simp [this]
    let ⟨v, hv⟩ := huu
    rw [hv, Nat.mul_comm p, ← Nat.mul_assoc] at hu
    exact Nat.dvd_one.mp ⟨v, Nat.mul_right_cancel hb.zero_lt (by simp; exact hu)⟩

theorem Nat.prime_def {p : Nat} : p.Prime ↔ 1 < p ∧ ∀ (m : Nat), m ∣ p → m = 1 ∨ m = p := by
  refine ⟨fun h => ⟨h.two_le, h.eq_one_or_self_of_dvd⟩, fun h => ?_⟩
  simp [Nat.Prime, h.1]
  let ⟨h1, h2⟩ := h
  intro a b hd
  apply Or.elim (h2 (Nat.gcd p a) (by simp [Nat.gcd_dvd]))
  intro ha
  apply Or.elim (h2 (Nat.gcd p b) (by simp [Nat.gcd_dvd]))
  intro hb
  rw [← Nat.dvd_gcd_mul_iff_dvd_mul, Nat.mul_comm, ← Nat.dvd_gcd_mul_iff_dvd_mul, ha, hb, Nat.mul_one, Nat.dvd_one] at hd
  simp [hd]
  intro h; rw [← h]; right; simp [Nat.gcd_dvd]
  intro h; rw [← h]; left; simp [Nat.gcd_dvd]

theorem Nat.Prime.not_dvd_of_ne {a b : Nat} (ha : Prime a) (hb : Prime b) (hne : a ≠ b) : ¬a ∣ b :=
  (fun h => Or.elim (hb.eq_one_or_self_of_dvd _ h) ha.ne_one hne)

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/Prime/Defs.html#Prime.dvd_mul
theorem Nat.Prime.dvd_mul (hp : Prime p) : p ∣ a * b ↔ p ∣ a ∨ p ∣ b := by
  constructor
  · exact hp.right
  · exact (Or.elim · (Nat.dvd_trans · (Nat.dvd_mul_right _ _)) (Nat.dvd_trans · (Nat.dvd_mul_left _ _)))

theorem Nat.Prime.dvd_div_of_dvd_mul {p a b : Nat} (hp : Prime p) (ha : p ∣ a) (hb : ¬p ∣ b) (hab : b ∣ a) : p ∣ a / b := by
  rcases ha with ⟨u, hu⟩
  suffices a / b = p * (u / b) by exact ⟨u / b, this⟩
  suffices b ∣ u by rw [hu, Nat.mul_div_assoc _ this]
  rw [hu] at hab
  rcases hab with ⟨v, hv⟩
  suffices u = b * (v / p) by exact ⟨v / p, this⟩
  suffices p ∣ v by rw [← Nat.mul_div_assoc _ this, ← hv, Nat.mul_comm, Nat.mul_div_cancel _ hp.zero_lt]
  have : p ∣ b * v := ⟨u, Eq.symm hv⟩
  rw [Nat.Prime.dvd_mul hp] at this
  apply Or.elim this
  · intro h; contradiction
  · exact fun x => x

-- Section: Smallest prime factor

theorem Nat.minFac.go_dvd {n : Nat} : Nat.minFac.go n 2 ∣ n := by
  fun_induction Nat.minFac.go n 2
  simp; assumption; assumption

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html#Nat.minFac_dvd
theorem Nat.minFac_dvd (n : Nat) : n.minFac ∣ n := by
  simp [Nat.minFac, Nat.minFac.go_dvd]

theorem not_lt_iff_eq_or_lt {a b : Nat} : ¬a < b ↔ a = b ∨ a > b := by
  simp
  constructor
  · intro h
    match h with
    | Nat.le.refl => simp
    | Nat.le.step a => exact Or.inr (Nat.lt_add_one_of_le a)
  · intro h
    rcases h with ⟨h1, h2⟩
    simp
    omega

theorem minFac_go_prime
    {n i : Nat} (hn : 1 < n) (hi : 1 < i):
    (∀ k, 1 < k → k < i → ¬ k ∣ n) →
      (Nat.minFac.go n i).Prime := by
  fun_induction Nat.minFac.go n i
  with
  | case1 i hlt =>
    intro h
    simp [Nat.prime_def, hn]
    intro m hd
    if g : m = 1 ∨ m = n then
      exact g
    else
      simp [g]
      simp at g
      have hm₁ : 1 < m := by match m with
        | 0 => rw [Nat.zero_dvd] at hd; rw [hd] at hn; contradiction
        | 1 => simp at g
        | _ + 2 => simp

      suffices m < i by
        specialize h m hm₁ this
        exact h hd

      let ⟨m', hm'⟩ := hd
      symm at hm'
      rw [← hm'] at hlt
      apply Or.elim (Nat.mul_lt_sq_imp_lt hlt)
      simp
      intro hd'
      have hm₁' : 1 < m' := by match m' with
        | 0 => simp at hm'; rw [hm']; exact hn
        | 1 => simp at hm'; rw [hm'] at g; simp at g
        | _ + 2 => simp
      specialize h m' hm₁' hd'
      exfalso
      apply h
      rw [← hm']
      exact ⟨m, by simp [Nat.mul_comm]⟩

  | case2 i hlt hdiv =>
    intro h
    simp [Nat.prime_def, hi]
    intro m hm
    match m with
    | 0 => rw [Nat.zero_dvd] at hm; symm at hm; simp [hm]
    | 1 => simp
    | m' + 2 =>
      if he : m' + 2 = i then
        simp [he]
      else
        simp [he]
        specialize h (m' + 2) (by simp) (Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hm) he)
        exact h (Nat.dvd_trans hm hdiv)
  | case3 i h1 h2 ih =>
    intro hk
    apply ih (Nat.lt_add_right 1 hi)
    intro k h3 h4
    if h5 : k < i then
      exact hk k h3 h5
    else if h6 : k = i then
      rw [h6]; exact h2
    else
      exfalso
      rw [not_lt_iff_eq_or_lt] at h5
      apply Or.elim h5
      · exact h6
      · simp [Nat.le_of_lt_add_one, h4]

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Prime/Defs.html#Nat.minFac_prime
theorem Nat.minFac_prime {n : Nat} (hn : 1 < n) : Prime (n.minFac) := by
  apply minFac_go_prime hn (by simp)
  intro k _ _
  match k with
  | 0 => contradiction
  | 1 => contradiction
  | n + 2 => contradiction

-- Section: List

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/List/Defs.html#List.prod
def List.prod {α} [Mul α] [One α] : List α → α :=
  List.foldr (· * ·) 1

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Ring/List.html#List.prod_ne_zero
theorem List.prod_ne_zero (l : List Nat) (h : ∀ x ∈ l, x ≠ 0) : l.prod ≠ 0 := by
  induction l with
  | nil => simp [List.prod]
  | cons x xs ih =>
    have : (x :: xs).prod = x * xs.prod := by simp [List.prod]
    rw [this]
    apply Nat.mul_ne_zero
    · apply h x; simp
    · apply ih; intro x1 hx; apply h; simp [hx]

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/List/Defs.html#List.prod_cons
theorem List.prod_cons (a : α) (l : List α) [Mul α] [One α] : (a :: l).prod = a * l.prod := by
  simp [List.prod]

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/List/Lemmas.html#List.dvd_prod
theorem List.dvd_prod {l : List Nat} {n : Nat} (h : n ∈ l) : n ∣ l.prod := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    rw [List.prod_cons]
    if hd : head = n then
      simp [hd, Nat.dvd_mul_right]
    else
      suffices n ∈ tail by exact Nat.dvd_mul_left_of_dvd (ih this) head
      simp at h
      apply Or.elim h
      · intro x; symm at x; contradiction
      · simp

-- https://leanprover-community.github.io/mathlib4_docs/Mathlib/Algebra/BigOperators/Group/List/Basic.html#List.prod_erase
theorem List.prod_erase (l : List Nat) (p : Nat) (h : p ∈ l) (h1 : 0 < p) : (l.erase p).prod = l.prod / p := by
  induction l with
  | nil => contradiction
  | cons head tail ih =>
    if hp : head = p then
      simp [hp, List.prod, Nat.mul_comm p, Nat.mul_div_cancel _ h1]
    else
      simp [List.prod_cons, hp]
      have ht : p ∈ tail := by
        simp at h
        apply Or.elim h
        intro x; symm at x; contradiction
        simp
      rw [ih ht, ← Nat.mul_div_assoc]
      exact List.dvd_prod ht

theorem List.prod_three_mul {a b c : Nat} : [a, b, c].prod = a * b * c := by
  simp [List.prod]
  rw [Nat.mul_assoc]

-- Section: Prime decomposition

structure PrimeDecomposition (n : Nat) where
  -- Multiset is only available in mathlib, using List instead
  ps : List Nat
  all_prime : ∀ p ∈ ps, p.Prime
  is_decomposition : ps.prod = n

def PrimeDecomposition.length (d : PrimeDecomposition n) : Nat := d.ps.length

def PrimeDecomposition.push (d : PrimeDecomposition n) (p : Nat) (hp : p.Prime) : PrimeDecomposition (n * p) :=
  ⟨p :: d.ps,
  by
    intro p1 h
    simp at h
    apply Or.elim h
    · intro t; rw[t]; exact hp
    · exact (d.all_prime p1 ·),
  by
    simp [List.prod_cons]
    rw [d.is_decomposition, Nat.mul_comm]
  ⟩

def PrimeDecomposition.erase_head (d : PrimeDecomposition n) : PrimeDecomposition (n / d.ps.headD 1) :=
  let ⟨ps, ha, hb⟩ := d
  match ps with
  | [] => ⟨[], ha, by simp; exact hb⟩
  | head :: tail =>
    ⟨tail,
     fun p h => ha p (by simp [h]),
     by simp
        simp [List.prod_cons] at hb
        symm at hb
        rw [hb, Nat.mul_comm, Nat.mul_div_cancel _ (ha head (by simp)).zero_lt]⟩

theorem PrimeDecomposition.prime_mem (d : PrimeDecomposition n) (hp : p.Prime) (hd : p ∣ n) : p ∈ d.ps := by
  let ⟨ps, ha, hb⟩ := d
  induction ps generalizing n with
  | nil =>
    simp [List.prod] at hb
    symm at hb
    rw [hb] at hd
    let c := Nat.le_trans (hp.two_le) (Nat.le_of_dvd (by simp) hd)
    contradiction
  | cons head tail ih =>
    simp
    simp at ih
    if hh : p = head then
      simp [hh]
    else
      simp [hh]
      let ih := ih ((⟨head :: tail, ha, hb⟩ : PrimeDecomposition n).erase_head)
      simp at ih
      simp [List.prod_cons] at hb
      symm at hb
      apply ih
      · apply hp.dvd_div_of_dvd_mul hd (hp.not_dvd_of_ne (ha head (by simp)) hh)
        simp [hb, Nat.dvd_mul_right]
      · intro p1 ht
        specialize ha p1
        simp [ht] at ha
        exact ha
      · rw [hb, Nat.mul_comm, Nat.mul_div_cancel _ (ha head (by simp)).zero_lt]

def PrimeDecomposition.erase (d : PrimeDecomposition n) (p : Nat) (hp : p.Prime) (hd : p ∣ n) : PrimeDecomposition (n / p) :=
  ⟨d.ps.erase p,
    fun p1 h1 => d.all_prime p1 (List.mem_of_mem_erase h1),
    by rw [List.prod_erase d.ps p (PrimeDecomposition.prime_mem d hp hd) hp.zero_lt]; simp [d.is_decomposition]⟩

theorem PrimeDecomposition.push_length {d : PrimeDecomposition n} : (d.push p hp).length = d.length + 1 := by
  simp [PrimeDecomposition.push, PrimeDecomposition.length]

theorem PrimeDecomposition.erase_length (d : PrimeDecomposition n) (p : Nat) (hp : p.Prime) (hd : p ∣ n) : (d.erase p hp hd).length = d.length - 1 := by
  simp [PrimeDecomposition.length, PrimeDecomposition.erase]
  rw [List.length_erase_of_mem (PrimeDecomposition.prime_mem d hp hd)]

def PrimeDecomposition.one : PrimeDecomposition 1 := ⟨[], by simp, (by simp [List.prod])⟩

theorem PrimeDecomposition.zero_not_exist (d : PrimeDecomposition 0) : False := by
  exact List.prod_ne_zero d.ps (fun x h => (d.all_prime x h).ne_zero) d.is_decomposition

theorem PrimeDecomposition.one_length (d : PrimeDecomposition 1) : d.length = 0 := by
  let ⟨ps, hp, hd⟩ := d
  simp [PrimeDecomposition.length]
  apply by_contra
  intro h
  rw [← List.isEmpty_iff, Bool.not_eq_true_eq_eq_false, List.isEmpty_eq_false_iff_exists_mem] at h
  rcases h with ⟨x, hx⟩
  specialize hp x hx
  have : x ∣ 1 := by rw [← hd]; exact List.dvd_prod hx
  let e := Nat.le_trans hp.two_le (Nat.le_of_dvd (by simp) this)
  contradiction

theorem isMultipleOfKPrimes_iff_primeDecomposition_length {n k : Nat} :
  isMultipleOfKPrimes n k ↔ ∃ (d : PrimeDecomposition n), d.length = k := by
    if hn₀ : n = 0 then
      rw [hn₀]
      simp [isMultipleOfKPrimes]
      intro x h
      exact PrimeDecomposition.zero_not_exist x
    else
      unfold isMultipleOfKPrimes
      simp [hn₀]
      if hk : k = 0 then
        simp [hk]
        constructor
        · intro h1
          rw [h1]
          exact ⟨PrimeDecomposition.one, by simp [PrimeDecomposition.one_length]⟩
        · intro ⟨d, hd⟩
          simp [PrimeDecomposition.length] at hd
          symm
          let x := d.is_decomposition
          simp [hd, List.prod] at x
          trivial
      else
        simp [hk]
        constructor
        · intro ⟨hn₁, hrec⟩
          let ⟨d, hd⟩ := isMultipleOfKPrimes_iff_primeDecomposition_length.mp hrec
          have hn_ge_1 : 1 < n := by match n with
            | 0 => trivial
            | 1 => trivial
            | n + 2 => simp
          let d₁ := d.push n.minFac (Nat.minFac_prime hn_ge_1)
          rw [← Nat.div_mul_cancel (Nat.minFac_dvd n)]
          suffices d₁.length = k by
            exact ⟨d₁, by simp [this]⟩
          rw [PrimeDecomposition.push_length, hd]
          have hk₀ : 1 ≤ k := by match k with
            | 0 => contradiction
            | k + 1 => simp
          rw [← Nat.sub_add_comm hk₀, Nat.add_sub_cancel]
        · intro ⟨d, hd⟩
          have hn_ge_1 : 1 < n := by match n with
            | 0 => trivial
            | 1 =>
              exfalso
              rw [PrimeDecomposition.one_length d] at hd
              symm at hd
              contradiction
            | n + 2 => simp
          constructor
          · intro h1
            revert hd d
            rw [h1]
            intro d hd
            rw [PrimeDecomposition.one_length d] at hd
            symm at hd
            contradiction
          · let d2 := d.erase n.minFac (Nat.minFac_prime hn_ge_1) (Nat.minFac_dvd n)
            suffices d2.length = k - 1 by
              exact isMultipleOfKPrimes_iff_primeDecomposition_length.mpr ⟨d2, by simp [this]⟩
            let x := PrimeDecomposition.erase_length d n.minFac (Nat.minFac_prime hn_ge_1) (Nat.minFac_dvd n)
            rw [x, hd]

theorem PrimeDecomposition.length_three (n : Nat) :
  (∃ (p₁ p₂ p₃ : Nat), p₁ * p₂ * p₃ = n ∧ p₁.Prime ∧ p₂.Prime ∧ p₃.Prime)
  ↔ ∃ (d : PrimeDecomposition n), d.length = 3 := by
  constructor
  · intro ⟨a, b, c, ⟨h, ha, hb, hc⟩⟩
    let d := PrimeDecomposition.one.push a ha |>.push b hb |>.push c hc

    suffices ∃ d : PrimeDecomposition (1 * a * b * c), d.length = 3 by
      have h1 : 1 * a * b * c = n := by simp [h]
      rw [h1] at this
      exact this

    suffices d.length = 3 by
      exact ⟨d, this⟩

    repeat rw [PrimeDecomposition.push_length]
    rw [PrimeDecomposition.one_length]
  · intro ⟨⟨ps, hp, ha⟩, hd⟩
    simp [PrimeDecomposition.length] at hd
    match ps with
    | [] => contradiction
    | a₁ :: rest => match rest with
      | [] => simp at hd
      | a₂ :: rest => match rest with
        | [] => simp at hd
        | a₃ :: rest =>
          simp at hd
          rw [hd] at ha
          suffices a₁ * a₂ * a₃ = n ∧ a₁.Prime ∧ a₂.Prime ∧ a₃.Prime by
            exact ⟨a₁, a₂, a₃, this⟩
          rw [List.prod_three_mul] at ha
          constructor
          · exact ha
          exact ⟨by simp [hp a₁], by simp [hp a₂], by simp [hp a₃]⟩

def IsMultiplyPrimeIff (solution : Nat → Bool) : Prop :=
  (a : Nat) → solution a ↔ ∃ (p₁ p₂ p₃ : Nat), p₁ * p₂ * p₃ = a ∧ p₁.Prime ∧ p₂.Prime ∧ p₃.Prime

theorem isMultiplyPrime_correct : IsMultiplyPrimeIff isMultiplyPrime := by
  intro a
  rw [PrimeDecomposition.length_three a]
  simp [isMultiplyPrime, isMultipleOfKPrimes_iff_primeDecomposition_length]

/-!
## Prompt

```python3

def is_multiply_prime(a):
    """Write a function that returns true if the given number is the multiplication of 3 prime numbers
    and false otherwise.
    Knowing that (a) is less then 100.
    Example:
    is_multiply_prime(30) == True
    30 = 2 * 3 * 5
    """
```

## Canonical solution

```python3
    def is_prime(n):
        for j in range(2,n):
            if n%j == 0:
                return False
        return True

    for i in range(2,101):
        if not is_prime(i): continue
        for j in range(2,101):
            if not is_prime(j): continue
            for k in range(2,101):
                if not is_prime(k): continue
                if i*j*k == a: return True
    return False
```

## Tests

```python3
def check(candidate):

    assert candidate(5) == False
    assert candidate(30) == True
    assert candidate(8) == True
    assert candidate(10) == False
    assert candidate(125) == True
    assert candidate(3 * 5 * 7) == True
    assert candidate(3 * 6 * 7) == False
    assert candidate(9 * 9 * 9) == False
    assert candidate(11 * 9 * 9) == False
    assert candidate(11 * 13 * 7) == True

```
-/
