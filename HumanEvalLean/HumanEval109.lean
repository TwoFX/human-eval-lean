variable {α : Type _}

section helper

theorem Nat.lt_two_iff {n : Nat} : n < 2 ↔ n = 0 ∨ n = 1 := by
  omega

theorem List.exists_mem_and {P : α → Prop} {l : List α} :
    (∃ a, a ∈ l ∧ P a) ↔ (∃ (n : Nat), ∃ h, P (l[n]'h)) := by
  refine ⟨fun ⟨a, h, h'⟩ => ?_, fun ⟨n, h, h'⟩ => ⟨l[n], by simp, h'⟩⟩
  obtain ⟨i, h'', rfl⟩ := List.getElem_of_mem h
  exact ⟨_, _, h'⟩

theorem List.sum_eq_zero {l : List Nat} : l.sum = 0 ↔
    ∀ (i : Nat) (hi : i < l.length), l[i]'hi = 0 := by
  rw [← Decidable.not_iff_not]
  simp [← Nat.pos_iff_ne_zero, Nat.sum_pos_iff_exists_pos, List.exists_mem_and]

theorem List.sum_eq_one_iff {l : List Nat} : l.sum = 1 ↔ ∃ (i : Nat) (hi : i < l.length),
    l[i] = 1 ∧ ∀ (j : Nat) (hj : j < l.length), i ≠ j → l[j] = 0 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [sum_cons, Nat.add_eq_one_iff, length_cons, ne_eq, exists_and_right]
    constructor
    · intro h
      cases h with
      | inl h =>
        rcases h with ⟨hl, hr⟩
        rw [ih] at hr
        rcases hr with ⟨i, hi, h⟩
        exists (i + 1)
        simp only [getElem_cons_succ, Nat.add_lt_add_iff_right]
        constructor
        · exists hi
          simp [h]
        · intro j hj hij
          cases j with
          | zero => simp[hl]
          | succ k =>
            simp only [getElem_cons_succ]
            apply (And.right h)
            simp only [Nat.add_right_cancel_iff] at hij
            assumption
      | inr h =>
        exists 0
        simp only [h, getElem_cons_zero, Nat.zero_lt_succ, exists_const, true_and]
        rw [sum_eq_zero] at h
        intro j hj hij
        cases j with
        | zero => simp at hij
        | succ k =>
          simp only [getElem_cons_succ]
          rcases h with ⟨_, h⟩
          apply h
    · intro h
      rcases h with ⟨i, hi, h⟩
      cases i with
      | zero =>
        right
        simp only [getElem_cons_zero, Nat.zero_lt_succ, exists_const] at hi
        simp only [hi, true_and]
        rw [List.sum_eq_zero]
        intro x hx
        specialize h (x+1)
        simp only [Nat.add_lt_add_iff_right, Nat.right_eq_add, Nat.add_eq_zero, Nat.succ_ne_self,
          and_false, not_false_eq_true, getElem_cons_succ, forall_const] at h
        apply h
        exact hx
      | succ k =>
        simp only [getElem_cons_succ, Nat.add_lt_add_iff_right] at hi
        left
        constructor
        · specialize h 0
          simp only [Nat.zero_lt_succ, Nat.add_eq_zero, Nat.succ_ne_self, and_false,
            not_false_eq_true, getElem_cons_zero, forall_const] at h
          assumption
        · rw [ih]
          exists k
          rcases hi with ⟨hk, tlk⟩
          exists hk
          simp only [tlk, ne_eq, true_and]
          intro j hj hkj
          specialize h (j + 1)
          simp only [Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff, getElem_cons_succ] at h
          apply h hj hkj

theorem List.two_le_sum_iff {l : List Nat} (h : ∀ (i : Nat) (hi : i < l.length), l[i] ≤ 1) :
    2 ≤ l.sum ↔ ∃ (i j : Nat) (_hij : i ≠ j) (hi : i < l.length) (hj : j < l.length),
      l[i] = 1 ∧ l[j] = 1 := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [sum_cons, length_cons, exists_and_left, exists_and_right, ne_eq, exists_prop]
    by_cases h' : 2 ≤ tl.sum
    · have : 2 ≤ hd + tl.sum := by omega
      rw [ih] at h'
      · simp only [this, true_iff]
        rcases h' with ⟨i, j, hij, hi, hj, h'⟩
        exists (i+1)
        simp only [getElem_cons_succ, Nat.add_lt_add_iff_right]
        constructor
        · exists hi
          simp [h']
        · exists (j+1)
          simp only [Nat.add_right_cancel_iff, hij, not_false_eq_true, getElem_cons_succ,
            Nat.add_lt_add_iff_right, true_and]
          exists hj
          simp [h']
      · intro i hi
        specialize h (i+1)
        simp only [length_cons, Nat.add_lt_add_iff_right, getElem_cons_succ] at h
        apply h hi
    · simp only [Nat.not_le] at h'
      cases htl : tl.sum with
      | zero =>
        simp only [Nat.add_zero]
        have hhd : ¬ 2 ≤ hd := by
          intro h'
          specialize h 0
          simp only [length_cons, Nat.zero_lt_succ, getElem_cons_zero, forall_const] at h
          omega
        rw [List.sum_eq_zero] at htl
        simp only [hhd, false_iff, not_exists, not_and, forall_exists_index]
        intro i hi hi' j hij hj
        cases i with
        | zero =>
          simp only [getElem_cons_zero] at hi'
          cases j with
          | zero => contradiction
          | succ k =>
            simp only [getElem_cons_succ]
            intro hk
            specialize htl k
            have : k < tl.length := by omega
            specialize htl this
            rw [hk] at htl
            simp only [Nat.succ_ne_self] at htl
        | succ k =>
          simp only [getElem_cons_succ] at hi'
          specialize htl k
          have : k < tl.length := by omega
          specialize htl this
          rw [hi'] at htl
          simp at htl
      | succ k =>
        have hk : k = 0 := by omega
        simp only [hk, Nat.zero_add, Nat.reduceLeDiff]
        constructor
        · intro h₁
          exists 0
          simp only [getElem_cons_zero, Nat.zero_lt_succ, exists_const]
          constructor
          · specialize h 0
            simp only [length_cons, Nat.zero_lt_succ, getElem_cons_zero, forall_const] at h
            omega
          · simp only [hk, Nat.zero_add] at htl
            rw [List.sum_eq_one_iff] at htl
            rcases htl with ⟨i, hi,hi', _⟩
            exists (i+1)
            simp only [Nat.right_eq_add, Nat.add_eq_zero, Nat.succ_ne_self, and_false,
              not_false_eq_true, getElem_cons_succ, Nat.add_lt_add_iff_right, true_and]
            exists hi
        · intro h₁
          simp only [hk, Nat.zero_add] at htl
          rw [List.sum_eq_one_iff] at htl
          rcases htl with ⟨i, hi,hi', htl⟩
          rcases h₁ with ⟨j, hj, k, hjk, hk⟩
          cases j with
          | zero =>
            simp only [getElem_cons_zero, Nat.zero_lt_succ, exists_const] at hj
            simp [hj]
          | succ l =>
            simp only [getElem_cons_succ, Nat.add_lt_add_iff_right] at hj
            cases k with
            | zero =>
              simp only [getElem_cons_zero, Nat.zero_lt_succ, exists_const] at hk
              simp [hk]
            | succ m =>
              simp only [getElem_cons_succ, Nat.add_lt_add_iff_right] at hk
              by_cases hil : i = l
              · specialize htl m
                rcases hk with ⟨hm, hm'⟩
                specialize htl hm
                omega
              · rcases hj with ⟨hl, hl'⟩
                specialize htl l hl
                omega


-- from mathlib
@[simp] theorem List.take_eq_self_iff (x : List α) {n : Nat} : x.take n = x ↔ x.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp only [length_take]; omega, List.take_of_length_le⟩

theorem List.sum_append {l₁ l₂ : List Nat} :
    (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  induction l₁ with
  | nil => simp
  | cons hd tl ih =>
    simp only [cons_append, sum_cons, ih]
    omega

end helper

def rightShift (l : List α) (n : Nat) :=
    l.drop (l.length - n) ++ l.take (l.length - n)

theorem rightShiftExample : rightShift [3,4,5,1,2] 2 = [1,2,3,4,5] := by native_decide

@[simp]
theorem rightShift_zero {l : List α} : rightShift l 0 = l := by
  simp [rightShift]

@[simp]
theorem length_rightShift {l : List α} {n : Nat} :
    (rightShift l n).length = l.length := by
  simp [rightShift]

def leftShift (l : List α) (n : Nat) :=
    l.drop n ++ l.take n

@[simp]
theorem length_leftShift {l : List α} {n : Nat} :
    (leftShift l n).length = l.length := by
  simp [leftShift]
  omega

theorem leftShiftExample1 : leftShift [3,4,5,1,2] 2 = [5,1,2,3,4] := by native_decide

theorem leftShiftExample2 : leftShift [3,4,5,1,2] 3 = [1,2,3,4,5] := by native_decide

theorem List.sum_leftShift_eq_sum {l : List Nat} {n : Nat} :
    (leftShift l n).sum = l.sum := by
  simp only [leftShift]
  rw [List.sum_append, Nat.add_comm, ← List.sum_append, take_append_drop]

theorem exists_rightShift_iff_exists_leftShift {l : List α} (p : List α → Prop) :
    (∃ (n : Nat), p (rightShift l n)) ↔ ∃ (n : Nat), p (leftShift l n) := by
  simp only [rightShift, leftShift]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    exists (l.length - n)
  · intro h
    obtain ⟨n, hn⟩ := h
    by_cases n < l.length
    · exists (l.length - n)
      have : l.length - (l.length - n) = n := by omega
      simp only [this]
      exact hn
    · exists 0
      simp only [Nat.sub_zero, List.drop_length, List.take_length, List.nil_append]
      rename_i h
      simp only [Nat.not_lt] at h
      have := List.drop_eq_nil_iff (l := l) (i := n)
      simp only [this.mpr h, List.nil_append] at hn
      have := List.take_eq_self_iff l (n := n)
      simp only [this.mpr h] at hn
      exact hn

def isBreakPoint (l : List Int) (pos : Nat) :=
  if h:pos < l.length
  then
    if h':pos + 1 < l.length
    then
      if l[pos] < l[pos + 1]
      then 0
      else 1
    else
      if l[0] > l[pos]
      then 0
      else 1
  else 0

def countBreakPoints (l : List Int) : Nat :=
  if l.length < 2
  then 0
  else
    ((List.range l.length).map (fun x => isBreakPoint l x)).sum

theorem ne_nil_of_two_ge {l : List α} (h : 2 ≤ l.length) : l ≠ [] := by
  cases l with
  | nil => simp at h
  | cons hd tl => simp

theorem sorted_of_countBreakPoints_eq_zero {l : List Int} (h : countBreakPoints l = 0):
    ∀ (i : Nat) (hi : i + 1 < l.length), l[i] < l[i+1] := by
  simp [countBreakPoints] at h
  cases l with
  | nil => simp
  | cons hd tl =>
    cases tl with
    | nil => simp
    | cons hd' tl' =>
      simp only [List.length_cons, Nat.le_add_left, isBreakPoint, Nat.add_lt_add_iff_right,
        List.getElem_cons_succ, List.getElem_cons_zero, gt_iff_lt, List.sum_eq_zero,
        List.length_map, List.length_range, List.getElem_map, List.getElem_range, dite_eq_right_iff,
        forall_const] at h
      simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ]
      intro i hi
      specialize h i (by omega)
      simp only [hi, ↓reduceDIte, ite_eq_left_iff, Int.not_lt, Nat.succ_ne_self, imp_false,
        Int.not_le] at h
      apply h
      omega

theorem pairwise_sorted_of_sorted {l : List Int} {i j : Nat}
    (hj: j > 0) (hij : i + j < l.length)
    (sorted : ∀ (i : Nat) (hi : i + 1 < l.length), l[i] < l[i+1]) :
    l[i]'(by omega) < l[i + j] := by
  induction l generalizing i j with
  | nil => simp at hij
  | cons hd tl ih =>
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, Nat.zero_add]
      simp only [gt_iff_lt, Nat.lt_iff_add_one_le, Nat.zero_add] at hj
      cases j with
      | zero => simp at hj
      | succ k =>
        cases k with
        | zero =>
          simp only [Nat.zero_add, List.getElem_cons_succ]
          specialize sorted 0
          simp only [Nat.zero_add, List.length_cons, Nat.lt_add_left_iff_pos,
            List.getElem_cons_zero, List.getElem_cons_succ] at sorted
          apply sorted
          simp only [Nat.zero_add, List.length_cons, Nat.lt_add_left_iff_pos] at hij
          assumption
        | succ m =>
          simp only [List.getElem_cons_succ]
          have : m + 1 > 0 := by omega
          have ih' := ih (i:= 0) (j := m+1)
          specialize ih' this
          simp only [Nat.zero_add] at ih'
          simp only [Nat.zero_add, List.length_cons, Nat.add_lt_add_iff_right] at hij
          specialize ih' hij
          apply Int.lt_trans (b := tl[0])
          · specialize sorted 0
            simp only [Nat.zero_add, List.length_cons, Nat.lt_add_left_iff_pos,
              List.getElem_cons_zero, List.getElem_cons_succ] at sorted
            apply sorted
            apply Nat.lt_trans (m:= m + 1)
            · simp
            · exact hij
          · apply ih'
            intro i hi
            specialize sorted (i+1)
            simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ] at sorted
            apply sorted hi
    | succ n =>
      simp only [List.getElem_cons_succ]
      have : n + 1 + j = (n + j).succ := by omega
      simp only [this, Nat.succ_eq_add_one, List.getElem_cons_succ, gt_iff_lt]
      apply ih
      · exact hj
      · intro i hi
        specialize sorted (i+1)
        simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ] at sorted
        apply sorted hi

theorem countBreakPoints_eq_zero_iff {l : List Int} : countBreakPoints l = 0 ↔ l.length < 2 := by
  constructor
  · intro h
    have sorted := sorted_of_countBreakPoints_eq_zero h
    false_or_by_contra
    rename_i hl
    simp only [gt_iff_lt, Nat.not_lt] at hl
    cases l with
    | nil => simp at hl
    | cons hd tl =>
      cases tl with
      | nil => simp at hl
      | cons hd' tl' =>
        have h₁ : hd < (hd' :: tl')[tl'.length] := by
          have head_lt_getLast := pairwise_sorted_of_sorted (l := hd :: hd' :: tl') (i := 0)
              (j := tl'.length + 1) (by simp) (by simp) sorted
          simp only [List.getElem_cons_zero, Nat.zero_add,
            List.getElem_cons_succ] at head_lt_getLast
          exact head_lt_getLast
        have h₂ : (hd' :: tl')[tl'.length] < hd := by
          simp only [countBreakPoints, List.length_cons, isBreakPoint, Nat.add_lt_add_iff_right,
            List.getElem_cons_succ, List.getElem_cons_zero, gt_iff_lt, ite_eq_left_iff, Nat.not_lt,
            Nat.le_add_left, List.sum_eq_zero, List.length_map, List.length_range, List.getElem_map,
            List.getElem_range, dite_eq_right_iff, forall_const] at h
          specialize h (tl'.length + 1)
          simp only [Nat.lt_add_one, Nat.lt_irrefl, ↓reduceDIte, List.getElem_cons_succ,
            ite_eq_left_iff, Int.not_lt, Nat.succ_ne_self, imp_false, Int.not_le] at h
          apply h
          · trivial
          · trivial
        have := Int.lt_trans h₁ h₂
        simp at this
  · intro h
    simp [countBreakPoints, h]

theorem countBreakPoints_leftShift_eq_countBreakPoints {l : List Int} {n : Nat} :
    countBreakPoints (leftShift l n) = countBreakPoints l := by
  simp only [countBreakPoints, length_leftShift]
  by_cases h: l.length < 2
  · simp [h]
  · by_cases hn: n < l.length
    · simp only [h, ↓reduceIte]
      have : List.map (fun x => isBreakPoint (leftShift l n) x) (List.range l.length) =
              leftShift (List.map (fun x => isBreakPoint l x) (List.range l.length)) n := by
        apply List.ext_get
        · simp
        · simp only [List.length_map, List.length_range, length_leftShift, List.get_eq_getElem,
          List.getElem_map, List.getElem_range]
          intro m h₁ _
          conv =>
            rhs
            simp only [leftShift]
            rw [List.getElem_append]
            simp
          split
          · simp only [isBreakPoint, length_leftShift, h₁, ↓reduceDIte, gt_iff_lt]
            split
            · have : n + m < l.length := by omega
              simp only [this, ↓reduceDIte]
              by_cases hnm : n + m +1 < l.length
              · simp only [leftShift, List.getElem_append, List.length_drop, List.getElem_drop,
                List.getElem_take, hnm, ↓reduceDIte]
                simp only [↓reduceDIte, *]
                have : m + 1 < l.length - n := by omega
                simp only [this, ↓reduceDIte]
                rfl
              · simp only [leftShift, List.getElem_append, List.length_drop, List.getElem_drop,
                List.getElem_take, hnm, ↓reduceDIte]
                simp only [↓reduceDIte, *]
                have : ¬ m + 1 < l.length - n := by omega
                simp only [this, ↓reduceDIte]
                have : m + 1 - (l.length - n) = 0 := by omega
                simp [this]
            · have : n + m < l.length := by omega
              simp only [this, ↓reduceDIte]
              by_cases hnm : n + m +1 < l.length
              · omega
              · simp only [leftShift, List.getElem_append, List.length_drop, List.getElem_drop,
                List.getElem_take, Nat.add_zero, Nat.zero_le, Nat.sub_eq_zero_of_le, hnm,
                ↓reduceDIte]
                simp only [↓reduceDIte, *]
                have : 0 < l.length -n := by omega
                simp only [this, ↓reduceDIte]
                have : n = 0 := by omega
                simp [this]
          · rename_i hnm
            simp only [isBreakPoint, length_leftShift, h₁, ↓reduceDIte, gt_iff_lt]
            by_cases h₂ : m + 1 < l.length
            · simp only [h₂, ↓reduceDIte]
              have : m - (l.length - n) < l.length := by omega
              simp only [this, ↓reduceDIte]
              have : m - (l.length - n) + 1 < l.length := by omega
              simp only [leftShift, List.getElem_append, List.length_drop, List.getElem_drop,
                List.getElem_take, this, ↓reduceDIte, hnm]
              have : ¬ m + 1 < l.length - n := by omega
              simp only [this, ↓reduceDIte]
              congr
              omega
            · simp only [h₂, ↓reduceDIte]
              have : m - (l.length - n) < l.length := by omega
              simp only [this, ↓reduceDIte]
              have : m - (l.length - n) + 1 < l.length := by omega
              simp only [leftShift, List.getElem_append, List.length_drop, hnm, ↓reduceDIte,
                List.getElem_take, List.getElem_drop, Nat.add_zero, Nat.zero_le,
                Nat.sub_eq_zero_of_le, this]
              have : 0 < l.length - n := by omega
              simp only [this, ↓reduceDIte]
              congr
              omega
      simp only [this]
      rw [List.sum_leftShift_eq_sum (n:= n) (l:= (List.map (fun x => isBreakPoint l x) (List.range l.length)))]
    · congr
      funext
      congr
      simp only [Nat.not_lt] at hn
      simp [leftShift, List.drop_eq_nil_iff.mpr, hn]


theorem not_sorted_of_countBreakPoints_ge_two {l : List Int} (h : countBreakPoints l ≥ 2) :
    ∃ (i : Nat) (hi : i + 1 < l.length),
      l[i] ≥ l[i+1] := by
  simp only [countBreakPoints, ge_iff_le] at h
  split at h
  · simp at h
  · rw [List.two_le_sum_iff] at h
    · rcases h with ⟨i, j, hij, hi, hj, h⟩
      simp only [isBreakPoint, gt_iff_lt, List.getElem_map, List.getElem_range] at h
      simp only [List.length_map, List.length_range] at hi
      simp only [List.length_map, List.length_range] at hj
      have : i + 1 < l.length ∨ j + 1 < l.length := by omega
      cases this with
      | inl this =>
        simp only [this, ↓reduceDIte] at h
        exists i
        exists this
        simp only [hi, ↓reduceDIte, ite_eq_right_iff, Nat.zero_ne_one, imp_false, Int.not_lt] at h
        simp [h]
      | inr this =>
        simp only [this, ↓reduceDIte] at h
        exists j
        exists this
        simp only [hj, ↓reduceDIte, ite_eq_right_iff, Nat.zero_ne_one, imp_false, Int.not_lt] at h
        simp [h]
    · simp only [isBreakPoint, gt_iff_lt, List.length_map, List.length_range, List.getElem_map,
      List.getElem_range]
      intro _ _
      split <;> split <;> split <;> simp

def move_one_ball (l : List Int) : Bool :=
  countBreakPoints l < 2

theorem testCase1 : move_one_ball [3,4,5,1,2] = True := by native_decide
theorem testCase2 : move_one_ball [3,5,10,1,2] = True := by native_decide
theorem testCase3 : move_one_ball [4,3,1,2] = False := by native_decide
theorem testCase4 : move_one_ball [3,5,4,1,2] = False := by native_decide
theorem testCase5 : move_one_ball [] = True := by native_decide

theorem move_one_ball_correct {l : List Int} :
    move_one_ball l = true ↔
    ∃ (n : Nat), ∀ (i : Nat) (hi : i + 1 < l.length),
      (rightShift l n)[i]'(by simp only [length_rightShift]; omega) <
        (rightShift l n)[i +1]'(by simpa) := by
  by_cases hl : l.length < 2
  · simp only [move_one_ball, countBreakPoints, hl, ↓reduceIte, Nat.zero_lt_succ, decide_true,
    true_iff]
    exists 0
    cases l with
    | nil => simp
    | cons hd tl =>
      cases tl with
      | nil => simp
      | cons hd' tl' =>
        simp only [List.length_cons] at hl
        omega
  · simp only [move_one_ball, decide_eq_true_eq]
    constructor
    · intro h
      rw [Nat.lt_two_iff] at h
      cases h with
      | inl h =>
        rw [countBreakPoints_eq_zero_iff] at h
        contradiction
      | inr h =>
        simp only [countBreakPoints, hl, ↓reduceIte, List.sum_eq_one_iff, List.getElem_map,
          List.getElem_range, List.length_map, List.length_range, ne_eq, exists_and_left,
          exists_prop] at h
        have := exists_rightShift_iff_exists_leftShift (l:= l) (p := fun (l : List Int) =>
          ∀ (i : Nat) (hi : i + 1 < l.length), l[i]'(by omega) < l[i + 1])
        simp only [length_rightShift, length_leftShift] at this
        rw [this]
        rcases h with ⟨i, hi1, hi2⟩
        exists (i + 1)
        intro j hj
        simp only [leftShift]
        simp only [List.getElem_append, List.length_drop, List.getElem_drop, List.getElem_take]
        simp only [isBreakPoint, gt_iff_lt, dite_eq_right_iff] at hi2
        rcases hi2 with ⟨hi, hi2⟩
        split
        · split
          · specialize hi2 (i + 1 + j) (by omega)
            have : ¬ i = i + 1 + j := by omega
            simp only [this, not_false_eq_true, forall_const] at hi2
            have :  i + 1 + j + 1 < l.length := by omega
            simp only [this, ↓reduceDIte, ite_eq_left_iff, Int.not_lt, Nat.succ_ne_self, imp_false,
              Int.not_le] at hi2
            apply hi2
            omega
          · specialize hi2 (i + 1 + j) (by omega)
            have : ¬ i = i + 1 + j := by omega
            simp only [this, not_false_eq_true, forall_const] at hi2
            have : ¬ i + 1 + j + 1 < l.length := by omega
            simp only [this, ↓reduceDIte, ite_eq_left_iff, Int.not_lt, Nat.succ_ne_self, imp_false,
              Int.not_le] at hi2
            have : j + 1 - (l.length - (i + 1)) = 0 := by omega
            simp only [this, gt_iff_lt]
            apply hi2
            omega
        · split
          · specialize hi2 0 (by omega)
            have : ¬ i = 0 := by omega
            simp only [this, not_false_eq_true, Nat.zero_add, Int.lt_irrefl, ↓reduceIte,
              forall_const] at hi2
            have : 1 < l.length := by omega
            simp only [this, ↓reduceDIte, ite_eq_left_iff, Int.not_lt, Nat.succ_ne_self, imp_false,
              Int.not_le] at hi2
            omega
          · rename_i h₁ h₂
            specialize hi2 (j - (l.length - (i + 1))) (by omega) (by omega)
            have : j - (l.length - (i + 1)) + 1 < l.length := by omega
            simp only [this, ↓reduceDIte, ite_eq_left_iff, Int.not_lt, Nat.succ_ne_self, imp_false,
              Int.not_le] at hi2
            have : j - (l.length - (i + 1)) + 1 = j + 1 - (l.length - (i + 1)) := by omega
            simp only [this] at hi2
            apply hi2
            omega
    · false_or_by_contra
      rename_i h h'
      simp only [Nat.not_lt] at h'
      have := exists_rightShift_iff_exists_leftShift (l:= l) (p := fun (l : List Int) =>
          ∀ (i : Nat) (hi : i + 1 < l.length), l[i]'(by omega) < l[i + 1])
      simp only [length_rightShift, length_leftShift] at this
      rw [this] at h
      rcases h with ⟨n,h⟩
      have := not_sorted_of_countBreakPoints_ge_two (l := leftShift l n)
      rw [countBreakPoints_leftShift_eq_countBreakPoints] at this
      simp only [ge_iff_le, h', length_leftShift, forall_const] at this
      rcases this with ⟨i, hi, this⟩
      specialize h i hi
      omega

/-!
## Prompt

```python3

def move_one_ball(arr):
    """We have an array 'arr' of N integers arr[1], arr[2], ..., arr[N].The
    numbers in the array will be randomly ordered. Your task is to determine if
    it is possible to get an array sorted in non-decreasing order by performing
    the following operation on the given array:
        You are allowed to perform right shift operation any number of times.

    One right shift operation means shifting all elements of the array by one
    position in the right direction. The last element of the array will be moved to
    the starting position in the array i.e. 0th index.

    If it is possible to obtain the sorted array by performing the above operation
    then return True else return False.
    If the given array is empty then return True.

    Note: The given list is guaranteed to have unique elements.

    For Example:

    move_one_ball([3, 4, 5, 1, 2])==>True
    Explanation: By performin 2 right shift operations, non-decreasing order can
                 be achieved for the given array.
    move_one_ball([3, 5, 4, 1, 2])==>False
    Explanation:It is not possible to get non-decreasing order for the given
                array by performing any number of right shift operations.

    """
```

## Canonical solution

```python3
    if len(arr)==0:
      return True
    sorted_array=sorted(arr)
    my_arr=[]

    min_value=min(arr)
    min_index=arr.index(min_value)
    my_arr=arr[min_index:]+arr[0:min_index]
    for i in range(len(arr)):
      if my_arr[i]!=sorted_array[i]:
        return False
    return True
```

## Tests

```python3
def check(candidate):

    # Check some simple cases
    assert candidate([3, 4, 5, 1, 2])==True, "This prints if this assert fails 1 (good for debugging!)"
    assert candidate([3, 5, 10, 1, 2])==True
    assert candidate([4, 3, 1, 2])==False
    # Check some edge cases that are easy to work out by hand.
    assert candidate([3, 5, 4, 1, 2])==False, "This prints if this assert fails 2 (also good for debugging!)"
    assert candidate([])==True
```
-/
