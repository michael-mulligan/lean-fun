import Mathlib

abbrev abelian.FreeAbelianMonoid (n : ℕ) := Multiset (Fin n)

def abelian.A (n : ℕ) : Set (abelian.FreeAbelianMonoid n) := { m | ∃ i : Fin n, m = Multiset.replicate 1 i }

def abelian.Ball {n : ℕ} (s : ℕ) (G : Set (abelian.FreeAbelianMonoid n)) : Set (abelian.FreeAbelianMonoid n) := { m | ∃ l : List (abelian.FreeAbelianMonoid n), l.length ≤ s ∧ (∀ x ∈ l, x ∈ G) ∧ l.sum = m }

def fibMacros : Set (abelian.FreeAbelianMonoid 1) := { m | ∃ j : ℕ, 1 ≤ j ∧ m = Multiset.replicate (Nat.fib (2 * j + 1)) (0 : Fin 1) }

theorem fibMacros_union_A: fibMacros ∪ abelian.A 1 = { m | ∃ j : ℕ, m = Multiset.replicate (Nat.fib (2 * j + 1)) (0 : Fin 1) } := by
  ext m
  constructor
  · intro hm
    rcases hm with hfm | hA
    · rcases hfm with ⟨j, hj, rfl⟩
      exact ⟨j, rfl⟩
    · rcases hA with ⟨i, rfl⟩
      refine ⟨0, ?_⟩
      have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
      rw [hi]
      norm_num [Nat.fib]
  · intro hm
    rcases hm with ⟨j, rfl⟩
    cases j with
    | zero =>
        right
        refine ⟨0, ?_⟩
        norm_num [abelian.A, Nat.fib]
    | succ j =>
        left
        refine ⟨j + 1, Nat.succ_le_succ (Nat.zero_le _), rfl⟩

theorem fib_coverage (s k : ℕ) (hk : k < Nat.fib (2 * s + 2)) : ∃ l : List ℕ, l.length ≤ s ∧ (∀ x ∈ l, ∃ j, x = Nat.fib (2 * j + 1)) ∧ l.sum = k := by
  induction s generalizing k with
  | zero =>
      have hk0 : k = 0 := by
        norm_num [Nat.fib] at hk
        omega
      refine ⟨[], ?_, ?_, ?_⟩
      · exact le_rfl
      · intro x hx
        cases hx
      · simpa only [hk0, List.sum_nil]
  | succ s ih =>
      have hk4 : k < Nat.fib ((2 * s + 2) + 2) := by
        simpa [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk
      have hF3 : Nat.fib (2 * s + 3) = Nat.fib (2 * s + 1) + Nat.fib (2 * s + 2) := by
        calc
          Nat.fib (2 * s + 3) = Nat.fib ((2 * s + 2) + 1) := by
            congr
          _ = Nat.fib ((2 * s + 2) - 1) + Nat.fib (2 * s + 2) :=
            Nat.fib_add_one (n := 2 * s + 2) (by omega)
          _ = Nat.fib (2 * s + 1) + Nat.fib (2 * s + 2) := by
            congr
      have hF4 : Nat.fib ((2 * s + 2) + 2) = Nat.fib (2 * s + 2) + Nat.fib (2 * s + 3) := by
        calc
          Nat.fib ((2 * s + 2) + 2) = Nat.fib (2 * s + 2) + Nat.fib ((2 * s + 2) + 1) :=
            Nat.fib_add_two (n := 2 * s + 2)
          _ = Nat.fib (2 * s + 2) + Nat.fib (2 * s + 3) := by
            congr
      have hF2pos : 0 < Nat.fib (2 * s + 2) := by
        exact (Nat.fib_pos).2 (by omega)
      by_cases hk0 : k < Nat.fib (2 * s + 2)
      · rcases ih k hk0 with ⟨l, hl1, hl2, hl3⟩
        refine ⟨l, ?_, hl2, hl3⟩
        exact le_trans hl1 (Nat.le_succ s)
      · by_cases hk1 : k < Nat.fib (2 * s + 3)
        · have hkrem : k - Nat.fib (2 * s + 1) < Nat.fib (2 * s + 2) := by
            rw [hF3] at hk1
            omega
          rcases ih (k - Nat.fib (2 * s + 1)) hkrem with ⟨l, hl1, hl2, hl3⟩
          refine ⟨Nat.fib (2 * s + 1) :: l, ?_, ?_, ?_⟩
          · simpa only [List.length_cons] using Nat.succ_le_succ hl1
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · exact ⟨s, rfl⟩
            · exact hl2 x hx
          · have hmono : Nat.fib (2 * s + 1) ≤ Nat.fib (2 * s + 2) := by
              apply Nat.fib_mono
              omega
            have hle : Nat.fib (2 * s + 1) ≤ k := by
              omega
            simpa only [List.sum_cons, hl3] using (Nat.add_sub_of_le hle)
        · have hkrem : k - Nat.fib (2 * s + 3) < Nat.fib (2 * s + 2) := by
            rw [hF4] at hk4
            omega
          rcases ih (k - Nat.fib (2 * s + 3)) hkrem with ⟨l, hl1, hl2, hl3⟩
          refine ⟨Nat.fib (2 * s + 3) :: l, ?_, ?_, ?_⟩
          · simpa only [List.length_cons] using Nat.succ_le_succ hl1
          · intro x hx
            simp only [List.mem_cons] at hx
            rcases hx with rfl | hx
            · refine ⟨s + 1, ?_⟩
              have hidx : 2 * s + 3 = 2 * (s + 1) + 1 := by
                omega
              rw [hidx]
            · exact hl2 x hx
          · have hle : Nat.fib (2 * s + 3) ≤ k := by
              omega
            simpa only [List.sum_cons, hl3] using (Nat.add_sub_of_le hle)

theorem fib_even_lt_two_prev_odd (s : ℕ) : Nat.fib (2 * s + 2) < 2 * Nat.fib (2 * s + 1) := by
  rw [Nat.fib_add_two]
  have h : Nat.fib (2 * s) < Nat.fib (2 * s + 1) := by
    cases s with
    | zero =>
        norm_num [Nat.fib]
    | succ s =>
        have hs : 2 ≤ 2 * Nat.succ s := by
          omega
        simpa using Nat.fib_lt_fib_succ hs
  omega

theorem fib_min_length_rep (N : ℕ) (l : List ℕ) (hmem : ∀ x ∈ l, ∃ j, x = Nat.fib (2 * j + 1)) (hsum : l.sum = N) : ∃ l' : List ℕ, (∀ x ∈ l', ∃ j, x = Nat.fib (2 * j + 1)) ∧ l'.sum = N ∧ l'.length ≤ l.length ∧ (∀ l'' : List ℕ, (∀ x ∈ l'', ∃ j, x = Nat.fib (2 * j + 1)) → l''.sum = N → l'.length ≤ l''.length) := by
  classical
  let P : ℕ → Prop := fun n => ∃ l' : List ℕ, (∀ x ∈ l', ∃ j, x = Nat.fib (2 * j + 1)) ∧ l'.sum = N ∧ l'.length = n
  have hP : ∃ n, P n := by
    refine ⟨l.length, l, hmem, hsum, rfl⟩
  let n := Nat.find hP
  have hn : P n := Nat.find_spec hP
  rcases hn with ⟨l', hmem', hsum', hlen'⟩
  refine ⟨l', hmem', hsum', ?_, ?_⟩
  · rw [hlen']
    exact Nat.find_min' hP ⟨l, hmem, hsum, rfl⟩
  · intro l'' hmem'' hsum''
    rw [hlen']
    exact Nat.find_min' hP ⟨l'', hmem'', hsum'', rfl⟩

theorem fib_odd_strictMono: StrictMono (fun j => Nat.fib (2 * j + 1)) := by
  refine strictMono_nat_of_lt_succ ?_
  intro j
  have hrec : Nat.fib ((2 * j + 1) + 2) = Nat.fib (2 * j + 1) + Nat.fib ((2 * j + 1) + 1) := Nat.fib_add_two
  rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, hrec]
  have hpos : 0 < Nat.fib (2 * j + 2) := by
    exact Nat.fib_pos.2 (by omega)
  exact Nat.lt_add_of_pos_right hpos

theorem fib_sum_odd_range (k : ℕ) : Finset.sum (Finset.range (k + 1)) (fun i => Nat.fib (2 * i + 1)) = Nat.fib (2 * k + 2) := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        Finset.sum (Finset.range (k + 2)) (fun i => Nat.fib (2 * i + 1))
            = Finset.sum (Finset.range (k + 1)) (fun i => Nat.fib (2 * i + 1)) + Nat.fib (2 * (k + 1) + 1) := by
                rw [Finset.sum_range_succ]
        _ = Nat.fib (2 * k + 2) + Nat.fib (2 * k + 3) := by
              rw [ih]
              ring_nf
        _ = Nat.fib ((2 * k + 2) + 2) := by
              rw [← Nat.fib_add_two]
        _ = Nat.fib (2 * k + 4) := by
              ring_nf

theorem fib_three_mul_odd (i : ℕ) : 3 * Nat.fib (2 * i + 3) = Nat.fib (2 * i + 5) + Nat.fib (2 * i + 1) := by
  have h1 : Nat.fib (2 * i + 3) = Nat.fib (2 * i + 1) + Nat.fib (2 * i + 2) := by
    convert (Nat.fib_add_two (n := 2 * i + 1)) using 1 <;> omega
  have h2 : Nat.fib (2 * i + 4) = Nat.fib (2 * i + 2) + Nat.fib (2 * i + 3) := by
    convert (Nat.fib_add_two (n := 2 * i + 2)) using 1 <;> omega
  have h3 : Nat.fib (2 * i + 5) = Nat.fib (2 * i + 3) + Nat.fib (2 * i + 4) := by
    convert (Nat.fib_add_two (n := 2 * i + 3)) using 1 <;> omega
  rw [h1, h3, h2, h1]
  ring_nf

theorem fib_three_mul_odd_shifted (j : ℕ) (hj : 1 ≤ j) : 3 * Nat.fib (2 * j + 1) = Nat.fib (2 * j + 3) + Nat.fib (2 * j - 1) := by
  let i := j - 1
  have hj' : 0 < j := Nat.succ_le_iff.mp hj
  have hji : j = i + 1 := by
    dsimp [i]
    simpa [Nat.succ_eq_add_one] using (Nat.succ_pred_eq_of_pos hj').symm
  rw [hji]
  convert fib_three_mul_odd i using 1 <;> omega

theorem fib_shorten_three_odd (j : ℕ) (hj : 1 ≤ j) (l : List ℕ) (hmem : ∀ x ∈ l, ∃ k, x = Nat.fib (2 * k + 1)) (hcount : 3 ≤ l.count (Nat.fib (2 * j + 1))) : ∃ l' : List ℕ, (∀ x ∈ l', ∃ k, x = Nat.fib (2 * k + 1)) ∧ l'.sum = l.sum ∧ l'.length + 1 = l.length := by
  classical
  let a := Nat.fib (2 * j + 1)
  let b := Nat.fib (2 * j + 3)
  let c := Nat.fib (2 * j - 1)
  let l1 := l.erase a
  let l2 := l1.erase a
  let l3 := l2.erase a
  have hcount0 : 3 ≤ l.count a := by
    simpa [a] using hcount
  have hcount1eq : l1.count a = l.count a - 1 := by
    simpa [a, l1] using (List.count_erase_self (l := l) (a := a))
  have hcount1 : 2 ≤ l1.count a := by
    omega
  have hm1 : a ∈ l := by
    by_contra hnot
    have : l.count a = 0 := (List.count_eq_zero (l := l) (a := a)).2 hnot
    omega
  have hm2 : a ∈ l1 := by
    by_contra hnot
    have : l1.count a = 0 := (List.count_eq_zero (l := l1) (a := a)).2 hnot
    omega
  have hcount2eq : l2.count a = l1.count a - 1 := by
    simpa [a, l1, l2] using (List.count_erase_self (l := l1) (a := a))
  have hcount2 : 1 ≤ l2.count a := by
    omega
  have hm3 : a ∈ l2 := by
    by_contra hnot
    have : l2.count a = 0 := (List.count_eq_zero (l := l2) (a := a)).2 hnot
    omega
  have hsum1 : a + l1.sum = l.sum := by
    simpa [a, l1] using (List.sum_erase (l := l) (a := a) hm1)
  have hsum2 : a + l2.sum = l1.sum := by
    simpa [a, l1, l2] using (List.sum_erase (l := l1) (a := a) hm2)
  have hsum3 : a + l3.sum = l2.sum := by
    simpa [a, l2, l3] using (List.sum_erase (l := l2) (a := a) hm3)
  have hlen1 : l1.length + 1 = l.length := by
    simpa [a, l1] using (List.length_erase_add_one (l := l) (a := a) hm1)
  have hlen2 : l2.length + 1 = l1.length := by
    simpa [a, l1, l2] using (List.length_erase_add_one (l := l1) (a := a) hm2)
  have hlen3 : l3.length + 1 = l2.length := by
    simpa [a, l2, l3] using (List.length_erase_add_one (l := l2) (a := a) hm3)
  have hfib : b + c = 3 * a := by
    simpa [a, b, c] using (fib_three_mul_odd_shifted j hj).symm
  refine ⟨b :: c :: l3, ?_, ?_, ?_⟩
  · intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨j + 1, ?_⟩
      have harg : 2 * j + 3 = 2 * (j + 1) + 1 := by
        omega
      dsimp [b]
      rw [harg]
    · rcases hx with rfl | hx
      · refine ⟨j - 1, ?_⟩
        have harg : 2 * j - 1 = 2 * (j - 1) + 1 := by
          omega
        dsimp [c]
        rw [harg]
      · have hx2 : x ∈ l2 := List.mem_of_mem_erase hx
        have hx1 : x ∈ l1 := List.mem_of_mem_erase hx2
        have hx0 : x ∈ l := List.mem_of_mem_erase hx1
        exact hmem x hx0
  · simp only [List.sum_cons]
    omega
  · simp only [List.length_cons]
    omega

theorem fib_two_mul_one: 2 * Nat.fib 1 = Nat.fib 3 := by
  norm_num [Nat.fib]

theorem fib_shorten_two_one (l : List ℕ) (hmem : ∀ x ∈ l, ∃ j, x = Nat.fib (2 * j + 1)) (hcount : 2 ≤ l.count (Nat.fib 1)) : ∃ l' : List ℕ, (∀ x ∈ l', ∃ j, x = Nat.fib (2 * j + 1)) ∧ l'.sum = l.sum ∧ l'.length + 1 = l.length := by
  classical
  let a := Nat.fib 1
  let s : Multiset ℕ := (l : Multiset ℕ)
  have hcount_s : 2 ≤ s.count a := by
    simpa [s, a, Multiset.coe_count] using hcount
  have ha : a ∈ s := by
    exact (Multiset.one_le_count_iff_mem).1 (le_trans (by decide : 1 ≤ 2) hcount_s)
  have hcount_erase : 1 ≤ (s.erase a).count a := by
    rw [Multiset.count_erase_self]
    omega
  have ha' : a ∈ s.erase a := by
    exact (Multiset.one_le_count_iff_mem).1 hcount_erase
  let s' : Multiset ℕ := Nat.fib 3 ::ₘ (s.erase a).erase a
  have hs_toList : s'.toList.sum = s'.sum := by
    simpa using congrArg Multiset.sum (Multiset.coe_toList s')
  have hl_sum : s.sum = l.sum := by
    rfl
  have hl_len : s.card = l.length := by
    simpa [s] using (Multiset.coe_card l)
  have hs'_len : s'.toList.length = s'.card := by
    simpa using (Multiset.length_toList s')
  have hs1 : a + (s.erase a).sum = s.sum := by
    simpa [a] using congrArg Multiset.sum (Multiset.cons_erase ha)
  have hs2 : a + ((s.erase a).erase a).sum = (s.erase a).sum := by
    simpa [a] using congrArg Multiset.sum (Multiset.cons_erase ha')
  have hs_sum : s'.sum = s.sum := by
    calc
      s'.sum = Nat.fib 3 + ((s.erase a).erase a).sum := by simp [s']
      _ = a + (a + ((s.erase a).erase a).sum) := by
        calc
          Nat.fib 3 + ((s.erase a).erase a).sum = (2 * a) + ((s.erase a).erase a).sum := by
            simpa [a] using congrArg (fun n => n + ((s.erase a).erase a).sum) fib_two_mul_one.symm
          _ = a + (a + ((s.erase a).erase a).sum) := by
            simp [two_mul, add_assoc, add_left_comm, add_comm]
      _ = a + (s.erase a).sum := by rw [hs2]
      _ = s.sum := hs1
  have hs_card : s'.card + 1 = s.card := by
    calc
      s'.card + 1 = (((s.erase a).erase a).card + 1) + 1 := by simp [s']
      _ = s.card := by rw [Multiset.card_erase_add_one ha', Multiset.card_erase_add_one ha]
  refine ⟨s'.toList, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : x ∈ s' := (Multiset.mem_toList).1 hx
    simp only [s', Multiset.mem_cons] at hx'
    rcases hx' with rfl | hx'
    · refine ⟨1, ?_⟩
      norm_num
    · have hx'' : x ∈ s := by
        exact Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase hx')
      have : x ∈ l := by
        simpa [s] using hx''
      exact hmem x this
  · calc
      s'.toList.sum = s'.sum := hs_toList
      _ = s.sum := hs_sum
      _ = l.sum := hl_sum
  · calc
      s'.toList.length + 1 = s'.card + 1 := by rw [hs'_len]
      _ = s.card := hs_card
      _ = l.length := hl_len

theorem fib_shortest_reduced (N : ℕ) (l : List ℕ) (hmem : ∀ x ∈ l, ∃ j, x = Nat.fib (2 * j + 1)) (hsum : l.sum = N) (hmin : ∀ l' : List ℕ, (∀ x ∈ l', ∃ j, x = Nat.fib (2 * j + 1)) → l'.sum = N → l.length ≤ l'.length) : l.count (Nat.fib 1) ≤ 1 ∧ (∀ j, 1 ≤ j → l.count (Nat.fib (2 * j + 1)) ≤ 2) := by
  constructor
  · by_contra hbad
    have hcount : 2 ≤ l.count (Nat.fib 1) := by
      omega
    rcases fib_shorten_two_one l hmem hcount with ⟨l', hmem', hsum', hlen'⟩
    have hmin' : l.length ≤ l'.length := by
      apply hmin l' hmem'
      exact hsum'.trans hsum
    omega
  · intro j hj
    by_contra hbad
    have hcount : 3 ≤ l.count (Nat.fib (2 * j + 1)) := by
      omega
    rcases fib_shorten_three_odd j hj l hmem hcount with ⟨l', hmem', hsum', hlen'⟩
    have hmin' : l.length ≤ l'.length := by
      apply hmin l' hmem'
      exact hsum'.trans hsum
    omega

theorem fib_reduce (N : ℕ) (l : List ℕ) (hmem : ∀ x ∈ l, ∃ j, x = Nat.fib (2 * j + 1)) (hsum : l.sum = N) : ∃ l' : List ℕ, (∀ x ∈ l', ∃ j, x = Nat.fib (2 * j + 1)) ∧ l'.sum = N ∧ l'.length ≤ l.length ∧ l'.count (Nat.fib 1) ≤ 1 ∧ (∀ j, 1 ≤ j → l'.count (Nat.fib (2 * j + 1)) ≤ 2) := by
  rcases fib_min_length_rep N l hmem hsum with ⟨l', hmem', hsum', hlen, hmin⟩
  rcases fib_shortest_reduced N l' hmem' hsum' hmin with ⟨hcount1, hcount2⟩
  exact ⟨l', hmem', hsum', hlen, hcount1, hcount2⟩

theorem fin1_multiset_eq_replicate_card (m : abelian.FreeAbelianMonoid 1) : m = Multiset.replicate m.card (0 : Fin 1) := by
  refine Multiset.induction_on m ?_ ?_
  · rfl
  · intro a s ih
    fin_cases a
    rw [ih]
    simp

theorem list_nat_mem_le_sum {l : List ℕ} {x : ℕ} (hx : x ∈ l) : x ≤ l.sum := by
  induction l with
  | nil =>
      cases hx
  | cons a t ih =>
      simp only [List.mem_cons] at hx
      simp only [List.sum_cons]
      rcases hx with rfl | hx
      · exact Nat.le_add_right _ _
      · exact le_trans (ih hx) (Nat.le_add_left _ _)

theorem list_sum_eq_sum_count_mul (l : List ℕ) : l.sum = Finset.sum l.toFinset (fun x => l.count x * x) := by
  simpa [Multiset.nsmul_singleton, nsmul_eq_mul] using
    congrArg Multiset.sumAddMonoidHom (Multiset.toFinset_sum_count_nsmul_eq (s := (l : Multiset ℕ))).symm

theorem fib_reduced_lt (s : ℕ) (l : List ℕ) (hmem : ∀ x ∈ l, ∃ j, j < s ∧ x = Nat.fib (2 * j + 1)) (h0 : l.count (Nat.fib 1) ≤ 1) (h2 : ∀ j, 1 ≤ j → l.count (Nat.fib (2 * j + 1)) ≤ 2) : l.sum < Nat.fib (2 * s + 2) := by
  classical
  cases s with
  | zero =>
      cases l with
      | nil => simp
      | cons a t =>
          exfalso
          rcases hmem a (by simp) with ⟨j, hj, hEq⟩
          omega
  | succ s =>
      let F : ℕ → ℕ := fun j => Nat.fib (2 * j + 1)
      have hF0 : F 0 = 1 := by
        simp [F, Nat.fib_one]
      have hsubset : l.toFinset ⊆ (Finset.range (s + 1)).image F := by
        intro x hx
        have hx' : x ∈ l := by simpa using hx
        rcases hmem x hx' with ⟨j, hj, rfl⟩
        refine Finset.mem_image.mpr ?_
        exact ⟨j, by simpa using hj, rfl⟩
      have hsum0 : l.sum = ∑ x ∈ l.toFinset, l.count x * x := list_sum_eq_sum_count_mul l
      have hle0 :
          ∑ x ∈ l.toFinset, l.count x * x ≤ ∑ x ∈ (Finset.range (s + 1)).image F, l.count x * x :=
        Finset.sum_le_sum_of_subset hsubset
      have hFstrict : StrictMono F := fib_odd_strictMono
      have hFinj : Set.InjOn F (Finset.range (s + 1)) := hFstrict.injective.injOn
      have himage :
          ∑ x ∈ (Finset.range (s + 1)).image F, l.count x * x = ∑ j ∈ Finset.range (s + 1), l.count (F j) * F j := by
        simpa using (Finset.sum_image (s := Finset.range (s + 1)) (g := F) (f := fun x => l.count x * x) hFinj)
      have hle1 :
          ∑ j ∈ Finset.range (s + 1), l.count (F j) * F j ≤
            ∑ j ∈ Finset.range (s + 1), (if j = 0 then 1 else 2) * F j := by
        exact Finset.sum_le_sum (by
          intro j hj
          by_cases hj0 : j = 0
          · subst hj0
            calc
              l.count (F 0) * F 0 = F 0 * l.count (F 0) := by ac_rfl
              _ ≤ F 0 * 1 := Nat.mul_le_mul_left _ h0
              _ = (if 0 = 0 then 1 else 2) * F 0 := by simp [Nat.mul_comm]
          · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
            calc
              l.count (F j) * F j = F j * l.count (F j) := by ac_rfl
              _ ≤ F j * 2 := Nat.mul_le_mul_left _ (h2 j hj1)
              _ = (if j = 0 then 1 else 2) * F j := by simp [hj0, Nat.mul_comm])
      have hupsplit :
          ∑ j ∈ Finset.range (s + 1), (if j = 0 then 1 else 2) * F j = F 0 + ∑ j ∈ Finset.range s, 2 * F (j + 1) := by
        rw [Finset.range_add_one']
        simp [F]
      have hsumF : ∑ j ∈ Finset.range (s + 1), F j = Nat.fib (2 * s + 2) := by
        simpa [F] using fib_sum_odd_range s
      have hsumFsplit :
          ∑ j ∈ Finset.range (s + 1), F j = F 0 + ∑ j ∈ Finset.range s, F (j + 1) := by
        rw [Finset.range_add_one']
        simp [F]
      have htail : ∑ j ∈ Finset.range s, F (j + 1) = Nat.fib (2 * s + 2) - 1 := by
        have htmp : F 0 + ∑ j ∈ Finset.range s, F (j + 1) = Nat.fib (2 * s + 2) := by
          rw [← hsumFsplit, hsumF]
        omega
      have hupper :
          F 0 + ∑ j ∈ Finset.range s, 2 * F (j + 1) = 1 + 2 * (Nat.fib (2 * s + 2) - 1) := by
        rw [hF0, ← Finset.mul_sum, htail]
      have hrec : Nat.fib (2 * s + 4) = Nat.fib (2 * s + 2) + Nat.fib (2 * s + 3) := by
        simpa [show 2 * s + 4 = (2 * s + 2) + 2 by omega, show 2 * s + 3 = (2 * s + 2) + 1 by omega] using
          (Nat.fib_add_two (n := 2 * s + 2))
      have hfinal : 1 + 2 * (Nat.fib (2 * s + 2) - 1) < Nat.fib (2 * s + 4) := by
        rw [hrec]
        have hmon : Nat.fib (2 * s + 2) ≤ Nat.fib (2 * s + 3) := Nat.fib_le_fib_succ
        have hpos : 0 < Nat.fib (2 * s + 2) := by
          exact (Nat.fib_pos).2 (by omega)
        omega
      calc
        l.sum = ∑ x ∈ l.toFinset, l.count x * x := hsum0
        _ ≤ ∑ x ∈ (Finset.range (s + 1)).image F, l.count x * x := hle0
        _ = ∑ j ∈ Finset.range (s + 1), l.count (F j) * F j := himage
        _ ≤ ∑ j ∈ Finset.range (s + 1), (if j = 0 then 1 else 2) * F j := hle1
        _ = F 0 + ∑ j ∈ Finset.range s, 2 * F (j + 1) := hupsplit
        _ = 1 + 2 * (Nat.fib (2 * s + 2) - 1) := hupper
        _ < Nat.fib (2 * s + 4) := hfinal
        _ = Nat.fib (2 * (s + 1) + 2) := by
          have h : 2 * s + 4 = 2 * (s + 1) + 2 := by omega
          simpa [h]

theorem fib_gap (s : ℕ) : ¬ ∃ l : List ℕ, l.length ≤ s ∧ (∀ x ∈ l, ∃ j, x = Nat.fib (2 * j + 1)) ∧ l.sum = Nat.fib (2 * s + 2) := by
  induction s with
  | zero =>
      intro h
      rcases h with ⟨l, hlen, hmem, hsum⟩
      cases l with
      | nil =>
          simp at hsum
      | cons a t =>
          simp at hlen
  | succ s ih =>
      intro h
      rcases h with ⟨l, hlen, hmem, hsum⟩
      rcases fib_reduce (Nat.fib (2 * Nat.succ s + 2)) l hmem hsum with
        ⟨l', hmem', hsum', hlen', hcount1, hcount2⟩
      have hlen'' : l'.length ≤ Nat.succ s := le_trans hlen' hlen
      let a : ℕ := Nat.fib (2 * Nat.succ s + 1)
      have hbound : ∀ {x}, x ∈ l' → ∃ j, j ≤ Nat.succ s ∧ x = Nat.fib (2 * j + 1) := by
        intro x hx
        rcases hmem' x hx with ⟨j, rfl⟩
        have hle_sum : Nat.fib (2 * j + 1) ≤ Nat.fib (2 * Nat.succ s + 2) := by
          simpa [hsum'] using (list_nat_mem_le_sum (l := l') (x := Nat.fib (2 * j + 1)) hx)
        have hjnot : ¬ Nat.succ (Nat.succ s) ≤ j := by
          intro hjge
          have hltfib : Nat.fib (2 * Nat.succ s + 2) < Nat.fib (2 * Nat.succ (Nat.succ s) + 1) := by
            change Nat.fib (2 * Nat.succ s + 2) < Nat.fib ((2 * Nat.succ s + 2) + 1)
            exact Nat.fib_lt_fib_succ (by omega)
          have hmono : Nat.fib (2 * Nat.succ (Nat.succ s) + 1) ≤ Nat.fib (2 * j + 1) :=
            fib_odd_strictMono.monotone hjge
          exact (Nat.not_le_of_lt hltfib) (le_trans hmono hle_sum)
        have hj : j ≤ Nat.succ s := by
          omega
        exact ⟨j, hj, rfl⟩
      have ha_mem : a ∈ l' := by
        by_contra ha_not
        have halllt : ∀ x ∈ l', ∃ j, j < Nat.succ s ∧ x = Nat.fib (2 * j + 1) := by
          intro x hx
          rcases hbound hx with ⟨j, hjle, rfl⟩
          have hjne : j ≠ Nat.succ s := by
            intro hjeq
            apply ha_not
            simpa [a, hjeq] using hx
          have hjlt : j < Nat.succ s := by
            omega
          exact ⟨j, hjlt, rfl⟩
        have hlt := fib_reduced_lt (Nat.succ s) l' halllt hcount1 hcount2
        omega
      have hlen_erase : (l'.erase a).length ≤ s := by
        have hlenerase : (l'.erase a).length + 1 = l'.length := List.length_erase_add_one ha_mem
        omega
      have hmem_erase : ∀ x ∈ l'.erase a, ∃ j, x = Nat.fib (2 * j + 1) := by
        intro x hx
        exact hmem' x (List.mem_of_mem_erase hx)
      have hsum_erase : a + (l'.erase a).sum = Nat.fib (2 * Nat.succ s + 2) := by
        simpa [a, hsum'] using (List.sum_erase (l := l') (a := a) ha_mem)
      have hfib : Nat.fib (2 * Nat.succ s + 2) = Nat.fib (2 * Nat.succ s) + a := by
        simpa [a, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
          (Nat.fib_add_two (n := 2 * Nat.succ s))
      have hsum_erase' : (l'.erase a).sum = Nat.fib (2 * Nat.succ s) := by
        have htmp : a + (l'.erase a).sum = a + Nat.fib (2 * Nat.succ s) := by
          calc
            a + (l'.erase a).sum = Nat.fib (2 * Nat.succ s + 2) := hsum_erase
            _ = Nat.fib (2 * Nat.succ s) + a := hfib
            _ = a + Nat.fib (2 * Nat.succ s) := by ac_rfl
        exact Nat.add_left_cancel htmp
      have hsum_erase'' : (l'.erase a).sum = Nat.fib (2 * s + 2) := by
        simpa [Nat.succ_eq_add_one, Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hsum_erase'
      exact ih ⟨l'.erase a, hlen_erase, hmem_erase, hsum_erase''⟩

theorem mem_ball_A1_iff_card_le (r : ℕ) (m : abelian.FreeAbelianMonoid 1) : m ∈ abelian.Ball r (abelian.A 1) ↔ m.card ≤ r := by
  have hsum_card :
      ∀ l : List (abelian.FreeAbelianMonoid 1),
        (∀ x ∈ l, x ∈ abelian.A 1) → l.sum.card = l.length := by
    intro l
    induction l with
    | nil =>
        intro hA
        simp
    | cons x xs ih =>
        intro hA
        have hxA : x ∈ abelian.A 1 := hA x (by simp)
        have hxsA : ∀ y ∈ xs, y ∈ abelian.A 1 := by
          intro y hy
          exact hA y (by simp [hy])
        rcases hxA with ⟨i, rfl⟩
        simp [List.sum_cons, Multiset.card_add, ih hxsA]
  constructor
  · intro hm
    rcases hm with ⟨l, hlr, hA, hsum⟩
    have hcard : l.sum.card = l.length := hsum_card l hA
    rw [← hsum, hcard]
    exact hlr
  · intro hm
    let l : List (abelian.FreeAbelianMonoid 1) :=
      List.replicate m.card (Multiset.replicate 1 (0 : Fin 1))
    have hA : ∀ x ∈ l, x ∈ abelian.A 1 := by
      intro x hx
      have hxr : m.card ≠ 0 ∧ x = Multiset.replicate 1 (0 : Fin 1) := by
        simpa [l] using hx
      rw [hxr.2]
      exact ⟨0, rfl⟩
    refine ⟨l, ?_, hA, ?_⟩
    · simp [l, hm]
    · have hcard : l.sum.card = l.length := hsum_card l hA
      rw [fin1_multiset_eq_replicate_card l.sum, fin1_multiset_eq_replicate_card m]
      rw [hcard]
      simp [l]

theorem mem_ball_fib_iff (s : ℕ) (m : abelian.FreeAbelianMonoid 1) : m ∈ abelian.Ball s (fibMacros ∪ abelian.A 1) ↔ ∃ l : List ℕ, l.length ≤ s ∧ (∀ x ∈ l, ∃ j, x = Nat.fib (2 * j + 1)) ∧ l.sum = m.card := by
  constructor
  · intro hm
    rcases hm with ⟨L, hLlen, hLmem, hLsum⟩
    refine ⟨L.map Multiset.card, ?_, ?_, ?_⟩
    · simpa using hLlen
    · intro x hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : y ∈ ({ m | ∃ j : ℕ, m = Multiset.replicate (Nat.fib (2 * j + 1)) (0 : Fin 1) } : Set (abelian.FreeAbelianMonoid 1)) := by
        rw [← fibMacros_union_A]
        exact hLmem y hy
      rcases hy' with ⟨j, rfl⟩
      exact ⟨j, by simpa only [Multiset.card_replicate]⟩
    · have hcardsum : ∀ L : List (abelian.FreeAbelianMonoid 1), (L.map Multiset.card).sum = (L.sum).card := by
        intro L
        induction L with
        | nil => rfl
        | cons a t ih =>
            simpa only [List.map_cons, List.sum_cons, Multiset.card_add, ih]
      exact (hcardsum L).trans (congrArg Multiset.card hLsum)
  · rintro ⟨l, hl_len, hl_mem, hl_sum⟩
    refine ⟨l.map (fun x => Multiset.replicate x (0 : Fin 1)), ?_, ?_, ?_⟩
    · simpa using hl_len
    · intro x hx
      rcases List.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : Multiset.replicate y (0 : Fin 1) ∈ ({ m | ∃ j : ℕ, m = Multiset.replicate (Nat.fib (2 * j + 1)) (0 : Fin 1) } : Set (abelian.FreeAbelianMonoid 1)) := by
        rcases hl_mem y hy with ⟨j, rfl⟩
        exact ⟨j, rfl⟩
      rw [fibMacros_union_A]
      exact hy'
    · have hcardsum : ∀ l : List ℕ, ((l.map (fun x => Multiset.replicate x (0 : Fin 1))).sum).card = l.sum := by
        intro l
        induction l with
        | nil => rfl
        | cons a t ih =>
            simpa only [List.map_cons, List.sum_cons, Multiset.card_add, Multiset.card_replicate, ih]
      calc
        (l.map (fun x => Multiset.replicate x (0 : Fin 1))).sum
            = Multiset.replicate (((l.map (fun x => Multiset.replicate x (0 : Fin 1))).sum).card) (0 : Fin 1) := by
              exact fin1_multiset_eq_replicate_card _
        _ = Multiset.replicate l.sum (0 : Fin 1) := by rw [hcardsum l]
        _ = Multiset.replicate m.card (0 : Fin 1) := by rw [hl_sum]
        _ = m := by exact (fin1_multiset_eq_replicate_card m).symm

theorem fib_expansion_iff (s r : ℕ) : abelian.Ball r (abelian.A 1) ⊆ abelian.Ball s (fibMacros ∪ abelian.A 1) ↔ r ≤ Nat.fib (2 * s + 2) - 1 := by
  constructor
  · intro hsub
    by_contra hle
    have hfib_le : Nat.fib (2 * s + 2) ≤ r := by
      omega
    let m0 : abelian.FreeAbelianMonoid 1 := Multiset.replicate (Nat.fib (2 * s + 2)) (0 : Fin 1)
    have hm0A : m0 ∈ abelian.Ball r (abelian.A 1) := by
      rw [mem_ball_A1_iff_card_le]
      simp [m0, hfib_le]
    have hm0B : m0 ∈ abelian.Ball s (fibMacros ∪ abelian.A 1) := hsub hm0A
    rw [mem_ball_fib_iff] at hm0B
    have hm0card : m0.card = Nat.fib (2 * s + 2) := by
      simp [m0]
    apply fib_gap s
    rcases hm0B with ⟨l, hlens, hmem, hsum⟩
    refine ⟨l, hlens, hmem, ?_⟩
    simpa [hm0card] using hsum
  · intro hr m hmA
    rw [mem_ball_A1_iff_card_le] at hmA
    rw [mem_ball_fib_iff]
    set N : ℕ := Nat.fib (2 * s + 2)
    have hrN : r ≤ N - 1 := by
      simpa [N] using hr
    have hNpos : 0 < N := by
      have h : 0 < 2 * s + 2 := by omega
      simpa [N] using (Nat.fib_pos).2 h
    have hlt : m.card < N := by
      omega
    have hlt' : m.card < Nat.fib (2 * s + 2) := by
      simpa [N] using hlt
    rcases fib_coverage s m.card hlt' with ⟨l, hlens, hmem, hsum⟩
    exact ⟨l, hlens, hmem, hsum⟩

theorem fib_expansion (s : ℕ) : (abelian.Ball (Nat.fib (2 * s + 2) - 1) (abelian.A 1) ⊆ abelian.Ball s (fibMacros ∪ abelian.A 1)) ∧ (¬ (abelian.Ball (Nat.fib (2 * s + 2)) (abelian.A 1) ⊆ abelian.Ball s (fibMacros ∪ abelian.A 1))) := by
  constructor
  · exact (fib_expansion_iff s (Nat.fib (2 * s + 2) - 1)).2 le_rfl
  · intro h
    have hle : Nat.fib (2 * s + 2) ≤ Nat.fib (2 * s + 2) - 1 :=
      (fib_expansion_iff s (Nat.fib (2 * s + 2))).1 h
    have hn : 0 < Nat.fib (2 * s + 2) := by
      rw [Nat.fib_pos]
      omega
    omega
