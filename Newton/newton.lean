import Newton.Reverse
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial

open Polynomial

lemma real_split_of_deriv_of_real_split {P: ℝ[X]} (hP: Splits (RingHom.id ℝ) P) : Splits (RingHom.id ℝ) (derivative P) := by
  rw [splits_iff_card_roots] at hP ⊢
  apply le_antisymm (card_roots' (derivative P)) ((natDegree_derivative_le P).trans _)
  rw [<-hP]
  convert Nat.sub_le_sub_right (card_roots_le_derivative P) 1

private def newton_hyp (n i : ℕ) := ∀ P: ℝ[X], P.natDegree = n → Splits (RingHom.id ℝ) P → (i+2) * (n-i) * (P.coeff i) * (P.coeff (i+2)) ≤ (i+1) * (n-i-1) * (P.coeff (i+1))^2

private lemma newton_hyp_triv {n i : ℕ} (h: i+2 > n): newton_hyp n i := by
  intro P hdeg _
  have : P.natDegree < i+2 := by rwa [hdeg]
  simp [coeff_eq_zero_of_natDegree_lt this]
  by_cases h' : n = i+1
  . simp [h']
  have : P.natDegree < i+1 := by rw [hdeg]; contrapose! h'; linarith
  simp [coeff_eq_zero_of_natDegree_lt this]

private lemma newton_hyp_refl {i:ℕ} (hn: newton_hyp (i+2) i) : newton_hyp (i+2) 0 := by
  intro P hdeg hsplit
  replace hsplit := split_of_reverse hsplit
  simp
  rcases (Nat.eq_zero_or_pos P.natTrailingDegree).symm with hP | hP
  . rw [coeff_eq_zero_of_lt_natTrailingDegree hP]
    simp
    have : 0 < (i:ℝ)+2-1 := by linarith
    positivity
  have hdeg' : P.reverse.natDegree = i+2 := by
    rw [reverse_natDegree, hdeg, hP]; simp
  replace hn := hn (reverse P) hdeg' hsplit
  rw [coeff_reverse, coeff_reverse, coeff_reverse, hdeg, revAt_le (by linarith), revAt_le (by linarith), revAt_le (by linarith)] at hn
  push_cast at hn
  simp at hn
  convert hn using 1 <;> ring

private lemma newton_hyp_induct {n i:ℕ} (hn: newton_hyp n i) : newton_hyp (n+1) (i+1) := by
  intro P hdeg hsplit
  replace hsplit := real_split_of_deriv_of_real_split hsplit
  replace hdeg : P.derivative.natDegree = n := by
    apply natDegree_eq_of_le_of_coeff_ne_zero
    . convert natDegree_derivative_le P
      simp [hdeg]
    rw [coeff_derivative, <-hdeg]
    simp
    intro h
    rcases h with h | h
    . simp [h] at hdeg; linarith
    linarith
  replace hn := hn (derivative P) hdeg hsplit
  rw [coeff_derivative, coeff_derivative, coeff_derivative] at hn
  push_cast at hn ⊢
  rw [<-mul_le_mul_left (show 0 < i+(1:ℝ) by positivity), <-mul_le_mul_left (show 0 < i+(2:ℝ) by positivity)]
  convert hn using 1 <;> ring

private lemma newton_hyp_base : newton_hyp 2 0 := by
  intro P hdeg hsplit
  have := eq_prod_roots_of_splits_id hsplit
  rw [<- splits_iff_card_roots.mp hsplit, Multiset.card_eq_two] at hdeg
  rcases hdeg with ⟨ x, y, hxy ⟩
  rw [hxy] at this
  simp at this
  rw [this]
  simp
  ring_nf
  rw [mul_assoc, mul_assoc, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simp [Polynomial.coeff_X, Polynomial.coeff_C]
  rw [(show (-x - y)^2 = x*(y*4) + (x-y)^2 by ring)]
  simp; positivity

private lemma newton_ineq_prelim (n:ℕ) : ∀ i : ℕ, newton_hyp n i := by
  apply Nat.strong_induction_on n (p := fun n => ∀ i : ℕ, newton_hyp n i)
  intro n hind i
  rcases le_or_gt n 1 with h0 | h0
  . apply newton_hyp_triv
    linarith
  replace h0 : 2 ≤ n := by linarith
  rcases Nat.le.dest h0 with ⟨ n, rfl ⟩
  by_cases hi : i = 0
  . rw [add_comm, hi]
    apply newton_hyp_refl
    by_cases hn : n = 0
    . rw [hn]; simp; exact newton_hyp_base
    replace hn : 1 ≤ n := by contrapose! hn; linarith
    rcases Nat.le.dest hn with ⟨ n, rfl ⟩
    convert newton_hyp_induct (hind (n+2) (by linarith) n) using 1 <;> abel
  replace hi : 1 ≤ i := by contrapose! hi; linarith
  rcases Nat.le.dest hi with ⟨ j, rfl ⟩
  rw [add_comm 1 j, (show 2+n = n+1+1 by ring)]
  exact newton_hyp_induct ((hind (n+1) (by linarith)) j)

open Multiset

@[simp]
lemma Multiset.esymm_eq_zero {i:ℕ} {x : Multiset ℝ} (hx: Multiset.card x < i) : esymm x i = 0 := by
  unfold esymm
  simp [hx]

/-- A division-free form of the Newton inequalities, with no constraints on i. -/
lemma newton_ineq' (i n: ℕ) {x : Multiset ℝ} (hx: Multiset.card x = n) : (i+2) * (n-i) * (esymm x i) * (esymm x (i+2)) ≤ (i+1) * (n-i-1) * (esymm x (i+1))^2 := by
  rcases (le_or_gt (i+2) n).symm with h | h
  . rcases (le_or_gt (i+1) n).symm with h' | h'
    . rw [<-hx] at h h'
      simp [h, h']
    have : n=i+1 := by linarith
    rw [<-hx] at h
    rw [this]
    simp [h]
  rcases Nat.le.dest h with ⟨ m, rfl ⟩
  let P : ℝ[X] := prod (map (fun (a : ℝ) => X - C a) x)
  have hP : P.leadingCoeff = 1 := by
    apply Monic.leadingCoeff
    apply monic_multiset_prod_of_monic
    intro a _
    exact monic_X_sub_C a
  have hsplit : P.Splits (RingHom.id ℝ) := by
    apply splits_of_exists_multiset (s := x)
    simp [hP]
  have hdeg : P.natDegree = i + 2 + m := by
    rw [natDegree_multiset_prod]
    simp [hx]
    by_contra this
    simp at this
    rcases this with ⟨ a, _, hxa ⟩
    have := Polynomial.natDegree_X_sub_C a
    simp [hxa] at this
  have := newton_ineq_prelim (i+2+m) m P hdeg hsplit
  have hd {j:ℕ} (hj: j ≤ i+2+m) : P.coeff j = (-1)^(i+2+m-j) * (esymm x (i+2+m-j)) := by
     rw [<-hx] at hj ⊢
     rw [prod_X_sub_C_coeff x hj]
  have hd0 : m ≤ i+2+m := by linarith
  have hd1 : m+1 ≤ i+2+m := by linarith
  have hd2 : m+2 ≤ i+2+m := by linarith
  rw [hd hd0, hd hd1,hd hd2] at this
  have h1 : i+2+m - (m+2) = i := by zify [hd2]; ring
  have h2 : i+2+m - (m+1) = i+1 := by zify [hd1]; ring
  simp [hx, h1, h2] at this
  convert this using 1
  . have (a b c d e f : ℝ) : a * b * (c * d) * (e * f) = b * a * f * d * (c * e) := by ring
    rw [this, <-pow_add, <-mul_one (_ * esymm x (i+2))]
    congr
    . push_cast; abel
    rw [(show i+2+i = 2*(i+1) by ring), pow_mul]
    simp
  have (a b c d:ℝ) : a * b * (c * d)^2 = b * a * d^2 * c^2 := by ring
  rw [this, <-pow_mul, mul_comm _ 2, pow_mul]
  push_cast; simp; left; ring


/-- A more traditional form of the Newton inequalities. -/
lemma newton_ineq {i n: ℕ} (hi: i+2 ≤ n) {x : Multiset ℝ} (hx: Multiset.card x = n) : (esymm x i / Nat.choose n i) * (esymm x (i+2) / Nat.choose n (i+2)) ≤ (esymm x (i+1) / Nat.choose n (i+1))^2 := by
  have {k : ℕ} (hk: k ≤ n): ((Nat.choose n k): ℝ) = Nat.factorial n / (Nat.factorial k * Nat.factorial (n-k)) := by
    rw [<-Nat.choose_mul_factorial_mul_factorial hk]
    push_cast; field_simp; ring
  rw [this (by linarith), this (by linarith), this (by linarith)]
  field_simp
  rw [<-sq]
  apply div_le_div_of_le_of_nonneg _ (by positivity)
  have hi' : i+1 ≤ n := by linarith
  have hi'' : i ≤ n := by linarith
  have hf1 : Nat.factorial (i+1) = (i+1) * Nat.factorial i := Nat.factorial_succ i
  have hf2 : Nat.factorial (i+2) = (i+2) * Nat.factorial (i+1) := by convert Nat.factorial_succ (i+1) <;> ring
  have hf3 : Nat.factorial (n-(i+1)) = (n-(i+1)) * Nat.factorial (n-(i+2)) := by convert Nat.factorial_succ (n-(i+2)) using 2 <;> zify [hi, hi'] <;> ring
  have hf4 : Nat.factorial (n-i) = (n-i) * Nat.factorial (n-(i+1)) := by convert Nat.factorial_succ (n-(i+1)) using 2 <;> zify [hi', hi''] <;> ring
  rw [sq]
  nth_rewrite 1 [hf1]
  nth_rewrite 1 [hf3]
  rw [hf2, hf4]
  push_cast
  have (a b c d e f g h: ℝ): a*(b*(c*d))*(e*((f*g)*h)) = f*c*a*e*(b*g*h*d) := by ring
  rw [this]
  have (a b c d e f g: ℝ): a*((b*c)*(d*e))*(a*(f*g)) = b*d*a^2*(c*f*e*g) := by ring
  rw [this]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  convert newton_ineq' i n hx
  . zify [hi'']
  zify [hi']; ring
