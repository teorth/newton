import Mathlib.Data.Real.Basic
import Mathlib.Data.Polynomial.Splits

namespace Polynomial

@[simp]
theorem reverse_one (R : Type u_1) [Semiring R] : (1 : R[X]).reverse = 1 := by
  convert reverse_C (R := R) 1

@[simp]
theorem reverse_X (R : Type u_1) [Semiring R] : (X : R[X]).reverse = 1 := by
  rw [<-one_mul X, reverse_mul_X 1, reverse_one]

@[simp]
lemma reverse_sub_C {R : Type u_1} [Ring R] (p : R[X]) (t : R) :
(p - C t).reverse = p.reverse - (C t) * X ^ p.natDegree := by
  change (p + -C t).reverse  = p.reverse + -(C t * X ^ p.natDegree)
  rw [<-C_neg, neg_mul_eq_neg_mul, <-C_neg]
  exact reverse_add_C p (-t)

/-- Reflection is an involution. -/
@[simp]
lemma reflect_reflect {R : Type u_1} [Ring R] (p : R[X]) (n : ℕ) : (p.reflect n).reflect n = p := by
  rcases p with ⟨ f ⟩
  simp [reflect]
  apply Finsupp.ext
  intro i
  conv_lhs => rw [<-Polynomial.revAt_invol (N := n) (i := i)]
  rw [Finsupp.embDomain_apply, Finsupp.embDomain_apply]

/-- Reversion is an involution if the trailing degree vanishes. -/
@[simp]
lemma reverse_reverse {R : Type u_1} [Ring R] (p : R[X]) (hp: p.natTrailingDegree = 0) : p.reverse.reverse = p := by
  have := p.reverse_natDegree
  simp [hp] at this
  unfold reverse at this ⊢
  rw [this]
  exact p.reflect_reflect _

@[simp]
lemma natTrailingDegree_eq_zero_iff {R : Type u_1} [Semiring R] {P: R[X]} : P.natTrailingDegree = 0 ↔ P.coeff 0 ≠ 0 ∨ P = 0:= by
  by_cases h0 : P = 0
  . simp [h0]
  constructor
  . intro h; left
    conv_lhs => rw [<- h]
    change P.trailingCoeff ≠ 0
    simp [h0]
  simp [h0]
  intro h
  linarith [natTrailingDegree_le_of_ne_zero h]

lemma natTrailingDegree_eq_rootMultiplicity {k:Type*} [Field k] (P: k[X]) : P.natTrailingDegree = P.rootMultiplicity 0 := by
  by_cases h0 : P = 0
  . simp [h0]
  rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd P h0 0 with ⟨ Q, hQ ⟩
  simp at hQ
  set m := P.rootMultiplicity 0
  rw [hQ.1, mul_comm, natTrailingDegree_mul_X_pow]
  . simp
    contrapose! hQ
    intro _
    exact X_dvd_iff.mpr hQ.1
  contrapose! hQ
  simp [hQ]

/-- Reversing a polynomial twice removes all factors of `X`. -/
lemma reverse_reverse' {k:Type*} [Field k] (P: k[X]) : P.reverse.reverse * X^P.natTrailingDegree = P := by
  by_cases h0 : P = 0
  . simp [h0]
  rw [natTrailingDegree_eq_rootMultiplicity]
  rcases exists_eq_pow_rootMultiplicity_mul_and_not_dvd P h0 0 with ⟨ Q, hQ ⟩
  simp at hQ
  set m := P.rootMultiplicity 0
  rw [hQ.1, reverse_X_pow_mul, mul_comm]
  congr
  apply reverse_reverse
  simp
  left; contrapose! hQ; intro _
  exact X_dvd_iff.mpr hQ

/-- Reversing a polynomial three times is the same as reversing it once. -/
@[simp]
lemma reverse_reverse_reverse {k:Type*} [Field k] (P: k[X]) : P.reverse.reverse.reverse = P.reverse := by
  conv_rhs => rw [<- P.reverse_reverse', reverse_mul_X_pow]

/-- Reversion preserves polynomial division -/
lemma reverse_dvd_of_domain {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]} (hfg: f ∣ g) : f.reverse ∣  g.reverse := by
  rcases exists_eq_mul_right_of_dvd hfg with ⟨h, rfl⟩
  simp only [reverse_mul_of_domain, dvd_mul_right]

@[simp]
lemma reverse_pow_of_domain {R:Type*} [CommRing R] [IsDomain R] (f : R[X]) (n: ℕ) : (f^n).reverse = f.reverse^n := by
  induction' n with n hn
  . simp only [Nat.zero_eq, pow_zero, reverse_one]
  rw [<-Nat.add_one, pow_succ, pow_succ, reverse_mul_of_domain, hn]

lemma rootMultiplicity_eq_multiplicity' {R : Type u} [CommRing R] [DecidableEq R] [DecidableRel fun (x x_1 : Polynomial R) => x ∣ x_1] {p : R[X]} (a : R) (hp: p ≠ 0) : p.rootMultiplicity a = multiplicity (X - C a) p := by
  rw [p.rootMultiplicity_eq_multiplicity a]
  simp only [hp, dite_false, PartENat.natCast_get]

--superseded by rootMultiplicity_of_reverse_eq
private lemma rootMultiplicity_of_reverse_ge {k:Type*} [Field k] (P: k[X]) {a:k} (ha: a ≠ 0) : P.reverse.rootMultiplicity a⁻¹ ≥ P.rootMultiplicity a := by
  by_cases h0 : P = 0
  . simp only [h0, reverse_zero, rootMultiplicity_zero, le_refl]
  have := reverse_dvd_of_domain (pow_rootMultiplicity_dvd P a)
  simp only [reverse_pow_of_domain, reverse_sub_C, reverse_X, natDegree_X, pow_one, ne_eq, rootMultiplicity_eq_zero_iff,
    IsRoot.def, not_forall, exists_prop] at this
  have hp : P.reverse ≠ 0 := by simp only [ne_eq, reverse_eq_zero, h0, not_false_eq_true]
  classical
  rw [ge_iff_le, <-PartENat.coe_le_coe, rootMultiplicity_eq_multiplicity' a⁻¹ hp]
  apply multiplicity.le_multiplicity_of_pow_dvd  (dvd_trans (pow_dvd_pow_of_dvd (Dvd.intro (-C a) _) _) this)
  ring_nf
  rw [<-Polynomial.C_mul, inv_mul_cancel ha]
  simp only [X_mul_C, map_one]; abel

/-- Reversion preserves root multiplicities. -/
lemma rootMultiplicity_of_reverse_eq {k:Type*} [Field k] (P: k[X]) {a:k} (ha: a ≠ 0) : P.reverse.rootMultiplicity a⁻¹ = P.rootMultiplicity a := by
  by_cases h0 : P = 0
  . simp [h0]
  apply LE.le.antisymm
  . rw [<-ge_iff_le]
    convert P.reverse.rootMultiplicity_of_reverse_ge  (inv_ne_zero ha) using 1
    conv_lhs => rw [<- P.reverse_reverse']
    rw [rootMultiplicity_mul]
    simp [ha]
    rw [mul_ne_zero_iff]
    simp [h0]
    intro hX
    contrapose! hX
    exact X_ne_zero
  exact P.rootMultiplicity_of_reverse_ge ha

/-- Reversion preserves the number of non-zero roots. -/
lemma card_roots_of_reverse {k:Type*} [Field k] (P: k[X]) : Multiset.card P.reverse.roots + P.natTrailingDegree = Multiset.card P.roots := by
  by_cases h0 : P = 0
  . simp only [h0, reverse_zero, roots_zero, map_zero, natTrailingDegree_zero, add_zero]
  classical
  symm
  rw [<-Multiset.toFinset_sum_count_eq, <-Multiset.toFinset_sum_count_eq, <-Finset.sum_insert_of_eq_zero_if_not_mem (a:=0), <-Finset.add_sum_erase (a:=0), add_comm]
  rotate_left
  . exact Finset.mem_insert_self 0 _
  . simp; tauto
  simp [natTrailingDegree_eq_rootMultiplicity]
  let g := fun (a : k) ↦ a⁻¹
  have : P.reverse.roots.toFinset = (Finset.erase P.roots.toFinset 0).image g := by
    ext a
    by_cases h : a = 0
    . simp only [h, Multiset.mem_toFinset, mem_roots', ne_eq, reverse_eq_zero, h0,
      not_false_eq_true, true_and, Finset.mem_image, Finset.mem_erase, inv_eq_zero,
      exists_eq_right, not_true_eq_false, false_and, iff_false, <-rootMultiplicity_pos,<-natTrailingDegree_eq_rootMultiplicity, reverse_natTrailingDegree,lt_self_iff_false]
    simp only [Multiset.mem_toFinset, mem_roots', ne_eq, reverse_eq_zero, h0, not_false_eq_true,
      true_and, Finset.mem_image, Finset.mem_erase,<-rootMultiplicity_pos]
    have := P.rootMultiplicity_of_reverse_eq (inv_ne_zero h)
    rw [inv_inv] at this
    rw [this]
    constructor
    . intro hm
      use a⁻¹
      simp only [inv_eq_zero, h, not_false_eq_true, ne_eq, h0, true_and, inv_inv, and_true, hm]
    rintro ⟨b, ⟨ _, hm ⟩, hab⟩
    rwa [<-hab, inv_inv]
  rw [this, Finset.sum_image]
  . apply Finset.sum_congr rfl
    intro x hx
    exact (rootMultiplicity_of_reverse_eq _ (Finset.ne_of_mem_erase hx)).symm
  intro x _ y _ hg
  rwa [<-inv_inj]

/-- Reversion preserves the splitting property. -/
lemma split_of_reverse {k:Type*} [Field k] {P: k[X]} (hP: P.Splits (RingHom.id k)) : P.reverse.Splits (RingHom.id k) := by
  rw [splits_iff_card_roots] at hP ⊢
  rw [<-P.card_roots_of_reverse, natDegree_eq_reverse_natDegree_add_natTrailingDegree] at hP
  exact Nat.add_right_cancel hP
