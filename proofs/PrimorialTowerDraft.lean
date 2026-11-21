def primorialTower (p : Nat → Nat) : Nat → Nat
  | 0 => 2
  | r + 1 => primorialTower p r * p (r + 1)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

theorem mirrorWheelSym (V r : Nat) (h1 : r ≤ V) (h2 : Nat.gcd r V = 1) :
    Nat.gcd (V - r) V = 1 := by
  apply Nat.dvd_antisymm _ (Nat.one_dvd _)
  rw [← h2]
  apply Nat.dvd_gcd _ (Nat.gcd_dvd_right (V - r) V)
  rcases Nat.gcd_dvd_left (V - r) V with ⟨k1, hk1⟩
  rcases Nat.gcd_dvd_right (V - r) V with ⟨k2, hk2⟩
  refine ⟨k2 - k1, ?_⟩
  rw [Nat.mul_sub_left_distrib]
  omega

theorem primorialTower_dvd_of_le (p : Nat → Nat) {r s : Nat} (h : r ≤ s) :
    primorialTower p r ∣ primorialTower p s := by
  induction s with
  | zero =>
    have hr : r = 0 := by omega
    rw [hr]
    exact Nat.dvd_refl _
  | succ k ih =>
    by_cases h_eq : r = k + 1
    · rw [h_eq]
      exact Nat.dvd_refl _
    · have hrk : r ≤ k := by omega
      rcases ih hrk with ⟨c, hc⟩
      dsimp only [primorialTower]
      refine ⟨c * p (k + 1), ?_⟩
      rw [hc, Nat.mul_assoc]

theorem universalWheelProjection (p : Nat → Nat) {r s : Nat} (h : r ≤ s) (x : Nat)
    (h_coprime_s : Nat.gcd x (primorialTower p s) = 1) :
    Nat.gcd x (primorialTower p r) = 1 := by
  have h_div : primorialTower p r ∣ primorialTower p s := primorialTower_dvd_of_le p h
  apply Nat.dvd_antisymm _ (Nat.one_dvd _)
  rw [← h_coprime_s]
  apply Nat.dvd_gcd (Nat.gcd_dvd_left x _)
  exact Nat.dvd_trans (Nat.gcd_dvd_right x _) h_div

theorem gcd_shift_general (x m S : Nat) (h_adm : Nat.gcd x S = 1) :
    Nat.gcd (x + m * S) S = 1 := by
  induction m with
  | zero => simp [h_adm]
  | succ k ih =>
    have h_step : x + (k + 1) * S = (x + k * S) + S := by
      rw [Nat.succ_mul, ← Nat.add_assoc]
    rw [h_step, Nat.gcd_add_self_left, ih]

theorem universalWheelShift (p : Nat → Nat) (r x m : Nat)
    (h_adm : Nat.gcd x (primorialTower p r) = 1) :
    Nat.gcd (x + m * primorialTower p r) (primorialTower p r) = 1 :=
  gcd_shift_general x m (primorialTower p r) h_adm

theorem nttProthStructure (n K : Nat) :
    (2 ^ n * K + 1) - 1 = 2 ^ n * K := by
  omega

theorem prothKRedIdentity (k n H L : Nat) :
    k * (H * 2 ^ n + L) + H = H * (k * 2 ^ n + 1) + k * L := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have h_assoc : k * (H * 2 ^ n) = H * (k * 2 ^ n) := by ac_rfl
  rw [h_assoc]
  omega

theorem goldbachSecondComponentCoprime (S r0 m : Nat)
    (h_Q0 : Nat.gcd (2 * r0 + 1) S = 1) :
    Nat.gcd (2 * (r0 + m * S) + 1) S = 1 := by
  have hQ : 2 * (r0 + m * S) + 1 = (2 * r0 + 1) + (2 * m) * S := by
    rw [Nat.mul_add, ← Nat.mul_assoc 2 m S]
    omega
  rw [hQ]
  exact gcd_shift_general (2 * r0 + 1) (2 * m) S h_Q0

theorem lemoineSecondComponentCoprime (S q0 m : Nat)
    (h_q0 : Nat.gcd q0 S = 1) :
    Nat.gcd (q0 + m * S) S = 1 :=
  gcd_shift_general q0 m S h_q0

theorem batemanHornLinearStep (a b r0 m S : Nat)
    (h_adm : Nat.gcd (a * r0 + b) S = 1) :
    Nat.gcd (a * (r0 + m * S) + b) S = 1 := by
  have h_expand : a * (r0 + m * S) + b = (a * r0 + b) + (a * m) * S := by
    rw [Nat.mul_add, ← Nat.mul_assoc a m S]
    omega
  rw [h_expand]
  exact gcd_shift_general (a * r0 + b) (a * m) S h_adm

theorem batemanHornQuadraticStep (c r0 m S : Nat)
    (h_adm : Nat.gcd (r0 * r0 + c) S = 1) :
    Nat.gcd ((r0 + m * S) * (r0 + m * S) + c) S = 1 := by
  have h1 : r0 * (m * S) = (r0 * m) * S := by ac_rfl
  have h2 : (m * S) * r0 = (r0 * m) * S := by ac_rfl
  have h3 : (m * S) * (m * S) = (m * m * S) * S := by ac_rfl
  have h_two : 2 * r0 = r0 + r0 := by omega
  have h4 : (2 * r0 * m) * S = (r0 * m) * S + (r0 * m) * S := by
    rw [h_two, Nat.add_mul, Nat.add_mul]
  have h_expand : (r0 + m * S) * (r0 + m * S) + c =
      (r0 * r0 + c) + (2 * r0 * m + m * m * S) * S := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, h1, h2, h3, Nat.add_mul, h4]
    omega
  rw [h_expand]
  exact gcd_shift_general (r0 * r0 + c) (2 * r0 * m + m * m * S) S h_adm

theorem erdosStrausEven (k : Nat) :
    4 * k * (2 * k) * (2 * k) = (2 * k) * (2 * k * (2 * k) + k * (2 * k) + k * (2 * k)) := by
  have h1 : 2 * k * (2 * k) = 4 * (k * k) := by
    have h_eq : 2 * k * (2 * k) = (2 * 2) * (k * k) := by ac_rfl
    rw [h_eq]
  have h2 : k * (2 * k) = 2 * (k * k) := by ac_rfl
  rw [h1, h2]
  have h3 : 4 * (k * k) + 2 * (k * k) + 2 * (k * k) = 8 * (k * k) := by omega
  rw [h3]
  have h_lhs : 4 * k * (2 * k) * (2 * k) = 16 * (k * k * k) := by
    have h_eq : 4 * k * (2 * k) * (2 * k) = (4 * 2 * 2) * (k * k * k) := by ac_rfl
    rw [h_eq]
  have h_rhs : 2 * k * (8 * (k * k)) = 16 * (k * k * k) := by
    have h_eq : 2 * k * (8 * (k * k)) = (2 * 8) * (k * k * k) := by ac_rfl
    rw [h_eq]
  rw [h_lhs, h_rhs]

theorem universalBrocardObstruction (p : Nat → Nat) (r n m : Nat)
    (h_div : primorialTower p r ∣ fact n)
    (h_brocard : fact n + 1 = m * m) :
    primorialTower p r ∣ (m * m - 1) := by
  have h_sub : m * m - 1 = fact n := by omega
  rw [h_sub]
  exact h_div

theorem firoozbakhtSmallerGapMonotone (p g1 g2 n : Nat)
    (hg : g2 ≤ g1)
    (h_valid : (p + g1) ^ n < p ^ (n + 1)) :
    (p + g2) ^ n < p ^ (n + 1) := by
  have h_le : (p + g2) ^ n ≤ (p + g1) ^ n := Nat.pow_le_pow_left (by omega) n
  omega

theorem cunninghamLinkFormula (A m : Nat) :
    2 * (2 ^ (m + 1) * A + (2 ^ (m + 1) - 1)) + 1 =
    2 ^ (m + 2) * A + (2 ^ (m + 2) - 1) := by
  have h1 : 1 ≤ 2 ^ (m + 1) := Nat.pow_pos (by omega : 0 < 2)
  have h2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    rw [Nat.pow_succ]; omega
  have h3 : 2 ^ (m + 2) * A = 2 * (2 ^ (m + 1) * A) := by
    rw [h2, Nat.mul_assoc]
  omega

theorem cunninghamModularObstruction (A q : Nat) (hq : 2 ≤ q)
    (h_div_A : q ∣ A) (h_fermat : q ∣ (2 ^ (q - 1) - 1)) :
    q ∣ (2 ^ ((q - 2) + 1) * A + (2 ^ ((q - 2) + 1) - 1)) := by
  have h_exp : (q - 2) + 1 = q - 1 := by omega
  rw [h_exp]
  rcases h_div_A with ⟨k1, hk1⟩
  rcases h_fermat with ⟨k2, hk2⟩
  refine ⟨2 ^ (q - 1) * k1 + k2, ?_⟩
  rw [hk1, hk2, Nat.mul_add, Nat.mul_left_comm]

theorem abundanceFactorStrictGrowth (p a : Nat) (hp : 2 ≤ p) (ha : 1 ≤ a) :
    p ^ a * (p - 1) < p ^ (a + 1) - 1 := by
  have h_pow : p ^ (a + 1) = p ^ a * p := Nat.pow_succ p a
  have h_pa : 2 ≤ p ^ a := by
    have h1 : p ^ 1 ≤ p ^ a := Nat.pow_le_pow_right (by omega) ha
    rw [Nat.pow_one] at h1
    omega
  have h_diff : p ^ a * p = p ^ a * (p - 1) + p ^ a := by
    have h_eq : p = (p - 1) + 1 := by omega
    calc p ^ a * p = p ^ a * ((p - 1) + 1) := by rw [← h_eq]
    _ = p ^ a * (p - 1) + p ^ a := by rw [Nat.mul_add, Nat.mul_one]
  rw [h_pow, h_diff]
  omega

theorem goldbachInvolution (N Q : Nat) (h : Q ≤ N) :
    N - (N - Q) = Q := by
  omega

theorem lemoineParamId (N S q0 m : Nat)
    (h_bound : 2 * (q0 + m * S) ≤ N) :
    (N - 2 * (q0 + m * S)) + 2 * (q0 + m * S) = N := by
  omega

theorem dvd_fact_of_le (k n : Nat) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    k ∣ fact n := by
  induction n with
  | zero => omega
  | succ m ih =>
    dsimp only [fact]
    by_cases h_eq : k = m + 1
    · rw [h_eq]
      exact Nat.dvd_mul_right (m + 1) (fact m)
    · have hkm : k ≤ m := by omega
      rcases ih hkm with ⟨c, hc⟩
      refine ⟨(m + 1) * c, ?_⟩
      rw [hc, ← Nat.mul_assoc]
      ac_rfl

theorem wieferichImpliesFermat (x k : Nat)
    (h_wief : k % (x * x) = 1) :
    k % x = 1 % x := by
  have h_mod : (k % (x * x)) % x = k % x := Nat.mod_mul_left_mod k x x
  rw [← h_mod, h_wief]

theorem firoozbakhtZeroGap (p n : Nat) (hp : 2 ≤ p) :
    p ^ n < p ^ (n + 1) := by
  have h_pow : p ^ (n + 1) = p ^ n * p := Nat.pow_succ p n
  have h_pos : 0 < p ^ n := Nat.pow_pos (by omega : 0 < p)
  rw [h_pow]
  have h_mul : p ^ n * 1 < p ^ n * p := Nat.mul_lt_mul_of_pos_left hp h_pos
  rw [Nat.mul_one] at h_mul
  exact h_mul

theorem goldbachParamId (S K r m : Nat) (h : m ≤ K) :
    (2 * S * (K - m) + 1) + (2 * (r + m * S) + 1) = 2 * (K * S + r) + 2 := by
  have h1 : 2 * S * (K - m) + 2 * (m * S) = 2 * (K * S) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm m S, ← Nat.mul_assoc 2 S m,
        Nat.sub_add_cancel (Nat.mul_le_mul_left (2 * S) h),
        Nat.mul_assoc, Nat.mul_comm S K]
  omega

#print axioms mirrorWheelSym
#print axioms primorialTower_dvd_of_le
#print axioms universalWheelProjection
#print axioms universalWheelShift
#print axioms batemanHornQuadraticStep
#print axioms erdosStrausEven
#print axioms cunninghamModularObstruction
#print axioms abundanceFactorStrictGrowth
#print axioms universalBrocardObstruction
#print axioms firoozbakhtSmallerGapMonotone

-- Lemme maître d'Erdős-Straus : si (4*x - n)*M = n*x (avec n ≤ 4*x),
-- alors y = M + 1 et z = M*(M + 1) résolvent 4*x*y*z = n*(y*z + x*z + x*y).
theorem erdosStrausMasterSplit (n x M : Nat) (h_cond : 4 * x * M = (M + x) * n) :
    4 * x * (M + 1) * (M * (M + 1)) =
    n * ((M + 1) * (M * (M + 1)) + x * (M * (M + 1)) + x * (M + 1)) := by
  have h_inner : (M + 1) * (M * (M + 1)) + x * (M * (M + 1)) + x * (M + 1) =
      (M + 1) * (M * (M + 1) + x * M + x) := by
    have h2 : x * (M * (M + 1)) = (M + 1) * (x * M) := by ac_rfl
    have h3 : x * (M + 1) = (M + 1) * x := by ac_rfl
    rw [h2, h3, ← Nat.mul_add, ← Nat.mul_add]
  have h_mid : M * (M + 1) + x * M + x = (M + x) * (M + 1) := by
    have h1 : M * (M + 1) = M * M + M := by rw [Nat.mul_add, Nat.mul_one]
    have h2 : (M + x) * (M + 1) = (M * M + M) + (x * M + x) := by
      rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_add, Nat.mul_one]
    rw [h1, h2]
    omega
  rw [h_inner, h_mid]
  have h_lhs : 4 * x * (M + 1) * (M * (M + 1)) = (4 * x * M) * ((M + 1) * (M + 1)) := by
    ac_rfl
  have h_rhs : n * ((M + 1) * ((M + x) * (M + 1))) = ((M + x) * n) * ((M + 1) * (M + 1)) := by
    ac_rfl
  rw [h_lhs, h_rhs, h_cond]

-- 23. Conjecture d'Erdős-Straus : classe impaire n ≡ 3 (mod 4) (n = 4k + 3)
theorem erdosStrausMod4Eq3 (k : Nat) :
    4 * (k + 1) * ((4 * k + 3) * (k + 1) + 1) * (((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1)) =
    (4 * k + 3) * ((((4 * k + 3) * (k + 1) + 1) * (((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1))) +
    (k + 1) * (((4 * k + 3) * (k + 1)) * ((4 * k + 3) * (k + 1) + 1)) +
    (k + 1) * ((4 * k + 3) * (k + 1) + 1)) := by
  apply erdosStrausMasterSplit (4 * k + 3) (k + 1) ((4 * k + 3) * (k + 1))
  have h1 : 4 * (k + 1) * ((4 * k + 3) * (k + 1)) =
      (4 * (k + 1) * (k + 1)) * (4 * k + 3) := by ac_rfl
  have h_coeff : 4 * (k + 1) = 4 * k + 4 := by omega
  have h2 : (4 * k + 3) * (k + 1) + (k + 1) = 4 * (k + 1) * (k + 1) := by
    rw [h_coeff, Nat.add_mul (4 * k) 3 (k + 1), Nat.mul_add (4 * k) k 1, Nat.mul_one,
        Nat.mul_add 3 k 1, Nat.mul_one, Nat.add_mul (4 * k) 4 (k + 1),
        Nat.mul_add (4 * k) k 1, Nat.mul_one, Nat.mul_add 4 k 1, Nat.mul_one]
    omega
  rw [h1, h2]
-- 24. Conjecture d'Erdős-Straus : classe impaire n ≡ 9 (mod 12) (n = 12k + 9)
theorem erdosStrausMod12Eq9 (k : Nat) :
    4 * (3 * k + 3) * ((12 * k + 9) * (k + 1) + 1) * (((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1)) =
    (12 * k + 9) * ((((12 * k + 9) * (k + 1) + 1) * (((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1))) +
    (3 * k + 3) * (((12 * k + 9) * (k + 1)) * ((12 * k + 9) * (k + 1) + 1)) +
    (3 * k + 3) * ((12 * k + 9) * (k + 1) + 1)) := by
  apply erdosStrausMasterSplit (12 * k + 9) (3 * k + 3) ((12 * k + 9) * (k + 1))
  have h1 : 4 * (3 * k + 3) * ((12 * k + 9) * (k + 1)) =
      (4 * (3 * k + 3) * (k + 1)) * (12 * k + 9) := by ac_rfl
  have h_3k3 : 3 * k + 3 = 3 * (k + 1) := by omega
  have h_12k12 : 4 * (3 * k + 3) = 12 * (k + 1) := by omega
  have h2 : (12 * k + 9) * (k + 1) + (3 * k + 3) = 4 * (3 * k + 3) * (k + 1) := by
    have h_12 : 12 * k + 9 + 3 = 12 * (k + 1) := by omega
    rw [h_12k12, h_3k3, ← Nat.add_mul, h_12]
  rw [h1, h2]
#print axioms erdosStrausMasterSplit
#print axioms erdosStrausMod4Eq3
#print axioms erdosStrausMod12Eq9
-- 25. Conjecture d'Erdős-Straus : classe n ≡ 5 (mod 24) (n = 24q + 5)
-- Identité exacte : x = 6q + 2, y = (24q + 5)(3q + 1), z = (24q + 5)(6q + 2)
theorem erdosStrausMod24Eq5 (q : Nat) :
    4 * (6 * q + 2) * ((24 * q + 5) * (3 * q + 1)) * ((24 * q + 5) * (6 * q + 2)) =
    (24 * q + 5) * (((24 * q + 5) * (3 * q + 1)) * ((24 * q + 5) * (6 * q + 2)) +
    (6 * q + 2) * ((24 * q + 5) * (6 * q + 2)) +
    (6 * q + 2) * ((24 * q + 5) * (3 * q + 1))) := by
  have h_6q2 : 6 * q + 2 = 2 * (3 * q + 1) := by omega
  have h1 : ((24 * q + 5) * (3 * q + 1)) * ((24 * q + 5) * (6 * q + 2)) =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * (24 * q + 5) := by ac_rfl
  have h2 : (6 * q + 2) * ((24 * q + 5) * (6 * q + 2)) =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 2 := by
    rw [h_6q2]; ac_rfl
  have h3 : (6 * q + 2) * ((24 * q + 5) * (3 * q + 1)) =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 1 := by
    rw [Nat.mul_one]; ac_rfl
  have h_sum : ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * (24 * q + 5) +
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 2 +
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * 1 =
      ((24 * q + 5) * (3 * q + 1)) * (6 * q + 2) * (4 * (6 * q + 2)) := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    have h_24q8 : (24 * q + 5) + 2 + 1 = 4 * (6 * q + 2) := by omega
    rw [h_24q8]
  rw [h1, h2, h3, h_sum]
  ac_rfl

-- 26. Conjecture d'Erdős-Straus : classe n ≡ 13 (mod 24) (n = 24q + 13)
-- Identité exacte : x = 6q + 4, y = (24q + 13)(3q + 2), z = (24q + 13)(6q + 4)
-- Porte la couverture formelle certifiée à 22/24 = 91,67 % des entiers naturels !
theorem erdosStrausMod24Eq13 (q : Nat) :
    4 * (6 * q + 4) * ((24 * q + 13) * (3 * q + 2)) * ((24 * q + 13) * (6 * q + 4)) =
    (24 * q + 13) * (((24 * q + 13) * (3 * q + 2)) * ((24 * q + 13) * (6 * q + 4)) +
    (6 * q + 4) * ((24 * q + 13) * (6 * q + 4)) +
    (6 * q + 4) * ((24 * q + 13) * (3 * q + 2))) := by
  have h_6q4 : 6 * q + 4 = 2 * (3 * q + 2) := by omega
  have h1 : ((24 * q + 13) * (3 * q + 2)) * ((24 * q + 13) * (6 * q + 4)) =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * (24 * q + 13) := by ac_rfl
  have h2 : (6 * q + 4) * ((24 * q + 13) * (6 * q + 4)) =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 2 := by
    rw [h_6q4]; ac_rfl
  have h3 : (6 * q + 4) * ((24 * q + 13) * (3 * q + 2)) =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 1 := by
    rw [Nat.mul_one]; ac_rfl
  have h_sum : ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * (24 * q + 13) +
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 2 +
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * 1 =
      ((24 * q + 13) * (3 * q + 2)) * (6 * q + 4) * (4 * (6 * q + 4)) := by
    rw [← Nat.mul_add, ← Nat.mul_add]
    have h_24q16 : (24 * q + 13) + 2 + 1 = 4 * (6 * q + 4) := by omega
    rw [h_24q16]
  rw [h1, h2, h3, h_sum]
  ac_rfl

#print axioms erdosStrausMod24Eq5
#print axioms erdosStrausMod24Eq13
-- ============================================================================
-- CONJECTURE DE COLLATZ (3n + 1) : DESCENTE DYADIQUE PAR CLASSES MODULO 2^k
-- ============================================================================

def collatzStep (n : Nat) : Nat :=
  if n % 2 = 0 then n / 2 else 3 * n + 1

def collatzIter : Nat → Nat → Nat
  | 0, n => n
  | s + 1, n => collatzIter s (collatzStep n)

theorem collatzStep_even (m : Nat) : collatzStep (2 * m) = m := by
  dsimp only [collatzStep]
  have h : (2 * m) % 2 = 0 := by omega
  rw [if_pos h]
  omega

theorem collatzStep_odd (m : Nat) : collatzStep (2 * m + 1) = 6 * m + 4 := by
  dsimp only [collatzStep]
  have h : (2 * m + 1) % 2 ≠ 0 := by omega
  rw [if_neg h]
  omega

-- 27. Collatz : descente en 1 étape pour n ≡ 0 (mod 2) (50 % des entiers)
theorem collatzDescentMod2Eq0 (k : Nat) (hk : 0 < k) :
    collatzIter 1 (2 * k) < 2 * k := by
  dsimp only [collatzIter]
  rw [collatzStep_even k]
  omega

-- 28. Collatz : descente en 3 étapes pour n ≡ 1 (mod 4) (75 % cumulés des entiers)
-- Trajectoire : 4k + 1 -> 12k + 4 -> 6k + 2 -> 3k + 1 < 4k + 1
theorem collatzDescentMod4Eq1 (k : Nat) (hk : 0 < k) :
    collatzIter 3 (4 * k + 1) < 4 * k + 1 := by
  dsimp only [collatzIter]
  have s0 : 4 * k + 1 = 2 * (2 * k) + 1 := by omega
  have s1 : 12 * k + 4 = 2 * (6 * k + 2) := by omega
  have s2 : 6 * k + 2 = 2 * (3 * k + 1) := by omega
  rw [s0, collatzStep_odd (2 * k)]
  have e1 : 6 * (2 * k) + 4 = 2 * (6 * k + 2) := by omega
  rw [e1, collatzStep_even (6 * k + 2), s2, collatzStep_even (3 * k + 1)]
  omega

-- 29. Collatz : descente en 6 étapes pour n ≡ 3 (mod 16) (81,25 % cumulés des entiers)
-- Trajectoire : 16k+3 -> 48k+10 -> 24k+5 -> 72k+16 -> 36k+8 -> 18k+4 -> 9k+2 < 16k+3
theorem collatzDescentMod16Eq3 (k : Nat) :
    collatzIter 6 (16 * k + 3) < 16 * k + 3 := by
  dsimp only [collatzIter]
  have s0 : 16 * k + 3 = 2 * (8 * k + 1) + 1 := by omega
  rw [s0, collatzStep_odd (8 * k + 1)]
  have e1 : 6 * (8 * k + 1) + 4 = 2 * (24 * k + 5) := by omega
  rw [e1, collatzStep_even (24 * k + 5)]
  have s2 : 24 * k + 5 = 2 * (12 * k + 2) + 1 := by omega
  rw [s2, collatzStep_odd (12 * k + 2)]
  have e3 : 6 * (12 * k + 2) + 4 = 2 * (36 * k + 8) := by omega
  rw [e3, collatzStep_even (36 * k + 8)]
  have s4 : 36 * k + 8 = 2 * (18 * k + 4) := by omega
  rw [s4, collatzStep_even (18 * k + 4)]
  have s5 : 18 * k + 4 = 2 * (9 * k + 2) := by omega
  rw [s5, collatzStep_even (9 * k + 2)]
  omega

#print axioms collatzDescentMod2Eq0
#print axioms collatzDescentMod4Eq1
#print axioms collatzDescentMod16Eq3
-- ============================================================================
-- NOMBRES DE CARMICHAEL & CRITÈRE DE KORSELT SUR LES PRODUITS SANS CARRÉ
-- ============================================================================

-- 30. Identité fondamentale de Korselt : p*q - 1 = p*(q - 1) + (p - 1)
theorem korseltTwoPrimeIdentity (p q : Nat) (hp : 1 ≤ p) (hq : 1 ≤ q) :
    p * q - 1 = p * (q - 1) + (p - 1) := by
  have hq_eq : q = (q - 1) + 1 := by omega
  have hp_eq : p = (p - 1) + 1 := by omega
  have h1 : p * q = p * ((q - 1) + 1) := by rw [← hq_eq]
  rw [h1, Nat.mul_add, Nat.mul_one]
  omega

-- 31. Théorème d'impossibilité des nombres de Carmichael semi-premiers (n = p * q) :
-- Si 1 < p < q, alors (q - 1) ne peut JAMAIS diviser (p * q - 1).
-- Tout nombre de Carmichael possède donc au moins 3 facteurs premiers distincts.
theorem noTwoPrimeCarmichael (p q : Nat) (hp : 1 < p) (hpq : p < q) :
    ¬ ((q - 1) ∣ (p * q - 1)) := by
  intro h_dvd
  rw [korseltTwoPrimeIdentity p q (by omega) (by omega)] at h_dvd
  have h_mod : (p * (q - 1) + (p - 1)) % (q - 1) = 0 := Nat.mod_eq_zero_of_dvd h_dvd
  have h_reduce : (p * (q - 1) + (p - 1)) % (q - 1) = (p - 1) % (q - 1) := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right]
  rw [h_reduce, Nat.mod_eq_of_lt (by omega)] at h_mod
  omega

#print axioms korseltTwoPrimeIdentity
#print axioms noTwoPrimeCarmichael

-- ============================================================================
-- CONJECTURE DE GIUGA : OBSTRUCTION MODULAIRE SUR LES PRODUITS SANS CARRÉ
-- ============================================================================

-- 32. Condition de Giuga : si p ∣ (n / p - 1) et n = p * m, alors p ∣ (m - 1)
theorem giugaCofactorCondition (p m : Nat) (hp : 0 < p) (hm : 1 ≤ m)
    (h_giuga : p ∣ ((p * m) / p - 1)) :
    p ∣ (m - 1) := by
  have h_div : (p * m) / p = m := Nat.mul_div_cancel_left m hp
  rw [h_div] at h_giuga
  exact h_giuga

-- 33. Impossibilité d'un nombre de Giuga à deux facteurs premiers (n = p * q) :
-- Si 1 < p < q, il est impossible que q ∣ (p - 1) (donc aucun semi-premier
-- ne peut violer la conjecture de Giuga).
theorem noTwoPrimeGiuga (p q : Nat) (hp : 1 < p) (hpq : p < q) :
    ¬ (q ∣ (p - 1)) := by
  intro h_dvd
  have h_le : q ≤ p - 1 := Nat.le_of_dvd (by omega) h_dvd
  omega

#print axioms giugaCofactorCondition
#print axioms noTwoPrimeGiuga
-- ============================================================================
-- NOMBRES PARFAITS IMPAIRS & CRITÈRE D'EULER (N = p^α * m^2)
-- ============================================================================

-- 34. Congruence du carré d'un entier impair : (2k + 1)^2 ≡ 1 (mod 8)
theorem oddSquareMod8 (k : Nat) :
    ((2 * k + 1) * (2 * k + 1)) % 8 = 1 := by
  have h1 : (2 * k + 1) * (2 * k + 1) = 4 * (k * (k + 1)) + 1 := by
    rw [Nat.add_mul, Nat.mul_add, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    have hc : 2 * k * (2 * k) = 4 * (k * k) := by ac_rfl
    rw [hc]
    omega
  rw [h1]
  -- Parmi k et (k + 1), l'un est pair, donc 8 ∣ 4 * (k * (k + 1))
  have h_even : (k * (k + 1)) % 2 = 0 := by
    have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases hk with h0 | h1_mod
    · have hq : k = 2 * (k / 2) := by omega
      rw [hq, Nat.mul_assoc]
      omega
    · have hq : k + 1 = 2 * ((k + 1) / 2) := by omega
      rw [hq]
      have ha : k * (2 * ((k + 1) / 2)) = 2 * (k * ((k + 1) / 2)) := by ac_rfl
      rw [ha]
      omega
  have h8 : (4 * (k * (k + 1))) % 8 = 0 := by omega
  omega

-- 35. Obstruction d'Euler sur les nombres parfaits impairs :
-- Si un entier N a la forme d'Euler N = p_pow * m^2 avec p_pow ≡ 1 (mod 4) et m impair,
-- alors N ≡ 1 (mod 4) : aucun entier N ≡ 3 (mod 4) ne peut jamais être parfait impair !
theorem oddPerfectEulerMod4Obstruction (p_pow k : Nat)
    (hp : p_pow % 4 = 1) :
    (p_pow * ((2 * k + 1) * (2 * k + 1))) % 4 = 1 := by
  have hm8 : ((2 * k + 1) * (2 * k + 1)) % 8 = 1 := oddSquareMod8 k
  have hm4 : ((2 * k + 1) * (2 * k + 1)) % 4 = 1 := by omega
  rw [Nat.mul_mod, hp, hm4]

#print axioms oddSquareMod8
#print axioms oddPerfectEulerMod4Obstruction
-- ============================================================================
-- NOMBRES DE SOPHIE GERMAIN & NOMBRES DE MERSENNE (M_p = 2^p - 1)
-- ============================================================================

-- 36. Obstruction modulaire sur les nombres premiers de Sophie Germain :
-- Si p ≡ 1 (mod 3), alors 3 ∣ (2 * p + 1). Ainsi, tout premier de Sophie Germain
-- p > 3 appartient obligatoirement à la classe p ≡ 2 (mod 3).
theorem sophieGermainObstructionMod3 (p : Nat) (hp : p % 3 = 1) :
    (2 * p + 1) % 3 = 0 := by
  omega

-- 37. Structure d'Euler des facteurs de Mersenne (q = 2 * k * p + 1) :
-- Tout facteur q vérifiant q % (2 * p) = 1 (pour p > 0) s'écrit exactement
-- sous la forme q = 2 * k * p + 1.
theorem mersenneFactorEulerForm (p q : Nat) (hp : 0 < p)
    (h_mod : q % (2 * p) = 1) :
    ∃ k : Nat, q = 2 * k * p + 1 := by
  refine ⟨q / (2 * p), ?_⟩
  have h_div : 2 * p * (q / (2 * p)) + q % (2 * p) = q := Nat.div_add_mod q (2 * p)
  rw [h_mod] at h_div
  have h_comm : 2 * p * (q / (2 * p)) = 2 * (q / (2 * p)) * p := by ac_rfl
  rw [h_comm] at h_div
  omega

#print axioms sophieGermainObstructionMod3
#print axioms mersenneFactorEulerForm
