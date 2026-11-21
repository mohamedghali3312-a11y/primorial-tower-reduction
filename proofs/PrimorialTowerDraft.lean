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
-- 23. Conjecture d'Erdős-Straus : classe impaire n ≡ 3 (mod 4) (n = 4k + 3)
-- Couvre 25 % supplémentaires des entiers (75 % au total avec n = 2k).
theorem erdosStrausMod4Eq3 (k : Nat) :
    let n := 4 * k + 3
    let x := k + 1
    let M := n * x
    let y := M + 1
    let z := M * (M + 1)
    4 * x * y * z = n * (y * z + x * z + x * y) := by
  dsimp only
  set n := 4 * k + 3
  set x := k + 1
  set M := n * x
  have h_4x : 4 * x = n + 1 := by omega
  have h_inner : (M + 1) * (M * (M + 1)) + x * (M * (M + 1)) + x * (M + 1) =
      (M + 1) * (M * (M + 1) + x * M + x) := by
    have h2 : x * (M * (M + 1)) = (M + 1) * (x * M) := by ac_rfl
    have h3 : x * (M + 1) = (M + 1) * x := by ac_rfl
    rw [h2, h3, ← Nat.mul_add, ← Nat.mul_add]
  have h_mid : M * (M + 1) + x * M + x = (M + x) * (M + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_add, Nat.one_mul]
    have hc : x * M = M * x := by ac_rfl
    rw [hc]
    omega
  have h_4xM : (4 * x) * M = (M + x) * n := by
    rw [h_4x, Nat.add_mul, Nat.one_mul]
    have hM : M = n * x := rfl
    have hc1 : n * M = M * n := by ac_rfl
    have hc2 : M = x * n := by rw [hM]; ac_rfl
    rw [hc1, hc2, Nat.add_mul]
  rw [h_inner, h_mid]
  have h_lhs : 4 * x * (M + 1) * (M * (M + 1)) = ((4 * x) * M) * ((M + 1) * (M + 1)) := by
    ac_rfl
  have h_rhs : n * ((M + 1) * ((M + x) * (M + 1))) = ((M + x) * n) * ((M + 1) * (M + 1)) := by
    ac_rfl
  rw [h_lhs, h_rhs, h_4xM]

-- 24. Conjecture d'Erdős-Straus : sous-classe n ≡ 5 (mod 24) (n = 24k + 5)
-- Ici 2k + 2 = 6k + 2 et 8(3k) + 5 = 24k + 5 = 3(8k + 1) + 2 ; prenons n = 24k + 13
-- où x = 6k + 4 = 2(3k + 2) et n = 3(8k + 4) + 1 : voyons le cas n = 24k + 21 = 3(8k + 7)
-- et le cas général où 3 ∣ (n + 1) : n = 12k + 5 => x = 3k + 2, 4x - n = 3, et 3 ∣ (3k + 3) !
theorem erdosStrausMod12Eq5 (k : Nat) :
    let n := 12 * k + 5
    let x := 3 * k + 2
    let M := (12 * k + 5) * (k + 1)
    let y := M + 1
    let z := M * (M + 1)
    4 * x * y * z = n * (y * z + x * z + x * y) := by
  dsimp only
  set n := 12 * k + 5
  set x := 3 * k + 2
  set M := n * (k + 1)
  have h_x3 : x = 3 * (k + 1) - 1 := by omega
  have h_4x : 4 * x = n + 3 := by omega
  have h_inner : (M + 1) * (M * (M + 1)) + x * (M * (M + 1)) + x * (M + 1) =
      (M + 1) * (M * (M + 1) + x * M + x) := by
    have h2 : x * (M * (M + 1)) = (M + 1) * (x * M) := by ac_rfl
    have h3 : x * (M + 1) = (M + 1) * x := by ac_rfl
    rw [h2, h3, ← Nat.mul_add, ← Nat.mul_add]
  have h_mid : M * (M + 1) + x * M + x = (M + x) * (M + 1) := by
    rw [Nat.mul_add, Nat.mul_one, Nat.add_mul, Nat.mul_add, Nat.one_mul]
    have hc : x * M = M * x := by ac_rfl
    rw [hc]
    omega
  have h_key : (4 * x) * M = (M + x) * n := by
    have hM : M = n * (k + 1) := rfl
    have h_lhs_eq : (4 * x) * M = (4 * x * (k + 1)) * n := by
      rw [hM]; ac_rfl
    have h_rhs_eq : (M + x) * n = (n * (k + 1) + x) * n := by rw [hM]
    have h_coeff : 4 * x * (k + 1) = n * (k + 1) + x := by
      have h1 : 4 * x * (k + 1) = (n + 3) * (k + 1) := by rw [h_4x]
      rw [h1, Nat.add_mul]
      have h3k : 3 * (k + 1) = x + 1 := by omega
      rw [h3k]
      omega
    rw [h_lhs_eq, h_rhs_eq, h_coeff]
  rw [h_inner, h_mid]
  have h_lhs : 4 * x * (M + 1) * (M * (M + 1)) = ((4 * x) * M) * ((M + 1) * (M + 1)) := by
    ac_rfl
  have h_rhs : n * ((M + 1) * ((M + x) * (M + 1))) = ((M + x) * n) * ((M + 1) * (M + 1)) := by
    ac_rfl
  rw [h_lhs, h_rhs, h_key]

#print axioms erdosStrausMod4Eq3
#print axioms erdosStrausMod12Eq5

