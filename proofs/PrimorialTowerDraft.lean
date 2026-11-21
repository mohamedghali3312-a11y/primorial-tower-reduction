def primorialTower (p : Nat → Nat) : Nat → Nat
  | 0 => 2
  | r + 1 => primorialTower p r * p (r + 1)

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

-- 1. Symétrie miroir de la roue primorielle
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

-- 2. Divisibilité monotone de la tour primorielle (∀ r ≤ s, V_r ∣ V_s)
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

-- 3. Projection universelle de coprimalité sur tout rang r ≤ s
theorem universalWheelProjection (p : Nat → Nat) {r s : Nat} (h : r ≤ s) (x : Nat)
    (h_coprime_s : Nat.gcd x (primorialTower p s) = 1) :
    Nat.gcd x (primorialTower p r) = 1 := by
  have h_div : primorialTower p r ∣ primorialTower p s := primorialTower_dvd_of_le p h
  apply Nat.dvd_antisymm _ (Nat.one_dvd _)
  rw [← h_coprime_s]
  apply Nat.dvd_gcd (Nat.gcd_dvd_left x _)
  exact Nat.dvd_trans (Nat.gcd_dvd_right x _) h_div

-- Lemme utilitaire général de décalage sur un socle S
theorem gcd_shift_general (x m S : Nat) (h_adm : Nat.gcd x S = 1) :
    Nat.gcd (x + m * S) S = 1 := by
  induction m with
  | zero => simp [h_adm]
  | succ k ih =>
    have h_step : x + (k + 1) * S = (x + k * S) + S := by
      rw [Nat.succ_mul, ← Nat.add_assoc]
    rw [h_step, Nat.gcd_add_self_left, ih]

-- 4. Invariance universelle par translation sur V_r
theorem universalWheelShift (p : Nat → Nat) (r x m : Nat)
    (h_adm : Nat.gcd x (primorialTower p r) = 1) :
    Nat.gcd (x + m * primorialTower p r) (primorialTower p r) = 1 :=
  gcd_shift_general x m (primorialTower p r) h_adm

-- 5. Cryptographie NTT : structure multiplicative des corps premiers de Proth
theorem nttProthStructure (n K : Nat) :
    (2 ^ n * K + 1) - 1 = 2 ^ n * K := by
  omega

-- 6. Cryptographie NTT : identité de réduction paresseuse K-RED
theorem prothKRedIdentity (k n H L : Nat) :
    k * (H * 2 ^ n + L) + H = H * (k * 2 ^ n + 1) + k * L := by
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  have h_assoc : k * (H * 2 ^ n) = H * (k * 2 ^ n) := by ac_rfl
  rw [h_assoc]
  omega

-- 7. Conjecture de Goldbach : coprimalité sur la composante Q_m
theorem goldbachSecondComponentCoprime (S r0 m : Nat)
    (h_Q0 : Nat.gcd (2 * r0 + 1) S = 1) :
    Nat.gcd (2 * (r0 + m * S) + 1) S = 1 := by
  have hQ : 2 * (r0 + m * S) + 1 = (2 * r0 + 1) + (2 * m) * S := by
    rw [Nat.mul_add, ← Nat.mul_assoc 2 m S]
    omega
  rw [hQ]
  exact gcd_shift_general (2 * r0 + 1) (2 * m) S h_Q0

-- 8. Conjecture de Lemoine (N = p + 2q) : coprimalité sur q_m
theorem lemoineSecondComponentCoprime (S q0 m : Nat)
    (h_q0 : Nat.gcd q0 S = 1) :
    Nat.gcd (q0 + m * S) S = 1 :=
  gcd_shift_general q0 m S h_q0

-- 9. Bateman-Horn linéaire (Premiers jumeaux, Sophie Germain)
theorem batemanHornLinearStep (a b r0 m S : Nat)
    (h_adm : Nat.gcd (a * r0 + b) S = 1) :
    Nat.gcd (a * (r0 + m * S) + b) S = 1 := by
  have h_expand : a * (r0 + m * S) + b = (a * r0 + b) + (a * m) * S := by
    rw [Nat.mul_add, ← Nat.mul_assoc a m S]
    omega
  rw [h_expand]
  exact gcd_shift_general (a * r0 + b) (a * m) S h_adm

-- 10. Bateman-Horn quadratique (Conjecture de Landau X^2 + 1)
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

-- 11. Conjecture d'Erdős-Straus : classe paire (n = 2k)
theorem erdosStrausEven (k : Nat) :
    4 * k * (2 * k) * (2 * k) = (2 * k) * (2 * k * (2 * k) + k * (2 * k) + k * (2 * k)) := by
  have h1 : 2 * k * (2 * k) = 4 * (k * k) := by
    have h_eq : 2 * k * (2 * k) = (2 * 2) * (k * k) := by ac_rfl
    rw [h_eq]; rfl
  have h2 : k * (2 * k) = 2 * (k * k) := by ac_rfl
  rw [h1, h2]
  have h3 : 4 * (k * k) + 2 * (k * k) + 2 * (k * k) = 8 * (k * k) := by omega
  rw [h3]
  have h_lhs : 4 * k * (2 * k) * (2 * k) = 16 * (k * k * k) := by
    have h_eq : 4 * k * (2 * k) * (2 * k) = (4 * 2 * 2) * (k * k * k) := by ac_rfl
    rw [h_eq]; rfl
  have h_rhs : 2 * k * (8 * (k * k)) = 16 * (k * k * k) := by
    have h_eq : 2 * k * (8 * (k * k)) = (2 * 8) * (k * k * k) := by ac_rfl
    rw [h_eq]; rfl
  rw [h_lhs, h_rhs]

-- 12. Conjecture de Brocard-Ramanujan : obstruction universelle sur V_r
theorem universalBrocardObstruction (p : Nat → Nat) (r n m : Nat)
    (h_div : primorialTower p r ∣ fact n)
    (h_brocard : fact n + 1 = m * m) :
    primorialTower p r ∣ (m * m - 1) := by
  have h_sub : m * m - 1 = fact n := by omega
  rw [h_sub]
  exact h_div

-- 13. Conjecture de Firoozbakht : monotonie du critère entier sur les écarts
theorem firoozbakhtSmallerGapMonotone (p g1 g2 n : Nat)
    (hg : g2 ≤ g1)
    (h_valid : (p + g1) ^ n < p ^ (n + 1)) :
    (p + g2) ^ n < p ^ (n + 1) := by
  have h_le : (p + g2) ^ n ≤ (p + g1) ^ n := Nat.pow_le_pow_left (by omega) n
  omega

-- 14. Chaînes de Cunningham : formule fermée des maillons
theorem cunninghamLinkFormula (A m : Nat) :
    2 * (2 ^ (m + 1) * A + (2 ^ (m + 1) - 1)) + 1 =
    2 ^ (m + 2) * A + (2 ^ (m + 2) - 1) := by
  have h1 : 1 ≤ 2 ^ (m + 1) := Nat.pow_pos (by omega : 0 < 2)
  have h2 : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    rw [Nat.pow_succ]; omega
  have h3 : 2 ^ (m + 2) * A = 2 * (2 ^ (m + 1) * A) := by
    rw [h2, Nat.mul_assoc]
  omega

-- 15. Chaînes de Cunningham : loi de troncature modulaire
theorem cunninghamModularObstruction (A q : Nat) (hq : 2 ≤ q)
    (h_div_A : q ∣ A) (h_fermat : q ∣ (2 ^ (q - 1) - 1)) :
    q ∣ (2 ^ ((q - 2) + 1) * A + (2 ^ ((q - 2) + 1) - 1)) := by
  have h_exp : (q - 2) + 1 = q - 1 := by omega
  rw [h_exp]
  rcases h_div_A with ⟨k1, hk1⟩
  rcases h_fermat with ⟨k2, hk2⟩
  refine ⟨2 ^ (q - 1) * k1 + k2, ?_⟩
  rw [hk1, hk2, Nat.mul_add, Nat.mul_left_comm]
-- 16. Critère de Guy Robin : croissance géométrique stricte du facteur d'abondance
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
-- 17. Conjecture de Goldbach : symétrie involutive Q ↦ N - Q
theorem goldbachInvolution (N Q : Nat) (h : Q ≤ N) :
    N - (N - Q) = Q := by
  omega

-- 18. Conjecture de Lemoine : identité algébrique p_m + 2 * q_m = N
theorem lemoineParamId (N S q0 m : Nat)
    (h_bound : 2 * (q0 + m * S) ≤ N) :
    (N - 2 * (q0 + m * S)) + 2 * (q0 + m * S) = N := by
  omega
-- 19. Factorielle : divisibilité universelle k ∣ fact n pour 1 ≤ k ≤ n
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
-- 20. Nombres premiers de Wieferich : hiérarchie mod x^2 => mod x
theorem wieferichImpliesFermat (x k : Nat)
    (h_wief : k % (x * x) = 1) :
    k % x = 1 % x := by
  have h_mod : (k % (x * x)) % x = k % x := Nat.mod_mul_left_mod k x x
  rw [← h_mod, h_wief]

-- 21. Conjecture de Firoozbakht : borne stricte à écart nul
theorem firoozbakhtZeroGap (p n : Nat) (hp : 2 ≤ p) :
    p ^ n < p ^ (n + 1) := by
  have h_pow : p ^ (n + 1) = p ^ n * p := Nat.pow_succ p n
  have h_pos : 0 < p ^ n := Nat.pow_pos (by omega : 0 < p)
  rw [h_pow]
  have h_mul : p ^ n * 1 < p ^ n * p := Nat.mul_lt_mul_of_pos_left hp h_pos
  rw [Nat.mul_one] at h_mul
  exact h_mul

-- 22. Identité paramétrique de Goldbach sur le socle S
theorem goldbachParamId (S K r m : Nat) (h : m ≤ K) :
    (2 * S * (K - m) + 1) + (2 * (r + m * S) + 1) = 2 * (K * S + r) + 2 := by
  have h1 : 2 * S * (K - m) + 2 * (m * S) = 2 * (K * S) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_comm m S, ← Nat.mul_assoc 2 S m,
        Nat.sub_add_cancel (Nat.mul_le_mul_left (2 * S) h),
        Nat.mul_assoc, Nat.mul_comm S K]
  omega
