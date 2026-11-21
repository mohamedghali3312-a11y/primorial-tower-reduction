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
  have h_expand : (r0 + m * S) * (r0 + m * S) + c =
      (r0 * r0 + c) + (2 * r0 * m + m * m * S) * S := by
    have h1 : r0 * (m * S) = (r0 * m) * S := by ac_rfl
    have h2 : (m * S) * r0 = (r0 * m) * S := by ac_rfl
    have h3 : (m * S) * (m * S) = (m * m * S) * S := by ac_rfl
    have h4 : (2 * r0 * m) * S = (r0 * m) * S + (r0 * m) * S := by
      have h_two : 2 * r0 = r0 + r0 := by omega
      rw [h_two, Nat.add_mul, Nat.add_mul]
   calc (r0 + m * S) * (r0 + m * S) + c
      _ = r0 * r0 + r0 * (m * S) + (m * S) * r0 + (m * S) * (m * S) + c := by
          rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
          omega
      _ = (r0 * r0 + c) + (2 * r0 * m + m * m * S) * S := by
          rw [h1, h2, h3, Nat.add_mul, h4]
          omega
  rw [h_expand]
  exact gcd_shift_general (r0 * r0 + c) (2 * r0 * m + m * m * S) S h_adm

theorem erdosStrausEven (k : Nat) :
    4 * k * (2 * k) * (2 * k) = (2 * k) * (2 * k * (2 * k) + k * (2 * k) + k * (2 * k)) := by
  have h1 : 2 * k * (2 * k) = 4 * (k * k) := by
    calc 2 * k * (2 * k) = (2 * 2) * (k * k) := by ac_rfl
    _ = 4 * (k * k) := rfl
  have h2 : k * (2 * k) = 2 * (k * k) := by ac_rfl
  rw [h1, h2]
  have h3 : 4 * (k * k) + 2 * (k * k) + 2 * (k * k) = 8 * (k * k) := by omega
  rw [h3]
  calc 4 * k * (2 * k) * (2 * k)
    _ = (4 * 2 * 2) * (k * k * k) := by ac_rfl
    _ = (2 * 8) * (k * k * k) := rfl
    _ = 2 * k * (8 * (k * k)) := by ac_rfl

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
