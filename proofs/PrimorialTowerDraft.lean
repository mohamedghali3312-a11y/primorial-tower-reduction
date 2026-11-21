/-
  ==============================================================================
  PROJET : PRIMORIAL-TOWER-REDUCTION — ÉBAUCHES DE DÉMONSTRATIONS FORMELLES
  Auteur : Mohamed Ghali (ORCID : 0009-0006-3364-5341)
  Statut : Démonstrations constructives préparées pour Lean 4 (en cours de
           vérification mécanique ; ouvertes aux tests et à la relecture).
  Dépendances : Aucune (Noyau standard Lean 4 uniquement).
  ==============================================================================
-/

-- Définition de la tour primorielle V_0 = 2, V_{r+1} = V_r * p_{r+1}
def primorialTower (p : Nat → Nat) : Nat → Nat
  | 0 => 2
  | r + 1 => primorialTower p r * p (r + 1)

-- Démonstration 1 : Symétrie miroir sur le socle V
lemma mirrorWheelSym (V r : Nat) (h1 : r ≤ V) (h2 : Nat.gcd r V = 1) :
    Nat.gcd (V - r) V = 1 := by
  apply Nat.dvd_antisymm _ (Nat.one_dvd _)
  rw [← h2]
  apply Nat.dvd_gcd _ (Nat.gcd_dvd_right (V - r) V)
  rcases Nat.gcd_dvd_left (V - r) V with ⟨k1, hk1⟩
  rcases Nat.gcd_dvd_right (V - r) V with ⟨k2, hk2⟩
  refine ⟨k2 - k1, ?_⟩
  rw [Nat.mul_sub_left_distrib]
  omega

-- Démonstration 2 : Divisibilité monotone de la tour (∀ r ≤ s, V_r ∣ V_s)
lemma primorialTower_dvd_of_le (p : Nat → Nat) {r s : Nat} (h : r ≤ s) :
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
      have h_div_k := ih hrk
      dsimp only [primorialTower]
      exact Nat.dvd_mul_of_dvd_left h_div_k (p (k + 1))

-- Démonstration 3 : Projection universelle de coprimalité sur tout rang r ≤ s
lemma universalWheelProjection (p : Nat → Nat) {r s : Nat} (h : r ≤ s) (x : Nat)
    (h_coprime_s : Nat.gcd x (primorialTower p s) = 1) :
    Nat.gcd x (primorialTower p r) = 1 := by
  have h_div : primorialTower p r ∣ primorialTower p s := primorialTower_dvd_of_le p h
  apply Nat.dvd_antisymm _ (Nat.one_dvd _)
  rw [← h_coprime_s]
  apply Nat.dvd_gcd (Nat.gcd_dvd_left x _)
  exact Nat.dvd_trans (Nat.gcd_dvd_right x _) h_div

-- Démonstration 4 : Invariance universelle par translation sur V_r
lemma universalWheelShift (p : Nat → Nat) (r x m : Nat)
    (h_adm : Nat.gcd x (primorialTower p r) = 1) :
    Nat.gcd (x + m * primorialTower p r) (primorialTower p r) = 1 := by
  have h : x + m * primorialTower p r = x + primorialTower p r * m := by
    rw [Nat.mul_comm m _]
  rw [h, Nat.gcd_add_mul_right_right, h_adm]

-- Démonstration 5 : Réduction modulaire d'Erdős-Straus (cas pair n = 2k)
lemma erdosStrausEven (k : Nat) :
    let n := 2 * k
    let x := k
    let y := 2 * k
    let z := 2 * k
    4 * x * y * z = n * (y * z + x * z + x * y) := by
  intro n x y z
  dsimp only [n, x, y, z]
  calc 4 * k * (2 * k) * (2 * k)
    _ = 16 * (k * k * k) := by
        rw [Nat.mul_assoc 4 k, Nat.mul_comm k (2 * k), ← Nat.mul_assoc 4 2,
            Nat.mul_assoc 8 k, Nat.mul_assoc 8 (k * k), Nat.mul_comm (k * k) (2 * k)]
        omega
    _ = (2 * k) * (2 * k * (2 * k) + k * (2 * k) + k * (2 * k)) := by
        have h1 : 2 * k * (2 * k) = 4 * (k * k) := by
          rw [Nat.mul_assoc 2 k, Nat.mul_comm k (2 * k), ← Nat.mul_assoc 2 2]
          omega
        have h2 : k * (2 * k) = 2 * (k * k) := by
          rw [Nat.mul_comm k (2 * k), Nat.mul_assoc 2 k k]
        rw [h1, h2]
        have h3 : 4 * (k * k) + 2 * (k * k) + 2 * (k * k) = 8 * (k * k) := by omega
        rw [h3, Nat.mul_assoc 2 k, Nat.mul_comm k (8 * (k * k)), ← Nat.mul_assoc 2 8,
            Nat.mul_assoc 16 (k * k) k]
        omega

-- Démonstration 6 : Obstruction universelle de Brocard-Ramanujan sur V_r
lemma universalBrocardObstruction (p : Nat → Nat) (r n m : Nat)
    (h_div : primorialTower p r ∣ Nat.factorial n)
    (h_brocard : Nat.factorial n + 1 = m * m) :
    primorialTower p r ∣ (m * m - 1) := by
  have h_sub : m * m - 1 = Nat.factorial n := by omega
  rw [h_sub]
  exact h_div
