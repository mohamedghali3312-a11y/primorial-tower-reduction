import math
from typing import Callable, List


class UniversalPrimorialWheel:
    """
    Générateur universel de socles primoriels V_r (r >= 0) avec V_0 = 2.
    Implémentation en mémoire bornée O(1) pour l'exploration modulaire
    des constellations polynomiales et conjectures arithmétiques.
    """

    def __init__(self, rank: int):
        if rank < 0:
            raise ValueError("Le rang r doit être un entier naturel >= 0.")
        self.rank = rank
        self.primes = self._generate_first_primes(rank + 1)
        self.Vr = math.prod(self.primes)
        self.p_r = self.primes[-1]

        # Calcul des résidus unitaires (Z / V_r Z)^x
        self.residues = tuple(x for x in range(1, self.Vr) if math.gcd(x, self.Vr) == 1)
        self.phi_Vr = len(self.residues)
        self.elimination_rate = (1.0 - self.phi_Vr / self.Vr) * 100.0
        self.memory_kb = (self.phi_Vr * 2) / 1024.0

    @staticmethod
    def _generate_first_primes(count: int) -> List[int]:
        primes = []
        cand = 2
        while len(primes) < count:
            if all(cand % p != 0 for p in primes if p * p <= cand):
                primes.append(cand)
            cand += 1
        return primes

    def admissible_constellation(self, polynomials: List[Callable[[int], int]]) -> List[int]:
        """Calcule l'ensemble admissible A_{V_r}(F) pour toute famille de polynômes."""
        return [
            r0 for r0 in self.residues
            if all(math.gcd(f(r0), self.Vr) == 1 for f in polynomials)
        ]

    def brocard_residues(self) -> List[int]:
        """Retourne les 2^r résidus admissibles m mod V_r tels que m^2 ≡ 1 (mod V_r)."""
        return [r0 for r0 in self.residues if (r0 * r0 - 1) % self.Vr == 0]


if __name__ == "__main__":
    print("=== PRIMORIAL-TOWER-REDUCTION : ANALYSE MULTI-RANGS V_r (r = 0 .. 6) ===\n")
    print(f"{'Rang':<5} | {'p_r':<4} | {'Socle V_r':<10} | {'φ(V_r)':<8} | {'Élim. k=1':<10} | {'Élim. Goldbach':<14} | {'Mémoire L1/L2'}")
    print("-" * 80)

    for r in range(7):
        wheel = UniversalPrimorialWheel(r)
        N_test = 10**12 + 4
        goldbach_adm = [
            x for x in wheel.residues
            if math.gcd((N_test - x) % wheel.Vr, wheel.Vr) == 1
        ]
        gb_elim = (1.0 - len(goldbach_adm) / (2 * wheel.Vr)) * 100.0
        print(
            f"V_{r:<3} | {wheel.p_r:<4} | {wheel.Vr:<10,} | {wheel.phi_Vr:<8,} | "
            f"{wheel.elimination_rate:>8.3f} % | {gb_elim:>12.3f} % | {wheel.memory_kb:>8.2f} Ko"
        )
