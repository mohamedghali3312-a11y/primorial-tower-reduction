# 🗼 Primorial-Tower-Reduction : Réduction Modulaire Constructive en Mémoire Bornée O(1)

**Tours Primorielles $V_r$, Algorithmes en Mémoire Bornée et 40 Démonstrations Certifiées en Lean 4 Pur**

**Auteur :** Mohamed Ghali (`ORCID: 0009-0006-3364-5341`) • **Licence :** MIT • **Certification :** Lean 4 Pur (`#print axioms` audité)

---

## 📋 Vue d'ensemble

Ce dépôt formalise et implémente un cadre algorithmique et algébrique déterministe basé sur les **tours primorielles** $V_r = \prod_{k=0}^r p_k$ permettant d'éliminer les candidats arithmétiquement impossibles en **mémoire bornée $O(1)$** avant tout test coûteux.

### Panorama des 40 Démonstrations Certifiées en Lean 4 Pur (`proofs/PrimorialTowerDraft.lean`)

1. **Invariance sur les Tours Primorielles $V_r$ (`1–5`)** : Divisibilité emboîtée $V_r \mid V_s$, projection projective, décalage par multiples $x + m V_r$ et symétrie miroir $V_r - r$.
2. **Goldbach, Lemoine & Bateman–Horn (`8–11, 18–19, 23`)** : Préservation modulaire pour les polynômes linéaires et quadratiques $r_0^2 + c$.
3. **Conjecture d'Erdős–Straus (`12, 23–26`)** : Résolution constructive explicite de **22 classes sur 24 modulo 24 (91,67 % des entiers naturels)** via le lemme maître `erdosStrausMasterSplit`.
4. **Conjecture de Collatz $3n+1$ (`27–29`)** : Descente dyadique stricte en 1, 3 et 6 étapes couvrant **81,25 % des entiers naturels** modulo $2^k$.
5. **Nombres de Carmichael & Conjecture de Giuga (`30–33`)** : Critère de Korselt et preuve formelle d'impossibilité pour tout produit de deux nombres premiers $p \cdot q$.
6. **Nombres Parfaits Impairs & Critère d'Euler (`34–35`)** : Congruence $(2k+1)^2 \equiv 1 \pmod 8$ et exclusion formelle de la classe $N \equiv 3 \pmod 4$.
7. **Nombres de Sophie Germain & Mersenne (`36–37`)** : Obstruction modulo 3 ($p \equiv 2 \pmod 3$) et forme d'Euler $q = 2kp + 1$ des facteurs de $2^p - 1$.
8. **Conjectures de Legendre & d'Oppermann (`38–40`)** : Fenêtre quadratique $(n+1)^2 - n^2 = 2n + 1$, bipartition d'Oppermann et parité systématique du pivot $n(n+1)$.
9. **Critère de Guy Robin (RH), Brocard–Ramanujan, Firoozbakht, Wieferich, Cunningham & NTT Proth (`6–7, 13–17, 20–22`)** : Réductions modulaires et croissance stricte des facteurs d'abondance.

> **Note méthodologique :** L'ensemble des 40 énoncés est vérifié mécaniquement par le noyau standard de **Lean 4** (sans dépendance externe ni `sorryAx`, audité via `#print axioms`). Ces théorèmes établissent des réductions modulaires exactes de l'espace de recherche sans revendiquer la résolution globale des conjectures analytiques ouvertes.

---

## 📂 Architecture du Dépôt

* `proofs/PrimorialTowerDraft.lean` : Les **40 démonstrations constructives certifiées** et leur audit d'axiomes.
* `src/primorial_engine.py` : Moteur Python de réduction modulaire en mémoire $O(1)$ et suite de tests automatisés.
* `docs/Livre_Blanc_Tours_Primorielles.tex` : Monographie théorique complète en LaTeX.
* `.github/workflows/verify.yml` : Intégration continue Lean 4 + Python.
