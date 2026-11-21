# 🧭 Primorial-Tower-Reduction : Réduction Modulaire Universelle sur les Tours $V_r$

**Exploration algébrique et algorithmique en mémoire bornée $O(1)$ des constellations polynomiales et conjectures arithmétiques**

[![Auteur](https://shields.io)](https://orcid.org)
[![ORCID](https://shields.io)](https://orcid.org)
[![Lean 4 CI](https://shields.io)](../../actions)
[![License: MIT](https://shields.io)](LICENSE)

> **📋 Note méthodologique :**  
> Ce dépôt présente des **démonstrations constructives de réduction modulaire** généralisant le filtrage par roues primorielles $V_r$ à diverses familles de polynômes et conjectures ouvertes (Goldbach, Lemoine, Bateman--Horn, Erdős--Straus, Brocard--Ramanujan, Wieferich, Firoozbakht et cryptographie NTT).  
> L'intégralité des **22 lemmes de réduction** du fichier [`proofs/PrimorialTowerDraft.lean`](proofs/PrimorialTowerDraft.lean) est **vérifiée mécaniquement par le compilateur Lean 4** à chaque mise à jour via GitHub Actions.

---

## 🎯 Démonstrations Constructives Certifiées (Lean 4 Pur)

| Domaine / Problème | Démonstrations Lean 4 (22 preuves) | Propriété de réduction certifiée |
| :--- | :--- | :--- |
| **Tour Universelle $V_r$** | `mirrorWheelSym`, `primorialTower_dvd_of_le`, `universalWheelProjection`, `gcd_shift_general`, `universalWheelShift` | Symétrie miroir, divisibilité $V_r \mid V_s$, projection et invariance par translation sur tout rang $r \le s$. |
| **Cryptographie NTT** | `nttProthStructure`, `prothKRedIdentity` | Structure multiplicative des corps de Proth ($2^n K + 1$) et réduction paresseuse K-RED. |
| **Goldbach & Lemoine** | `goldbachParamId`, `goldbachSecondComponentCoprime`, `goldbachInvolution`, `lemoineParamId`, `lemoineSecondComponentCoprime` | Identités paramétriques, symétrie involutive et préservation de coprimalité modulo $S$. |
| **Bateman--Horn** | `batemanHornLinearStep`, `batemanHornQuadraticStep` | Invariance modulaire des polynômes affines ($X+2, 2X+1$) et quadratiques ($X^2+1$). |
| **Chaînes de Cunningham** | `cunninghamLinkFormula`, `cunninghamModularObstruction` | Formule fermée des maillons et loi de troncature modulaire ($q \mid A \implies q \mid p_{q-2}$). |
| **Critère de Guy Robin** | `abundanceFactorStrictGrowth` | Croissance géométrique stricte du facteur d'abondance $p^a(p-1) < p^{a+1}-1$. |
| **Erdős--Straus** | `erdosStrausEven` | Résolution diophantienne exacte $4xyz = n(yz+xz+xy)$ pour la classe paire ($n = 2k$). |
| **Brocard, Wieferich & Firoozbakht** | `dvd_fact_of_le`, `universalBrocardObstruction`, `wieferichImpliesFermat`, `firoozbakhtSmallerGapMonotone`, `firoozbakhtZeroGap` | Obstruction $V_r \mid (m^2 - 1)$ pour $n!+1=m^2$, hiérarchie mod $x^2$ et bornes entières sur les écarts records. |

---

## 📂 Structure du dépôt

* `proofs/PrimorialTowerDraft.lean` : **22 démonstrations constructives** en Lean 4 pur (sans dépendance externe).
* `src/vr_universal_engine.py` : Moteur Python universel de génération des roues $V_r$ et d'analyse multi-rangs L1/L2/L3.
* `.github/workflows/verify.yml` : Intégration continue vérifiant automatiquement Python 3 et Lean 4.
* `LICENSE` : Licence libre MIT.
