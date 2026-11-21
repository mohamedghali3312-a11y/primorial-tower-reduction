# 🧭 Primorial-Tower-Reduction : Réduction Modulaire Universelle sur les Tours $V_r$

**Exploration algébrique et algorithmique en mémoire bornée $O(1)$ des constellations polynomiales et conjectures arithmétiques**

[![Auteur](https://shields.io)](https://orcid.org)
[![ORCID](https://shields.io)](https://orcid.org)
[![Lean 4 CI](https://shields.io)](../../actions)
[![License: MIT](https://shields.io)](LICENSE)

> **📋 Note méthodologique :**  
> Ce dépôt présente des **démonstrations constructives de réduction modulaire** généralisant le filtrage par roues primorielles $V_r$ à diverses familles de polynômes et conjectures ouvertes (Goldbach, Lemoine, Bateman--Horn, Erdős--Straus, Brocard--Ramanujan, Firoozbakht et cryptographie NTT).  
> L'intégralité des 14 lemmes de réduction du fichier [`proofs/PrimorialTowerDraft.lean`](proofs/PrimorialTowerDraft.lean) est **vérifiée mécaniquement par le compilateur Lean 4** à chaque mise à jour via GitHub Actions.

---

## 🎯 Démonstrations Constructives Certifiées (Lean 4 Pur)

| Domaine / Problème | Démonstration Lean 4 | Propriété de réduction certifiée |
| :--- | :--- | :--- |
| **Tour Universelle $V_r$** | `mirrorWheelSym`, `primorialTower_dvd_of_le`, `universalWheelProjection`, `universalWheelShift` | Symétrie miroir, divisibilité $V_r \mid V_s$, projection et invariance par translation sur tout rang $r \le s$. |
| **Cryptographie NTT** | `nttProthStructure`, `prothKRedIdentity` | Structure multiplicative des corps de Proth et réduction paresseuse K-RED. |
| **Goldbach & Lemoine** | `goldbachSecondComponentCoprime`, `lemoineSecondComponentCoprime` | Préservation de coprimalité sur les progressions modulaires modulo $S$. |
| **Bateman--Horn** | `batemanHornLinearStep`, `batemanHornQuadraticStep` | Invariance modulaire des polynômes affines ($X+2, 2X+1$) et quadratiques ($X^2+1$). |
| **Erdős--Straus** | `erdosStrausEven` | Résolution diophantienne exacte $4xyz = n(yz+xz+xy)$ pour la classe paire. |
| **Brocard & Firoozbakht** | `universalBrocardObstruction`, `firoozbakhtSmallerGapMonotone` | Obstruction $V_r \mid (m^2 - 1)$ pour $n!+1=m^2$ et monotonie entière sur les écarts records. |

---

## 📂 Structure du dépôt

* `proofs/PrimorialTowerDraft.lean` : 14 démonstrations constructives en Lean 4 pur (sans dépendance externe).
* `src/vr_universal_engine.py` : Moteur Python universel de génération des roues $V_r$ et d'analyse multi-rangs L1/L2/L3.
* `.github/workflows/verify.yml` : Intégration continue vérifiant automatiquement Python 3 et Lean 4.
