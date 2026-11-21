
# 🧭 Primorial-Tower-Reduction : Réduction Modulaire Universelle sur les Tours $V_r$

**Exploration algébrique et algorithmique en mémoire bornée $O(1)$ des constellations polynomiales et conjectures arithmétiques**

[![Auteur](https://shields.io)](https://orcid.org)
[![ORCID](https://shields.io)](https://orcid.org)
[![Statut](https://shields.io)](#statut-de-v%C3%A9rification)

> **⚠️ Note méthodologique & Statut de vérification :**  
> Ce dépôt présente des **démonstrations constructives** et des **lemmes de réduction** (`lemma` en Lean 4) généralisant le filtrage par roues primorielles $V_r$ à diverses familles de polynômes et conjectures ouvertes (Goldbach, Lemoine, Bateman--Horn, Erdős--Straus, Brocard--Ramanujan, Wieferich, Firoozbakht).  
> **Les fichiers Lean 4 fournis sont des ébauches formelles en cours de validation mécanique** : ils sont publiés de manière transparente pour faciliter la relecture, les tests et la vérification collaborative.

---

## 🎯 Objectif du projet

Ce projet généralise les architectures précédentes (*La Machine v21.2 – v22.0*) en un cadre unifié basé sur la tour primorielle récursive $V_0 = 2$, $V_{r+1} = V_r \cdot p_{r+1}$ :

1. **Invariance translationnelle sur $V_r$** : Préservation de la coprimalité $\gcd(f(x_0 + m V_r), V_r) = 1$ pour toute famille finie de polynômes $\mathcal{F} \subset \mathbb{Z}[X]$.
2. **Projection et relèvement chinois** : Passage récursif d'un socle $V_r$ à un socle supérieur $V_s$ ($r \le s$).
3. **Applications expérimentales en mémoire $O(1)$** : Réduction d'espace de recherche pour Goldbach, Lemoine, Erdős--Straus, Brocard--Ramanujan, Wieferich et Firoozbakht.

---

## 📂 Contenu du dépôt

* `proofs/PrimorialTowerDraft.lean` : Ébauches des démonstrations constructives en Lean 4 pur (sans dépendance externe).
* `src/vr_universal_engine.py` : Moteur Python universel de génération des roues $V_r$ et d'exploration numérique en mémoire $O(1)$.
