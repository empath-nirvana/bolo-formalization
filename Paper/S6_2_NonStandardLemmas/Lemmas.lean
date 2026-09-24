/-!
# [TR] §6.2 Non-standard Lemmas  (pp. 8–22)



**Stage 2.**  This file will hold the numbered results of the subsection, in printed order,
each under its printed statement and proof, with the Lean declaration moved from the
source and a numbered alias.  The results, with the inventory's status and the
declaration `Bridge/Plan.csv` assigns to each:

* **Lemma 6.16** — `proved`; planned: `Fig16.ResU.CompatS.of_flat`
* **Lemma 6.17** — `proved`; planned: `Fig16.ResU.compatS_of_hash_mut`
* **Lemma 6.18** — `proved`; planned: —
* **Lemma 6.19** — `proved`; planned: `Fig16.ResU.flatR_idem`
* **Lemma 6.20** — `proved`; planned: —
* **Lemma 6.21** — `proved`; planned: `Fig16.ResU.compatS_single_own`, `Fig16.ResU.six21`
* **Lemma 6.22** — `proved`; planned: `Fig16.ResU.compatS_of_hash_mut`, `Fig16.ResU.six22`
* **Lemma 6.23** — `proved`; planned: `Fig16.ResU.six23`
* **Lemma 6.24** — `proved`; planned: `Fig16.ResU.six24`
* **Lemma 6.25** — `proved`; planned: `Fig16.ResU.six25`
* **Lemma 6.26** — `proved`; planned: `Fig16.ResU.six33`, `Fig16.ResU.six26`
* **Lemma 6.27** — `proved`; planned: `Fig16.ResU.six27`
* **Lemma 6.28** — `proved`; planned: `Fig16.ResU.six28`
* **Lemma 6.29** — `proved`; planned: `Fig16.ExS.toExR`, `Fig16.ResU.six29`
* **Lemma 6.30** — `proved`; planned: —
* **Lemma 6.31** — `proved`; planned: —
* **Lemma 6.32** — `proved`; planned: `Fig16.ExS.toExR`
* **Lemma 6.33** — `proved`; planned: `Fig16.ResU.six33`
* **Lemma 6.34** — `proved`; planned: `Fig16.ResU.six34`
* **Lemma 6.35** — `proved`; planned: —
* **Lemma 6.36** — `proved`; planned: —
* **Lemma 6.37** — `proved`; planned: `Fig16.ResU.compatS_of_compR`, `Fig16.ResU.six37`
* **Lemma 6.38** — `proved`; planned: `Fig16.ResU.CompatS.of_flat`, `Fig16.ResU.six37`, `Fig16.ResU.six29`
* **Lemma 6.39** — `proved`; planned: `Fig16.ResU.six39`
* **Lemma 6.40** — `variant`; planned: —
* **Lemma 6.41** — `proved`; planned: `Fig16.ResU.compatS_single_own`
* **Lemma 6.42** — `proved`; planned: `Fig16.ResU.compatS_single_mut`
* **Lemma 6.43** — `proved`; planned: `Fig16.ResU.compS_single_imm`
* **Lemma 6.44** — `proved`; planned: `Fig16.ResU.compatS_single_imm_inv`
* **Lemma 6.45** — `proved`; planned: `Fig16.ResU.atLife_comp_sqsupset`
* **Lemma 6.46** — `proved`; planned: `Fig16.BoLo.hash_shift`
* **Lemma 6.47** — `proved`; planned: `Fig16.ResU.Upd.refl`
* **Lemma 6.48** — `proved`; planned: `Fig16.BoLo.updV_frame`
* **Lemma 6.49** — `proved`; planned: `Fig16.ResU.UpdV.trans`
* **Lemma 6.50** — `proved`; planned: `Fig16.BoLo.updV_outlives`
* **Lemma 6.51** — `proved`; planned: `Fig16.ResU.six51`
* **Lemma 6.52** — `proved`; planned: `Fig16.BoLo.updV_outlives`, `Fig16.ResU.six52`
* **Lemma 6.53** — `proved*`; planned: `Fig16.ResU.six53`
* **Lemma 6.54** — `proved`; planned: `Fig16.ResU.six54`
* **Lemma 6.55** — `proved*`; planned: `Fig16.ResU.six55`
* **Lemma 6.56** — `proved*`; planned: `Fig16.ResU.Lower.congr`, `Fig16.ResU.compS_single_imm`, `Fig16.ResU.six56`
* **Lemma 6.57** — `proved*`; planned: `Fig16.ResU.six57`
* **Lemma 6.58** — `proved*`; planned: `Fig16.ResU.six56`, `Fig16.ResU.six57`, `Fig16.ResU.six58_left`
* **Lemma 6.59** — `proved`; planned: `Fig16.ResU.six59`
* **Lemma 6.60** — `proved`; planned: `Fig16.LogRel.vDen_outlives`, `Fig16.LogRel.withbor2_compat`
* **Lemma 6.61** — `proved`; planned: `Fig16.ResU.six61`
* **Lemma 6.62** — `proved`; planned: `Fig16.LogRel.vDen_outlives`, `Fig16.LogRel.gDen_box`
* **Lemma 6.63** — `proved`; planned: —
-/
