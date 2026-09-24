/-!
# [TR] §6.7 Weakest Precondition Rules  (pp. 35–40)



**Stage 2.**  This file will hold the numbered results of the subsection, in printed order,
each under its printed statement and proof, with the Lean declaration moved from the
source and a numbered alias.  The results, with the inventory's status and the
declaration `Bridge/Plan.csv` assigns to each:

* **Lemma 6.135** (wp-bind) — `proved`; planned: `Fig16.BoLo.wp_bind`
* **Lemma 6.136** (wp-val) — `proved`; planned: `Fig16.BoLo.wp_val`
* **Lemma 6.137** (wp1) — `proved`; planned: `Fig16.BoLo.wp_1`
* **Lemma 6.138** (wp⊗) — `proved`; planned: `Fig16.BoLo.wp_tensor`
* **Lemma 6.139** (wp⊕) — `proved`; planned: `Fig16.BoLo.wp_sum₁`
* **Lemma 6.140** (wp⊸) — `proved`; planned: `Fig16.BoLo.wp_lolli`
* **Lemma 6.141** (wp-alloc) — `proved`; planned: `Fig16.BoLo.wp_alloc`
* **Lemma 6.142** (wp-free) — `proved`; planned: `Fig16.BoLo.wp_free`
* **Lemma 6.143** (wp-load) — `proved`; planned: `Fig16.BoLo.wp_load`
* **Lemma 6.144** (wp-load-I) — `proved`; planned: `Fig16.BoLo.wp_load_I`, `Fig16.BoLo.wp_load_I_nonvacuous`
* **Lemma 6.145** (wp-store) — `proved`; planned: `Fig16.BoLo.wp_store`
* **Lemma 6.146** (wp-ramify) — `proved`; planned: `Fig16.BoLo.wp_ramify`
* **Lemma 6.147** (wp[]) — `proved`; planned: `Fig16.BoLo.wp_box`
* **Lemma 6.148** (wp-M-forget) — `proved`; planned: `Fig16.BoLo.wp_M_forget`
* **Lemma 6.149** (wp-I-forget) — `proved`; planned: `Fig16.BoLo.wp_I_forget`
* **Theorem 6.150** (↺ rule) — `proved*`; planned: `Fig16.ResU.six55`, `Fig16.ResU.six58_left`, `Fig16.BoLo.wp_reborrow`
-/
