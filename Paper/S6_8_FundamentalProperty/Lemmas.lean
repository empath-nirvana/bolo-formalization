/-!
# [TR] §6.8 Fundamental Property  (pp. 40–49)



**Stage 2.**  This file will hold the numbered results of the subsection, in printed order,
each under its printed statement and proof, with the Lean declaration moved from the
source and a numbered alias.  The results, with the inventory's status and the
declaration `Bridge/Plan.csv` assigns to each:

* **Lemma 6.151** (Fundamental Property) — `proved*`; planned: `Fig16.LogRel.Typed.fundamentalProperty`
* **Lemma 6.152** (id-compat) — `proved`; planned: `Fig16.LogRel.id_compat`
* **Lemma 6.153** (1I-compat) — `proved`; planned: `Fig16.LogRel.unitI_compat`
* **Lemma 6.154** (1E-compat) — `proved`; planned: `Fig16.LogRel.unitE_compat`
* **Lemma 6.155** (⊗I-compat) — `proved`; planned: `Fig16.LogRel.tensorI_compat`
* **Lemma 6.156** (⊗E-compat) — `proved`; planned: `Fig16.LogRel.tensorE_compat`
* **Lemma 6.157** (⊕I-compat) — `proved`; planned: `Fig16.LogRel.sumI₁_compat`
* **Lemma 6.158** (⊕E-compat) — `proved`; planned: `Fig16.LogRel.sumE_compat`
* **Lemma 6.159** (⊸I-compat) — `proved`; planned: `Fig16.LogRel.lolliI_compat`
* **Lemma 6.160** (⊸E-compat) — `proved`; planned: `Fig16.LogRel.lolliE_compat`
* **Lemma 6.161** (∀ I-compat) — `variant`; planned: `Fig16.LogRel.allI_compat`
* **Lemma 6.162** (∀ E-compat) — `proved`; planned: `Fig16.LogRel.allE_compat`
* **Lemma 6.163** ([] I-compat) — `proved`; planned: `Fig16.LogRel.gDen_box`, `Fig16.LogRel.boxI_compat`
* **Lemma 6.164** ([] E-compat) — `proved`; planned: `Fig16.LogRel.boxE_compat`
* **Lemma 6.165** (alloc -compat) — `proved`; planned: `Fig16.LogRel.alloc_compat`
* **Lemma 6.166** (free -compat) — `proved`; planned: `Fig16.LogRel.free_compat`
* **Lemma 6.167** (⊑imm-compat) — `proved`; planned: `Fig16.LogRel.immSub_compat`
* **Lemma 6.168** (⊑mut-compat) — `proved`; planned: `Fig16.LogRel.mutSub_compat`
* **Lemma 6.169** (swap-compat) — `proved`; planned: `Fig16.LogRel.swap_compat`
* **Lemma 6.170** (copy-compat) — `proved`; planned: `Fig16.BoLo.ptoImm_dup`, `Fig16.LogRel.copy_compat`
* **Lemma 6.171** (forget-compat) — `proved`; planned: `Fig16.LogRel.forgetImm_compat`
* **Lemma 6.172** (withbor-compat1) — `variant`; planned: `Fig16.LogRel.wp_I_frame`, `Fig16.LogRel.withbor1_compat`
* **Lemma 6.173** (withbor-compat2) — `variant`; planned: `Fig16.LogRel.wp_M_frame`, `Fig16.LogRel.withbor2_compat`
* **Lemma 6.174** (withbor-compat3) — `variant`; planned: `Fig16.LogRel.withbor3_compat`
* **Lemma 6.175** (withload-compat) — `proved*`; planned: `Fig16.LogRel.reborrow_vDen_fresh`, `Fig16.LogRel.pure_sep_reborrow_vDen_fresh`, `Fig16.BoLo.wp_load_I`
* **Lemma 6.176** (withswap-compat) — `proved`; planned: `Fig16.LogRel.wp_M_antiFrame`, `Fig16.LogRel.withswap_compat`
-/
