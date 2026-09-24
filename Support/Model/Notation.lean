import Paper.S5_Model.Definitions

/-!
# Support — Model — Notation

`[about ours]`.  Nothing in this file is printed in the paper.  It holds what the
paper's definitions and results need in Lean and the paper leaves implicit:
the notation of the propositions of `[TR]` p. 6 (`⌜−⌝`, `⋆`, `─⋆`, `!`) and of `↓α`.  Declaration names are the source repository's (`borrow_lang` at
`970a9d0`), unchanged; `Bridge/Names.csv` maps each to its origin.
-/

noncomputable section

namespace BoCa.Fig16

@[inherit_doc] scoped notation:max "↓" a => Life.down a

end BoCa.Fig16

namespace BoCa.Fig16.BoLo

@[inherit_doc] scoped notation "⌜" p "⌝" => pure p

@[inherit_doc] scoped infixr:35 " ⋆ " => sep

@[inherit_doc] scoped infixr:27 " ─⋆ " => wand

@[inherit_doc] scoped prefix:max "!ₛ" => bang

end BoCa.Fig16.BoLo

end
