import Lean

/-!
# Syntax declarations for the ordered linear DSL

gterm and gpat syntax categories and their productions.
-/

namespace LambekD.Elab

declare_syntax_cat gterm

syntax ident : gterm
syntax num : gterm
syntax "#(" term ")" : gterm
syntax "ε" : gterm
syntax "tt" : gterm
syntax "(" gterm ", " gterm ")" : gterm
syntax "let" "(" ident ", " ident ")" "=" gterm "in" gterm : gterm
syntax "let" "⟨⟩" "=" gterm "in" gterm : gterm
syntax "let" "(" ")" "=" gterm "in" gterm : gterm
syntax "fun" "(" ident ":" term ")" "=>" gterm : gterm
syntax "funL" "(" ident ":" term ")" "=>" gterm : gterm
syntax:10 gterm:10 gterm:11 : gterm
syntax "⟨" gterm ", " gterm "⟩" : gterm
syntax "fst" gterm:11 : gterm
syntax "snd" gterm:11 : gterm
syntax "inl" gterm:11 : gterm
syntax "inr" gterm:11 : gterm
syntax "case" gterm "of" "|" "inl" ident "=>" gterm
                         "|" "inr" ident "=>" gterm : gterm
syntax "absurd" gterm : gterm
syntax "#[" term "]" gterm:11 : gterm
syntax "Λ" "(" ident ":" term ")" "=>" gterm : gterm
syntax gterm:10 "⌈" term "⌉" : gterm
syntax "σ⟨" term ", " gterm "⟩" : gterm
syntax "caseDep" gterm "of" "|" "σ⟨" ident ", " ident "⟩" "=>" gterm : gterm
syntax "fold" ident gterm:11 : gterm
declare_syntax_cat gbranchVar
syntax ident : gbranchVar
syntax "(" term ")" : gbranchVar

syntax (name := recGterm) "rec" gterm ("as" ident)? "of" ("|" ident gbranchVar+ "=>" gterm)* : gterm
syntax (name := caseIndGterm) "case" gterm "of" ("|" ident gbranchVar+ "=>" gterm)+ : gterm
syntax "sorry" : gterm
syntax "(" gterm ")" : gterm

declare_syntax_cat gpat
syntax ident : gpat
syntax "(" ident ":" term ")" : gpat
syntax "⟨" gpat ", " gpat "⟩" : gpat

syntax "[|" gpat+ " => " gterm "|]" : term

end LambekD.Elab
