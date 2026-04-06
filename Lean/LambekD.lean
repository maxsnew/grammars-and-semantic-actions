-- This module serves as the root of the `LambekD` library.
import LambekD.Elab
import LambekD.Examples.ElabExamples
-- Grammar theory (ported from Agda)
import LambekD.Grammar.Properties.Base
import LambekD.Grammar.Distributivity
import LambekD.Grammar.KleeneStar.Base
import LambekD.Grammar.String.Base
import LambekD.Grammar.String.Terminal
-- Parser and automata (ported from Agda)
import LambekD.Parser.Base
import LambekD.Automata.Deterministic
import LambekD.Automata.DFA.Base
import LambekD.Automata.NFA.Base
-- Thompson's construction (ported from Agda)
import LambekD.Grammar.RegularExpression.Base
import LambekD.Thompson.Construction
import LambekD.Thompson.Equivalence
-- Determinization (ported from Agda)
import LambekD.Determinization.WeakEquivalence
-- Examples (ported from Agda)
import LambekD.Examples.Dyck
import LambekD.Examples.BinOp
