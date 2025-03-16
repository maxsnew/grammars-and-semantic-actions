module README where

------------------------------------------------------------------------
-- A library for building intrinsically verified parsers in Cubical Agda
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Module Hierarchy
------------------------------------------------------------------------

-- Definitions of strings as lists over an alphabet type
import String.Everything

-- Definitons of formal grammars as shallowly embedded linear types
-- Grammars map strings to type of parses
-- Grammar = String → Type
import Grammar.Everything

-- Functions between formal grammars
import Term.Everything

-- Encodings of Automata formalisms as formal grammars
import DFA.Everything
import Automaton.Everything
import NFA.Everything
import PDA.Everything
import Turing.Everything

-- Some example parsers
import Examples.Everything

-- A soft fork of the Cubical standard repository with the utilities
-- we needed when building this library
-- (ideally these get merged upstream at some point)
import Cubical.Everything

-- Definition 4.4 of a Parser
import Parser.Everything

-- An attempt at defining a "Lexer" as a translation between alphabets
-- This is very underdeveloped at the moment.
--
-- It is imported at a couple points in the String directory
-- for some experiments on ergonomic changes we could make to
-- the language, such as easily changing alphabets or reducing
-- to only a subset of characters
--
-- It is *not* used in any examples mentioned in the paper, nor
-- is it imported in any of Grammar, Term, DFA, Automaton, NFA,
-- PDA, Turing, Examples, Cubical, or Parser
import Lexer.Everything
