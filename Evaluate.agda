module Evaluate where

------------------------------------------------------------------------
-- A library for building intrinsically verified parsers in Cubical Agda
------------------------------------------------------------------------

------------------------------------------------------------------------
-- Language Primitives
------------------------------------------------------------------------
-- Definitions of strings as lists over an alphabet type
import String.Everything

-- Definitons of formal grammars as shallowly embedded linear types
-- Grammars map strings to type of parses
-- Grammar = String → Type
import Grammar.Everything

-- Functions between formal grammars
import Term.Everything

-- Definition 4.4 of a parser
import Parser.Everything

------------------------------------------------------------------------
-- Encodings of automata formalisms as formal grammars
------------------------------------------------------------------------
-- Encodings of DFAs, NFAs,
-- determinstic (but not necessarily finite) automata,
-- and Turing machines
import Automata.Everything

------------------------------------------------------------------------
-- Examples
------------------------------------------------------------------------
-- Includes verified parsesrs for the Dyck grammar, a parser for
-- a language of arithmetic expressions,
-- a regular expression parser, and expanded examples from Section 2
import Examples.Everything

-- A verification of Thompson's construction
-- From a regular expression r, construct a corresponding NFA
-- and prove that NFA is strongly equivalent to r
import Thompson.Everything

-- A verification of the powerset construction. Given an NFA,
-- build a corresponding DFA and prove that it recognizes the
-- same language
import Determinization.Everything

------------------------------------------------------------------------
-- Utilities
------------------------------------------------------------------------
-- A soft fork of the Cubical standard repository with the utilities
-- we needed when building this library
-- (ideally these get merged upstream at some point)
import Cubical.Everything

