module Structures.All where
--
-- We are using Agda 2.5.3 with Brad Hardy's variant of the standard library:
-- https://github.com/bch29/agda-stdlib

-- ============================================================================================
-- Helpers
-- ============================================================================================

-- Creates forgetful functors from single sorted algebras to |Set|
-- 
import Forget

-- Re-exports all equality-related concepts
--
import EqualityCombinators

-- Contains properties about sums and products not found in standard library
--
import DataProperties

-- Houses contents brought over from RATH-Agda library.
-- import RATH
-- ‼ This module is not being called from anywhere ‼  June 9, 2017.

-- ============================================================================================
-- Variations on Sets
-- ============================================================================================

-- Considers |Set²|, pairs of sets.
--
import Structures.TwoSorted    

-- Considers pairs of sets along with a relation between them.
--
import Structures.Rel

-- Arrows in the one-object one-arrow category correspond to the functions to a singleton set.
import Structures.OneCat

-- A type along with a value of that type.
--
-- import Structures.Pointed
-- Currently has a hole

-- import Structures.Dependent
-- unsolved metas

-- import Structures.DistinguishedSubset
-- constraint issues

-- ============================================================================================
-- Unary Algebras
-- ============================================================================================

import Structures.UnaryAlgebra
import Structures.InvolutiveAlgebra
import Structures.IndexedUnaryAlgebra

-- ============================================================================================
-- Algebras with binary operators, Boom Hierarchy
-- ============================================================================================

import Structures.Magma        
import Structures.Semigroup
import Structures.Monoid
import Structures.CommMonoid
import Structures.CommMonoidTerm
-- import Structures.Multiset  -- has interaction points
-- import Structures.BagEquivalence
import Structures.AbelianGroup

-- ============================================================================================
-- Setoids
-- ============================================================================================

import SetoidEquiv
import SetoidOfIsos
import SetoidSetoid
import SetoidFamilyUnion

-- ============================================================================================
-- Equiv
-- ============================================================================================

import Equiv
import ISEquiv -- ought to be a lower-case `s`? As in `IsEquiv'?
import TypeEquiv

-- ============================================================================================
-- Misc
-- ============================================================================================

import Function2
import ParComp
import Belongs

-- |⊎⊎| not in scope
--
-- import CounterExample  
-- import Some
-- import Some-Alt  -- Multiple definitions of inSetoidEquiv


