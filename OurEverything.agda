-----------------------------------------------------------------------------------------------
-- The TheoriesAndDataStructures library
--
-- All library modules, along with short descriptions
--
-- Other experimental approaches can be found in the directory Experiments/
--
-- We are using Agda 2.5.3 with Brad Hardy's variant of the standard library:
-- https://github.com/bch29/agda-stdlib
-----------------------------------------------------------------------------------------------

module OurEverything where

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
-- ‼ This module is not being called from anywhere ‼

-- ============================================================================================
-- Variations on Sets
-- ============================================================================================

-- Arrows in the one-object one-arrow category correspond to the functions to a singleton set.
import Structures.OneCat

-- Category of algebras consisting of an index set and a family of sets on the index set. 
-- Along with forgetful functor to Sets with heterogenous equality and free functor, think “Σ”. 
--
-- Currently has a hole.
open import Structures.Dependent

-- “The” one-object one-arrow category, along with general free, forgetful, and adjoint constructions.
--
open import Structures.OneCat

-- Category of heterogenous relations along with a few forgetful and (co)free functors and
-- associated adjunction proofs.
--
open import Structures.Rel

-- Category of algebras of a predicate furnished type; c.f., Dependents.
-- Along with a forgetful functor to Sets.
--
-- Many simple-looking holes.
open import Structures.DistinguishedSubset

-- Category of pairs of sets with a few (co)free constructions.
-- Along with a proof that sum is adjoint to squaring which is adjoint to product.
--
open import Structures.TwoSorted

-- Category of pointed sets along with adjuntions with Sets and OneCat.
--
open import Structures.Pointed

-- ============================================================================================
-- Unary Algebras
-- ============================================================================================

-- Category of algebras consisting of a type endowed with an operator; along with
-- adjunctions with Sets.
-- The free structure corresponds to “performing a method” a number of times.
--
open import Structures.UnaryAlgebra 

-- Category of involutive algebras with a forgetful functor to Sets,
-- adjunctions, and (co)monads.
--
open import Structures.InvolutiveAlgebra

-- Category of algebras consisting of a carrier with a family of operations on it; i.e., actions.
-- Along with a forgetful functor to Sets and an initial algebra.
--
--
open import Structures.IndexedUnaryAlgebra

-- ============================================================================================
-- Algebras with binary operators, Boom Hierarchy
-- ============================================================================================

-- Interface for multisets over a given type, along with a free construction
-- via sequences.
--
open import Structures.Baguette

-- Category of Magmas along with explicit toolkit of operations for binary trees.
-- Also initial & terminal objects, along with adjunctions with OneCat.
--
open import Structures.Magma

-- Category of semigroups and an explicit theory of operators for non-empty lists.
-- Along with adjunctions with Sets, Magmas, and OneCat.
-- Also an involved proof of the non-existence of a certain adjunction:
-- There cannot be a (free) associative “extension” of an arbitrary binary operator.
--
open import Structures.Semigroup

-- Category of setoid-based commutative monoids over a given type, with a forgetful functor.
-- Free constructions can be found in baguette.lagda .
--
open import Structures.CommMonoid

-- Category of monoids with adjunctions with Sets and OneCat.
-- There are holes left intentionally for exposition purposes.
--
open import Structures.Monoid

-- A theory of bags; intend to be the free multisets.
-- ( A difficult read! )
--
open import Structures.SequencesAsBags

-- The category of Set-based Abelian groups, forgetful functor to Sets.
-- Work towards free construction; no free functor yet.
--
-- Contains a postulate.
open import Structures.AbelianGroup

-- ============================================================================================
-- ============================================================================================
-- ============================================================================================
-- The remaining modules are mostly technical ones needed for the strcuture-theory relationships.

-- open import FinUtils 
open import ParComp 
-- open import Some-Alt 
-- open import Belongs 
-- open import Forget 
-- open import Some 
-- open import CounterExample 
-- Data/
open import Function2
open import DataProperties 
open import ISEquiv 
open import report 
open import EqualityCombinators 

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

-- ============================================================================================
-- -- JC, these are from other projects?
-- ============================================================================================

open import Proofs
open import SubstLemmas
open import TypeEquivEquiv
open import FinEquivPlusTimes
open import EquivEquiv
open import LeqLemmas
open import FinEquivTypeEquiv
open import VectorLemmas
open import FiniteFunctions
open import FinNatLemmas
