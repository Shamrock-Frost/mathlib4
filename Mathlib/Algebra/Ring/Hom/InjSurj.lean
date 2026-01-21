/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston, Jireh Loreaux
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Algebra.Ring.Defs

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps
-/

public section

open Function

variable {R S : Type*}

/-- Pullback `IsDomain` instance along an injective function. -/
protected theorem Function.Injective.isDomain [Semiring R] [IsDomain R] [Semiring S] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) :
    IsDomain S where
  __ := domain_nontrivial f zero one
  __ := hf.isCancelMulZero f zero mul
