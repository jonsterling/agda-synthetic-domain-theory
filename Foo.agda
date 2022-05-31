{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Everything
open import Agda.Primitive using (SSet)

module Foo where

data L (A : SSet) : SSet where
  foo : (supp : I) (a : IsOne supp → A) → L A
