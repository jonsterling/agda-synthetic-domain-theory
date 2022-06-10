{-# OPTIONS --guardedness #-}

module Dominance where

open import Resizing
open import Cubical.Foundations.Everything
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.PropositionalTruncation using (∥_∥)

module _ {ℓ} (isOpen : Type ℓ → Type ℓ) where
  record isDominion : Type (ℓ-suc ℓ) where
    field
      isPropIsOpen : (A : Type ℓ) → isProp (isOpen A)
      isOpen→isProp : (A : Type ℓ) → isOpen A → isProp A
      isOpenUnit : isOpen Unit*
      isOpenSigma : (A : Type ℓ) (B : A → Type ℓ) → isOpen A → ((x : A) → isOpen (B x)) → isOpen (Σ A B)

  open isDominion public

  unquoteDecl isDominionIsoΣ = declareRecordIsoΣ isDominionIsoΣ (quote isDominion)

record Dominion ℓ : Type (ℓ-suc ℓ) where
  field
    isOpen : Type ℓ → Type ℓ
    isDominionIsOpen : isDominion isOpen

open Dominion public

module 𝕃 {ℓ} (𝒮 : Dominion ℓ) where

  -- This is a resizing axiom
  {-# NO_UNIVERSE_CHECK #-}
  record L {ℓ'} (A : Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      supp : Type ℓ
      suppIsOpen : 𝒮 .isOpen supp
      val : supp → A

  map : {ℓ' ℓ'' : _} {A : Type ℓ'} {B : Type ℓ''} (f : A → B) → L A → L B
  L.supp (map f x) = L.supp x
  L.suppIsOpen (map f x) = L.suppIsOpen x
  L.val (map f x) x↓ = f (L.val x x↓)

  record Alg ℓ' : Type (ℓ-suc (ℓ-max ℓ ℓ')) where
    field
      car : Type ℓ'
      force : L car → car

  record AlgHom {ℓ' ℓ''} (X : Alg ℓ') (Y : Alg ℓ'') : Type (ℓ-max ℓ (ℓ-max ℓ' ℓ'')) where
    field
      car : Alg.car X → Alg.car Y
      force : (x : L (Alg.car X)) → car (Alg.force X x) ≡ Alg.force Y (map car x)

  -- the initial L-algebra
  data ω : Type ℓ where
    alg : L ω → ω

  algInv : ω → L ω
  algInv (alg x) = x

  ωAlg : Alg _
  Alg.car ωAlg = ω
  Alg.force ωAlg = alg

  module _ {ℓ' : _} (X : Alg ℓ') where
    mutual
      ωAlgUnivMap : ω → Alg.car X
      ωAlgUnivMap (alg x) = Alg.force X (ωAlgUnivMapAux x)

      ωAlgUnivMapAux : L ω → L (Alg.car X)
      L.supp (ωAlgUnivMapAux x) = L.supp x
      L.suppIsOpen (ωAlgUnivMapAux x) = L.suppIsOpen x
      L.val (ωAlgUnivMapAux x) x↓ = ωAlgUnivMap (L.val x x↓)

    ωAlgUnivHom : AlgHom ωAlg X
    AlgHom.car ωAlgUnivHom = ωAlgUnivMap
    AlgHom.force ωAlgUnivHom x = refl


  -- the final L-coalgebra
  record ω* : Type ℓ where
    constructor coalgInv
    coinductive
    field
      coalg : L ω*

  ω*Alg : Alg ℓ
  Alg.car ω*Alg = ω*
  Alg.force ω*Alg = coalgInv

  coalgIso : Iso ω* (L ω*)
  Iso.fun coalgIso = ω*.coalg
  Iso.inv coalgIso = coalgInv
  Iso.rightInv coalgIso _ = refl
  ω*.coalg (Iso.leftInv coalgIso a _) = ω*.coalg a

  coalgIsEquiv : isEquiv ω*.coalg
  coalgIsEquiv = isoToIsEquiv coalgIso

  algIso : Iso (L ω) ω
  Iso.fun algIso = alg
  Iso.inv algIso = algInv
  Iso.rightInv algIso (alg _) = refl
  Iso.leftInv algIso _ = refl

  algIsEquiv : isEquiv ω.alg
  algIsEquiv = isoToIsEquiv algIso

  ε : ω → ω*
  ε = ωAlgUnivMap ω*Alg
