{-# OPTIONS --prop --rewriting --guardedness #-}

module Preamble where

open import Agda.Builtin.Equality public
open import Agda.Builtin.Equality.Rewrite public
import PropLogic


postulate
  𝕊 : Set
  [_] : 𝕊 → Prop

module 𝕊 where
  postulate
    ⊥ : 𝕊
    ⊤ : 𝕊
    _&_ : (α : 𝕊) (β : [ α ] → 𝕊) → 𝕊
    _∥_ : (α β : 𝕊) → 𝕊

open PropLogic

postulate
  ⊥/elim : {A : Set} → [ 𝕊.⊥ ] → A
  ⊤/decode : [ 𝕊.⊤ ] ≡ ⊤
  &/decode : (α : 𝕊) (β : [ α ] → 𝕊) → [ α 𝕊.& β ] ≡ ([ α ] & λ x → [ β x ])
  ∥/decode : (α β : 𝕊) → [ α 𝕊.∥ β ] ≡ ([ α ] ∥ [ β ])
  {-# REWRITE ⊤/decode &/decode ∥/decode #-}


record L (A : Set) : Set where
  constructor partial
  field
    supp : 𝕊
    val : [ supp ] → A

open L public

L/bind : {A B : Set} → L A → (A → L B) → L B
supp (L/bind u f) = supp u 𝕊.& λ p → supp (f (val u p))
val (L/bind u f) = {!!}

data I : Set where
  alg : L I → I

record F : Set where
  coinductive
  field
    coalg : L F

open F public

∞ : F
supp (coalg ∞) = 𝕊.⊤
val (coalg ∞) _ = ∞

ε : I → F
supp (coalg (ε (alg x))) = supp x
val (coalg (ε (alg x))) p = ε (val x p)

record is-complete (A : Set) : Set where
  field
    lift : (I → A) → F → A
    lift/β : (x : I → A) → (i : I) → lift x (ε i) ≡ x i
    lift/ext : (x y : F → A) → ((i : I) → x (ε i) ≡ y (ε i)) → (i : F) → x i ≡ y i

  lift/η : (x : F → A) (i : F) → x i ≡ lift (λ i → x (ε i)) i
  lift/η x = lift/ext x (lift (λ i → x (ε i))) λ i → sym (lift/β (λ j → x (ε j)) i)

record is-well-complete (A : Set) : Set where
  field
    lift : (α : F → 𝕊) → ((i : I) → [ α (ε i) ] → A) → (i : F) → [ α i ] → A
    lift/β : (α : F → 𝕊) (x : (i : I) → [ α (ε i) ] → A) (i : I) (p : [ α (ε i) ]) → lift α x (ε i) p ≡ x i p
    lift/ext : (α : F → 𝕊) (x y : (i : F) → [ α i ] → A) → ((i : I) → x (ε i) ≡ y (ε i)) → (i : F) (p : [ α i ]) → x i p ≡ y i p


std-chain : {A : Set} (f : L A → L A) → (I → L A)
std-chain {A} f (alg u) = f (partial (supp u 𝕊.& λ p → supp (std-chain f (val u p))) λ p → val (std-chain f (val u (fst p))) (snd p))

zero : I
zero = alg (partial 𝕊.⊥ ⊥/elim)

postulate
  A : Set
  f : L A → L A

_ : std-chain f zero ≡ f (partial 𝕊.⊥ ⊥/elim)
_ = {!!}
