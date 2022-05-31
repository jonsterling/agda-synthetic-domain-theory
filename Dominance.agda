{-# OPTIONS --guardedness #-}

module Dominance where

open import Resizing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Reflection.RecordEquiv
open import Cubical.Data.Sigma

module _ {ℓ} (𝒮 : Ω → Type ℓ) where
  HasTrue = 𝒮 ⊤
  HasDepConj = (P Q : Ω) → 𝒮 P → (Ω.prf P → 𝒮 Q) → 𝒮 (P ⊓ Q)
  HasSigma = (P : Ω) (Q : Ω.prf P → Ω) (hP : 𝒮 P) (hQ : (p : Ω.prf P) → 𝒮 (Q p)) → 𝒮 (Ω/Σ P Q)

  abstract
    HasDepConj→HasSigma : HasDepConj → HasSigma
    HasDepConj→HasSigma h𝒮 P Q hP hQ =
      subst 𝒮 lem' (h𝒮 P (⋀ (Ω.prf P) λ p → Q p) hP lem)

      where
      lem : Ω.prf P → 𝒮 (⋀ (Ω.prf P) (λ p → Q p))
      lem p = subst 𝒮 (Ω/ext (hPropExt (Ω.prop (Q p)) (Ω.prop (⋀ (Ω.prf P) Q)) fwd bwd)) (hQ p)
        where
        fwd : Ω.prf (Q p) → Ω.prf (⋀ (Ω.prf P) Q)
        fwd x = into λ p' → subst (λ z → Ω.prf (Q z)) (Ω.prop P p p') x

        bwd : Ω.prf (⋀ (Ω.prf P) Q) → Ω.prf (Q p)
        bwd (into x) = x p

      lem' : (P ⊓ ⋀ (Ω.prf P) (λ p → Q p)) ≡ Ω/Σ P Q
      lem' = Ω/ext (hPropExt (Ω.prop (P ⊓ ⋀ (Ω.prf P) Q)) (isPropΣ (Ω.prop P) λ p → Ω.prop (Q p)) fwd bwd)
        where
        fwd : Ω.prf (P ⊓ ⋀ (Ω.prf P) Q) → Σ (Ω.prf P) (λ z → Ω.prf (Q z))
        fst (fwd (p , _)) = p
        snd (fwd (p , into q)) = q p

        bwd : Σ (Ω.prf P) (λ z → Ω.prf (Q z)) → Ω.prf (P ⊓ ⋀ (Ω.prf P) Q)
        fst (bwd (p , q)) = p
        snd (bwd (p , q)) = into λ p' → subst (λ z → Ω.prf (Q z)) (Ω.prop P p p') q

  record IsDominion : Type (ℓ-suc ℓ) where
    field
      isPropValued : (P : Ω) → isProp (𝒮 P)
      hasTrue : HasTrue
      hasDepConj : HasDepConj

    hasSigma = HasDepConj→HasSigma hasDepConj

unquoteDecl IsDominionIsoΣ = declareRecordIsoΣ IsDominionIsoΣ (quote IsDominion)

isPropIsDominion : {ℓ : _} (𝒮 : Ω → Type ℓ) → isProp (IsDominion 𝒮)
isPropIsDominion 𝒮 =
  isOfHLevelRetractFromIso 1 IsDominionIsoΣ
    (isPropΣ (isPropΠ λ _ → isPropIsProp) λ prop-valued →
     isPropΣ (prop-valued _) λ _ →
     isPropΠ4 (λ _ _ _ _ → prop-valued _))


module Dominance (𝒮 : Ω → Type) (h𝒮 : IsDominion 𝒮) where
  𝕊 : Type
  𝕊 = Σ[ α ∈ Ω ] 𝒮 α

  [_] : 𝕊 → Type
  [ ϕ ] = Ω.prf (fst ϕ)

  isProp[_] : (ϕ : 𝕊) → isProp [ ϕ ]
  isProp[ ϕ ] = Ω.prop (fst ϕ)

  Ω/[_] : 𝕊 → Ω
  Ω/[ ϕ ] = fst ϕ

  [_]∈𝒮 : (ϕ : 𝕊) → 𝒮 Ω/[ ϕ ]
  [ ϕ ]∈𝒮 = snd ϕ

  𝕊/⊤ : 𝕊
  fst 𝕊/⊤ = ⊤
  snd 𝕊/⊤ = IsDominion.hasTrue h𝒮

  𝕊/& : (ϕ : 𝕊) (ψ : Ω) → ([ ϕ ] → 𝒮 ψ) → 𝕊
  fst (𝕊/& ϕ ψ hψ) = Ω/[ ϕ ] ⊓ ψ
  snd (𝕊/& ϕ ψ hψ) = IsDominion.hasDepConj h𝒮 Ω/[ ϕ ] ψ [ ϕ ]∈𝒮 hψ

  𝕊/Σ : (ϕ : 𝕊) (ψ : [ ϕ ] → 𝕊) → 𝕊
  fst (𝕊/Σ ϕ ψ) = Ω/Σ Ω/[ ϕ ] λ x → Ω/[ ψ x ]
  snd (𝕊/Σ ϕ ψ) = IsDominion.hasSigma h𝒮 Ω/[ ϕ ] (λ x → Ω/[ ψ x ]) [ ϕ ]∈𝒮 λ x → [ ψ x ]∈𝒮

  record L {ℓ : _} (A : Type ℓ) : Type ℓ where
    constructor partial
    field
      supp : 𝕊
      val : [ supp ] → A

  open L public

  module 𝕃 where
    η : {ℓ : _} {A : Type ℓ} → A → L A
    supp (η x) = 𝕊/⊤
    val (η x) _ = x

    module _ {ℓ ℓ' : _} {A : Type ℓ} {B : Type ℓ'} where
      bind : (u : L A) (f : A → L B) → L B
      supp (bind u f) = 𝕊/Σ (supp u) λ x → supp (f (val u x))
      val (bind u f) (p , q) = val (f (val u p)) q

      map : (f : A → B) (u : L A) → L B
      supp (map f u) = supp u
      val (map f u) u↓ = f (val u u↓)


module SDT (𝒮 : Ω → Type) (h𝒮 : IsDominion 𝒮) (hasFalse : 𝒮 ⊥) where
  open Dominance 𝒮 h𝒮

  𝕊/⊥ : 𝕊
  fst 𝕊/⊥ = ⊥
  snd 𝕊/⊥ = hasFalse

  -- the initial L-algebra
  data 𝕀 : Type where
    alg : L 𝕀 → 𝕀

  -- the final L-coalgebra
  record 𝔽 : Type where
    coinductive
    field
      coalg : L 𝔽

  z : 𝕀
  z = alg (partial 𝕊/⊥ ⊥-elim)

  -- is this the correct definition of the successor?
  s : 𝕀 → 𝕀
  s x = alg (𝕃.η x)

  ε : 𝕀 → 𝔽
  supp (𝔽.coalg (ε (alg x))) = supp x
  val (𝔽.coalg (ε (alg x))) x↓ = ε (val x x↓)

  ∞ : 𝔽
  supp (𝔽.coalg ∞) = 𝕊/⊤
  val (𝔽.coalg ∞) _ = ∞

  module _ {ℓ ℓ' : _} {A : Type ℓ} {B : Type ℓ'} where
    IsEquable : (f : A → B) → Type _
    IsEquable f = isEquiv {A = B → 𝕊} {B = A → 𝕊} λ ϕ x → ϕ (f x)

    isPropIsEquable : (f : A → B) → isProp (IsEquable f)
    isPropIsEquable f = isPropIsEquiv _

  IsReplete : (ℓ : _) {ℓ' : _} (A : Type ℓ') → Type (ℓ-max (ℓ-suc ℓ) ℓ')
  IsReplete ℓ A =
    (I J : Type ℓ) (i : J → I)
    → IsEquable i
    → isEquiv {A = I → A} {B = J → A} (λ a j → a (i j))

  isPropIsReplete : {ℓ ℓ' : _} (A : Type ℓ') → isProp (IsReplete ℓ A)
  isPropIsReplete A = isPropΠ4 λ _ _ _ _ → isPropIsEquiv _
