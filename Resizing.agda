module Resizing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure
import Cubical.Data.Empty as Empty

{-# NO_UNIVERSE_CHECK #-}
record Ω : Type where
  field
    prf : Type
    prop : isProp prf


-- TODO: figure out how best to use the SIP machinery for this?
Ω/ext : {P Q : Ω} → Ω.prf P ≡ Ω.prf Q → P ≡ Q
Ω.prf (Ω/ext {P} {Q} PQ i) = PQ i
Ω.prop (Ω/ext {P} {Q} PQ i) = aux i
  where
    aux : PathP (λ i → isProp (PQ i)) (Ω.prop P) (Ω.prop Q)
    aux = toPathP (isPropIsProp (Ω.prop _) (Ω.prop Q))


{-# NO_UNIVERSE_CHECK #-}
record Resize (ℓ ℓ' : Level) (P : Type ℓ) (hP : isProp P) : Type ℓ' where
  constructor into
  field
    out : P

ResizeIso : {ℓ ℓ' : Level} (P : Type ℓ) (hP : isProp P) → Iso (Resize ℓ ℓ' P hP) P
Iso.fun (ResizeIso P hP) (into p) = p
Iso.inv (ResizeIso P _) x = into x
Iso.rightInv (ResizeIso P _) _ = refl
Iso.leftInv (ResizeIso P _) _ = refl

isPropResize : {ℓ ℓ' : Level} (P : Type ℓ) (hP : isProp P) → isProp (Resize ℓ ℓ' P hP)
isPropResize P hP = isOfHLevelRetractFromIso 1 (ResizeIso P hP) hP

resize-Ω : {ℓ : _} (P : Type ℓ) → isProp P → Ω
Ω.prf (resize-Ω P hP) = Resize _ _ P hP
Ω.prop (resize-Ω P hP) = isPropResize P hP


⊤ : Ω
Ω.prf ⊤ = Unit
Ω.prop ⊤ = isPropUnit

⊥ : Ω
Ω.prf ⊥ = Empty.⊥
Ω.prop ⊥ = Empty.isProp⊥

⊥-elim = Empty.elim

_⊓_ : Ω → Ω → Ω
Ω.prf (P ⊓ Q) = Ω.prf P × Ω.prf Q
Ω.prop (P ⊓ Q) = isProp× (Ω.prop P) (Ω.prop Q)

⋀' : {ℓ : Level} (A : Type ℓ) (B : A → Ω) → Type ℓ
⋀' A B = (x : A) → Ω.prf (B x)

isProp-⋀' : {ℓ : Level} (A : Type ℓ) (B : A → Ω) → isProp (⋀' A B)
isProp-⋀' A B = isPropΠ λ _ → Ω.prop (B _)

⋀ : {ℓ : Level} (A : Type ℓ) (B : A → Ω) → Ω
⋀ A B = resize-Ω (⋀' A B) (isProp-⋀' A B)

Ω/Σ : (P : Ω) (Q : Ω.prf P → Ω) → Ω
Ω.prf (Ω/Σ P Q) = Σ (Ω.prf P) λ p → Ω.prf (Q p)
Ω.prop (Ω/Σ P Q) = isPropΣ (Ω.prop P) λ p → Ω.prop (Q p)
