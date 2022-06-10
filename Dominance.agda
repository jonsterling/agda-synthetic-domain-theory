{-# OPTIONS --guardedness #-}

module Dominance where

open import Cubical.Core.Everything
open import Cubical.Foundations.Everything
open import Cubical.Reflection.RecordEquiv
open import Cubical.Reflection.StrictEquiv
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

  abstract
    isPropIsDominion : isProp isDominion
    isPropIsDominion =
      isOfHLevelRetractFromIso 1 isDominionIsoΣ
      (isPropΣ (isPropΠ λ _ → isPropIsProp) λ h →
       isPropΣ (isPropΠ2 (λ A A' → isPropIsProp)) λ _ →
       isPropΣ (h _) λ _ →
       isPropΠ4 λ _ _ _ _ → h (Σ _ _))

record Dominion ℓ : Type (ℓ-suc ℓ) where
  field
    isOpen : Type ℓ → Type ℓ
    isDominionIsOpen : isDominion isOpen

open Dominion public

module 𝕃 {ℓ𝒮} (𝒮 : Dominion ℓ𝒮) where

  private
    variable ℓ ℓ' : Level

  -- This is a resizing axiom
  {-# NO_UNIVERSE_CHECK #-}
  record L (A : Type ℓ) : Type (ℓ-max ℓ𝒮 ℓ) where
    field
      supp : Type ℓ𝒮
      suppIsOpen : 𝒮 .isOpen supp
      val : supp → A

  map : {A : Type ℓ} {B : Type ℓ'} (f : A → B) → L A → L B
  L.supp (map f x) = L.supp x
  L.suppIsOpen (map f x) = L.suppIsOpen x
  L.val (map f x) x↓ = f (L.val x x↓)

  record Alg ℓ : Type (ℓ-suc (ℓ-max ℓ𝒮 ℓ)) where
    field
      car : Type ℓ
      force : L car → car

  record AlgHom (X : Alg ℓ) (Y : Alg ℓ') : Type (ℓ-max ℓ𝒮 (ℓ-max ℓ ℓ')) where
    field
      car : Alg.car X → Alg.car Y
      force : (x : L (Alg.car X)) → car (Alg.force X x) ≡ Alg.force Y (map car x)

  -- The following is based on the module Cubical.Data.Nat.Algebra, which is based on the work of Awodey, Gambino, and Sojakova.
  record AlgFib (X : Alg ℓ) ℓ' : Type (ℓ-max ℓ𝒮 (ℓ-max ℓ (ℓ-suc ℓ'))) where
    field
      fib : Alg.car X → Type ℓ'
      fib-force : (x : L (Alg.car X)) → ((x↓ : L.supp x) → fib (L.val x x↓)) → fib (Alg.force X x)

  record AlgSec (X : Alg ℓ) (F : AlgFib X ℓ') : Type (ℓ-max ℓ𝒮 (ℓ-max ℓ ℓ')) where
    field
      sect : ∀ x → AlgFib.fib F x
      sect-force : (x : L (Alg.car X)) → sect (Alg.force X x) ≡ AlgFib.fib-force F x (λ x↓ → sect (L.val x x↓))

  isLiftHInitial : (X : Alg ℓ) (ℓ' : _) → Type _
  isLiftHInitial X ℓ' = (Y : Alg ℓ') → isContr (AlgHom X Y)

  isLiftInductive : (X : Alg ℓ) (ℓ' : _) → Type _
  isLiftInductive X ℓ' = (S : AlgFib X ℓ') → AlgSec X S

  module AlgPropositionality {X : Alg ℓ'} where
    isPropIsLiftHInitial : isProp (isLiftHInitial X ℓ)
    isPropIsLiftHInitial = isPropΠ (λ _ → isPropIsContr)

    module SectionProp (ind : isLiftInductive X ℓ) {F : AlgFib X ℓ} (S T : AlgSec X F) where
      connectingFiber : AlgFib X ℓ
      AlgFib.fib connectingFiber x = AlgSec.sect S x ≡ AlgSec.sect T x
      AlgFib.fib-force connectingFiber x h = AlgSec.sect-force S x ∙∙ cong (AlgFib.fib-force F x) (funExt h) ∙∙ sym (AlgSec.sect-force T x)

      module U = AlgSec (ind connectingFiber)

      -- I hate this!
      squeezeSquare : ∀{a}{A : Type a} {w x y z : A} (p : w ≡ x) {q : x ≡ y} (r : z ≡ y) (P : w ≡ z) (sq : P ≡ p ∙∙ q ∙∙ sym r) → I → I → A
      squeezeSquare p {q} r P sq i j = transport (sym (PathP≡doubleCompPathʳ p P q r)) sq i j

      S≡T : S ≡ T
      AlgSec.sect (S≡T i) x = U.sect x i
      AlgSec.sect-force (S≡T i) x j = squeezeSquare (AlgSec.sect-force S x) (AlgSec.sect-force T x) (U.sect (Alg.force X x)) (U.sect-force x) j i

    isPropIsLiftInductive : isProp (isLiftInductive X ℓ')
    isPropIsLiftInductive a b i F = SectionProp.S≡T a (a F) (b F) i


  module AlgebraHInd→HInit {N : Alg ℓ'} (ind : isLiftInductive N ℓ) (M : Alg ℓ) where
    open Alg
    open AlgFib

    constFibM : AlgFib N ℓ
    fib constFibM _ = M .car
    fib-force constFibM x h = M .force aux
      where
        aux : L _
        L.supp aux = L.supp x
        L.suppIsOpen aux = L.suppIsOpen x
        L.val aux = h

    AlgHom→AlgSec : AlgHom N M → AlgSec N constFibM
    AlgSec.sect (AlgHom→AlgSec f) = AlgHom.car f
    AlgSec.sect-force (AlgHom→AlgSec f) = AlgHom.force f

    AlgSec→AlgHom : AlgSec N constFibM → AlgHom N M
    AlgHom.car (AlgSec→AlgHom x) = AlgSec.sect x
    AlgHom.force (AlgSec→AlgHom x) = AlgSec.sect-force x

    Hom≡Sec : AlgSec _ constFibM ≡ AlgHom N M
    Hom≡Sec = ua e
      where
      unquoteDecl e = declStrictEquiv e AlgSec→AlgHom AlgHom→AlgSec

    isContrHom : isContr (AlgHom N M)
    isContrHom = subst isContr Hom≡Sec (inhProp→isContr (ind constFibM) (AlgPropositionality.SectionProp.S≡T ind))


  module AlgHInit→Ind (N : Alg ℓ') ℓ (hinit : isLiftHInitial N (ℓ-max ℓ' ℓ)) (F : AlgFib N (ℓ-max ℓ' ℓ)) where

    totAlg : Alg (ℓ-max ℓ' ℓ)
    Alg.car totAlg = Σ (Alg.car N) (AlgFib.fib F)
    fst (Alg.force totAlg x) = Alg.force N (map fst x)
    snd (Alg.force totAlg x) = AlgFib.fib-force F (map fst x) (λ x↓ → snd (L.val x x↓))

    hoistN : Alg (ℓ-max ℓ' ℓ)
    Alg.car hoistN = Lift {ℓ'} {ℓ-max ℓ' ℓ} (Alg.car N)
    Alg.force hoistN x = lift (Alg.force N (map lower x))

    _!_ : ∀ {x y} → x ≡ y → AlgFib.fib F x → AlgFib.fib F y
    _!_ = subst (AlgFib.fib F)

    hoistHom : AlgHom N hoistN
    AlgHom.car hoistHom x = lift x
    AlgHom.force hoistHom x = cong lift (cong (Alg.force N) aux)
      where
      aux : x ≡ map (lower {ℓ'} {ℓ-max ℓ' ℓ}) (map lift x)
      L.supp (aux i) = L.supp x
      L.suppIsOpen (aux i) = L.suppIsOpen x
      L.val (aux i) = L.val x


    -- TO BE CONTINUED



  -- the initial L-algebra
  data ω : Type ℓ𝒮 where
    alg : L ω → ω

  algInv : ω → L ω
  algInv (alg x) = x

  ωAlg : Alg _
  Alg.car ωAlg = ω
  Alg.force ωAlg = alg

  module _ (X : Alg ℓ) where
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

    ωAlgUnivMapUniq : (f : AlgHom ωAlg X) → AlgHom.car f ≡ ωAlgUnivMap
    ωAlgUnivMapUniq f = funExt λ x → sym (aux x)
      where
      aux : (x : ω) → ωAlgUnivMap x ≡ AlgHom.car f x
      aux (alg x) =
        ωAlgUnivMap (alg x) ≡⟨ cong (Alg.force X) aux' ⟩
        Alg.force X (map (AlgHom.car f) x) ≡⟨ sym (AlgHom.force f x) ⟩
        AlgHom.car f (alg x) ∎
        where
          aux' : map ωAlgUnivMap x ≡ map (AlgHom.car f) x
          L.supp (aux' i) = L.supp x
          L.suppIsOpen (aux' i) = L.suppIsOpen x
          L.val (aux' i) x↓ = aux (L.val x x↓) i


  -- the final L-coalgebra
  record ω* : Type ℓ𝒮 where
    constructor coalgInv
    coinductive
    field
      coalg : L ω*

  ω*Alg : Alg ℓ𝒮
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
