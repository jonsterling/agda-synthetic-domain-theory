{-# OPTIONS --prop --rewriting #-}

module PropLogic where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

sym : {A : Set} {u v : A} → u ≡ v → v ≡ u
sym refl = refl

record ⊤ : Prop where
  constructor ⟨⟩

record _&_ (P : Prop) (Q : P → Prop) : Prop where
  field
    fst : P
    snd : Q fst

open _&_ public

data _∥_ (P Q : Prop) : Prop where
  inl : P → P ∥ Q
  inr : Q → P ∥ Q

postulate
  _≣_ : {A : Set} (u v : A) → Prop
  ≣/ι : {A : Set} {u v : A} → u ≡ v → u ≣ v
  ≣/π : {A : Set} {u v : A} → u ≣ v → u ≡ v

module _ {P Q : Prop} {A : Set} where
  postulate
    split : (p : P → A) (q : Q → A) (pq : (i : P) (j : Q) → p i ≡ q j) → P ∥ Q → A
    split/β/inl : (p : P → A) (q : Q → A) (pq : (i : P) (j : Q) → p i ≡ q j) (i : P) → split p q pq (inl i) ≡ p i
    split/β/inr : (p : P → A) (q : Q → A) (pq : (i : P) (j : Q) → p i ≡ q j) (j : Q) → split p q pq (inr j) ≡ q j

  split/ext : (f g : P ∥ Q → A) → ((i : P) → f (inl i) ≡ g (inl i)) → ((j : Q) → f (inr j) ≡ g (inr j)) → (i : P ∥ Q) → f i ≡ g i
  split/ext f g hp hq i = ≣/π (aux i)
    where
    aux : (i : P ∥ Q) → f i ≣ g i
    aux (inl x) = ≣/ι (hp x)
    aux (inr x) = ≣/ι (hq x)

  split/η : (f : P ∥ Q → A) (i : P ∥ Q) → f i ≡ split (λ x → f (inl x)) (λ x → f (inr x)) (λ _ _ → refl) i
  split/η f =
    split/ext f
      (λ i → split (λ x → f (inl x)) (λ x → f (inr x)) (λ _ _ → refl) i)
      (λ x → sym (split/β/inl (λ _ → f _) (λ _ → f _) (λ _ _ → refl) x))
      (λ x → sym (split/β/inr (λ _ → f _) (λ _ → f _) (λ _ _ → refl) x))
