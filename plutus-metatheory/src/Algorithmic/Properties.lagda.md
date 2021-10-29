```
module Algorithmic.Properties where
```

## Imports

```
open import Utils
open import Type
open import Type.BetaNormal
open import Algorithmic
open import Type.BetaNBE.RenamingSubstitution

open import Relation.Binary.HeterogeneousEquality using (_≅_;refl)
open import Relation.Binary.PropositionalEquality
open import Data.Product renaming (_,_ to _,,_)
open import Data.Empty
```

## Pragmas

```
{-# INJECTIVE _⊢_ #-}
```

## Some syntactic lemmas

```
lem-·⋆' : ∀{K K'}{A : ∅ ⊢Nf⋆ K}{A' : ∅ ⊢Nf⋆ K'}{B : ∅ ,⋆ K ⊢Nf⋆ *}{B' : ∅ ,⋆ K' ⊢Nf⋆ *}
  → ∀{M : ∅ ⊢ Π B}{M' : ∅ ⊢ Π B'}
  → M' _⊢_.·⋆ A' ≅ M _⊢_.·⋆ A
  → K ≅ K' × A ≅ A' × B ≅ B' × M ≅ M'
lem-·⋆' refl = refl ,, refl ,, refl ,, refl

lem-·⋆ : ∀{K K'}{A : ∅ ⊢Nf⋆ K}{A' : ∅ ⊢Nf⋆ K'}{B B'}
  → (o : K ≡ K')
  → (p : subst (∅ ⊢Nf⋆_) o A ≡ A')
  → (q : Π B ≡ Π B')
  → (r : B [ A ]Nf ≡ B' [ A' ]Nf)
  → ∀{M}
  → subst (∅ ⊢_) q M ·⋆ A' ≡ subst (∅ ⊢_) r (M ·⋆ A)
lem-·⋆ refl refl refl refl = refl

lem-·⋆wrap : ∀{K K'}{A : ∅ ⊢Nf⋆ K}{A'}{B : ∅ ,⋆ K ⊢Nf⋆ *}{B' : ∅ ⊢Nf⋆ K'}
  → ∀{M : ∅ ⊢ Π B}{M' : ∅ ⊢ _}
  → M _⊢_.·⋆ A ≅ _⊢_.wrap A' B' M'
  → ⊥
lem-·⋆wrap ()

lem-·⋆unwrap : ∀{K K'}{A : ∅ ⊢Nf⋆ K}{A'}{B : ∅ ,⋆ K ⊢Nf⋆ *}{B' : ∅ ⊢Nf⋆ K'}
  → ∀{M : ∅ ⊢ Π B}{M' : ∅ ⊢ μ A' B'}
  → M _⊢_.·⋆ A ≅ _⊢_.unwrap M'
  → ⊥
lem-·⋆unwrap ()

lem-unwrap : ∀{K K'}{A}{A'}{B : ∅ ⊢Nf⋆ K}{B' : ∅ ⊢Nf⋆ K'}
  → ∀{M : ∅ ⊢ μ A B}{M' : ∅ ⊢ μ A' B'}
  → _⊢_.unwrap M ≅ _⊢_.unwrap M'
  → A ≅ A' × B ≅ B' × M ≅ M'
lem-unwrap refl = refl ,, refl ,, refl

inj⊢ : ∀{A A' : ∅ ⊢Nf⋆ *}{L : ∅ ⊢ A}{L' : ∅ ⊢ A'} → L ≅ L' → A ≡ A'
inj⊢ refl = refl

lem-Λ·⋆ : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}
  → ∀{L : ∅ ,⋆ K ⊢ B}
  → ∀{K'}{C : ∅ ,⋆ K' ⊢Nf⋆ *}{L' : ∅ ⊢ Π C}{A : ∅ ⊢Nf⋆ K'}
  → Λ L ≅ (L' _⊢_.·⋆ A)
  → ⊥
lem-Λ·⋆ ()

postulate lem-Λ· : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *} → ∀{L : ∅ ,⋆ K ⊢ B} → ∀{A' B'}{L' : ∅ ⊢ A' ⇒ B'}{M'} → Λ L ≅ (L' _⊢_.· M') → ⊥

postulate lem-builtin·⋆ : ∀{b} → ∀{K'}{C : ∅ ,⋆ K' ⊢Nf⋆ *}{L' : ∅ ⊢ Π C}{A : ∅ ⊢Nf⋆ K'} → builtin {∅}{∅} b ≅ (L' _⊢_.·⋆ A) → ⊥

postulate lem-··⋆ : ∀{A B}{L : ∅ ⊢ A ⇒ B}{M} → ∀{K'}{C : ∅ ,⋆ K' ⊢Nf⋆ *}{L' : ∅ ⊢ Π C}{D : ∅ ⊢Nf⋆ K'} → L _⊢_.· M ≅ (L' _⊢_.·⋆ D) → ⊥

postulate lem-ƛ·⋆ : ∀{A B}{L : ∅ , A ⊢ B} → ∀{K'}{C : ∅ ,⋆ K' ⊢Nf⋆ *}{L' : ∅ ⊢ Π C}{D : ∅ ⊢Nf⋆ K'} → _⊢_.ƛ L ≅ (L' _⊢_.·⋆ D) → ⊥

