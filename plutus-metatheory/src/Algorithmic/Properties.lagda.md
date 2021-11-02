```
module Algorithmic.Properties where
```

## Imports

```
open import Utils
open import Type
open import Type.RenamingSubstitution
open import Type.BetaNormal
open import Algorithmic
open import Type.BetaNBE.RenamingSubstitution

open import Relation.Binary.HeterogeneousEquality using (_≅_;refl;≅-to-type-≡)
open import Relation.Binary.PropositionalEquality hiding ([_])
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

postulate lem-Λerror : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{L : ∅ ,⋆ K ⊢ B}{A : ∅ ⊢Nf⋆ *} → Λ L ≅ error {Γ = ∅} A → ⊥

postulate lem-Λunwrap : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *}{L : ∅ ,⋆ K ⊢ B}{K'}{A'}{B' : ∅ ⊢Nf⋆ K'}{L' : ∅ ⊢ μ A' B'} → Λ L ≅ _⊢_.unwrap L' → ⊥


postulate lem-Λ· : ∀{K}{B : ∅ ,⋆ K ⊢Nf⋆ *} → ∀{L : ∅ ,⋆ K ⊢ B} → ∀{A' B'}{L' : ∅ ⊢ A' ⇒ B'}{M'} → Λ L ≅ (L' _⊢_.· M') → ⊥

postulate lem-builtin·⋆ : ∀{b} → ∀{K'}{C : ∅ ,⋆ K' ⊢Nf⋆ *}{L' : ∅ ⊢ Π C}{A : ∅ ⊢Nf⋆ K'} → builtin {∅}{∅} b ≅ (L' _⊢_.·⋆ A) → ⊥

postulate lem-··⋆ : ∀{A B}{L : ∅ ⊢ A ⇒ B}{M} → ∀{K'}{C : ∅ ,⋆ K' ⊢Nf⋆ *}{L' : ∅ ⊢ Π C}{D : ∅ ⊢Nf⋆ K'} → L _⊢_.· M ≅ (L' _⊢_.·⋆ D) → ⊥

postulate lem-ƛ·⋆ : ∀{A B}{L : ∅ , A ⊢ B} → ∀{K'}{C : ∅ ,⋆ K' ⊢Nf⋆ *}{L' : ∅ ⊢ Π C}{D : ∅ ⊢Nf⋆ K'} → _⊢_.ƛ L ≅ (L' _⊢_.·⋆ D) → ⊥

open import Data.Sum

-- we can analyze the substitution when a substituted type equals
-- something in particular e.g., if it's a Pi there are only a couple
-- of possibilities:

lemma : ∀{K}{C : ∅ ,⋆ K ⊢⋆ *}{K'}{A : ∅ ⊢⋆ K'}{B : ∅ ,⋆ K' ⊢⋆ *}
  → Π C ≡ (B [ A ]) → (∃ λ K''
  → ∃ λ (B' : ∅ ,⋆ K' ,⋆ K'' ⊢⋆ *) → B ≡ Π B')
  ⊎
  (∃ λ K'' → ∃ λ (A' : ∅ ,⋆ K'' ⊢⋆ *) → ∃ λ p → subst (∅ ⊢⋆_) p A ≡  Π A' )
  -- ^ and B == ` Z
lemma {B = Π B} p = inj₁ (_ ,, _ ,, refl)
lemma {B = B ⇒ B'} ()
lemma {B = ` Z} refl = inj₂ (_ ,, _ ,, _ ,, refl)
lemma {B = B · B'} ()
lemma {B = con c} ()
lemma {B = μ B B'} ()

open import Type.BetaNBE.Stability
open import Type.BetaNBE

-- for normal types it's not so straightforward, A could be a lambda
-- which would cause some computatation

{-
lemmaNf: ∀{K}{C : ∅ ,⋆ K ⊢Nf⋆ *}{K'}{A : ∅ ⊢Nf⋆ K'}{B : ∅ ,⋆ K' ⊢Nf⋆ *}
  → Π C ≡ (B [ A ]Nf)
  → (∃ λ K'' → ∃ λ (B' : ∅ ,⋆ K' ,⋆ K'' ⊢Nf⋆ *) → B ≡ Π B')
  ⊎ (∃ λ K'' → ∃ λ (A' : ∅ ,⋆ K'' ⊢Nf⋆ *) → ∃ λ p → subst (∅ ⊢Nf⋆_) p A ≡  Π A' )
-}
-- -}
