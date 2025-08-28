----------------------------------------------------------------------------------------------------
-- Syntax basics.
--
-- This file defines directions for sessions, steps/paths, and renamings.

module PrefixStripping.Syntax where

open import PrefixStripping.Prelude
open import Relation.Binary
open import Function using (Injective)
open import Data.List using (List)

open Nat.Variables

open Fin using (_↑ˡ_; _↑ʳ_) public

variable α α′ α″ α₁ α₂ α₃ : 𝔽 n

----------------------------------------------------------------------------------------------------
-- Directions for session types. Used for differentiate between send/recieve, internal/external
-- choice, and Term/Wait.

data Dir : Set where
  ‼ ⁇ : Dir

variable ⁉ ⁉₁ ⁉₂ : Dir

infix 4 _≟⁉_

_≟⁉_ : DecidableEquality Dir
‼ ≟⁉ ‼ = yes refl
⁇ ≟⁉ ⁇ = yes refl
‼ ≟⁉ ⁇ = no λ()
⁇ ≟⁉ ‼ = no λ()


----------------------------------------------------------------------------------------------------
-- Sessions can be traversed step by step. Here we define raw steps and raw paths. In
-- PrefixStripping.Sessions we define well-formed steps/paths.

data RawStep : Set where
  step-♯ step-⋆₁ step-⋆₂ : RawStep

RawPath = List RawStep

variable
  𝓢 𝓢′ 𝓢₁ 𝓢₂ 𝓢₃ : RawStep
  𝓢* 𝓢*′ 𝓢₁* 𝓢₂* 𝓢₃* : RawPath


----------------------------------------------------------------------------------------------------
-- We define renamings and injective renamings.

Ren : ℕ → ℕ → Set
Ren m n = 𝔽 m → 𝔽 n

variable ρ ρ₁ ρ₂ : Ren m n

Inj : ∀ m n → Pred (Ren m n) _
Inj _ _ = Injective _≡_ _≡_

Inj′ : Pred (Ren m n) _
Inj′ = Inj _ _

infixr 11 ↑_ _↑⋆_

↑_ : Ren m n → Ren (suc m) (suc n)
(↑ ρ) zero    = zero
(↑ ρ) (suc x) = suc (ρ x)

_↑⋆_ : (m : ℕ) → Ren n₁ n₂ → Ren (m + n₁) (m + n₂)
zero  ↑⋆ ρ = ρ
suc m ↑⋆ ρ = ↑ m ↑⋆ ρ

↑-injective : Inj m n ρ → Inj′ (↑ ρ)
↑-injective inj-ρ {zero}  {zero}  eq = refl
↑-injective inj-ρ {suc x} {suc y} eq = cong suc $ inj-ρ $ Fin.suc-injective eq

↑⋆-injective : Inj n₁ n₂ ρ → Inj′ (m ↑⋆ ρ)
↑⋆-injective {m = zero}  inj-ρ = inj-ρ
↑⋆-injective {m = suc m} inj-ρ = ↑-injective (↑⋆-injective inj-ρ)

↑-dist-∘ : (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) → ↑ ρ₂ ∘ ↑ ρ₁ ≗ ↑ (ρ₂ ∘ ρ₁)
↑-dist-∘ ρ₁ ρ₂ zero    = refl
↑-dist-∘ ρ₁ ρ₂ (suc x) = refl

↑-pres-≗ : ρ₁ ≗ ρ₂ → ↑ ρ₁ ≗ ↑ ρ₂
↑-pres-≗ eq zero    = refl
↑-pres-≗ eq (suc x) = cong suc (eq x)

↑-id : ρ ≗ id → ↑ ρ ≗ id
↑-id eq zero    = refl
↑-id eq (suc x) = cong suc (eq x)

wk : Ren n (suc n)
wk = suc

wk⋆ : (m : ℕ) → Ren n (m + n)
wk⋆ m x = m ↑ʳ x

wk-injective : Inj n (suc n) wk
wk-injective = Fin.suc-injective
