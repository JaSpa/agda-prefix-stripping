----------------------------------------------------------------------------------------------------
-- This module defines sessions types parameterized over some set of base types 𝕋.

module PrefixStripping.Sessions (𝕋 : Set) where

open import PrefixStripping.Prelude hiding (subst₂)
open import Data.Unit as Unit using (⊤)
open import Data.List using (List; []; _∷_)

open Nat.Variables
open Relation.Binary hiding (Irrelevant; _⇒_)

open import PrefixStripping.Syntax

module Core (END : Set) where
  infix 8 `_ _⟨_⨟_⟩
  infixr 5 _♯_▸_

  private variable T T₁ T₂ : 𝕋

  -- Sessions are intrinsically scoped and use de-Bruijn indices.
  data 𝕊 (n : ℕ) : Set where
    -- a completed session (Wait/Term when END is instantiated with Dir, Return when instantiated with ⊤)
    □ : END → 𝕊 n
    -- send/recieve: ?/! T.S
    _♯_▸_ : (⁉ : Dir) (T : 𝕋) (S : 𝕊 n) → 𝕊 n
    -- binary choice: &/⊕ { l₁: S₁; l₂: S₂ }
    _⟨_⨟_⟩ : (⁉ : Dir) (S₁ S₂ : 𝕊 n) → 𝕊 n
    -- recursion: μ S
    μ : (S : 𝕊 (suc n)) → 𝕊 n
    -- recursion variables α
    `_ : 𝔽 n → 𝕊 n

module Variables (END : Set) where
  variable
    T T₁ T₂ : 𝕋
    E E₁ E₂ : END
    s s₁ s₂ s₃ s′ s₁′ s₂′ : Core.𝕊 END n

module Functions {END : Set} where
  open Core (END)
  open Variables (END)

  open Nat using (_≤_; z≤n; s≤s)

  infix  4 ⊢ᶜ_·_ ⊢ᶜ_ ⊢_
  infixr 5 ⊢♯_·_▸_

  `-injective : ∀ {x y : 𝔽 n} → ` x ≡ ` y → x ≡ y
  `-injective refl = refl

  μX-injective : μ s₁ ≡ μ s₂ → s₁ ≡ s₂
  μX-injective refl = refl

  data ⊢ᶜ_·_ {n} (α : 𝔽 n) : 𝕊 n → Set where
    ⊢c-□ : ⊢ᶜ α · □ E
    ⊢c-♯ : ⊢ᶜ α · ⁉ ♯ T ▸ s
    ⊢c-⋆ : ⊢ᶜ α · ⁉ ⟨ s₁ ⨟ s₂ ⟩
    ⊢c-μ : ⊢ᶜ suc α · s → ⊢ᶜ α · μ s
    ⊢c-` : α ≢· α′ → ⊢ᶜ α · ` α′

  ⊢ᶜ_ : 𝕊 (suc n) → Set
  ⊢ᶜ_ = ⊢ᶜ zero ·_

  ¬-⊢c-`x : {x : 𝔽 n} → ¬ ⊢ᶜ x · ` x
  ¬-⊢c-`x (⊢c-` x≠x) = x≠x refl

  ⊢c-μ⁻¹ : {x : 𝔽 n} → ⊢ᶜ x · μ s → ⊢ᶜ suc x · s
  ⊢c-μ⁻¹ (⊢c-μ x) = x

  -- Well formed sessions ensure that every new variable introduced appears guarded.
  data ⊢_ {n} : 𝕊 n → Set where
    ⊢□′      : ∀ E → ⊢ □ E
    ⊢♯_·_▸_  : ∀ ⁉ T → ⊢ s → ⊢ ⁉ ♯ T ▸ s
    ⊢_⋆⟨_⨟_⟩ : ∀ ⁉ → ⊢ s₁ → ⊢ s₂ → ⊢ ⁉ ⟨ s₁ ⨟ s₂ ⟩
    ⊢μ       : ⊢ s → ⊢ᶜ s → ⊢ μ s
    ⊢`       : ∀ α → ⊢ ` α

  -- Some abbreviations for when the direction/payload is not of interest or can be inferred.
  pattern ⊢□ = ⊢□′ _
  pattern ⊢♯ s = ⊢♯ _ · _ ▸ s
  pattern ⊢⋆⟨_⨟_⟩ s₁ s₂ = ⊢ _ ⋆⟨ s₁ ⨟ s₂ ⟩

  -- Easy extraction of the underlying session from a well-formedness proof.
  ⌊_⌋ : {s : 𝕊 n} → ⊢ s → 𝕊 n
  ⌊_⌋ {s = s} _ = s

  ⊢ᶜ-irr : {s : 𝕊 n} → Irrelevant (⊢ᶜ α · s)
  ⊢ᶜ-irr ⊢c-□      ⊢c-□     = refl
  ⊢ᶜ-irr ⊢c-♯      ⊢c-♯     = refl
  ⊢ᶜ-irr ⊢c-⋆      ⊢c-⋆     = refl
  ⊢ᶜ-irr (⊢c-` _) (⊢c-` _) = refl
  ⊢ᶜ-irr (⊢c-μ x) (⊢c-μ y) = cong ⊢c-μ (⊢ᶜ-irr x y)

  -- Two well-formedness proofs are equivalent.
  ⊢-irr : {s : 𝕊 n} (x y : ⊢ s) → x ≡ y
  ⊢-irr ⊢□      ⊢□     = refl
  ⊢-irr (⊢` _)  (⊢` _) = refl
  ⊢-irr (⊢♯ x)  (⊢♯ y)
    rewrite ⊢-irr x y
    = refl
  ⊢-irr ⊢⋆⟨ x₁ ⨟ x₂ ⟩ ⊢⋆⟨ y₁ ⨟ y₂ ⟩
    rewrite ⊢-irr x₁ y₁ | ⊢-irr x₂ y₂
    = refl
  ⊢-irr (⊢μ x xᶜ) (⊢μ y yᶜ)
    rewrite ⊢-irr x y | ⊢ᶜ-irr xᶜ yᶜ
    = refl

  dcong-⊢ : {x : ⊢ s₁} (y : ⊢ s₂) (eq : s₁ ≡ s₂) → x ≡ subst ⊢_ (sym eq) y
  dcong-⊢ y refl = ⊢-irr _ y


----------------------------------------------------------------------------------------------------
-- Renaming and substitution of sessions.
--
-- These are standard results applied to our setting.

  infixl 7 _⋯_

  _⋯_ : 𝕊 m → Ren m n → 𝕊 n
  □ e           ⋯ ρ = □ e
  (⁉ ♯ T ▸ s)   ⋯ ρ = ⁉ ♯ T ▸ (s ⋯ ρ)
  ⁉ ⟨ s₁ ⨟ s₂ ⟩ ⋯ ρ = ⁉ ⟨ s₁ ⋯ ρ ⨟ s₂ ⋯ ρ ⟩
  μ s           ⋯ ρ = μ (s ⋯ ↑ ρ)
  ` α           ⋯ ρ = ` ρ α

  ⋯-cong : (s : 𝕊 n) → ρ₁ ≗ ρ₂ → s ⋯ ρ₁ ≡ s ⋯ ρ₂
  ⋯-cong (□ E)           eq = refl
  ⋯-cong (⁉ ♯ T ▸ s)     eq = cong (⁉ ♯ T ▸_) (⋯-cong s eq)
  ⋯-cong (⁉ ⟨ s₁ ⨟ s₂ ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯-cong s₁ eq) (⋯-cong s₂ eq)
  ⋯-cong (μ s)           eq = cong μ (⋯-cong s (↑-pres-≗ eq))
  ⋯-cong (` α)           eq = cong `_ (eq α)

  ⋯-composes : (s : 𝕊 n₁) (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) → s ⋯ ρ₁ ⋯ ρ₂ ≡ s ⋯ (ρ₂ ∘ ρ₁)
  ⋯-composes (□ E)           ρ₁ ρ₂ = refl
  ⋯-composes (⁉ ♯ T ▸ s)     ρ₁ ρ₂ = cong (⁉ ♯ T ▸_) (⋯-composes s ρ₁ ρ₂)
  ⋯-composes (⁉ ⟨ s₁ ⨟ s₂ ⟩) ρ₁ ρ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯-composes s₁ ρ₁ ρ₂) (⋯-composes s₂ ρ₁ ρ₂)
  ⋯-composes (μ s)           ρ₁ ρ₂ = cong μ (trans (⋯-composes s (↑ ρ₁) (↑ ρ₂)) (⋯-cong s (↑-dist-∘ ρ₁ ρ₂)))
  ⋯-composes (` α)           ρ₁ ρ₂ = refl

  ⋯-id : (s : 𝕊 n) → ρ ≗ id → s ⋯ ρ ≡ s
  ⋯-id (□ E)           eq = refl
  ⋯-id (⁉ ♯ T ▸ s)     eq = cong (⁉ ♯ T ▸_) (⋯-id s eq)
  ⋯-id (⁉ ⟨ s₁ ⨟ s₂ ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯-id s₁ eq) (⋯-id s₂ eq)
  ⋯-id (μ s)           eq = cong μ (⋯-id s (λ{ zero → refl; (suc x) → cong suc (eq x) }))
  ⋯-id (` α)           eq = cong `_ (eq α)

  Sub : ℕ → ℕ → Set
  Sub m n = 𝔽 m → 𝕊 n

  infixl 7 _⋯ₛ_
  infixr 7.5 _∷ₛ_
  infixr 11 ↑ₛ_ _↑ₛ⋆_

  idₛ : Sub n n
  idₛ = `_

  _∷ₛ_ : 𝕊 n → Sub m n → Sub (suc m) n
  (s ∷ₛ σ) zero = s
  (s ∷ₛ σ) (suc α) = σ α

  liftₛ : Sub m n → Sub m (suc n)
  liftₛ σ α = σ α ⋯ wk

  ↑ₛ_ : Sub m n → Sub (suc m) (suc n)
  ↑ₛ σ = ` zero ∷ₛ liftₛ σ

  _↑ₛ⋆_ : ∀ m → Sub n n′ → Sub (m + n) (m + n′)
  zero  ↑ₛ⋆ σ = σ
  suc m ↑ₛ⋆ σ = ↑ₛ m ↑ₛ⋆ σ

  0↦ : 𝕊 n → Sub (suc n) n
  0↦ s = s ∷ₛ idₛ

  _⋯ₛ_ : 𝕊 m → Sub m n → 𝕊 n
  □ E           ⋯ₛ σ = □ E
  (⁉ ♯ T ▸ s)   ⋯ₛ σ = ⁉ ♯ T ▸ (s ⋯ₛ σ)
  ⁉ ⟨ s₁ ⨟ s₂ ⟩ ⋯ₛ σ = ⁉ ⟨ s₁ ⋯ₛ σ ⨟ s₂ ⋯ₛ σ ⟩
  μ s           ⋯ₛ σ = μ (s ⋯ₛ ↑ₛ σ)
  ` α           ⋯ₛ σ = σ α

  ↑ₛ-id : {σ : Sub n n} → σ ≗ idₛ → ↑ₛ σ ≗ idₛ
  ↑ₛ-id eq zero = refl
  ↑ₛ-id eq (suc α) rewrite eq α = refl

  ↑ₛ-pres-≗ : {σ₁ σ₂ : Sub m n} → σ₁ ≗ σ₂ → ↑ₛ σ₁ ≗ ↑ₛ σ₂
  ↑ₛ-pres-≗ eq zero    = refl
  ↑ₛ-pres-≗ eq (suc α) = cong (_⋯ wk) (eq α)

  ⋯ₛ-id : (s : 𝕊 n) {σ : Sub n n} → σ ≗ idₛ → s ⋯ₛ σ ≡ s
  ⋯ₛ-id (□ E)           eq = refl
  ⋯ₛ-id (⁉ ♯ T ▸ s)     eq = cong (⁉ ♯ T ▸_) (⋯ₛ-id s eq)
  ⋯ₛ-id (⁉ ⟨ s₁ ⨟ s₂ ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛ-id s₁ eq) (⋯ₛ-id s₂ eq)
  ⋯ₛ-id (μ s)           eq = cong μ (⋯ₛ-id s (↑ₛ-id eq))
  ⋯ₛ-id (` α)           eq = eq α

  ⋯ₛ-cong : (s : 𝕊 m) {σ₁ σ₂ : Sub m n} → σ₁ ≗ σ₂ → s ⋯ₛ σ₁ ≡ s ⋯ₛ σ₂
  ⋯ₛ-cong (□ E)           eq = refl
  ⋯ₛ-cong (⁉ ♯ T ▸ s)     eq = cong (⁉ ♯ T ▸_) (⋯ₛ-cong s eq)
  ⋯ₛ-cong (⁉ ⟨ s₁ ⨟ s₂ ⟩) eq = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛ-cong s₁ eq) (⋯ₛ-cong s₂ eq)
  ⋯ₛ-cong (μ s)           eq = cong μ (⋯ₛ-cong s (↑ₛ-pres-≗ eq))
  ⋯ₛ-cong (` α)           eq = eq α

  infix 7.5 _·ᵣᵣ_ _·ᵣₛ_ _·ₛᵣ_ _·ₛₛ_

  _·ᵣᵣ_ : ∀ {m n o} → Ren m n → Ren n o → Ren m o
  (ρ₁ ·ᵣᵣ ρ₂) α = ρ₂ (ρ₁ α)

  _·ᵣₛ_ : ∀ {m n o} → Ren m n → Sub n o → Sub m o
  (ρ₁ ·ᵣₛ σ₂) α = σ₂ (ρ₁ α)

  _·ₛᵣ_ : ∀ {m n o} → Sub m n → Ren n o → Sub m o
  (σ₁ ·ₛᵣ ρ₂) α = σ₁ α ⋯ ρ₂

  _·ₛₛ_ : ∀ {m n o} → Sub m n → Sub n o → Sub m o
  (σ₁ ·ₛₛ σ₂) α = σ₁ α ⋯ₛ σ₂

  private variable
    σ σ₁ σ₂ : Sub m n

  ↑-dist-·ᵣᵣ : ∀ (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    ↑ (ρ₁ ·ᵣᵣ ρ₂) ≗ ↑ ρ₁ ·ᵣᵣ ↑ ρ₂
  ↑-dist-·ᵣᵣ ρ₁ ρ₂ = sym ∘ ↑-dist-∘ ρ₁ ρ₂

  ⋯ᵣᵣ-fusion : ∀ (s : 𝕊 n₁) (ρ₁ : Ren n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    s ⋯ ρ₁ ⋯ ρ₂ ≡ s ⋯ (ρ₁ ·ᵣᵣ ρ₂)
  ⋯ᵣᵣ-fusion (` α)           ρ₁ ρ₂ = refl
  ⋯ᵣᵣ-fusion (□ E)           ρ₁ ρ₂ = refl
  ⋯ᵣᵣ-fusion (⁉ ♯ T ▸ s)     ρ₁ ρ₂ = cong (⁉ ♯ T ▸_) (⋯ᵣᵣ-fusion s ρ₁ ρ₂)
  ⋯ᵣᵣ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) ρ₁ ρ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ᵣᵣ-fusion s₁ ρ₁ ρ₂) (⋯ᵣᵣ-fusion s₂ ρ₁ ρ₂)
  ⋯ᵣᵣ-fusion (μ s)           ρ₁ ρ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ ↑ ρ₁ ⋯ ↑ ρ₂      ≡⟨ ⋯ᵣᵣ-fusion s (↑ ρ₁) (↑ ρ₂) ⟩
    s ⋯ (↑ ρ₁ ·ᵣᵣ ↑ ρ₂)  ≡⟨ ⋯-cong s (↑-dist-·ᵣᵣ ρ₁ ρ₂) ⟨
    s ⋯ ↑ (ρ₁ ·ᵣᵣ ρ₂)    ∎

  ↑-dist-·ᵣₛ : ∀ (ρ₁ : Ren n₁ n₂) (σ₂ : Sub n₂ n₃) →
    ↑ₛ (ρ₁ ·ᵣₛ σ₂) ≗ ↑ ρ₁ ·ᵣₛ ↑ₛ σ₂
  ↑-dist-·ᵣₛ ρ₁ σ₂ zero = refl
  ↑-dist-·ᵣₛ ρ₁ σ₂ (suc α) = refl

  ⋯ᵣₛ-fusion : ∀ (s : 𝕊 n₁) (ρ₁ : Ren n₁ n₂) (σ₂ : Sub n₂ n₃) →
    s ⋯ ρ₁ ⋯ₛ σ₂ ≡ s ⋯ₛ (ρ₁ ·ᵣₛ σ₂)
  ⋯ᵣₛ-fusion (` α) ρ₁ σ₂ = refl
  ⋯ᵣₛ-fusion (□ E) ρ₁ σ₂ = refl
  ⋯ᵣₛ-fusion (⁉ ♯ T ▸ s) ρ₁ σ₂ = cong (⁉ ♯ T ▸_) (⋯ᵣₛ-fusion s ρ₁ σ₂)
  ⋯ᵣₛ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) ρ₁ σ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ᵣₛ-fusion s₁ ρ₁ σ₂) (⋯ᵣₛ-fusion s₂ ρ₁ σ₂)
  ⋯ᵣₛ-fusion (μ s) ρ₁ σ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ ↑ ρ₁ ⋯ₛ ↑ₛ σ₂      ≡⟨ ⋯ᵣₛ-fusion s (↑ ρ₁) (↑ₛ σ₂) ⟩
    s ⋯ₛ (↑ ρ₁ ·ᵣₛ ↑ₛ σ₂)  ≡⟨ ⋯ₛ-cong s (↑-dist-·ᵣₛ ρ₁ σ₂) ⟨
    s ⋯ₛ ↑ₛ (ρ₁ ·ᵣₛ σ₂)    ∎

  ·-↑ᵣ-wk : ∀ (ρ : Ren n₁ n₂) → ρ ·ᵣᵣ wk ≡ wk ·ᵣᵣ ↑ ρ
  ·-↑ᵣ-wk ρ = refl

  ↑-dist-·ₛᵣ : ∀ (σ₁ : Sub n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    ↑ₛ (σ₁ ·ₛᵣ ρ₂) ≗ ↑ₛ σ₁ ·ₛᵣ ↑ ρ₂
  ↑-dist-·ₛᵣ σ₁ ρ₂ zero = refl
  ↑-dist-·ₛᵣ σ₁ ρ₂ (suc α) =
    let open ≡-Reasoning in
    σ₁ α ⋯ ρ₂ ⋯ wk        ≡⟨ ⋯ᵣᵣ-fusion (σ₁ α) ρ₂ wk ⟩
    σ₁ α ⋯ (ρ₂ ·ᵣᵣ wk)    ≡⟨ cong (σ₁ α ⋯_) (·-↑ᵣ-wk ρ₂) ⟩
    σ₁ α ⋯ (wk ·ᵣᵣ ↑ ρ₂)  ≡⟨ ⋯ᵣᵣ-fusion (σ₁ α) wk (↑ ρ₂) ⟨
    σ₁ α ⋯ wk ⋯ ↑ ρ₂     ∎

  ⋯ₛᵣ-fusion : ∀ (s : 𝕊 n₁) (σ₁ : Sub n₁ n₂) (ρ₂ : Ren n₂ n₃) →
    s ⋯ₛ σ₁ ⋯ ρ₂ ≡ s ⋯ₛ (σ₁ ·ₛᵣ ρ₂)
  ⋯ₛᵣ-fusion (` α) σ₁ ρ₂ = refl
  ⋯ₛᵣ-fusion (□ E) σ₁ ρ₂ = refl
  ⋯ₛᵣ-fusion (⁉ ♯ T ▸ s) σ₁ ρ₂ = cong (⁉ ♯ T ▸_) (⋯ₛᵣ-fusion s σ₁ ρ₂)
  ⋯ₛᵣ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) σ₁ ρ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛᵣ-fusion s₁ σ₁ ρ₂) (⋯ₛᵣ-fusion s₂ σ₁ ρ₂)
  ⋯ₛᵣ-fusion (μ s) σ₁ ρ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ₛ ↑ₛ σ₁ ⋯ ↑ ρ₂      ≡⟨ ⋯ₛᵣ-fusion s (↑ₛ σ₁) (↑ ρ₂) ⟩
    s ⋯ₛ (↑ₛ σ₁ ·ₛᵣ ↑ ρ₂)  ≡⟨ ⋯ₛ-cong s (↑-dist-·ₛᵣ σ₁ ρ₂) ⟨
    s ⋯ₛ ↑ₛ (σ₁ ·ₛᵣ ρ₂)    ∎

  ·-↑ₛ-wk : ∀ (σ : Sub n₁ n₂) → σ ·ₛᵣ wk ≡ wk ·ᵣₛ ↑ₛ σ
  ·-↑ₛ-wk σ = refl

  ↑-dist-·ₛₛ : ∀ (σ₁ : Sub n₁ n₂) (σ₂ : Sub n₂ n₃) →
    ↑ₛ (σ₁ ·ₛₛ σ₂) ≗ ↑ₛ σ₁ ·ₛₛ ↑ₛ σ₂
  ↑-dist-·ₛₛ σ₁ σ₂ zero    = refl
  ↑-dist-·ₛₛ σ₁ σ₂ (suc α) =
    let open ≡-Reasoning in
    σ₁ α ⋯ₛ σ₂ ⋯ wk         ≡⟨ ⋯ₛᵣ-fusion (σ₁ α) σ₂ wk ⟩
    σ₁ α ⋯ₛ (σ₂ ·ₛᵣ wk)     ≡⟨ cong (σ₁ α ⋯ₛ_) (·-↑ₛ-wk σ₂) ⟩
    σ₁ α ⋯ₛ (wk ·ᵣₛ ↑ₛ σ₂)  ≡⟨ ⋯ᵣₛ-fusion (σ₁ α) wk (↑ₛ σ₂) ⟨
    σ₁ α ⋯ wk ⋯ₛ ↑ₛ σ₂      ∎

  ⋯ₛₛ-fusion : ∀ (s : 𝕊 n₁) (σ₁ : Sub n₁ n₂) (σ₂ : Sub n₂ n₃) →
    s ⋯ₛ σ₁ ⋯ₛ σ₂ ≡ s ⋯ₛ (σ₁ ·ₛₛ σ₂)
  ⋯ₛₛ-fusion (` α) σ₁ σ₂ = refl
  ⋯ₛₛ-fusion (□ E) σ₁ σ₂ = refl
  ⋯ₛₛ-fusion (⁉ ♯ T ▸ s) σ₁ σ₂ = cong (⁉ ♯ T ▸_) (⋯ₛₛ-fusion s σ₁ σ₂)
  ⋯ₛₛ-fusion (⁉ ⟨ s₁ ⨟ s₂ ⟩) σ₁ σ₂ = cong₂ (⁉ ⟨_⨟_⟩) (⋯ₛₛ-fusion s₁ σ₁ σ₂) (⋯ₛₛ-fusion s₂ σ₁ σ₂)
  ⋯ₛₛ-fusion (μ s) σ₁ σ₂ = cong μ $
    let open ≡-Reasoning in
    s ⋯ₛ ↑ₛ σ₁ ⋯ₛ ↑ₛ σ₂     ≡⟨ ⋯ₛₛ-fusion s (↑ₛ σ₁) (↑ₛ σ₂) ⟩
    s ⋯ₛ (↑ₛ σ₁ ·ₛₛ ↑ₛ σ₂)  ≡⟨ ⋯ₛ-cong s (↑-dist-·ₛₛ σ₁ σ₂) ⟨
    s ⋯ₛ ↑ₛ (σ₁ ·ₛₛ σ₂)     ∎

  exchangeᵣₛ : (s : 𝕊 m) (ρ : Ren m n) → ↑ ρ ·ᵣₛ 0↦ (s ⋯ ρ) ≗ 0↦ s ·ₛᵣ ρ
  exchangeᵣₛ s ρ zero    = refl
  exchangeᵣₛ s ρ (suc α) = refl

  exchangeₛₛ : (s : 𝕊 m) (σ : Sub m n) → ↑ₛ σ ·ₛₛ 0↦ (s ⋯ₛ σ) ≗ 0↦ s ·ₛₛ σ
  exchangeₛₛ s σ zero = refl
  exchangeₛₛ s σ (suc α) =
    let open ≡-Reasoning in
    σ α ⋯ wk ⋯ₛ (s ⋯ₛ σ) ∷ₛ idₛ      ≡⟨ ⋯ᵣₛ-fusion (σ α) suc _ ⟩
    σ α ⋯ₛ wk ·ᵣₛ ((s ⋯ₛ σ) ∷ₛ idₛ)  ≡⟨⟩
    σ α ⋯ₛ idₛ                       ≡⟨ ⋯ₛ-id (σ α) (λ _ → refl) ⟩
    σ α                              ∎

  ⋯-exchangeᵣₛ : (s : 𝕊 (suc m)) (s′ : 𝕊 m) (ρ : Ren m n) → s ⋯ ↑ ρ ⋯ₛ 0↦ (s′ ⋯ ρ) ≡ s ⋯ₛ 0↦ s′ ⋯ ρ
  ⋯-exchangeᵣₛ s s′ ρ =
    let open ≡-Reasoning in
    s ⋯ ↑ ρ ⋯ₛ 0↦ (s′ ⋯ ρ)    ≡⟨ ⋯ᵣₛ-fusion s (↑ ρ) (0↦ (s′ ⋯ ρ)) ⟩
    s ⋯ₛ ↑ ρ ·ᵣₛ 0↦ (s′ ⋯ ρ)  ≡⟨ ⋯ₛ-cong s (exchangeᵣₛ s′ ρ) ⟩
    s ⋯ₛ 0↦ s′ ·ₛᵣ ρ          ≡⟨ ⋯ₛᵣ-fusion s (0↦ s′) ρ ⟨
    s ⋯ₛ 0↦ s′ ⋯ ρ            ∎

  ⋯-exchangeₛₛ : (s : 𝕊 (suc m)) (s′ : 𝕊 m) (σ : Sub m n) → s ⋯ₛ ↑ₛ σ ⋯ₛ 0↦ (s′ ⋯ₛ σ) ≡ s ⋯ₛ 0↦ s′ ⋯ₛ σ
  ⋯-exchangeₛₛ s s′ σ =
    let open ≡-Reasoning in
    s ⋯ₛ ↑ₛ σ ⋯ₛ 0↦ (s′ ⋯ₛ σ)   ≡⟨ ⋯ₛₛ-fusion s (↑ₛ σ) (0↦ (s′ ⋯ₛ σ)) ⟩
    s ⋯ₛ ↑ₛ σ ·ₛₛ 0↦ (s′ ⋯ₛ σ)  ≡⟨ ⋯ₛ-cong s (exchangeₛₛ s′ σ) ⟩
    s ⋯ₛ 0↦ s′ ·ₛₛ σ            ≡⟨ ⋯ₛₛ-fusion s (0↦ s′) σ ⟨
    s ⋯ₛ 0↦ s′ ⋯ₛ σ             ∎

  ·-wk-cancels-ext : (s : 𝕊 n) (σ : Sub m n) → wk ·ᵣₛ (s ∷ₛ σ) ≡ σ
  ·-wk-cancels-ext s σ = refl

  ·-wk⋆-cancels-0↦ : ∀ m (s : 𝕊 n) → m ↑⋆ wk ·ᵣₛ m ↑ₛ⋆ 0↦ s ≗ idₛ
  ·-wk⋆-cancels-0↦ zero s _ = refl
  ·-wk⋆-cancels-0↦ (suc m) s zero = refl
  ·-wk⋆-cancels-0↦ (suc m) s (suc α) rewrite ·-wk⋆-cancels-0↦ m s α = refl

  ·-wk-cancels-0↦ : ∀ (s : 𝕊 n) → wk ·ᵣₛ 0↦ s ≗ idₛ
  ·-wk-cancels-0↦ s = ·-wk⋆-cancels-0↦ 0 s

  ⋯-wk⋆-cancels-0↦ : ∀ m {s : 𝕊 (m + n)} (s′ : 𝕊 n) →
    s ⋯ m ↑⋆ wk ⋯ₛ m ↑ₛ⋆ 0↦ s′ ≡ s
  ⋯-wk⋆-cancels-0↦ m {s} s′ = let open ≡-Reasoning in
    s ⋯ m ↑⋆ wk ⋯ₛ m ↑ₛ⋆ 0↦ s′    ≡⟨ ⋯ᵣₛ-fusion s (m ↑⋆ wk) (m ↑ₛ⋆ 0↦ s′) ⟩
    s ⋯ₛ m ↑⋆ wk ·ᵣₛ m ↑ₛ⋆ 0↦ s′  ≡⟨ ⋯ₛ-id s (·-wk⋆-cancels-0↦ m s′) ⟩
    s ∎

  ⋯-wk-cancels-0↦ : ∀ (s′ : 𝕊 n) → s ⋯ wk ⋯ₛ 0↦ s′ ≡ s
  ⋯-wk-cancels-0↦ s′ = ⋯-wk⋆-cancels-0↦ 0 s′

  ·-wk-↑ᵣ : (ρ : Ren m n) → ρ ·ᵣᵣ wk ≗ wk ·ᵣᵣ ↑ ρ
  ·-wk-↑ᵣ ρ zero = refl
  ·-wk-↑ᵣ ρ (suc α) = refl

  ⋯-wk-↑ᵣ : ∀ (s : 𝕊 m) (ρ : Ren m n) →
    s ⋯ ρ ⋯ wk ≡ s ⋯ wk ⋯ ↑ ρ
  ⋯-wk-↑ᵣ s ρ = let open ≡-Reasoning in
    s ⋯ ρ ⋯ wk       ≡⟨ ⋯ᵣᵣ-fusion s ρ wk ⟩
    s ⋯ ρ ·ᵣᵣ wk     ≡⟨ ⋯-cong s (·-wk-↑ᵣ ρ) ⟩
    s ⋯ wk ·ᵣᵣ ↑ ρ   ≡⟨ ⋯ᵣᵣ-fusion s wk (↑ ρ) ⟨
    s ⋯ wk ⋯ ↑ ρ     ∎

  ·-wk-↑ₛ : ∀ (σ : Sub n₁ n₂) → σ ·ₛᵣ wk ≗ wk ·ᵣₛ ↑ₛ σ
  ·-wk-↑ₛ σ zero    = refl
  ·-wk-↑ₛ σ (suc α) = refl

  ⋯-wk-↑ₛ : ∀ (s : 𝕊 n₁) (σ : Sub n₁ n₂) →
    s ⋯ₛ σ ⋯ wk ≡ s ⋯ wk ⋯ₛ ↑ₛ σ
  ⋯-wk-↑ₛ s σ =
    let open ≡-Reasoning in
    s ⋯ₛ σ ⋯ wk         ≡⟨ ⋯ₛᵣ-fusion s σ wk ⟩
    s ⋯ₛ (σ ·ₛᵣ wk)     ≡⟨ ⋯ₛ-cong s (·-wk-↑ₛ σ) ⟩
    s ⋯ₛ (wk ·ᵣₛ ↑ₛ σ)  ≡⟨ ⋯ᵣₛ-fusion s wk (↑ₛ σ) ⟨
    s ⋯ wk ⋯ₛ ↑ₛ σ      ∎

  ·-wk-↑ₛ⋆ : (m : ℕ) (σ : Sub n₁ n₂) →
    σ ·ₛᵣ wk⋆ m ≗ wk⋆ m ·ᵣₛ m ↑ₛ⋆ σ
  ·-wk-↑ₛ⋆ zero σ α = ⋯-id (σ α) (λ _ → refl)
  ·-wk-↑ₛ⋆ (suc m) σ α =
    let open ≡-Reasoning in
    σ α ⋯ wk⋆ (suc m)                ≡⟨⟩
    σ α ⋯ wk⋆ m ·ᵣᵣ wk               ≡⟨ ⋯ᵣᵣ-fusion (σ α) (wk⋆ m) wk ⟨
    σ α ⋯ wk⋆ m ⋯ wk                 ≡⟨ cong (_⋯ suc) (·-wk-↑ₛ⋆ m σ α) ⟩
    (m ↑ₛ⋆ σ) (m ↑ʳ α) ⋯ wk          ≡⟨⟩
    (wk⋆ (suc m) ·ᵣₛ suc m ↑ₛ⋆ σ) α  ∎

  ⋯-wk-↑ₛ⋆ : ∀ (s : 𝕊 n₁) (m : ℕ) (σ : Sub n₁ n₂) →
    s ⋯ₛ σ ⋯ wk⋆ m ≡ s ⋯ wk⋆ m ⋯ₛ m ↑ₛ⋆ σ
  ⋯-wk-↑ₛ⋆ s m σ =
    let open ≡-Reasoning in
    s ⋯ₛ σ ⋯ wk⋆ m          ≡⟨ ⋯ₛᵣ-fusion s σ (wk⋆ m) ⟩
    s ⋯ₛ σ ·ₛᵣ wk⋆ m        ≡⟨ ⋯ₛ-cong s (·-wk-↑ₛ⋆ m σ) ⟩
    s ⋯ₛ wk⋆ m ·ᵣₛ m ↑ₛ⋆ σ  ≡⟨ ⋯ᵣₛ-fusion s (wk⋆ m) (m ↑ₛ⋆ σ) ⟨
    s ⋯ wk⋆ m ⋯ₛ m ↑ₛ⋆ σ    ∎

----------------------------------------------------------------------------------------------------
-- Renaming and substitution preserve well-formedness

  module _ where
    open Relation.Unary

    RenOn : Sub m n → Pred (𝔽 m) _
    RenOn σ α = ∃ λ α′ → σ α ≡ ` α′

    renOrC : 𝕊 m → Pred (Sub m n) _
    renOrC {m = m} s σ = ∀ α → RenOn σ α ⊎ ⊢ᶜ α · s

  ⊢ᶜ-⋯ : ⊢ᶜ α · s → Inj m n ρ → ⊢ᶜ ρ α · s ⋯ ρ
  ⊢ᶜ-⋯ ⊢c-□      ρ = ⊢c-□
  ⊢ᶜ-⋯ ⊢c-♯      ρ = ⊢c-♯
  ⊢ᶜ-⋯ ⊢c-⋆      ρ = ⊢c-⋆
  ⊢ᶜ-⋯ (⊢c-μ s)  ρ = ⊢c-μ (⊢ᶜ-⋯ s (↑-injective ρ))
  ⊢ᶜ-⋯ (⊢c-` ≠x) ρ = ⊢c-` (≠x ∘· ρ)

  ⊢ᶜ-⋯↑wk : ∀ m (s : 𝕊 (m + n)) → ⊢ᶜ m ↑ʳ zero · s ⋯ m ↑⋆ wk
  ⊢ᶜ-⋯↑wk m (□ E)           = ⊢c-□
  ⊢ᶜ-⋯↑wk m (⁉ ♯ T ▸ s)     = ⊢c-♯
  ⊢ᶜ-⋯↑wk m (⁉ ⟨ s₁ ⨟ s₂ ⟩) = ⊢c-⋆
  ⊢ᶜ-⋯↑wk m (μ s)           = ⊢c-μ (⊢ᶜ-⋯↑wk (suc m) s)
  ⊢ᶜ-⋯↑wk zero    (` α)     = ⊢c-` λ()
  ⊢ᶜ-⋯↑wk (suc m) (` zero)  = ⊢c-` λ()
  ⊢ᶜ-⋯↑wk (suc m) (` suc α) = ⊢ᶜ-⋯ (⊢ᶜ-⋯↑wk m (` α)) wk-injective

  ⊢ᶜ-⋯wk : (s : 𝕊 n) → ⊢ᶜ zero · s ⋯ wk
  ⊢ᶜ-⋯wk = ⊢ᶜ-⋯↑wk 0

  ⊢-⋯ : ⊢ s → Inj m n ρ → ⊢ s ⋯ ρ
  ⊢-⋯ ⊢□              ρ = ⊢□
  ⊢-⋯ (⊢♯ s)          ρ = ⊢♯ (⊢-⋯ s ρ)
  ⊢-⋯ (⊢⋆⟨ s₁ ⨟ s₂ ⟩) ρ = ⊢⋆⟨ ⊢-⋯ s₁ ρ ⨟ ⊢-⋯ s₂ ρ ⟩
  ⊢-⋯ (⊢μ s sᶜ)       ρ = ⊢μ (⊢-⋯ s (↑-injective ρ)) (⊢ᶜ-⋯ sᶜ (↑-injective ρ))
  ⊢-⋯ (⊢` α)          ρ = ⊢` _

  ⊢Sub : Pred (Sub m n) _
  ⊢Sub σ = ∀ α → ⊢ σ α

  ⊢lift : ⊢Sub σ → ⊢Sub (liftₛ σ)
  ⊢lift ⊢σ α = ⊢-⋯ (⊢σ α) wk-injective

  ⊢ext : ⊢ s → ⊢Sub σ → ⊢Sub (s ∷ₛ σ)
  ⊢ext s ⊢σ zero = s
  ⊢ext s ⊢σ (suc α) = ⊢σ α

  ⊢↑ : ⊢Sub σ → ⊢Sub (↑ₛ σ)
  ⊢↑ ⊢σ = ⊢ext (⊢` zero) (⊢lift ⊢σ)

  ⊢idₛ : ∀ n → ⊢Sub (idₛ {n})
  ⊢idₛ _ α = ⊢` α

  ⊢0↦ : ⊢ s → ⊢Sub (0↦ s)
  ⊢0↦ s = ⊢ext s (⊢idₛ _)

  ⊢ᶜ-⋯ₛ-∀c : (σ : Sub m n) → ⊢ᶜ α₁ · s → σ α₁ ≡ ` α₂ → (∀ α₃ → α₁ ≢· α₃ → ⊢ᶜ α₂ · σ α₃) → ⊢ᶜ α₂ · s ⋯ₛ σ
  ⊢ᶜ-⋯ₛ-∀c σ ⊢c-□ σα= ∀α-c = ⊢c-□
  ⊢ᶜ-⋯ₛ-∀c σ ⊢c-♯ σα= ∀α-c = ⊢c-♯
  ⊢ᶜ-⋯ₛ-∀c σ ⊢c-⋆ σα= ∀α-c = ⊢c-⋆
  ⊢ᶜ-⋯ₛ-∀c σ (⊢c-` α≠) σα= ∀α-c = ∀α-c _ α≠
  ⊢ᶜ-⋯ₛ-∀c σ (⊢c-μ αᶜ) σα= ∀α-c = ⊢c-μ $ ⊢ᶜ-⋯ₛ-∀c (↑ₛ σ) αᶜ (cong (_⋯ wk) σα=) λ where
    zero     α₁≠0 → ⊢c-` λ()
    (suc α₃) α₁≠₃ → ⊢ᶜ-⋯ (∀α-c α₃ (α₁≠₃ ∘· cong suc)) wk-injective

  ⊢ᶜ-⋯ₛ-↑ : (σ : Sub m n) → ⊢ᶜ s → ⊢ᶜ s ⋯ₛ ↑ₛ σ
  ⊢ᶜ-⋯ₛ-↑ σ sᶜ = ⊢ᶜ-⋯ₛ-∀c (↑ₛ σ) sᶜ refl λ where
    zero    0≠0   → ⊥-elim (0≠0 refl)
    (suc α) 0≠1+α → ⊢ᶜ-⋯wk (σ α)

  ⊢-⋯ₛ : ⊢ s → ⊢Sub σ → ⊢ s ⋯ₛ σ
  ⊢-⋯ₛ ⊢□          ⊢σ = ⊢□
  ⊢-⋯ₛ (⊢♯ s)      ⊢σ = ⊢♯ (⊢-⋯ₛ s ⊢σ)
  ⊢-⋯ₛ ⊢⋆⟨ x ⨟ y ⟩ ⊢σ = ⊢⋆⟨ ⊢-⋯ₛ x ⊢σ ⨟ ⊢-⋯ₛ y ⊢σ ⟩
  ⊢-⋯ₛ (⊢μ s sᶜ)   ⊢σ = ⊢μ (⊢-⋯ₛ s (⊢↑ ⊢σ)) (⊢ᶜ-⋯ₛ-↑ _ sᶜ)
  ⊢-⋯ₛ (⊢` α)      ⊢σ = ⊢σ α

  ⊢·ᵣₛ : (ρ : Ren m n) → ⊢Sub σ → ⊢Sub (ρ ·ᵣₛ σ)
  ⊢·ᵣₛ ρ ⊢σ α = ⊢σ (ρ α)

  ⊢·ₛᵣ : ⊢Sub σ → Inj′ ρ → ⊢Sub (σ ·ₛᵣ ρ)
  ⊢·ₛᵣ ⊢σ ρ α = ⊢-⋯ (⊢σ α) ρ

  ⊢·ₛₛ : ⊢Sub σ₁ → ⊢Sub σ₂ → ⊢Sub (σ₁ ·ₛₛ σ₂)
  ⊢·ₛₛ ⊢σ₁ ⊢σ₂ α = ⊢-⋯ₛ (⊢σ₁ α) ⊢σ₂

  ⊢fusionₛₛ : (⊢s : ⊢ s) (⊢σ₁ : ⊢Sub σ₁) (⊢σ₂ : ⊢Sub σ₂) →
    ⊢-⋯ₛ (⊢-⋯ₛ ⊢s ⊢σ₁) ⊢σ₂ ≡ subst ⊢_ (sym (⋯ₛₛ-fusion s σ₁ σ₂)) (⊢-⋯ₛ ⊢s (⊢·ₛₛ ⊢σ₁ ⊢σ₂))
  ⊢fusionₛₛ ⊢s ⊢σ₁ ⊢σ₂ = dcong-⊢ (⊢-⋯ₛ ⊢s (⊢·ₛₛ ⊢σ₁ ⊢σ₂)) (⋯ₛₛ-fusion ⌊ ⊢s ⌋ _ _)

  ⊢fusionₛᵣ : (⊢s : ⊢ s) (τ : ⊢Sub σ) (π : Inj′ ρ) →
    ⊢-⋯ (⊢-⋯ₛ ⊢s τ) π ≡ subst ⊢_ (sym (⋯ₛᵣ-fusion s σ ρ)) (⊢-⋯ₛ ⊢s (⊢·ₛᵣ τ π))
  ⊢fusionₛᵣ ⊢s τ π = dcong-⊢ (⊢-⋯ₛ ⊢s (⊢·ₛᵣ τ π)) (⋯ₛᵣ-fusion ⌊ ⊢s ⌋ _ _)

  ⊢fusionᵣₛ : (⊢s : ⊢ s) (π : Inj′ ρ) (τ : ⊢Sub σ) →
    ⊢-⋯ₛ (⊢-⋯ ⊢s π) τ ≡ subst ⊢_ (sym (⋯ᵣₛ-fusion s ρ σ)) (⊢-⋯ₛ ⊢s (⊢·ᵣₛ ρ τ))
  ⊢fusionᵣₛ ⊢s π τ = dcong-⊢ (⊢-⋯ₛ ⊢s (⊢·ᵣₛ _ τ)) (⋯ᵣₛ-fusion ⌊ ⊢s ⌋ _ _)

  unfold : 𝕊 (suc n) → 𝕊 n
  unfold s = s ⋯ₛ 0↦ (μ s)

  ⊢-unfold : ⊢ s → ⊢ᶜ s → ⊢ unfold s
  ⊢-unfold ⊢s sᶜ = ⊢-⋯ₛ ⊢s (⊢0↦ (⊢μ ⊢s sᶜ))

----------------------------------------------------------------------------------------------------
-- `Step`/`Path` restricts the raw steps/raw paths to the set fitting a specific session type.
--
-- We also define functions accessing the targets of steps/paths.

  data Step {n} : RawStep → 𝕊 n → Set where
    step-♯  : Step step-♯  (⁉ ♯ T ▸ s)
    step-⋆₁ : Step step-⋆₁ (⁉ ⟨ s₁ ⨟ s₂ ⟩)
    step-⋆₂ : Step step-⋆₂ (⁉ ⟨ s₁ ⨟ s₂ ⟩)
    step-μ  : Step 𝓢 (unfold s) → Step 𝓢 (μ s)

  step-irr : Relation.Binary.Irrelevant (Step {n})
  step-irr step-♯      step-♯      = refl
  step-irr step-⋆₁     step-⋆₁     = refl
  step-irr step-⋆₂     step-⋆₂     = refl
  step-irr (step-μ s₁) (step-μ s₂) = cong step-μ (step-irr s₁ s₂)

  step-⋯ₛ : Step 𝓢 s → Step 𝓢 (s ⋯ₛ σ)
  step-⋯ₛ {s = ⁉ ♯ T ▸ s} step-♯ = step-♯
  step-⋯ₛ {s = ⁉ ⟨ s₁ ⨟ s₂ ⟩} step-⋆₁ = step-⋆₁
  step-⋯ₛ {s = ⁉ ⟨ s₁ ⨟ s₂ ⟩} step-⋆₂ = step-⋆₂
  step-⋯ₛ {s = μ s} (step-μ x) = step-μ (subst (Step _) (sym (⋯-exchangeₛₛ s (μ s) _)) (step-⋯ₛ x))

  target : {s : 𝕊 n} → Step 𝓢 s → 𝕊 n
  target {s = ⁉ ♯ T ▸ s}   step-♯  = s
  target {s = ⁉ ⟨ s ⨟ _ ⟩} step-⋆₁ = s
  target {s = ⁉ ⟨ _ ⨟ s ⟩} step-⋆₂ = s
  target {s = μ s} (step-μ x) = target x

  ⊢-target : (⊢s : ⊢ s) (step : Step 𝓢 s) → ⊢ target step
  ⊢-target (⊢♯ x)      step-♯     = x
  ⊢-target ⊢⋆⟨ x ⨟ _ ⟩ step-⋆₁    = x
  ⊢-target ⊢⋆⟨ _ ⨟ x ⟩ step-⋆₂    = x
  ⊢-target (⊢μ x xᶜ)   (step-μ s) = ⊢-target (⊢-unfold x xᶜ) s

  Path : REL RawPath (𝕊 n) _
  Path []       s = ⊤
  Path (𝓢 ∷ 𝓢*) s = Σ[ step ∈ Step 𝓢 s ] Path 𝓢* (target step)

  path-irr : Relation.Binary.Irrelevant (Path {n})
  path-irr {x = []}    π₁        π₂        = refl
  path-irr {x = _ ∷ _} (s₁ , π₁) (s₂ , π₂)
    rewrite step-irr s₁ s₂ | path-irr π₁ π₂
    = refl

  target* : ∀ {s : 𝕊 n} → Path 𝓢* s → 𝕊 n
  target* {𝓢* = []} {s = s} _ = s
  target* {𝓢* = _ ∷ _} (x , π) = target* π

  ⊢-target* : {s : 𝕊 n} (⊢s : ⊢ s) (π : Path 𝓢* s) → ⊢ target* π
  ⊢-target* {𝓢* = []}    ⊢s _       = ⊢s
  ⊢-target* {𝓢* = _ ∷ _} ⊢s (x , π) = ⊢-target* (⊢-target ⊢s x) π

------------------------------------------------------------------------------------------------------------------------
-- We define an induction measure `μLeaders`.

  μLeaders : 𝕊 n → ℕ
  μLeaders (μ s) = suc (μLeaders s)
  μLeaders _     = 0

  μLeaders-⋯ : (s : 𝕊 m) (ρ : Ren m n) → μLeaders (s ⋯ ρ) ≡ μLeaders s
  μLeaders-⋯ (□ E)           _ = refl
  μLeaders-⋯ (⁉ ♯ T ▸ s)     _ = refl
  μLeaders-⋯ (⁉ ⟨ s₁ ⨟ s₂ ⟩) _ = refl
  μLeaders-⋯ (` α)           _ = refl
  μLeaders-⋯ (μ s)           _ = cong suc (μLeaders-⋯ s _)

  μLeaders-⋯ₛ : {s : 𝕊 m} → ⊢ s → renOrC s σ → μLeaders (s ⋯ₛ σ) ≡ μLeaders s
  μLeaders-⋯ₛ ⊢□          ρ⊎sᶜ = refl
  μLeaders-⋯ₛ (⊢♯ s)      ρ⊎sᶜ = refl
  μLeaders-⋯ₛ ⊢⋆⟨ _ ⨟ _ ⟩ ρ⊎sᶜ = refl
  μLeaders-⋯ₛ (⊢μ s sᶜ)   ρ⊎sᶜ = cong suc $ μLeaders-⋯ₛ s λ where
    zero    → inj₂ sᶜ
    (suc x) → Sum.map (Π.map wk (cong (_⋯ wk))) ⊢c-μ⁻¹ (ρ⊎sᶜ x)
  μLeaders-⋯ₛ {σ = σ} (⊢` α) ρ⊎sᶜ with σ α in eq
  ... | ` α′        = refl
  ... | □ E         = refl
  ... | ⁉ ♯ T ▸ _   = refl
  ... | ⁉ ⟨ _ ⨟ _ ⟩ = refl
  ... | μ s with ρ⊎sᶜ α
  ... | inj₁ (-, eq′) = case trans (sym eq) eq′ of λ()
  ... | inj₂ sᶜ       = case ¬-⊢c-`x sᶜ         of λ()

  -- The induction measure's main property: if s has at least one free variable then
  --
  --   μLeaders (unfold s) ≡ μLeaders s
  --
  -- (The type signature is slightly more general than that.)
  μLeaders-⋯ₛ-0↦ : {s⁰ : 𝕊 n} → ⊢ s → ⊢ᶜ s → μLeaders (s ⋯ₛ 0↦ s⁰) ≡ μLeaders s
  μLeaders-⋯ₛ-0↦ s sᶜ = μLeaders-⋯ₛ s λ where
    zero    → inj₂ sᶜ
    (suc α) → inj₁ (-, refl)

  μLeaders-⋯ₛ-≤ : (s : 𝕊 m) → μLeaders s ≤ μLeaders (s ⋯ₛ σ)
  μLeaders-⋯ₛ-≤ (□ E)           = z≤n
  μLeaders-⋯ₛ-≤ (⁉ ♯ T ▸ s)     = z≤n
  μLeaders-⋯ₛ-≤ (⁉ ⟨ s₁ ⨟ s₂ ⟩) = z≤n
  μLeaders-⋯ₛ-≤ (μ s)           = s≤s (μLeaders-⋯ₛ-≤ s)
  μLeaders-⋯ₛ-≤ (` α)           = z≤n


------------------------------------------------------------------------------------------------------------------------
-- Prefixes (borrowed sessions) only have one way to end (END = ⊤). Owned session types must differentiate between
-- Wait and Term which is done by instantiating END = Dir.
End-ℙ = ⊤
End-𝕊 = Dir

module _ {END : Set} where
  open Core End-ℙ using () renaming (𝕊 to ℙ)
  open Core END   using (𝕊)
  open Core.𝕊
  open Functions

  private variable
    p : ℙ n
    s : 𝕊 n

----------------------------------------------------------------------------------------------------
-- Session type composition (written in the paper as  R ⨟ S).

  infixr 6 _◇_

  _◇_ : ℙ n → 𝕊 n → 𝕊 n
  □ _           ◇ s = s
  (⁉ ♯ T ▸ p)   ◇ s = ⁉ ♯ T ▸ p ◇ s
  ⁉ ⟨ p₁ ⨟ p₂ ⟩ ◇ s = ⁉ ⟨ p₁ ◇ s ⨟ p₂ ◇ s ⟩
  μ p           ◇ s = μ (p ◇ s ⋯ suc)
  ` α           ◇ s = ` α

  ⊢ᶜ_·[_◇_] : ∀ α → ⊢ᶜ α · p → ⊢ᶜ α · s → ⊢ᶜ α · p ◇ s
  ⊢ᶜ α ·[ ⊢c-□    ◇ sᶜ ] = sᶜ
  ⊢ᶜ α ·[ ⊢c-♯    ◇ sᶜ ] = ⊢c-♯
  ⊢ᶜ α ·[ ⊢c-⋆    ◇ sᶜ ] = ⊢c-⋆
  ⊢ᶜ α ·[ ⊢c-μ pᶜ ◇ sᶜ ] = ⊢c-μ ⊢ᶜ suc α ·[ pᶜ ◇ ⊢ᶜ-⋯ sᶜ wk-injective ]
  ⊢ᶜ α ·[ ⊢c-` α≠ ◇ sᶜ ] = ⊢c-` α≠

  ⊢ᶜ[_◇_] : ⊢ᶜ p → (s : 𝕊 n) → ⊢ᶜ p ◇ (s ⋯ wk)
  ⊢ᶜ[ pᶜ ◇ s ] = ⊢ᶜ zero ·[ pᶜ ◇ ⊢ᶜ-⋯wk s ]

  ⊢[_◇_] : ⊢ p → ⊢ s → ⊢ p ◇ s
  ⊢[ ⊢□            ◇ s ] = s
  ⊢[ ⊢♯ p          ◇ s ] = ⊢♯ ⊢[ p ◇ s ]
  ⊢[ ⊢⋆⟨ p₁ ⨟ p₂ ⟩ ◇ s ] = ⊢⋆⟨ ⊢[ p₁ ◇ s ] ⨟ ⊢[ p₂ ◇ s ] ⟩
  ⊢[ ⊢μ p pᶜ       ◇ s ] = ⊢μ ⊢[ p ◇ ⊢-⋯ s wk-injective ] ⊢ᶜ[ pᶜ ◇ _ ]
  ⊢[ ⊢` α          ◇ s ] = ⊢` α

  [_◇_]⋯-dist : (p : ℙ m) (s : 𝕊 m) (ρ : Ren m n) → (p ◇ s) ⋯ ρ ≡ p ⋯ ρ ◇ s ⋯ ρ
  [ ` α           ◇ s ]⋯-dist ρ = refl
  [ □ E           ◇ s ]⋯-dist ρ = refl
  [ ⁉ ♯ T ▸ p     ◇ s ]⋯-dist ρ = cong (⁉ ♯ T ▸_) ([ p ◇ s ]⋯-dist ρ)
  [ ⁉ ⟨ p₁ ⨟ p₂ ⟩ ◇ s ]⋯-dist ρ = cong₂ (⁉ ⟨_⨟_⟩) ([ p₁ ◇ s ]⋯-dist ρ) ([ p₂ ◇ s ]⋯-dist ρ)
  [ μ p           ◇ s ]⋯-dist ρ =
    cong μ
      $ trans ([ p ◇ s ⋯ wk ]⋯-dist (↑ ρ))
      $ cong (p ⋯ ↑ ρ ◇_) (sym (⋯-wk-↑ᵣ s ρ))

  ◇-⋯0↦⋆-dist : (m : ℕ) (p : ℙ (m + suc n)) (s : 𝕊 n) (p′ : ℙ n) →
    (p ◇ (s ⋯ wk ⋯ wk⋆ m)) ⋯ₛ m ↑ₛ⋆ 0↦ (p′ ◇ s) ≡ p ⋯ₛ m ↑ₛ⋆ 0↦ p′ ◇ s ⋯ wk⋆ m
  ◇-⋯0↦⋆-dist m (□ x) s p′ =
    trans (sym (⋯-wk-↑ₛ⋆ (s ⋯ wk) m (0↦ (p′ ◇ s))))
      $ cong (_⋯ wk⋆ m) (⋯-wk-cancels-0↦ (p′ ◇ s))
  ◇-⋯0↦⋆-dist m (⁉ ♯ T ▸ p) s p′ = cong (⁉ ♯ T ▸_) (◇-⋯0↦⋆-dist m p s p′)
  ◇-⋯0↦⋆-dist m (⁉ ⟨ p₁ ⨟ p₂ ⟩) s p′ = cong₂ (⁉ ⟨_⨟_⟩) (◇-⋯0↦⋆-dist m p₁ s p′) (◇-⋯0↦⋆-dist m p₂ s p′)
  ◇-⋯0↦⋆-dist m (μ p) s p′
    rewrite ⋯ᵣᵣ-fusion s (wk⋆ m) wk
    rewrite ⋯ᵣᵣ-fusion (s ⋯ wk) (wk⋆ m) wk
    = cong μ (◇-⋯0↦⋆-dist (suc m) p s p′)
  ◇-⋯0↦⋆-dist zero    (` zero)  s p′ rewrite ⋯-id s (λ z → refl) = refl
  ◇-⋯0↦⋆-dist zero    (` suc z) s p′ = refl
  ◇-⋯0↦⋆-dist (suc m) (` zero)  s p′ = refl
  ◇-⋯0↦⋆-dist (suc m) (` suc z) s p′ =
    trans (cong (_⋯ suc) (◇-⋯0↦⋆-dist m (` z) s p′))
      $ trans ([ (m ↑ₛ⋆ 0↦ p′) z ◇ s ⋯ wk⋆ m ]⋯-dist wk)
      $ cong ((m ↑ₛ⋆ 0↦ p′) z ⋯ wk ◇_) (⋯ᵣᵣ-fusion s (wk⋆ m) wk)

  unfold[_◇_] : (p : ℙ (suc n)) (s : 𝕊 n) → unfold (p ◇ s ⋯ wk) ≡ unfold p ◇ s
  unfold[ p ◇ s ] =
    trans (cong (λ s′ → (p ◇ s′) ⋯ₛ 0↦ (μ p ◇ s)) (sym (⋯-id (s ⋯ wk) (λ _ → refl))))
      $ trans (◇-⋯0↦⋆-dist 0 p s (μ p))
      $ cong (unfold p ◇_) (⋯-id s λ _ → refl)

  μLeaders-◇-⋯0↦⋆ : ∀ m (p : ℙ (m + suc n)) (pᶜ : ⊢ᶜ m ↑ʳ zero · p) (p′ : ℙ n) (s : 𝕊 n) →
    μLeaders (p ⋯ₛ m ↑ₛ⋆ 0↦ p′ ◇ s ⋯ wk⋆ m) ≡ μLeaders (p ◇ s ⋯ wk ⋯ wk⋆ m)
  μLeaders-◇-⋯0↦⋆ m (□ E) pᶜ p′ s =
    let open ≡-Reasoning in
    μLeaders (s ⋯ wk⋆ m)       ≡⟨ μLeaders-⋯ s (wk⋆ m) ⟩
    μLeaders s                 ≡⟨ μLeaders-⋯ s wk ⟨
    μLeaders (s ⋯ wk)          ≡⟨ μLeaders-⋯ (s ⋯ wk) (wk⋆ m) ⟨
    μLeaders (s ⋯ wk ⋯ wk⋆ m)  ∎
  μLeaders-◇-⋯0↦⋆ m (⁉ ♯ T ▸ p)   pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ m (⁉ ⟨ _ ⨟ _ ⟩) pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ m (μ p) (⊢c-μ pᶜ) p′ s
    rewrite ⋯ᵣᵣ-fusion s (wk⋆ m) wk
    rewrite ⋯ᵣᵣ-fusion (s ⋯ wk) (wk⋆ m) wk
    = cong suc $ μLeaders-◇-⋯0↦⋆ (suc m) p pᶜ p′ s
  μLeaders-◇-⋯0↦⋆ zero (` zero) pᶜ p′ s = ⊥-elim (¬-⊢c-`x pᶜ)
  μLeaders-◇-⋯0↦⋆ zero (` suc α) pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ (suc m) (` zero) pᶜ p′ s = refl
  μLeaders-◇-⋯0↦⋆ (suc m) (` suc α) (⊢c-` 0≠) p′ s =
    let open ≡-Reasoning in
    let α⋯ₛ = ` α ⋯ₛ m ↑ₛ⋆ 0↦ p′ in
    let IH = μLeaders-◇-⋯0↦⋆ m (` α) (⊢c-` (0≠ ∘· cong suc)) p′ s in
    μLeaders (α⋯ₛ ⋯ wk ◇ s ⋯ wk⋆ (suc m))       ≡⟨ cong (μLeaders ∘ (α⋯ₛ ⋯ wk ◇_)) (⋯ᵣᵣ-fusion s (wk⋆ m) wk) ⟨
    μLeaders (α⋯ₛ ⋯ wk ◇ s ⋯ wk⋆ m ⋯ wk)        ≡⟨ cong μLeaders ([ α⋯ₛ ◇ s ⋯ wk⋆ m ]⋯-dist wk) ⟨
    μLeaders ((α⋯ₛ     ◇ s ⋯ wk⋆ m) ⋯ wk)       ≡⟨ μLeaders-⋯ (α⋯ₛ ◇ s ⋯ wk⋆ m) wk ⟩
    μLeaders (α⋯ₛ      ◇ s ⋯ wk⋆ m)             ≡⟨ IH ⟩
    μLeaders (` suc α  ◇ s ⋯ wk ⋯ wk⋆ (suc m))  ∎

  μLeaders-unfold[_◇_] : (pᶜ : ⊢ᶜ p) (s : 𝕊 n) → μLeaders (unfold p ◇ s) ≡ μLeaders (p ◇ s ⋯ wk)
  μLeaders-unfold[_◇_] {p = p} pᶜ s =
    trans (cong (μLeaders ∘ (unfold p ◇_)) (sym (⋯-id s λ _ → refl)))
      $ trans (μLeaders-◇-⋯0↦⋆ 0 p pᶜ (μ p) s)
      $ cong (μLeaders ∘ (p ◇_))
      $ ⋯-id (s ⋯ wk) (λ _ → refl)

  step◇ : Step 𝓢 p → (s : 𝕊 n) → Step 𝓢 (p ◇ s)
  step◇ step-♯  s = step-♯
  step◇ step-⋆₁ s = step-⋆₁
  step◇ step-⋆₂ s = step-⋆₂
  step◇ (step-μ {s = p} x) s = step-μ (subst (Step _) (sym unfold[ p ◇ s ]) (step◇ x s))

  target-step◇ : (step : Step 𝓢 p) (s : 𝕊 n) → target (step◇ step s) ≡ target step ◇ s
  target-step◇ step-♯  s = refl
  target-step◇ step-⋆₁ s = refl
  target-step◇ step-⋆₂ s = refl
  target-step◇ (step-μ {s = p} step) s rewrite unfold[ p ◇ s ] = target-step◇ step s

  path◇ : Path 𝓢* p → (s : 𝕊 n) → Path 𝓢* (p ◇ s)
  path◇ {𝓢* = []}    _       s = _
  path◇ {𝓢* = _ ∷ _} (x , π) s = step◇ x s , subst (Path _) (sym (target-step◇ x s)) (path◇ π s)


------------------------------------------------------------------------------------------------------------------------
-- Given a decidable equality for the base types 𝕋 and END values the syntactic equality of sessions is decidable.
--
module EqualityCore (_≟T_ : DecidableEquality 𝕋) {END : Set} (_≟E_ : DecidableEquality END) where
  open Core (END)

  infix 4 _≟_

  _≟_ : DecidableEquality (𝕊 n)
  □ x ≟ □ y = map′ (λ{ refl → refl }) (λ{ refl → refl }) (x ≟E y)
  ⁉₁ ♯ T ▸ x ≟ ⁉₂ ♯ U ▸ y = map′ (λ{ (refl , refl , refl) → refl })
                                 (λ{ refl → refl , refl , refl })
                                 (⁉₁ ≟⁉ ⁉₂ ×-dec T ≟T U ×-dec x ≟ y)
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩ = map′ (λ{ (refl , refl , refl) → refl })
                                         (λ{ refl → refl , refl , refl })
                                         (⁉₁ ≟⁉ ⁉₂ ×-dec x₁ ≟ y₁ ×-dec x₂ ≟ y₂)
  μ x ≟ μ y = map′ (λ{ refl → refl }) (λ{ refl → refl }) (x ≟ y)
  ` x ≟ ` y = map′ (λ{ refl → refl }) (λ{ refl → refl }) (x Fin.≟ y)

  □ x ≟ ⁉ ♯ T ▸ y             = no λ()
  □ x ≟ ⁉ ⟨ y₁ ⨟ y₂ ⟩         = no λ()
  □ x ≟ μ y                   = no λ()
  □ x ≟ ` y                   = no λ()

  ⁉₁ ♯ T ▸ x ≟ □ y            = no λ()
  ⁉₁ ♯ T ▸ x ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩ = no λ()
  ⁉₁ ♯ T ▸ x ≟ μ y            = no λ()
  ⁉₁ ♯ T ▸ x ≟ ` y            = no λ()

  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ □ y        = no λ()
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ ⁉₂ ♯ U ▸ y = no λ()
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ μ y        = no λ()
  ⁉₁ ⟨ x₁ ⨟ x₂ ⟩ ≟ ` y        = no λ()

  μ x ≟ □ y                   = no λ()
  μ x ≟ ⁉₂ ♯ U ▸ y            = no λ()
  μ x ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩        = no λ()
  μ x ≟ ` y                   = no λ()

  ` x ≟ □ y                   = no λ()
  ` x ≟ ⁉₂ ♯ U ▸ y            = no λ()
  ` x ≟ ⁉₂ ⟨ y₁ ⨟ y₂ ⟩        = no λ()
  ` x ≟ μ y                   = no λ()

  decSetoid : ℕ → DecSetoid _ _
  decSetoid n = Eq.decSetoid (_≟_ {n})

  decSetoid₀ : DecSetoid _ _
  decSetoid₀ = decSetoid 0

open Core End-ℙ using () renaming (𝕊 to ℙ) public
open Core End-𝕊 using (𝕊) public
open Core.𝕊 public

module Equality (eq : DecidableEquality 𝕋) where
  open EqualityCore eq Unit._≟_ renaming
    ( _≟_ to infix 4 _≟ℙ_
    ; decSetoid  to decSetoid-ℙ
    ; decSetoid₀ to decSetoid-ℙ₀
    ) public
  open EqualityCore eq _≟⁉_ public
