open import Data.Nat

data Int : Set where
  swap    : Int
  clone   : Int
  drop    : Int
  quot    : Int
  compose : Int
  apply   : Int

infix  5 ⟦_⟧
infixl 7 _∘_
infix  9 `_

data Expr : Set where

  `_  : Int → Expr

  ⟦_⟧ : Expr → Expr

  _∘_ : Expr → Expr → Expr

data Value : Expr → Set where

  ⟦_⟧ : (e : Expr) → Value ⟦ e ⟧

infixl 4 _,_

data Stack : Set where

  ⟨⟩  : Stack

  _,_ : ∀ {e}
      → (V : Stack)
      → (v : Value e)
      → Stack

infix 3 ⟨_⟩_→⟨_⟩

variable
  V V′ W W′ : Stack
  e e′ : Expr
  v  : Value e
  v′ : Value e′

data ⟨_⟩_→⟨_⟩ : Stack → Expr → Stack → Set where

  -- intrinsics

  ξ-i-swap    : ⟨ V , v , v′ ⟩ ` swap →⟨ V , v′ , v ⟩
  ξ-i-clone   : ⟨ V , ⟦ e ⟧ ⟩ ` clone →⟨ V , ⟦ e ⟧ , ⟦ e ⟧ ⟩
  ξ-i-drop    : ⟨ V , ⟦ e ⟧ ⟩ ` drop →⟨ V ⟩
  ξ-i-quote   : ⟨ V , ⟦ e ⟧ ⟩ ` quot →⟨ V , ⟦ e ⟧ ⟩
  ξ-i-compose : ⟨ V , ⟦ e ⟧ , ⟦ e′ ⟧ ⟩ ` compose →⟨ V , ⟦ e ∘ e′ ⟧ ⟩
  ξ-i-apply   : ⟨ V ⟩ e →⟨ V′ ⟩ → ⟨ V , ⟦ e ⟧ ⟩ ` apply →⟨ V′ ⟩

  -- expressions

  ξ-⟦⟧ : ⟨ V ⟩ ⟦ e ⟧ →⟨ V , ⟦ e ⟧ ⟩

  ξ-∘ : ⟨ V  ⟩ e  →⟨ V′ ⟩
      → ⟨ V′ ⟩ e′ →⟨ W  ⟩
        -------------------
      → ⟨ V ⟩ e ∘ e′ →⟨ W ⟩

⊥ : Expr
⊥ = ⟦ ` drop ⟧

⊥-value : Value ⊥
⊥-value = ⟦ ` drop ⟧

⊤ : Expr
⊤ = ⟦ ` swap ∘ ` drop ⟧

⊤-value : Value ⊤
⊤-value = ⟦ ` swap ∘ ` drop ⟧

⊥-thm : ⟨ V , ⟦ e ⟧ , ⟦ e′ ⟧ ⟩ ⊥ ∘ ` apply →⟨ V , ⟦ e ⟧ ⟩
⊥-thm = ξ-∘ ξ-⟦⟧ (ξ-i-apply ξ-i-drop)

⊤-thm : ⟨ V , ⟦ e ⟧ , ⟦ e′ ⟧ ⟩ ⊤ ∘ ` apply →⟨ V , ⟦ e′ ⟧ ⟩
⊤-thm = ξ-∘ ξ-⟦⟧ (ξ-i-apply (ξ-∘ ξ-i-swap ξ-i-drop))

∨ : Expr
∨ = ` clone ∘ ` apply

∨-⊥-⊥ : ⟨ V , ⟦ e ⟧ , ⊥-value ⟩ ∨ →⟨ V , ⟦ e ⟧ ⟩
∨-⊥-⊥ = ξ-∘ ξ-i-clone (ξ-i-apply ξ-i-drop)

∨-⊤ : ⟨ V , ⟦ e ⟧ , ⊤-value ⟩ ∨ →⟨ V , ⊤-value ⟩
∨-⊤ = ξ-∘ ξ-i-clone (ξ-i-apply (ξ-∘ ξ-i-swap ξ-i-drop))

quoteₙ : ℕ → Expr
quoteₙ zero = ` quot
quoteₙ (suc n) = quoteₙ n ∘ ` swap ∘ ` quot ∘ ` swap ∘ ` compose

quote₂-thm : ⟨ V , ⟦ e ⟧ , ⟦ e′ ⟧ ⟩ quoteₙ 1 →⟨ V , ⟦ e ∘ e′ ⟧ ⟩
quote₂-thm = ξ-∘ (ξ-∘ (ξ-∘ (ξ-∘ ξ-i-quote ξ-i-swap) ξ-i-quote) ξ-i-swap) ξ-i-compose

composeₙ : ℕ → Expr
composeₙ zero = ` compose
composeₙ (suc n) = ` compose ∘ composeₙ n
