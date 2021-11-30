# The Untyped Concatenative Calculus

This is a partial formalization of Scott J Maddox's [Untyped Concatenative Calculus](https://www.dawn-lang.org/posts/foundations-ucc/).

## Imports

Some mathematics:

$$
f(x) = 42
$$

```
open import Data.Product hiding (swap; _,′_)
open import Data.Nat
open import Function hiding (_∘′_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
```

## Definitions

### Intrinsics & Expressions

```
data Int : Set where
  swap    : Int
  clone   : Int
  drop    : Int
  quot    : Int
  compose : Int
  apply   : Int

infix  5 [_]
infixl 7 _∘′_
infix  9 `_

data Expr : Set where
  `_   : Int → Expr
  [_]  : Expr → Expr
  _∘′_ : Expr → Expr → Expr
```

### Values and the Stack

```
data Value : Expr → Set where
  ⟦_⟧ : (e : Expr) → Value [ e ]

infixl 4 _,′_

data Stack : Set where
  ⟨⟩  : Stack
  _,′_ : ∀ {e}
       → (V : Stack)
       → (v : Value e)
       → Stack
```

# Small-Step Semantics

```
infix 3 ⟨_⟩_→⟨_⟩

data ⟨_⟩_→⟨_⟩ : Stack → Expr → Stack → Set where
```

### Intrinsics

```
  i-swap : ∀ {V e e′}
         → (v : Value e)
         → (v′ : Value e′)
           -----------------------------------------
         → ⟨ V ,′ v ,′ v′ ⟩ ` swap →⟨ V ,′ v′ ,′ v ⟩

  i-clone : ∀ {V e}
          → (v : Value e)
            -----------------------------------
          → ⟨ V ,′ v ⟩ ` clone →⟨ V ,′ v ,′ v ⟩

  i-drop : ∀ {V e}
           → (v : Value e)
             ------------------------
           → ⟨ V ,′ v ⟩ ` drop →⟨ V ⟩

  i-quote : ∀ {V e}
            → (v : Value e)
              ---------------------------------
            → ⟨ V ,′ v ⟩ ` quot →⟨ V ,′ ⟦ e ⟧ ⟩

  i-compose : ∀ {V e e′}
              --------------------------------------------------------
            → ⟨ V ,′ ⟦ e ⟧ ,′ ⟦ e′ ⟧ ⟩ ` compose →⟨ V ,′ ⟦ e ∘′ e′ ⟧ ⟩

  i-apply : ∀ {V V′ e}
          → ⟨ V ⟩ e →⟨ V′ ⟩
            ------------------------------
          → ⟨ V ,′ ⟦ e ⟧ ⟩ ` apply →⟨ V′ ⟩
```

### Expressions

```
  e-quote : ∀ {V e}
            ---------------------------
          → ⟨ V ⟩ [ e ] →⟨ V ,′ ⟦ e ⟧ ⟩

  _e-∘_ : ∀ {V V′ W e e′}
        → ⟨ V  ⟩ e  →⟨ V′ ⟩
        → ⟨ V′ ⟩ e′ →⟨ W  ⟩
          --------------------
        → ⟨ V ⟩ e ∘′ e′ →⟨ W ⟩
```

## Properties

### Composition

```
e-comp-assoc′ : ∀ {V W e₁ e₂ e₃} → ⟨ V ⟩ (e₁ ∘′ e₂) ∘′ e₃ →⟨ W ⟩ ↔ ⟨ V ⟩ e₁ ∘′ (e₂ ∘′ e₃) →⟨ W ⟩
e-comp-assoc′
  = mk↔
    {f = λ{ ((l e-∘ l₁) e-∘ r) → l e-∘ (l₁ e-∘ r) }}
    {f⁻¹ = λ{ (l e-∘ (r e-∘ r₁)) → (l e-∘ r) e-∘ r₁ }}
    ((λ{ (l e-∘ (r e-∘ r₁)) → refl }) , λ{ ((l e-∘ l₁) e-∘ r) → refl })
```

## Data Types

### Booleans

```
⊥ : Expr
⊥ = [ ` drop ]

⊥ᵥ : Value ⊥
⊥ᵥ = ⟦ ` drop ⟧

⊤ : Expr
⊤ = [ ` swap ∘′ ` drop ]

⊤ᵥ : Value ⊤
⊤ᵥ = ⟦ ` swap ∘′ ` drop ⟧
```

#### Properties

```
⊥-thm : ∀ {V e e′}
      → (v : Value e)
      → (v′ : Value e′)
      → ⟨ V ,′ v ,′ v′ ⟩ ⊥ ∘′ ` apply →⟨ V ,′ v ⟩
⊥-thm {V} v v′ = e-quote e-∘ i-apply (i-drop v′)

⊤-thm : ∀ {V e e′}
      → (v : Value e)
      → (v′ : Value e′)
      → ⟨ V ,′ v ,′ v′ ⟩ ⊤ ∘′ ` apply →⟨ V ,′ v′ ⟩
⊤-thm {V} {e} {e′} v v′ = e-quote e-∘ i-apply (i-swap v v′ e-∘ i-drop v)
```

### Boolean Operations

```
∨ : Expr
∨ = ` clone ∘′ ` apply
```

#### Operations

```
∨-⊥-⊥ : ∀ {V e} → ⟨ V ,′ ⟦ e ⟧ ,′ ⊥ᵥ ⟩ ∨ →⟨ V ,′ ⟦ e ⟧ ⟩
∨-⊥-⊥ = i-clone ⟦ ` drop ⟧ e-∘ i-apply (i-drop ⟦ ` drop ⟧)

∨-⊤ : ∀ {V e} → ⟨ V ,′ ⟦ e ⟧ ,′ ⊤ᵥ ⟩ ∨ →⟨ V ,′ ⊤ᵥ ⟩
∨-⊤ {V} {e} = i-clone ⟦ ` swap ∘′ ` drop ⟧ e-∘
                i-apply (i-swap ⟦ e ⟧ ⟦ ` swap ∘′ ` drop ⟧ e-∘ i-drop ⟦ e ⟧)
```

## Useful Terms

### Quotation

```
quoteₙ : ℕ → Expr
quoteₙ zero = ` quot
quoteₙ (suc n) = quoteₙ n ∘′ ` swap ∘′ ` quot ∘′ ` swap ∘′ ` compose
```

#### Properties

```
quote₂-thm : ∀ {V e e′}
           → (v : Value e)
           → (v′ : Value e′)
             -------------------------------------------
           → ⟨ V ,′ v ,′ v′ ⟩ quoteₙ 1 →⟨ V ,′ ⟦ e ∘′ e′ ⟧ ⟩
quote₂-thm {V} {e} {e′} v v′ = (((i-quote v′ e-∘ i-swap v ⟦ e′ ⟧) e-∘ i-quote v) e-∘
                                  i-swap ⟦ e′ ⟧ ⟦ e ⟧)
                                 e-∘ i-compose
```

### Composition

```
composeₙ : ℕ → Expr
composeₙ zero = ` compose
composeₙ (suc n) = ` compose ∘′ composeₙ n
```

-- TODO: Canonical forms
-- TODO: Progress
-- TODO: Preservation
-- TODO: Evaluation
