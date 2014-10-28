module Term.Substitution.Types where

import           Term.Synonyms

-- | The "context morphism" interpretation, and the "do stuff to term"
-- interpretation.
data Substitution t
  = Id
    --   Γ ⊢ Id : Γ
    --
    -- Leaves everything as-is
  | Weaken !Int (Substitution t)
    --   Γ ⊢ ρ : Δ
    -- --------------------------------
    --   Γ ⊢ Weaken |Ψ| ρ : Δ; Ψ
    --
    -- Weaken the term by that much.
  | Snoc (Substitution t) (Term t)
    --   Γ ⊢ u : Aρ    Γ ⊢ ρ : Δ
    -- --------------------------------
    --   Γ ⊢ Snoc ρ u : Δ; A
    --
    -- Add a new thing to substitute, now variable 0 will be replaced by
    -- that term.
  | Strengthen !Int (Substitution t)
    --   Γ ⊢ ρ : Δ
    -- --------------------------------
    --   Γ; Ψ ⊢ Strengthen |Ψ| ρ : Δ
    --
    -- Strengthen the term
  | Lift !Int (Substitution t)
    --   Γ ⊢ ρ : Δ
    -- --------------------------------
    --   Γ; Ψρ ⊢ Lift |Ψ| ρ : Δ; Ψ
    --
    -- Does whatere is in ρ lifted by n.
