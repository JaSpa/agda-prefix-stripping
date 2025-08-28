# Prefix Stripping

Complete proofs for prefix stripping.

To check all files:

    agda PrefixStripping/Decide.agda

## File Overview

```agda
-- Defines basic syntactic constructs.
import PrefixStripping.Syntax

-- Defines session types, substitution on session types, and type composition.
import PrefixStripping.Sessions

-- Defines equivalence of session types.
import PrefixStripping.Sessions.Equivalence

-- Proves that the set of syntactic subterms of all session types is finite.
import PrefixStripping.Sessions.Subterm

-- Supporting definitions for the decision procedure.
import PrefixStripping.Decide.Universe

-- Main workhorses for the soundness proofs.
import PrefixStripping.Decide.Soundness

-- Using the lemmas about syntactic subterms and Data.List.Countdown from
-- agda-stdlib this provides machinery proving that the algorithm terminates.
import PrefixStripping.Decide.Coinduction

-- Contains the prefix stripping algorithm and the final proofs.
import PrefixStripping.Decide
```
