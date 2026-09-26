/-
Copyright (c) 2026 The Erdős #1220 formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Erdős Problem #1220 — comparator solution

The untrusted half of the comparator challenge, modelled on elliotglazer/erdos501's
`Solution.lean`: the statements of `Challenge.lean` (Part B), repeated verbatim, each proved by
delegation to the library.  Only the statements are compared by the comparator; this file may
import anything (it must not import `Challenge`).

The shared definitions of `Challenge.lean` (Part A) are provided here by the library itself:
`Erdos1220.Problem1220` and friends by `Erdos1220.lean`, the sentence `Erdos1220.FOL.Erdos1220` by
`Erdos1220Full/Statement1220.lean` (Part A of the Challenge is generated verbatim from these two
files by `sync_challenge.py`), and `L`, `ZFC`, `zfsetStructure` by erdos501's
`Erdos501.FOL.Statement`.

Both targets are proved in the library: `Erdos1220.FOL.erdos1220_not_provable`
(`Erdos1220Full/Independence1220.lean`) and `Erdos1220.FOL.erdos1220_sentence_faithful`
(`Erdos1220Full/Faithful1220.lean`).
-/
import Mathlib.SetTheory.Cardinal.Continuum
import Mathlib.SetTheory.Cardinal.Regular
import Mathlib.Data.Finset.Card
import Mathlib.ModelTheory.Satisfiability
import Mathlib.SetTheory.ZFC.Basic
import Erdos501.FOL.Statement
import Erdos1220Full.Faithful1220
import Erdos1220Full.Independence1220

open scoped FirstOrder
open FirstOrder FirstOrder.Language
open Erdos501.FOL

theorem erdos1220_not_provable : ¬ (ZFC ⊨ᵇ Erdos1220.FOL.Erdos1220) :=
  Erdos1220.FOL.erdos1220_not_provable

theorem erdos1220_sentence_faithful :
    (ZFSet.{0} ⊨ Erdos1220.FOL.Erdos1220) ↔ Erdos1220.Problem1220.{0} :=
  Erdos1220.FOL.erdos1220_sentence_faithful
