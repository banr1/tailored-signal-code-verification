/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Over.HeapDefs
public meta import Lean -- shake: keep

/-!
# `SessionRecord::serialize` with One Previous Session: Specification

Wire encoding `encodeRecordPrev1` and subroutine contract `serializePrev1Spec` /
`SerializePrev1OkStmt` for `<SessionRecord>::serialize` when the record holds a current session
together with a single archived previous session (`previous_sessions = [enc]`).
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedVariables false

section SepPullPureTactic
open Lean Meta Elab Tactic Arm64

private meta partial def collectSepConjAtomsClose (e : Expr) : MetaM (Array Expr) := do
  let e := (← instantiateMVars e).consumeMData
  if e.isAppOfArity ``SepProp.sepConj 2 then
    return (← collectSepConjAtomsClose (e.getArg! 0)) ++ (← collectSepConjAtomsClose (e.getArg! 1))
  else
    return #[e]

private meta def mkSepConjChainClose (atoms : Array Expr) : Expr :=
  if h : atoms.size = 0 then
    mkConst ``SepProp.emp
  else
    atoms.foldl (init := atoms[0]) (start := 1) fun acc a =>
      mkApp2 (mkConst ``SepProp.sepConj) acc a

/-- Pull a matching `⌜P⌝` pure atom out of a `∗`-chain on `⊢ Q = ⌜P⌝ ∗ ?F` via `ac_rfl`. -/
elab "sep_pull_pure" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some (_, lhs, rhs) := tgt.eq?
    | throwError "sep_pull_pure: expected equality goal, got {tgt}"
  if !rhs.isAppOfArity ``SepProp.sepConj 2 then
    throwError "sep_pull_pure: expected `⌜P⌝ ∗ F` on RHS, got {rhs}"
  let pureTarget := rhs.getArg! 0
  let frameMVar := rhs.getArg! 1
  let atoms ← collectSepConjAtomsClose lhs
  let mut foundIdx? : Option Nat := none
  for i in [:atoms.size] do
    let a := atoms[i]!
    if a.isAppOfArity ``SepProp.pure 1 then
      if ← isDefEq a pureTarget then
        foundIdx? := some i
        break
  let some idx := foundIdx?
    | throwError "sep_pull_pure: no matching pure atom `{pureTarget}` in `{lhs}`"
  let rem := atoms.eraseIdx! idx
  let rest := mkSepConjChainClose rem
  if !(← isDefEq frameMVar rest) then
    throwError "sep_pull_pure: failed to unify frame `{frameMVar}` with `{rest}`"
  evalTactic (← `(tactic| ac_rfl))

end SepPullPureTactic

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Record.Serialization (CanonSession)

/-! ## Wire encoding -/

/-- Canonical wire bytes of a `SessionRecord` with current session `sess` and
`previous_sessions = [enc]`: length-delimited field 1 (`encodeRecord ⟨some sess⟩`) followed by
length-delimited field 2 (`0x12`, varint length, `enc`). -/
def encodeRecordPrev1 (sess : Session (List (BitVec 8))) (enc : List (BitVec 8)) :
    List (BitVec 8) :=
  CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩ ++
    CryptoVerification.E2E.Record.lenField 2 enc

theorem encodeRecordPrev1_length_pos (sess : Session (List (BitVec 8))) (enc : List (BitVec 8))
    (h0 : 0 < (CryptoVerification.E2E.Record.encodeRecord ⟨some sess⟩).length) :
    0 < (encodeRecordPrev1 sess enc).length := by
  unfold encodeRecordPrev1
  rw [List.length_append]
  omega

/-! ## Subroutine specification -/

structure SerializePrev1Ghost where
  self : BitVec 64
  prevCap : BitVec 64
  prevPtr : BitVec 64
  G : SessionGhost
  sess : Session (List (BitVec 8))
  enc : List (BitVec 8)
  out : BitVec 64

/-- Specification of `<SessionRecord>::serialize` on `sessionRecordPrevAt` with current session
`sess` and `previous_sessions = [enc]`, preserving the input record and writing
`encodeRecordPrev1 sess enc` to `out`. -/
def serializePrev1Spec (A : RustAlloc) : Spec SerializePrev1Ghost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.self ∧ s.readReg64 .x8 = x.out ∧
      BinCanonSession x.G x.sess ∧ (encodeRecordPrev1 x.sess x.enc).length < 2 ^ 32⌝ ∗
      sessionRecordPrevAt A x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      memRegion x.out 48 ∗ A.pool ∗ stackAt s.sp recordSerializeStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      sessionRecordPrevAt A x.self ⟨x.prevCap, x.prevPtr, some x.G⟩ [x.enc] ⟨some x.sess⟩ ∗
      (x.out ↦₆₄ okTagVec) ∗ vecU8 A (x.out + 8#64) (encodeRecordPrev1 x.sess x.enc) ∗
      memRegion (x.out + 32#64) 16 ∗ A.pool ∗ stackAt s0.sp recordSerializeStack
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

def SerializePrev1OkStmt (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (contractProg img.base ext) (img.base + serializeOff)
    ((serializePrev1Spec A).inImage img)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Over
