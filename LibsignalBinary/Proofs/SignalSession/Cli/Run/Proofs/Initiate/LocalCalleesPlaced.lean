/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.LocalCallees
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DefsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.HooksPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCalleesPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.KemPubSerializeLocal2Placed
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5Placed
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.HandshakeDerive
public import LibsignalBinary.Proofs.TripleRatchet.Keys.CreateChain
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Extract
public import LibsignalBinary.Proofs.TripleRatchet.Hkdf.Expand
public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.ModelBridge
import LibsignalBinary.Proofs.TripleRatchet.Alloc.DerivePublicKeyBytes

/-!
# Relocatable Local Handshake and E2E Callees for `initiate`

Transfers the 18 local handshake, PQXDH, TripleRatchet, and SPQR callees onto `initProgPlaced mmpl gh W`
(`lsProg_521`) under `[LibsignalPlacement]`, wrapped in `StoreKit.withLsCodeRoLoaded lsmpl` and
bundled into `InitLocalCalleesPlaced`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Obj Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet hiding
  withLsCodeRoLoaded extract_withLsCodeRoLoaded subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## Image-free inner specifications for `withLsCodeRoLoaded lsmpl` -/

/-- Image-free inner specification of `<kem::Key<Public>>::serialize [local#1]` (block `523`). -/
def kemPubSerializeInnerSpec (A : RustAlloc) (stk : Nat) : Spec KemPubSerializeGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.kpkPtr ∧ s.readReg64 .x1 = 1568#64 ∧ x.kpk.length = 1568⌝ ∗
      (x.keyRef ↦₆₄ x.kpkPtr) ∗ ((x.keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (x.kpkPtr ↦ₛ x.kpk) ∗ A.pool ∗ stackAt s.sp stk
  post := fun x s0 sf =>
    ⌜sf.readReg64 .x0 ≠ 0#64 ∧ sf.readReg64 .x1 = 1569#64 ∧ sf.trace = s0.trace⌝ ∗
      A.live (sf.readReg64 .x0) 1569 1 ∗
      ((sf.readReg64 .x0) ↦ₛ (0x08#8 :: x.kpk)) ∗
      (x.keyRef ↦₆₄ x.kpkPtr) ∗ ((x.keyRef + 8#64) ↦₆₄ 1568#64) ∗
      (x.kpkPtr ↦ₛ x.kpk) ∗ A.pool ∗ stackAt s0.sp stk
  onPanic := fun _ s0 sf => ⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap

/-- Image-free inner specification of `<PublicKey>::verify_signature` (block `203`). -/
def verifySignatureInnerSpec (P : SignalPqxdh.Primitives) : Spec VerifySignatureGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x0 = g.pkPtr ∧
      s.readReg64 .x1 = g.msgPtr ∧
      s.readReg64 .x2 = BitVec.ofNat 64 g.m.length ∧
      s.readReg64 .x3 = g.sigPtr ∧
      s.readReg64 .x4 = 64#64 ∧
      g.pk.length = 32 ∧
      (g.m.length = 33 ∨ g.m.length = 1569) ∧
      g.sig.length = 64⌝ ∗
      (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
      stackAt s.sp (Pqxdh.Shared.pqxdhHookStack + 1280)
  post := fun g s0 sf =>
    ⌜sf.readReg64 .x0 = (if P.sigVerify g.pk g.m g.sig = true then 1#64 else 0#64) ∧
      sf.trace = s0.trace⌝ ∗
      (g.pkPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.pk) ∗
      (g.msgPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.m) ∗
      (g.sigPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.sig) ∗
      stackAt s0.sp (Pqxdh.Shared.pqxdhHookStack + 1280)

/-- Image-free inner specification of `<PrivateKey>::calculate_agreement` (block `207`). -/
def pqxdhCalculateAgreementPlacedInnerSpec (P : SignalPqxdh.Primitives) (A : RustAlloc) :
    Spec (BitVec 64 × Pqxdh.Shared.Bytes × BitVec 64 × Pqxdh.Shared.Bytes ×
      BitVec 64 × BitVec 64) where
  pre := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) s =>
    ⌜s.readReg64 .x0 = ourA ∧ s.readReg64 .x1 = theirA ∧ s.readReg64 .x8 = ret ∧ s.sp = sp ∧
      ourSk32.length = 32 ∧ theirPk32.length = 32⌝ ∗
      (ourA ↦ₛ Pqxdh.Shared.bytesToBv8 ourSk32) ∗
      (theirA ↦ₛ Pqxdh.Shared.bytesToBv8 theirPk32) ∗
      memRegion ret 24 ∗ A.pool ∗ stackAt sp Pqxdh.Initiator.calculateAgreementStack
  post := fun (ourA, ourSk32, theirA, theirPk32, ret, sp) _s0 sf =>
    ⌜sf.trace = _s0.trace⌝ ∗
      (ourA ↦ₛ Pqxdh.Shared.bytesToBv8 ourSk32) ∗
      (theirA ↦ₛ Pqxdh.Shared.bytesToBv8 theirPk32) ∗
      Pqxdh.ResponderCore.pqxdhCalculateAgreementResultAt P A ret ourSk32 theirPk32 ∗
      A.pool ∗ stackAt sp Pqxdh.Initiator.calculateAgreementStack
  onPanic := Pqxdh.Initiator.rustPanicOnOomPlaced

/-- Image-free inner specification of `spqr::initial_state` (block `327`). -/
def spqrInitialStateInnerSpec [LibsignalPlacement] (A : RustAlloc) (F : ShaCompress) :
    Spec CryptoVerification.SpqrV1.Top.InitialState.InitialStateGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.pA ∧
      s.readReg64 .x8 = x.ret ∧
      x.akPtr ≠ 0#64 ∧
      x.p.authKey.length < 2 ^ 32⌝ ∗
      CryptoVerification.SpqrV1.Top.InitialState.paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      memRegion x.ret 32 ∗
      FromRecordCallees.lsLogOff ∗
      A.pool ∗ stackAt s.sp CryptoVerification.SpqrV1.Top.InitialState.initialStateStack
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      CryptoVerification.SpqrV1.Top.InitialState.paramsAt x.pA x.akPtr x.p ∗
      (x.akPtr ↦ₛ x.p.authKey) ∗
      CryptoVerification.SpqrV1.Top.InitialState.initialStateResultAt A x.ret
        (CryptoVerification.SpqrV1.Top.InitialState.initialStateValue F x.p) ∗
      FromRecordCallees.lsLogOff ∗
      A.pool ∗ stackAt s0.sp CryptoVerification.SpqrV1.Top.InitialState.initialStateStack
  onPanic := fun _ s0 sf => CryptoVerification.SpqrV1.Top.InitialState.initialStateOnPanic s0 sf

/-- Image-free inner specification of `<SessionState>::set_unacknowledged_pre_key_message` at `UNIX_EPOCH` (block `33`). -/
def setUnackPreKeyMsgEpochInnerSpec (A : RustAlloc) :
    Spec Pqxdh.TopLevel.SetUnackExactGhost where
  pre := fun g s =>
    ⌜s.readReg64 .x5 = 0#64 ∧ (s.readReg64 .x6).setWidth 32 = 0#32⌝ ∗
      ⌜s.readReg64 .x0 = g.statePtr ∧
        (s.readReg64 .x1).setWidth 32 = g.optOpkTag ∧
        (s.readReg64 .x2).setWidth 32 = g.optOpkVal ∧
        (s.readReg64 .x3).setWidth 32 = g.spkId ∧
        s.readReg64 .x4 = g.baseKeyPtr ∧
        g.baseKeyBytes.length = 32⌝ ∗
      (g.baseKeyPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.baseKeyBytes) ∗
      ((g.statePtr + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      memRegion (g.statePtr + 0x100#64) 40 ∗
      stackAt (s.sp - 144#64) (allocHookStack + 32) ∗
      cells (s.sp - 144#64) 18 ∗
      A.pool
  post := fun g s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗
      (g.baseKeyPtr ↦ₛ Pqxdh.Shared.bytesToBv8 g.baseKeyBytes) ∗
      Pqxdh.Initiator.vecU8 A (g.statePtr + 0xf8#64)
        (Pqxdh.Shared.bytesToBv8 (Pqxdh.Initiator.encodeEC g.baseKeyBytes)) ∗
      ((g.statePtr + 0x110#64) ↦₃₂ g.optOpkTag) ∗
      ((g.statePtr + 0x114#64) ↦₃₂ g.optOpkVal) ∗
      ((g.statePtr + 0x118#64) ↦₆₄ 0#64) ∗
      ((g.statePtr + 0x120#64) ↦₃₂ g.spkId) ∗
      memRegion (g.statePtr + 0x124#64) 4 ∗
      stackAt (s0.sp - 144#64) (allocHookStack + 32) ∗
      cells (s0.sp - 144#64) 18 ∗
      A.pool
  onPanic := Pqxdh.Initiator.rustPanicOnOomPlaced

/-! ## External callee bundle (`SubsetA4InitCalleesPlaced`) -/

/-- Bundle of external PQXDH, SPQR, and TripleRatchet callee contracts used by `initLocalCallees_placed_ok`. -/
structure SubsetA4InitCalleesPlaced [LibsignalPlacement] (A : RustAlloc) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) : Prop where
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 203)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩)))
  isSameAccount :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 17)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (Pqxdh.WireEntries.isSameAccountDistinctSpec A uuidTryParse))
  calculateAgreement : ∀ (X : UnreachedPqxdhPrimitives),
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 207)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A))
  spqrInitialState :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 327)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A W.C.F))
  setUnackPreKeyMsg :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 33)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A))
  pqxdhHkdfExtract : ∀ (X : UnreachedPqxdhPrimitives),
    Pqxdh.Initiator.PqxdhHkdfExtractPlacedOk (modelPrims X ⟨W.C, W.Q⟩)
      ((CryptoVerification.blkPC_59).rebase (CryptoVerification.blkPl_59).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
  pqxdhHkdfExpand : ∀ (X : UnreachedPqxdhPrimitives),
    Pqxdh.Initiator.PqxdhHkdfExpandMultiInfoPlacedOk (modelPrims X ⟨W.C, W.Q⟩)
      ((CryptoVerification.blkPC_59).rebase (CryptoVerification.blkPl_59).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
  ctEqSliceRO :
    subroutine_ok
      ((CryptoVerification.blkPC_207).rebase
        (CryptoVerification.blkPl_207).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 213)
      (withLsCodeLoaded lsmpl ctEqSliceROSpec)
  newFromSlice :
    subroutine_ok
      ((CryptoVerification.LibsignalTripleRatchet.blkPC_54).rebase
        (CryptoVerification.LibsignalTripleRatchet.blkPl_54).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 114)
      { newFromSliceSpec W.C.F with
        pre := fun x s0 =>
          (newFromSliceSpec W.C.F).pre x s0 ∗
            ⌜LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl s0.mem⌝ }

/-! ## Callee transfer theorems onto `initProgPlaced` -/

private theorem transfer_tr_codeLoaded [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry (withLsCodeLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) := by
  have hcrl : subroutine_ok calleeProg entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
    LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hcallee
  exact transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hcrl (by decide) hj hj_unmut

private theorem transfer_tr_codeRoLoaded [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl spec))
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) := by
  have hcrl : subroutine_ok calleeProg entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
    subroutine_ok_mono hcallee
      (fun _ _ _ hp => by
        obtain ⟨hc, hpre⟩ := LibsignalPublicApi.StoreKit.extract_withLsCodeRoLoaded hp
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded]
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
        exact ⟨⟨hc.1, hc.2⟩, hpre⟩)
      (fun _ _ _ _ hq => hq)
  exact transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W) hcrl (by decide) hj hj_unmut

private theorem transfer_plain_block [LibsignalPlacement] {α : Type}
    {calleeProg : Program} {j : Nat} {mmpl : MultiPlacement} {gh : CliGhostHooks} {W : CliHooks}
    [IsLsBlockProg calleeProg j (cliGhostExterns gh (cliExternsPlaced mmpl W))]
    {entry : BitVec 64} {spec : Spec α}
    (hcallee : subroutine_ok calleeProg entry spec)
    (hj : j < 619 := by decide)
    (hj_unmut : (j ∈ libsignalMutatedBlocks) = false := by decide) :
    subroutine_ok (initProgPlaced mmpl gh W) entry
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl spec) :=
  transfer_withLsCodeRoLoaded (callerProg := initProgPlaced mmpl gh W)
    (LibsignalPublicApi.StoreKit.subroutine_ok_withLsCodeRoLoaded_of_plain hcallee)
    (by decide) hj hj_unmut

/-- `<kem::Key<Public>>::serialize [local#1]` (block `523`) on `initProgPlaced`. -/
theorem kemPublicKeySerialize_local2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    {stk : Nat} (hstk : 0x30 + extHookStack ≤ stk) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 523)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (kemPubSerializeInnerSpec A stk)) := by
  have h523 : subroutine_ok (CryptoVerification.CliHandshake.Placed.lsProg_523 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 523) (kemPubSerializeInnerSpec A stk) := by
    refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp _hL => ?_
    exact (KemPubSerializeLocal2.kemPubKeySerialize_local2_full_placed_ok hh hstk).mono_outcome
      (x.keyRef, x.kpkPtr, x.kpk) R s0 hpc hrun hpre hsp (fun _ hout => hout)
  exact transfer_plain_block
    (calleeProg := CryptoVerification.CliHandshake.Placed.lsProg_523 (cliGhostExterns gh (cliExternsPlaced mmpl W))) h523

/-- `core::ptr::drop_glue::<SessionStructure> [local#4]` (block `512`) on `initProgPlaced`. -/
theorem dropSessionStructure_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (FromRecordCallees.dropSessionStructureLocal2Spec A)) :=
  transfer_tr_codeLoaded
    (calleeProg := CryptoVerification.CliHandshake.Placed.lsProg_512 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (CryptoVerification.SignalSession.Cli.Run.Proofs.Initiate.DropSessionStructureLocal5.drop_session_structure5_placed_ok
      hh.rawDealloc)

/-- `<curve25519::PrivateKey>::derive_public_key_bytes` (block `200`) on `initProgPlaced`. -/
theorem derivePubKeyBytes_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (derivePublicKeyBytesSpec W.C.pubKey)) :=
  transfer_plain_block
    (calleeProg := CryptoVerification.lsProg_200 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (derive_public_key_bytes_placed_ok hh.pubFromSecret)

/-- `<HandshakeKeys>::derive` (block `59`) on `initProgPlaced`. -/
theorem handshakeDerive_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (X : UnreachedPqxdhPrimitives) (ha4 : SubsetA4InitCalleesPlaced A mmpl gh W) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 59)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (Pqxdh.Initiator.handshakeKeysDerivePlacedBaseSpec (modelPrims X ⟨W.C, W.Q⟩) A)) :=
  transfer_tr_codeRoLoaded
    (calleeProg := CryptoVerification.lsProg_59 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.Initiator.handshakeKeysDerive_placed_ok
      (Pqxdh.Initiator.structuralPrims_initiatorModelPrims X ⟨W.C, W.Q⟩)
      (ha4.pqxdhHkdfExtract X) (ha4.pqxdhHkdfExpand X))

/-- `<kem::Ciphertext>::serialize` (block `71`) on `initProgPlaced`. -/
theorem kemCtSerialize_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 71)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (Pqxdh.kemCiphertextSerializeSpec A)) :=
  transfer_plain_block
    (calleeProg := CryptoVerification.lsProg_71 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.kemCiphertextSerialize_placed_ok hh.shim hh.rawAlloc hh.framelessMemcpy hh.panic_raw)

/-- `<RootKey>::create_chain` (block `40`) on `initProgPlaced`. -/
theorem rootKeyCreateChain_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A mmpl gh W) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (createChainSpec W.C A)) := by
  have : HkdfPlacedHooks W.C.F (cliGhostExterns gh (cliExternsPlaced mmpl W)) := hh.hkdf
  have hext54_raw :=
    extract_placed_ok_of_inv W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))
      (Inv := CryptoVerification.LibsignalTripleRatchet.LibsignalCodeRoLoaded lsmpl)
      (fun hcro hkf =>
        ⟨fun i hi hunmut ext panics svc =>
          (hcro.1 i hi hunmut ext panics svc).of_keepsFrozen hkf,
         libsignalRoLoaded_of_keepsFrozen hcro.2 hkf⟩)
      (fun hcro => hcro.1)
      ha4.newFromSlice
  have hext54 : subroutine_ok
      (CryptoVerification.LibsignalTripleRatchet.lsProg_54 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 54)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (extractSpec W.C.F)) :=
    subroutine_ok_mono hext54_raw
      (fun _ _ _ hp => by
        dsimp only [CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded] at hp
        rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj] at hp ⊢
        exact hp)
      (fun _ _ _ _ hq => hq)
  have hexp53 : ExpandMultiInfoPlacedOk W.C (cliGhostExterns gh (cliExternsPlaced mmpl W)) :=
    expand_multi_info_placed_ok W.C (cliGhostExterns gh (cliExternsPlaced mmpl W))
  have hext40 : subroutine_ok
      ((CryptoVerification.blkPC_40).rebase
        (CryptoVerification.blkPl_40).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 54)
      (CryptoVerification.LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (extractSpec W.C.F)) :=
    keys_ls_subroutine_ok_of_block_cro
      (calleeProg := CryptoVerification.LibsignalTripleRatchet.lsProg_54 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hext54
  have hexp40 : subroutine_ok
      ((CryptoVerification.blkPC_40).rebase
        (CryptoVerification.blkPl_40).base (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (lsmpl.base 53) (withLsCodeLoaded lsmpl (expandMultiInfoSpec W.C.F)) := by
    have hcl := ls_subroutine_ok_cl_of_block
      (callerProg := CryptoVerification.lsProg_40 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      (calleeProg := CryptoVerification.LibsignalTripleRatchet.lsProg_53 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
      hexp53 (by decide) (by decide) (by decide)
    exact subroutine_ok_mono hcl (fun _ _ _ hp => hp)
      (fun _ _ _ _ hq => by
        dsimp only [withLsCl, withLsCodeLoaded] at hq ⊢
        rw [sepConj_assoc, satisfies_pure_sepConj] at hq
        exact hq.2)
  exact transfer_tr_codeRoLoaded
    (calleeProg := CryptoVerification.lsProg_40 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Keys.createChain_placed_ok_of_contracts
      (keys_ls_subroutine_ok_of_block_cro
        (Keys.calculateAgreement_placed_ok hh.dh hh.sharedDrop ha4.ctEqSliceRO hh.shim hh.rawAlloc
          hh.staticDrop hh.panic_alloc))
      hext40
      (CryptoVerification.LibsignalTripleRatchet.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hexp40)
      (keys_ls_hook_ok_of_mem hh.rawDealloc))

/-- `spqr_chain_params` (block `74`) on `initProgPlaced`. -/
theorem spqrChainParams_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 74)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl Pqxdh.spqrChainParamsSpec) :=
  transfer_plain_block
    (calleeProg := CryptoVerification.lsProg_74 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.spqrChainParams_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- `<SessionState>::new` (block `37`) on `initProgPlaced`. -/
theorem sessionStateNew_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 37)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (Pqxdh.Initiator.sessionStateNewPlacedSpec A)) :=
  transfer_tr_codeLoaded
    (calleeProg := Pqxdh.Initiator.lsProg_37 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.Initiator.sessionStateNew_placed_ok hh.shim hh.rawAlloc hh.panic_raw)

/-- `<SessionState>::with_receiver_chain` (block `30`) on `initProgPlaced`. -/
theorem withReceiverChain_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 30)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (Pqxdh.Initiator.withReceiverChainEmptyPlacedSpec A)) :=
  transfer_tr_codeLoaded
    (calleeProg := Pqxdh.Initiator.lsProg_30 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.Initiator.withReceiverChain_empty_placed_ok hh.shim hh.rawAlloc hh.rawDealloc
      hh.sessionMemcpyRegion hh.panic_raw)

/-- `<SessionState>::with_sender_chain` (block `27`) on `initProgPlaced`. -/
theorem withSenderChain_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 27)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        (Pqxdh.Initiator.withSenderChainNonePlacedSpec A)) :=
  transfer_tr_codeLoaded
    (calleeProg := Pqxdh.Initiator.lsProg_27 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.Initiator.withSenderChain_none_placed_ok hh.shim hh.rawAlloc hh.rawDealloc
      hh.sessionMemcpyRegion hh.panic_raw)

/-- `<SessionState>::set_kyber_ciphertext` (block `31`) on `initProgPlaced`. -/
theorem setKyberCiphertext_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 31)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl Pqxdh.setKyberCiphertextNoneSpec) :=
  transfer_plain_block
    (calleeProg := CryptoVerification.lsProg_31 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.setKyberCiphertext_none_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- `<SessionState>::set_unacknowledged_kyber_pre_key_id` (block `34`) on `initProgPlaced`. -/
theorem setUnackKyberId_cli_placed_ok [LibsignalPlacement] (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 34)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl Pqxdh.setUnackKyberPreKeyIdSpec) :=
  transfer_plain_block
    (calleeProg := CryptoVerification.lsProg_34 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.setUnackKyberPreKeyId_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)))

/-- `<SessionRecord>::promote_state` (block `47`) on `initProgPlaced`. -/
theorem promoteState_cli_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W))) :
    subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
      (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
        Pqxdh.ResponderStore.promoteStateEmptySpec) :=
  transfer_tr_codeLoaded
    (calleeProg := CryptoVerification.lsProg_47 (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (Pqxdh.ResponderStore.promote_state_empty_placed_ok (cliGhostExterns gh (cliExternsPlaced mmpl W)) hh.framelessMemcpy)

/-! ## Bundled local and E2E callees (`InitLocalCalleesPlaced`) -/

/-- Relocatable bundle of all 18 local, PQXDH, TripleRatchet, and SPQR callees on `initProgPlaced`. -/
structure InitLocalCalleesPlaced [LibsignalPlacement] (A : RustAlloc) (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (stk : Nat) : Prop where
  kemPubSerialize : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 523)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (kemPubSerializeInnerSpec A (stk - cliInitiateFrame)))
  dropSessionStructure : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 512)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (FromRecordCallees.dropSessionStructureLocal2Spec A))
  verifySignature : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 203)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (verifySignatureInnerSpec (modelPrims X ⟨W.C, W.Q⟩)))
  isSameAccount : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 17)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (Pqxdh.WireEntries.isSameAccountDistinctSpec A uuidTryParse))
  calculateAgreement : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 207)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (pqxdhCalculateAgreementPlacedInnerSpec (modelPrims X ⟨W.C, W.Q⟩) A))
  derivePubKeyBytes : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 200)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (derivePublicKeyBytesSpec W.C.pubKey))
  handshakeDerive : ∀ (X : UnreachedPqxdhPrimitives), subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 59)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (Pqxdh.Initiator.handshakeKeysDerivePlacedBaseSpec (modelPrims X ⟨W.C, W.Q⟩) A))
  kemCtSerialize : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 71)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (Pqxdh.kemCiphertextSerializeSpec A))
  rootKeyCreateChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 40)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (createChainSpec W.C A))
  spqrChainParams : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 74)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl Pqxdh.spqrChainParamsSpec)
  spqrInitialState : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 327)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (spqrInitialStateInnerSpec A W.C.F))
  sessionStateNew : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 37)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (Pqxdh.Initiator.sessionStateNewPlacedSpec A))
  withReceiverChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 30)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (Pqxdh.Initiator.withReceiverChainEmptyPlacedSpec A))
  withSenderChain : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 27)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      (Pqxdh.Initiator.withSenderChainNonePlacedSpec A))
  setKyberCiphertext : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 31)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl Pqxdh.setKyberCiphertextNoneSpec)
  setUnackPreKeyMsg : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 33)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl (setUnackPreKeyMsgEpochInnerSpec A))
  setUnackKyberId : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 34)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl Pqxdh.setUnackKyberPreKeyIdSpec)
  promoteState : subroutine_ok (initProgPlaced mmpl gh W) (lsmpl.base 47)
    (LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
      Pqxdh.ResponderStore.promoteStateEmptySpec)

/-- Assembles `InitLocalCalleesPlaced` on `initProgPlaced` from `RunHooksPlaced` and `SubsetA4InitCalleesPlaced`. -/
theorem initLocalCallees_placed_ok [LibsignalPlacement] {A : RustAlloc} (mmpl : MultiPlacement) (gh : CliGhostHooks) (W : CliHooks)
    (B : RunBudgets)
    (hh : RunHooksPlaced W A (cliGhostExterns gh (cliExternsPlaced mmpl W)))
    (ha4 : SubsetA4InitCalleesPlaced A mmpl gh W)
    (stk : Nat) (hstk : cliInitiateNeed B ≤ stk) (_hstk64 : stk ≤ 2 ^ 63) :
    InitLocalCalleesPlaced A mmpl gh W stk := by
  exact
    { kemPubSerialize := kemPublicKeySerialize_local2_placed_ok mmpl gh W hh (by
        have h1 := stk_sub_ge_base hstk
        have hext : extHookStack ≤ 65536 := by decide
        omega)
      dropSessionStructure := dropSessionStructure_cli_placed_ok mmpl gh W hh
      verifySignature := ha4.verifySignature
      isSameAccount := ha4.isSameAccount
      calculateAgreement := ha4.calculateAgreement
      derivePubKeyBytes := derivePubKeyBytes_cli_placed_ok mmpl gh W hh
      handshakeDerive := fun X => handshakeDerive_cli_placed_ok mmpl gh W X ha4
      kemCtSerialize := kemCtSerialize_cli_placed_ok mmpl gh W hh
      rootKeyCreateChain := rootKeyCreateChain_cli_placed_ok mmpl gh W hh ha4
      spqrChainParams := spqrChainParams_cli_placed_ok mmpl gh W
      spqrInitialState := ha4.spqrInitialState
      sessionStateNew := sessionStateNew_cli_placed_ok mmpl gh W hh
      withReceiverChain := withReceiverChain_cli_placed_ok mmpl gh W hh
      withSenderChain := withSenderChain_cli_placed_ok mmpl gh W hh
      setKyberCiphertext := setKyberCiphertext_cli_placed_ok mmpl gh W
      setUnackPreKeyMsg := ha4.setUnackPreKeyMsg
      setUnackKyberId := setUnackKyberId_cli_placed_ok mmpl gh W
      promoteState := promoteState_cli_placed_ok mmpl gh W hh }

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
