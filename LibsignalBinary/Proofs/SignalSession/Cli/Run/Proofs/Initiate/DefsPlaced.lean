/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
public import LibsignalBinary.Proofs.SignalSession.Cli.SpecsPlaced
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.InitiateCodeSym
public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.Defs
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable Shared Definitions and Cut-Point Invariants for `initiate`

Defines `[LibsignalPlacement]` counterparts of `slotFrame`, `initSlotSpec`, program/PC shorthands
on block `521` (`lsProg_521`), `coinsCursorAtPlaced`, and the Stage 1–5 cut-point invariants under
`LibsignalCodeRoLoaded lsmpl`.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose

/-- Relocatable `[LibsignalPlacement]` counterpart of `RunCompose.slotFrame`. -/
def slotFramePlaced [LibsignalPlacement] (A : RustAlloc) (x : SlotCtx) : SepProp :=
  ⌜x.coins.length < 2 ^ 63⌝ ∗
  storesAt A x.stores StoresGhost.opened ∗ protocolAddressAt A x.peer x.peerA ∗
    protocolAddressAt A x.me x.meA ∗ coinsInstalledPlaced x.coinsP x.coins ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗ FromRecordCallees.lsLogOff ∗ A.pool

/-- Relocatable `[LibsignalPlacement]` counterpart of `RunCompose.initSlotSpec` on
`LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl`. -/
def initSlotSpecPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (stk : Nat) :
    Spec InitGhost :=
  LibsignalPublicApi.StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.peerA ∧ s.readReg64 .x1 = x.meA ∧
          s.readReg64 .x2 = x.stores + 0xf0#64 ∧ s.readReg64 .x3 = lsρ cliSessionVtSym ∧
          s.readReg64 .x4 = x.stores ∧ s.readReg64 .x5 = lsρ cliIdentityVtSym ∧
          s.readReg64 .x6 = x.bundleA ∧ s.readReg64 .x7 = 0#64 ∧
          s.readReg64 .x8 = x.ret ∧ s.fs.files = x.F ∧
          S.filesOk x.F x.peer.val x.me.val ∧ S.initOk x.F x.peer.val x.me.val ∧
          stk ≤ s.sp.toNat⌝ ∗
        slotFramePlaced A x.toSlotCtx ∗
        cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
        (s.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗ stackAt s.sp stk
      post := fun x s0 sf =>
        ∃∗ g' : StoresGhost, ∃∗ e : Except (ApiError AddrVal Unit) Unit,
          ⌜slotTrace s0 sf ∧
            slotOut (S.initiate x.F x.peer.val x.me.val x.bundle x.coins) g' e s0 sf⌝ ∗
          storesAt A x.stores g' ∗ initResAt A x.ret e ∗
          protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
          cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
          (s0.sp ↦₃₂ 0#32) ∗ FromRecordCallees.lsLogOff ∗ A.pool ∗
          stackAt s0.sp stk ∗ anyHeap
      onPanic := fun x s0 sf =>
        ⌜S.initiate x.F x.peer.val x.me.val x.bundle x.coins = none ∨ allocFailedIn s0 sf⌝ ∗
          anyHeap }

end CryptoVerification.SignalSession.Cli.RunProofs

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs
open CryptoVerification.CliHandshake.InitiatePlaced
open Arm64.Obj (MultiPlacement)
open LibsignalBinary.Proofs.SignalSession.Cli.AllocGhostLinkTransfer
  (CliGhostHooks cliGhostExterns)

/-! ## Program and symbolic PC definitions -/

/-- Block `521` (`signal_session_handshake::initiate`)'s program at arbitrary `H : LibsignalHooks`. -/
abbrev initProgExtPlaced [LibsignalPlacement] (H : LibsignalHooks) : Program :=
  lsProg_521 H

/-- Block `521` (`signal_session_handshake::initiate`)'s program with
`cliGhostExterns g (cliExternsPlaced mmpl W)` over the 39-row `cliHookTablePlaced mmpl W`. -/
abbrev initProgPlaced [LibsignalPlacement] (mmpl : MultiPlacement) (g : CliGhostHooks)
    (W : CliHooks) : Program :=
  initProgExtPlaced (cliGhostExterns g (cliExternsPlaced mmpl W))

/-- Entry address of Block `521` (`signal_session_handshake::initiate`). -/
abbrev initEntryPlaced [LibsignalPlacement] : BitVec 64 :=
  lsmpl.base 521

/-- Function-relative PC inside Block `521` (`signal_session_handshake::initiate`). -/
abbrev initPcPlaced [LibsignalPlacement] (k : Nat) : BitVec 64 :=
  initEntryPlaced + BitVec.ofNat 64 k

/-! ## Empty-scope `sessDeserializeSpecPlaced` discharge -/

theorem sessDeserialize_false_placed_ok [LibsignalPlacement] {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} :
    subroutine_ok prog entry
      (withLsRoCl lsmpl (sessDeserializeSpecPlaced (fun _ => False) A)) := by
  intro x s0 R _ _ _ hmem
  simp_all [LibsignalPublicApi.StoreKit.withLsCodeRoLoaded, sessDeserializeSpecPlaced]

/-! ## Coin cursor invariant -/

/-- Monotonic cursor view of `Coins.coinsNextPlaced`, `Coins.coinsLeftPlaced`, and `p₀ ↦ₛ coins`. -/
def coinsCursorAtPlaced [LibsignalPlacement] (p₀ : BitVec 64) (coins : List (BitVec 8))
    (pos : Nat) : SepProp :=
  (Coins.coinsNextPlaced ↦₆₄ (p₀ + BitVec.ofNat 64 (min pos coins.length))) ∗
    (Coins.coinsLeftPlaced ↦₆₄ BitVec.ofNat 64 (coins.length - min pos coins.length)) ∗
    (p₀ ↦ₛ coins)

theorem coinsInstalledPlaced_eq_cursorZero [LibsignalPlacement] (p₀ : BitVec 64)
    (coins : List (BitVec 8)) :
    coinsInstalledPlaced p₀ coins = coinsCursorAtPlaced p₀ coins 0 := by
  simp [coinsInstalledPlaced, coinsCursorAtPlaced]

/-! ## Frame layout, exit continuations, and stage cut points -/

/-- Entry state predicate for Block `521` (`signal_session_handshake::initiate`). -/
structure AtInitEntryPlaced [LibsignalPlacement] (x : InitGhost) (s0 : State) : Prop where
  pc : s0.pc = initEntryPlaced
  run : s0.status = .Running
  inv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s0.mem
  spAligned : s0.spAligned = true
  x0 : s0.readReg64 .x0 = x.peerA
  x1 : s0.readReg64 .x1 = x.meA
  x2 : s0.readReg64 .x2 = x.stores + 0xf0#64
  x3 : s0.readReg64 .x3 = lsρ cliSessionVtSym
  x4 : s0.readReg64 .x4 = x.stores
  x5 : s0.readReg64 .x5 = lsρ cliIdentityVtSym
  x6 : s0.readReg64 .x6 = x.bundleA
  x7 : s0.readReg64 .x7 = 0#64
  x8 : s0.readReg64 .x8 = x.ret
  files : s0.fs.files = x.F

/-- Control-state invariant inside Block `521` at relative offset `k`. -/
structure InInitiatePlaced [LibsignalPlacement] (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = initPcPlaced k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8
  files0 : s.fs.files = s0.fs.files
  inv : LibsignalPublicApi.StoreKit.LibsignalCodeRoLoaded lsmpl s.mem
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

/-- Immutable 88-byte argument spill table at `[fsp + 0xd0, fsp + 0x128)` written in BB000. -/
def initArgsAtPlaced [LibsignalPlacement] (fsp : BitVec 64) (x : InitGhost) (s0 : State) : SepProp :=
  ((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
    ((fsp + 0xd8#64) ↦₆₄ x.meA) ∗
    ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
    ((fsp + 0xe8#64) ↦₆₄ lsρ cliSessionVtSym) ∗
    ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
    ((fsp + 0xf8#64) ↦₆₄ lsρ cliIdentityVtSym) ∗
    ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
    ((fsp + 0x108#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (fsp + 0x114#64) 4 ∗
    ((fsp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
    ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64))

/-- Shared postcondition predicate for any completed exit path reaching `lr`. -/
def InitExitPostPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (x : InitGhost)
    (stk : Nat) (s0 : State) : State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (Pf ⊢ (initSlotSpecPlaced A S stk).post x s0 sf)

/-- Shared panic predicate matching `initSlotSpecPlaced`. -/
def InitPanicPostPlaced [LibsignalPlacement] (A : RustAlloc) (S : RunSem) (x : InitGhost)
    (stk : Nat) (s0 : State) : State → SepProp → Prop :=
  fun sf Pf => Pf ⊢ (initSlotSpecPlaced A S stk).onPanic x s0 sf

/-- Cut 1 (`BB038`, offset `0x0390`). -/
structure AtStage2Placed [LibsignalPlacement] (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (s0 s : State) : Prop where
  ctrl : InInitiatePlaced s0 s 0x0390
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  signaturesVerify : PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true
  x22 : s.readReg64 (.gpr 22#5) = 0#64
  x23 : s.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64
  x25 : s.readReg64 (.gpr 25#5) = 0xFFFFFFFFFFFFFFFF#64
  x26 : s.readReg64 (.gpr 26#5) = 8#64
  x27 : s.readReg64 (.gpr 27#5) = 0#64

def stage2MemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 0 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAtPlaced fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Cut 2 (`BB064b`, offset `0x0760`). -/
structure AtStage3Placed [LibsignalPlacement] (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiatePlaced s0 s 0x0760
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  signaturesVerify : PreKeyBundleFields.signaturesVerify X ⟨W.C, W.Q⟩ be = true
  kpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp
  ekPairEq :
    let ekKP := keyPairOf W.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList
  opkIdEq : ∀ p, x.bundle.opk = some p → opkId = p.1
  pqspkNonNull : pqspkPtr ≠ 0#64
  x20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64
  x21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64
  x22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64
  x23 : s.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64
  x24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64

def stage3MemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 32 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Cut 3 (`BB129`, offset `0x10a4`). -/
structure AtStage4Placed [LibsignalPlacement] (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (kemCtBytes hkSlotBytes : List (BitVec 8))
    (pqspkPtr kemCtPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiatePlaced s0 s 0x10a4
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  kpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp
  ekPairEq :
    let ekKP := keyPairOf W.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList
  opkIdEq : ∀ p, x.bundle.opk = some p → opkId = p.1
  keysOk : SignalPqxdh.Model.initiateKeys (modelPrims X ⟨W.C, W.Q⟩)
    (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr)
  kemCtEq : kemCtBytes = 0x08#8 :: ofU8 hdr.kemCt
  hkSlotEq : hkSlotBytes = ofU8 (dk.rootKey ++ dk.pqrKey ++ dk.chainKey ++ [0, 0, 0, 0])
  pqspkNonNull : pqspkPtr ≠ 0#64
  kemCtNonNull : kemCtPtr ≠ 0#64
  x20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64
  x21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64
  x22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64

def stage4MemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk kemCtBytes hkSlotBytes : List (BitVec 8))
    (pqspkPtr kemCtPtr : BitVec 64) (opkId : BitVec 32)
    (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  ⌜kemCtBytes.length = 1569 ∧ hkSlotBytes.length = 100⌝ ∗
    storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 160 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0x60 ∗
    ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
    A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ kemCtBytes) ∗
    ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
    ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗
    ((fsp + 0x930#64) ↦ₛ hkSlotBytes) ∗
    memRegion (fsp + 0x994#64) (initLocalsSize - 0x994) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Cut 4 (`BB143`, offset `0x1484`). -/
structure AtStage5Placed [LibsignalPlacement] (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiatePlaced s0 s 0x1484
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  kpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp
  ekPairEq :
    let ekKP := keyPairOf W.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList
  opkIdEq : ∀ p, x.bundle.opk = some p → opkId = p.1
  keysOk : SignalPqxdh.Model.initiateKeys (modelPrims X ⟨W.C, W.Q⟩)
    (initiateInput ⟨W.C, W.Q⟩ ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr)
  initSessOk : initializeInitiatorSession W.C (pqxdhSpqrSession ⟨W.C, W.Q⟩)
    ⟨(keyPairOf W.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
    (HKDF.bytesToKey32 (ofU8 dk.rootKey)) (HKDF.bytesToKey32 (ofU8 dk.chainKey))
    (HKDF.bytesToKey32 (ofU8 dk.pqrKey))
    (HKDF.bytesToKey32 (((padCoins x.coins).toList.drop 160).take 32)) = .ok ss
  pqLen : ss.pqRatchetState.length ≤ 1208
  canonPre :
    sg.localIk.bytes = ss.localIdentity.serialize ∧
    (match ss.remoteIdentity with
     | none => sg.remoteIk.bytes = []
     | some ik => sg.remoteIk.bytes = ik.serialize) ∧
    sg.alice.bytes = (PublicKey.mk (u8Vec 32 hdr.ekAPk)).serialize ∧
    sg.pending = none ∧
    (∃ kg, sg.kyber = some kg ∧ kg.vec.bytes = 0x08#8 :: ofU8 hdr.kemCt) ∧
    (∃ scg sc, sg.sender = some scg ∧ ss.senderChain = some sc ∧
      scg.srk.bytes = sc.ratchetKey.publicKey.serialize ∧
      scg.priv.bytes = sc.ratchetKey.privateKey.bytes.toList) ∧
    ∀ gc ∈ sg.chains.zip ss.receiverChains,
      gc.1.srk.bytes = gc.2.senderRatchetKey.serialize ∧ gc.1.priv.bytes = []
  pqspkNonNull : pqspkPtr ≠ 0#64
  x20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x460#64

def stage5MemPlaced [LibsignalPlacement] (A : RustAlloc) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAtPlaced x.coinsP x.coins 192 ∗
    SpqrV1.GF.Mul2U16.tokenInitPlacedAt ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    FromRecordCallees.lsLogOff ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗
    initArgsAtPlaced fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    sessionStateAt A (fsp + 0x460#64) sg ss ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
