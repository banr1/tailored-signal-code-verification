/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.SpecDefs
public import LibsignalBinary.Proofs.SignalSession.Cli.StoreSpecs.Session
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.Address.Loop
import LibsignalBinary.Proofs.SignalSession.Cli.Main.Proofs.KeepsFs

/-!
# Shared Definitions and Cut-Point Invariants for `signal_session_handshake::initiate`

Defines program/PC shorthands (`initProg`, `initProgExt`), stack-budget bounds, empty-scope
`SessionRecord::deserialize` discharge, accepted-call `StoresGhost` updates, the monotonic coin
cursor `coinsCursorAt`, and CFG cut-point invariants (`AtInitEntry`, `AtStage2`..`AtStage5`, and
their `*Ext` counterparts).
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError false

noncomputable section

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate

open Arm64 Arm64.Process ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.SignalSession CryptoVerification.SignalSession.Cli
open CryptoVerification.SignalSession.Cli.MainHops
open CryptoVerification.SignalSession.Cli.RunSkeleton
open CryptoVerification.SignalSession.Cli.RunCompose
open CryptoVerification.SignalSession.Cli.RunProofs

/-! ## Program and symbolic PC definitions -/

/-- The linked CLI program at `img.base` with `cliExterns W`. -/
abbrev initProg (img : Obj.Image) (W : CliHooks) : Program :=
  tripleRatchetProgAtExt img.base (cliExterns W)

/-- Entry address of `signal_session_handshake::initiate`. -/
abbrev initEntry (img : Obj.Image) (W : CliHooks) : BitVec 64 :=
  (initProg img W).fnAddr cliInitiateName

/-- Function-relative PC inside `signal_session_handshake::initiate`. -/
abbrev initPc (img : Obj.Image) (W : CliHooks) (k : Nat) : BitVec 64 :=
  initEntry img W + BitVec.ofNat 64 k

/-- Shared OOM postcondition matching `(initSlotSpec A img S stk).onOom`. -/
def initOom (_s0 : State) : State → SepProp :=
  fun _ => ⌜False⌝

/-- Size of `initiate`'s local stack area `[fsp, s0.sp - 0x60)`: `0x1000 + 0xc90 = 7312` bytes. -/
abbrev initLocalsSize : Nat := 0x1000 + 0xc90

/-! ## Stack budget arithmetic -/

theorem cliInitiateFrame_eq : cliInitiateFrame = 7408 := rfl

theorem initLocalsSize_add_saved : initLocalsSize + 0x60 = cliInitiateFrame := rfl

theorem cliInitiateFrame_dvd16 : 16 ∣ cliInitiateFrame := by decide

theorem stk_ge_frame {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    cliInitiateFrame ≤ stk := by
  unfold cliInitiateNeed at hstk
  unfold cliInitiateFrame at hstk ⊢
  omega

theorem stk_sub_ge_base {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    516880 ≤ stk - cliInitiateFrame := by
  unfold cliInitiateNeed at hstk
  unfold cliInitiateFrame at hstk ⊢
  omega

theorem stk_sub_ge_dirGet {B : RunBudgets} {stk : Nat} (hstk : cliInitiateNeed B ≤ stk) :
    848 + B.dirGetNeed ≤ stk - cliInitiateFrame := by
  unfold cliInitiateNeed at hstk
  unfold cliInitiateFrame at hstk ⊢
  omega

theorem sessLoadPoll_stk_le {B : RunBudgets} {addrStk stk : Nat}
    (haddr : addrStk ≤ 65536) (hstk : cliInitiateNeed B ≤ stk) :
    0x350 + max (max addrStk B.dirGetNeed) (max E2E.Record.recDeserializeStack extHookStack) ≤
      stk - cliInitiateFrame := by
  have h1 := stk_sub_ge_base hstk
  have h2 := stk_sub_ge_dirGet hstk
  have hrec : E2E.Record.recDeserializeStack ≤ 65536 := by decide
  have hext : extHookStack ≤ 65536 := by decide
  omega

/-! ## Empty-scope `SessionRecord::deserialize` discharge -/

theorem sessFileWf_false_of_nil : SessFileWf (fun _ => False) [] :=
  Or.inl rfl

/-- Instantiating `sessLoadPoll_ok_of_deps` at `Scope := fun _ => False` discharges `hDeser`
unconditionally for arbitrary `A : RustAlloc` (since `InitOk₀.noSession` ensures the peer's
session file is `[]`, so `Scope x.r` is `False`). -/
theorem sessDeserialize_false_ok {prog : Program} {entry : BitVec 64}
    {A : RustAlloc} {img : Obj.Image} :
    subroutine_ok prog entry (sessDeserializeSpec (fun _ => False) A img) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 _ _ hmem _ _ => ?_
  simp_all [sessDeserializeSpec]

/-! ## Accepted `StoresGhost` and `cliWrOk` -/

/-- Final `StoresGhost` produced on an accepted `initiate` call. -/
def initAcceptStoresGhost (F : FsFiles) (peer : AddrVal) (idKey : IdentityKey)
    (recBytes : List (BitVec 8)) : StoresGhost :=
  let g := StoresGhost.opened
  { g with
    identity := g.identity.saveUpd cliIo.rd F peer idKey
    sessions := g.sessions.put (addressText peer) recBytes }

theorem initAcceptStoresGhost_writes_cliWrOk {W : PEParams} {F : FsFiles}
    {peer me : AddrVal} (hok : InitOk₀ W F peer me) (idKey : IdentityKey)
    (recBytes : List (BitVec 8)) :
    ∀ pw ∈ (initAcceptStoresGhost F peer idKey recBytes).writes, cliWrOk pw.1 := by
  intro pw hpw
  rw [initAcceptStoresGhost] at hpw
  rw [IdGhost.saveUpd] at hpw
  split at hpw
  · simp only [StoresGhost.writes, StoresGhost.opened, DirGhost.new, DirGhost.put,
      DirGhost.setOrPush, DirGhost.writes, List.map, List.nil_append, List.append_nil,
      List.singleton_append, List.mem_cons, List.not_mem_nil, or_false] at hpw
    rcases hpw with rfl | rfl
    · exact ⟨hok.idPathOk, hok.idPathLt⟩
    · exact ⟨hok.sessPathOk, hok.sessPathLt⟩
  · simp only [StoresGhost.writes, StoresGhost.opened, DirGhost.new, DirGhost.put,
      DirGhost.setOrPush, DirGhost.writes, List.map, List.nil_append, List.append_nil,
      List.mem_singleton] at hpw
    subst hpw
    exact ⟨hok.sessPathOk, hok.sessPathLt⟩

/-! ## Coin cursor invariant -/

/-- Monotonic cursor view of `NEXT.0`, `LEFT.0`, and the leaked coin slice `p₀ ↦ₛ coins`.
Handles both `pos ≤ coins.length` and past-the-end zero-padded draws (`pos > coins.length`). -/
def coinsCursorAt (img : Obj.Image) (p₀ : BitVec 64) (coins : List (BitVec 8))
    (pos : Nat) : SepProp :=
  ((img.base + coinsNextOff) ↦₆₄ (p₀ + BitVec.ofNat 64 (min pos coins.length))) ∗
    ((img.base + coinsLeftOff) ↦₆₄ BitVec.ofNat 64 (coins.length - min pos coins.length)) ∗
    (p₀ ↦ₛ coins)

theorem coinsInstalled_eq_cursorZero (img : Obj.Image) (p₀ : BitVec 64)
    (coins : List (BitVec 8)) :
    coinsInstalled img p₀ coins = coinsCursorAt img p₀ coins 0 := by
  simp [coinsInstalled, coinsCursorAt]

/-! ## Frame layout, exit continuations, and stage cut points -/

/-- Entry state predicate for `signal_session_handshake::initiate`. -/
structure AtInitEntry (img : Obj.Image) (W : CliHooks) (x : InitGhost) (s0 : State) : Prop where
  pc : s0.pc = initEntry img W
  run : s0.status = .Running
  inv : ImgCallInv img s0
  spAligned : s0.spAligned = true
  x0 : s0.readReg64 .x0 = x.peerA
  x1 : s0.readReg64 .x1 = x.meA
  x2 : s0.readReg64 .x2 = x.stores + 0xf0#64
  x3 : s0.readReg64 .x3 = sessVt img
  x4 : s0.readReg64 .x4 = x.stores
  x5 : s0.readReg64 .x5 = idVt img
  x6 : s0.readReg64 .x6 = x.bundleA
  x7 : s0.readReg64 .x7 = 0#64
  x8 : s0.readReg64 .x8 = x.ret
  files : s0.fs.files = x.F

/-- Control-state invariant inside `signal_session_handshake::initiate` at relative offset `k`. -/
structure InInitiate (img : Obj.Image) (W : CliHooks) (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = initPc img W k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8
  /-- Filesystem files remain unchanged in `s.fs.files` (store writes buffer in ghost state). -/
  files0 : s.fs.files = s0.fs.files
  inv : ImgCallInv img s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

/-- The 12 callee-saved words stored by `initiate`'s prologue at `s0.sp - 0x60`. -/
def initSaved (s0 : State) : SepProp :=
  let b := s0.sp - 0x60#64
  let w (k : Nat) (r : Reg) := (b + BitVec.ofNat 64 k) ↦₆₄ s0.readReg64 r
  w 0x00 .fp ∗ w 0x08 .lr ∗ w 0x10 (.gpr 28#5) ∗ w 0x18 (.gpr 27#5) ∗ w 0x20 (.gpr 26#5) ∗
    w 0x28 (.gpr 25#5) ∗ w 0x30 (.gpr 24#5) ∗ w 0x38 (.gpr 23#5) ∗ w 0x40 (.gpr 22#5) ∗
    w 0x48 (.gpr 21#5) ∗ w 0x50 (.gpr 20#5) ∗ w 0x58 (.gpr 19#5)

/-- Immutable 88-byte argument spill table at `[fsp + 0xd0, fsp + 0x128)` written in BB000. -/
def initArgsAt (img : Obj.Image) (fsp : BitVec 64) (x : InitGhost) (s0 : State) : SepProp :=
  ((fsp + 0xd0#64) ↦₆₄ x.peerA) ∗
    ((fsp + 0xd8#64) ↦₆₄ x.meA) ∗
    ((fsp + 0xe0#64) ↦₆₄ (x.stores + 0xf0#64)) ∗
    ((fsp + 0xe8#64) ↦₆₄ sessVt img) ∗
    ((fsp + 0xf0#64) ↦₆₄ x.stores) ∗
    ((fsp + 0xf8#64) ↦₆₄ idVt img) ∗
    ((fsp + 0x100#64) ↦₆₄ x.bundleA) ∗
    ((fsp + 0x108#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (fsp + 0x114#64) 4 ∗
    ((fsp + 0x118#64) ↦₆₄ (s0.sp - 0x71#64)) ∗
    ((fsp + 0x120#64) ↦₆₄ (x.bundleA + 0x78#64))

/-- Empty/fresh `SessionRecord` header at `[fsp + 0x128, fsp + 0x148)` under `InitOk₀.noSession`. -/
def initFreshRecAt (fsp : BitVec 64) : SepProp :=
  ((fsp + 0x128#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x130#64) ↦₆₄ 8#64) ∗
    ((fsp + 0x138#64) ↦₆₄ 0#64) ∗
    ((fsp + 0x140#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64)

/-- Shared postcondition predicate for any completed exit path reaching `lr`. -/
def InitExitPost (A : RustAlloc) (img : Obj.Image) (S : RunSem) (x : InitGhost)
    (stk : Nat) (s0 : State) : State → SepProp → Prop :=
  fun sf Pf =>
    sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf ∧
      (Pf ⊢ (initSlotSpec A img S stk).post x s0 sf)

/-- Shared panic predicate matching `initSlotSpec`. -/
def InitPanicPost (A : RustAlloc) (img : Obj.Image) (S : RunSem) (x : InitGhost)
    (stk : Nat) (s0 : State) : State → SepProp → Prop :=
  fun sf Pf => Pf ⊢ (initSlotSpec A img S stk).onPanic x s0 sf

/-- Cut 1 (`BB038`, offset `0x0390`): `is_trusted_identity`, both XEdDSA signature checks, and
`load_session` (`Ok(None)`) all succeeded; `coins` cursor still at `0`. -/
structure AtStage2 (img : Obj.Image) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (s0 s : State) : Prop where
  ctrl : InInitiate img W s0 s 0x0390
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

def stage2Mem (A : RustAlloc) (img : Obj.Image) (x : InitGhost) (stk : Nat)
    (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAt img x.coinsP x.coins 0 ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    logOff img ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗ initArgsAt img fsp x s0 ∗
    memRegion (fsp + 0x128#64) 0x490 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Cut 2 (`BB064b`, offset `0x0760`): `ekASk` drawn (`pos = 32`), `get_identity_key_pair` read
`kp`, `pqspkB` serialized at `pqspkPtr`, `is_same_account` returned `false`, and optional `opk`
unpacked; about to allocate `secrets` (`192` bytes) and run `DH1..DH4`. -/
structure AtStage3 (img : Obj.Image) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiate img W s0 s 0x0760
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

def stage3KeySlotsAt (A : RustAlloc) (fsp : BitVec 64) (b : BundleV)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32) : SepProp :=
  let opkFlag : BitVec 32 := if b.opk.isSome then 1#32 else 0#32
  ((fsp + 0x298#64) ↦ₛ ekAPk) ∗
    memRegion (fsp + 0x2b8#64) 0x48 ∗
    ((fsp + 0x300#64) ↦₃₂ opkFlag) ∗ ((fsp + 0x304#64) ↦₃₂ opkId) ∗
    memRegion (fsp + 0x308#64) 0x40 ∗
    ((fsp + 0x348#64) ↦ₛ kp.identityKey.publicKey.bytes.toList) ∗
    ((fsp + 0x368#64) ↦ₛ kp.privateKey.bytes.toList) ∗
    ((fsp + 0x388#64) ↦ₛ ekAPk) ∗
    ((fsp + 0x3a8#64) ↦ₛ ekASk) ∗
    ((fsp + 0x3c8#64) ↦ₛ b.idKey.publicKey.bytes.toList) ∗
    ((fsp + 0x3e8#64) ↦ₛ b.spk.bytes.toList) ∗
    ((fsp + 0x408#64) ↦ₛ b.spk.bytes.toList) ∗
    ((fsp + 0x428#64) ↦₆₄ pqspkPtr) ∗ ((fsp + 0x430#64) ↦₆₄ 1568#64) ∗
    A.live pqspkPtr 1568 1 ∗ (pqspkPtr ↦ₛ b.kpk) ∗
    ((fsp + 0x438#64) ↦₈ opkFlag.truncate 8) ∗
    (match b.opk with
     | some (_, k) => (fsp + 0x439#64) ↦ₛ k.bytes.toList
     | none => memRegion (fsp + 0x439#64) 32) ∗
    ((fsp + 0x459#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x45a#64) 6

def stage3Mem (A : RustAlloc) (img : Obj.Image) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAt img x.coinsP x.coins 32 ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    logOff img ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0x78 ∗ ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAt img fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Cut 3 (`BB129`, offset `0x10a4`): `DH1..DH4` succeeded, 32×4 KEM seed coin draws succeeded
(`pos = 160`), `kyber::encapsulate` + `kem::Ciphertext::serialize` produced `kemCtBytes` (`1569` B)
at `kemCtPtr`, `HandshakeKeys::derive` wrote `100` bytes into `[fsp + 0x930, fsp + 0x994)`, and
`secrets` was freed. -/
structure AtStage4 (img : Obj.Image) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (kemCtBytes hkSlotBytes : List (BitVec 8))
    (pqspkPtr kemCtPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiate img W s0 s 0x10a4
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

def stage4Mem (A : RustAlloc) (img : Obj.Image) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk kemCtBytes hkSlotBytes : List (BitVec 8))
    (pqspkPtr kemCtPtr : BitVec 64) (opkId : BitVec 32)
    (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  ⌜kemCtBytes.length = 1569 ∧ hkSlotBytes.length = 100⌝ ∗
    storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAt img x.coinsP x.coins 160 ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    logOff img ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0x60 ∗
    ((fsp + 0x60#64) ↦₆₄ kemCtPtr) ∗ ((fsp + 0x68#64) ↦₆₄ 1569#64) ∗
    A.live kemCtPtr 1569 1 ∗ (kemCtPtr ↦ₛ kemCtBytes) ∗
    ((fsp + 0x70#64) ↦₆₄ (fsp + 0x408#64)) ∗
    ((fsp + 0x78#64) ↦₆₄ (fsp + 0x3c8#64)) ∗
    memRegion (fsp + 0x80#64) 0x50 ∗
    initArgsAt img fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    memRegion (fsp + 0x460#64) 0x158 ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 0#8) ∗
    memRegion (fsp + 0x5ba#64) (0x930 - 0x5ba) ∗
    ((fsp + 0x930#64) ↦ₛ hkSlotBytes) ∗
    memRegion (fsp + 0x994#64) (initLocalsSize - 0x994) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-- Cut 4 (`BB143`, offset `0x1484`): `ephASk` drawn (`pos = 192`), `RootKey::create_chain`,
`spqr_chain_params`, `spqr::initial_state`, `SessionState::{new, with_receiver_chain,
with_sender_chain, set_kyber_ciphertext}` succeeded into `[fsp + 0x460, fsp + 0x5b8)`, and
`logOff img` jumped directly to `BB143` (`x19 = x.ret`, `x20 = fsp + 0x460`). -/
structure AtStage5 (img : Obj.Image) (W : CliHooks) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiate img W s0 s 0x1484
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

def stage5Mem (A : RustAlloc) (img : Obj.Image) (x : InitGhost)
    (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (stk : Nat) (s0 : State) : SepProp :=
  let fsp := s0.sp - BitVec.ofNat 64 cliInitiateFrame
  storesAt A x.stores StoresGhost.opened ∗
    protocolAddressAt A x.peer x.peerA ∗ protocolAddressAt A x.me x.meA ∗
    cliBundleAt x.bundleA x.bundle x.spkSigPtr x.kpkSigPtr x.kpkPtr ∗
    coinsCursorAt img x.coinsP x.coins 192 ∗
    CryptoVerification.LibsignalSpqrV1.TokenInit img ∗
    (s0.sp ↦₃₂ 0#32) ∗ memRegion x.ret 48 ∗
    logOff img ∗ A.pool ∗ initSaved s0 ∗
    memRegion fsp 0xd0 ∗
    initArgsAt img fsp x s0 ∗
    initFreshRecAt fsp ∗
    memRegion (fsp + 0x148#64) 0x150 ∗
    stage3KeySlotsAt A fsp x.bundle kp ekASk ekAPk pqspkPtr opkId ∗
    sessionStateAt A (fsp + 0x460#64) sg ss ∗
    ((fsp + 0x5b8#64) ↦₈ 0#8) ∗ ((fsp + 0x5b9#64) ↦₈ 1#8) ∗
    memRegion (fsp + 0x5ba#64) (initLocalsSize - 0x5ba) ∗
    stackAt fsp (stk - cliInitiateFrame)

/-! ## Extern-parameterized program, hook lifting, and stage cut points (`*Ext`) -/

/-- Parameterized CLI program at `img.base` with `cliExternsWith ext`. -/
abbrev initProgExt (img : Obj.Image) (ext : String → Option (State → State)) : Program :=
  tripleRatchetProgAtExt img.base (cliExternsWith ext)

/-- Entry address of `signal_session_handshake::initiate` on `initProgExt img ext`. -/
abbrev initEntryExt (img : Obj.Image) (ext : String → Option (State → State)) : BitVec 64 :=
  (initProgExt img ext).fnAddr cliInitiateName

/-- Function-relative PC inside `signal_session_handshake::initiate` on `initProgExt img ext`. -/
abbrev initPcExt (img : Obj.Image) (ext : String → Option (State → State)) (k : Nat) : BitVec 64 :=
  initEntryExt img ext + BitVec.ofNat 64 k

theorem initProgExt_cliHookExterns (img : Obj.Image) (W : CliHooks) :
    initProgExt img (cliHookExterns W) = initProg img W :=
  rfl

theorem initEntryExt_cliHookExterns (img : Obj.Image) (W : CliHooks) :
    initEntryExt img (cliHookExterns W) = initEntry img W :=
  rfl

theorem initPcExt_cliHookExterns (img : Obj.Image) (W : CliHooks) (k : Nat) :
    initPcExt img (cliHookExterns W) k = initPc img W k :=
  rfl

/-- `Rust.withPanics` is idempotent on `cliExternsWith ext` because `isCliPanicSymbol`
subsumes `Rust.isPanicSymbol`. -/
theorem withPanics_cliExternsWith (ext : String → Option (State → State)) :
    Rust.withPanics (cliExternsWith ext) = cliExternsWith ext :=
  withPanics_withCliPanics ext

/-- Any non-panic symbol's `HookSat` contract on `ext` lifts unchanged to `cliExternsWith ext`. -/
theorem hookSat_cliExternsWith {α : Type} {ext : String → Option (State → State)}
    {name : String} {spec : Spec α}
    (hnp : E2E.isImagePanicSymbol name = false)
    (h : HookSat ext name spec) :
    HookSat (cliExternsWith ext) name spec := by
  simp only [HookSat, cliExternsWith, withCliPanics_of_isImagePanicSymbol_false _ hnp]
  exact h

/-- Any `HookSat ext name spec` on a non-panic symbol gives `subroutine_ok` at the stub's entry
on `initProgExt img ext`. -/
theorem ext_stub_ok {α : Type} (img : Obj.Image) {ext : String → Option (State → State)}
    {name : String} {spec : Spec α} {stub : Nat}
    (hfn : libsignalSessionCode.fnOff name = stub) (hs : stub < 2 ^ 64)
    (hstub : ∀ H, (libsignalSessionCode.rebase 0 H).hookAtOff? stub = H name)
    (hnp : E2E.isImagePanicSymbol name = false)
    (hsat : HookSat ext name spec) :
    subroutine_ok (initProgExt img ext) ((initProgExt img ext).fnAddr name) spec := by
  have hnpR : Rust.isPanicSymbol name = false := by
    cases h : Rust.isPanicSymbol name
    · rfl
    · simp [E2E.isImagePanicSymbol, h] at hnp
  have h1 := hook_ok_at (P := libsignalSessionCode) (b := img.base) (hooks := cliExternsWith ext)
    (hname := name) (k := 0) hfn (Nat.add_zero _) hs hstub hnpR
    (hookSat_cliExternsWith hnp hsat)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h1

/-- Any `HookSat ext name spec` on a non-I/O symbol under `CliExternsOk` lifts to `spec.keepsFs`. -/
theorem hookSat_keepsFs_of_ok {α : Type} {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} {name : String} {spec : Spec α}
    (hOk : CliExternsOk P A ext) (hnio : name ∉ CliExt.ioNames)
    (hsat : HookSat ext name spec) :
    HookSat ext name spec.keepsFs := by
  rcases hsat with ⟨f, hf, hok⟩
  exact ⟨f, hf, hok.keepsFs (hOk.fsKept name f hf hnio)⟩

/-- Filesystem preservation on `ext` lifts to `cliExternsWith ext` (`Rust.panicked` preserves `fs`). -/
theorem fsKept_cliExternsWith {ext : String → Option (State → State)} {name : String}
    (h : ∀ f, ext name = some f → ∀ s, (f s).fs = s.fs) :
    ∀ f, cliExternsWith ext name = some f → ∀ s, (f s).fs = s.fs := by
  intro f hf s
  simp only [cliExternsWith, withCliPanics] at hf
  cases hpan : isCliPanicSymbol name
  · rw [hpan] at hf
    exact h f hf s
  · rw [hpan] at hf
    cases hf
    rfl

private theorem quietEv_false_of_isFsChange (e : TraceEvent)
    (h : e.isFsChange = true) : ¬ QuietEv e := by
  cases e with
  | writeByte st _ => cases st <;> simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢
  | _ => simp [TraceEvent.isFsChange, QuietEv, quietEv] at h ⊢

private theorem hookFsTraced_panicked :
    HookFsTraced (fun e => e.isFsChange = true) Rust.panicked := by
  intro s
  exact ⟨[], by simp [Rust.panicked], fun _ => rfl⟩

private theorem externAt_fsTraced_local {prog : Program}
    (hX : ∀ n f, prog.externs n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    (hO : ∀ n f, prog.overrides n = some f → HookFsTraced (fun e => e.isFsChange = true) f)
    {pc : BitVec 64} {f : State → State} (h : prog.externAt? pc = some f) :
    HookFsTraced (fun e => e.isFsChange = true) f := by
  unfold Program.externAt? Program.hookAtOff? at h
  rcases Option.or_eq_some_iff.mp h with h | ⟨_, h⟩
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hX n f hno
    · cases hno
  · obtain ⟨⟨n, o⟩, _, hno⟩ := List.exists_of_findSome?_eq_some h
    dsimp only at hno
    split at hno
    · exact hO n f hno
    · cases hno

/-- `TraceFsSound` for `initProgExt img ext` directly from `CliExternsOk.fsTraced`. -/
theorem initProgExt_traceFsSound {P : PEParams} {A : RustAlloc}
    {ext : String → Option (State → State)} (img : Obj.Image)
    (hOk : CliExternsOk P A ext) :
    TraceFsSound (initProgExt img ext) := by
  refine TraceFsSound.of_isFs quietEv_false_of_isFsChange fun s s' hst => ?_
  refine hst.files_eq_of_noFs (fun _ h => h)
    (fun _ _ h => externAt_fsTraced_local ?_ (fun _ _ hn => by change none = some _ at hn; cases hn) h) rfl
  intro name f hf
  change (Rust.withPanics (cliExternsWith ext)) name = some f at hf
  rw [withPanics_cliExternsWith] at hf
  simp only [cliExternsWith, withCliPanics] at hf
  cases hpan : isCliPanicSymbol name
  · rw [hpan] at hf
    exact hOk.fsTraced name f hf
  · rw [hpan] at hf
    cases hf
    exact hookFsTraced_panicked

theorem idTrustPoll_eqStk_fits :
    192 + (64 + extHookStack) ≤ 516880 := by
  dsimp only [extHookStack]; decide

theorem idSavePoll_eqStk_fits :
    432 + (64 + extHookStack) ≤ 516880 := by
  dsimp only [extHookStack]; decide

theorem isSameAccount_eqStk_fits :
    208 + (64 + extHookStack) ≤ 516880 := by
  dsimp only [extHookStack]; decide

/-- Contract-parameterized entry state predicate for `signal_session_handshake::initiate`. -/
structure AtInitEntryExt (img : Obj.Image) (ext : String → Option (State → State))
    (x : InitGhost) (s0 : State) : Prop where
  pc : s0.pc = initEntryExt img ext
  run : s0.status = .Running
  inv : ImgCallInv img s0
  spAligned : s0.spAligned = true
  x0 : s0.readReg64 .x0 = x.peerA
  x1 : s0.readReg64 .x1 = x.meA
  x2 : s0.readReg64 .x2 = x.stores + 0xf0#64
  x3 : s0.readReg64 .x3 = sessVt img
  x4 : s0.readReg64 .x4 = x.stores
  x5 : s0.readReg64 .x5 = idVt img
  x6 : s0.readReg64 .x6 = x.bundleA
  x7 : s0.readReg64 .x7 = 0#64
  x8 : s0.readReg64 .x8 = x.ret
  files : s0.fs.files = x.F

/-- Contract-parameterized control-state invariant inside `signal_session_handshake::initiate`
at relative offset `k`. -/
structure InInitiateExt (img : Obj.Image) (ext : String → Option (State → State))
    (s0 s : State) (k : Nat) : Prop where
  pc : s.pc = initPcExt img ext k
  run : s.status = .Running
  sp : s.sp = s0.sp - BitVec.ofNat 64 cliInitiateFrame
  fp : s.readReg64 .fp = s0.sp - 0x60#64
  x19 : s.readReg64 (.gpr 19#5) = s0.readReg64 .x8
  files0 : s.fs.files = s0.fs.files
  inv : ImgCallInv img s
  vregs : calleeSavedVRegs s = calleeSavedVRegs s0
  spAligned : s0.spAligned = true

/-- Contract-parameterized Cut 1 (`BB038`, offset `0x0390`). -/
structure AtStage2Ext (img : Obj.Image) (P : PEParams)
    (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (s0 s : State) : Prop where
  ctrl : InInitiateExt img ext s0 s 0x0390
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  signaturesVerify : PreKeyBundleFields.signaturesVerify X P be = true
  x22 : s.readReg64 (.gpr 22#5) = 0#64
  x23 : s.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64
  x25 : s.readReg64 (.gpr 25#5) = 0xFFFFFFFFFFFFFFFF#64
  x26 : s.readReg64 (.gpr 26#5) = 8#64
  x27 : s.readReg64 (.gpr 27#5) = 0#64

/-- Contract-parameterized Cut 2 (`BB064b`, offset `0x0760`). -/
structure AtStage3Ext (img : Obj.Image) (P : PEParams)
    (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiateExt img ext s0 s 0x0760
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  signaturesVerify : PreKeyBundleFields.signaturesVerify X P be = true
  kpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp
  ekPairEq :
    let ekKP := keyPairOf P.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList
  opkIdEq : ∀ p, x.bundle.opk = some p → opkId = p.1
  pqspkNonNull : pqspkPtr ≠ 0#64
  x20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64
  x21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64
  x22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x408#64
  x23 : s.readReg64 (.gpr 23#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x80#64
  x24 : s.readReg64 (.gpr 24#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x3e8#64

/-- Contract-parameterized Cut 3 (`BB129`, offset `0x10a4`). -/
structure AtStage4Ext (img : Obj.Image) (P : PEParams)
    (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (kemCtBytes hkSlotBytes : List (BitVec 8))
    (pqspkPtr kemCtPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiateExt img ext s0 s 0x10a4
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  kpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp
  ekPairEq :
    let ekKP := keyPairOf P.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList
  opkIdEq : ∀ p, x.bundle.opk = some p → opkId = p.1
  keysOk : SignalPqxdh.Model.initiateKeys (modelPrims X P)
    (initiateInput P ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr)
  kemCtEq : kemCtBytes = 0x08#8 :: ofU8 hdr.kemCt
  hkSlotEq : hkSlotBytes = ofU8 (dk.rootKey ++ dk.pqrKey ++ dk.chainKey ++ [0, 0, 0, 0])
  pqspkNonNull : pqspkPtr ≠ 0#64
  kemCtNonNull : kemCtPtr ≠ 0#64
  x20 : s.readReg64 (.gpr 20#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x348#64
  x21 : s.readReg64 (.gpr 21#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x388#64
  x22 : s.readReg64 (.gpr 22#5) = (s0.sp - BitVec.ofNat 64 cliInitiateFrame) + 0x900#64

/-- Contract-parameterized Cut 4 (`BB143`, offset `0x1484`). -/
structure AtStage5Ext (img : Obj.Image) (P : PEParams)
    (ext : String → Option (State → State)) (X : UnreachedPqxdhPrimitives) (x : InitGhost)
    (be : PreKeyBundleFields) (kp : CryptoVerification.RecordCodecs.IdentityKeyPair)
    (ekASk ekAPk : List (BitVec 8)) (dk : SignalPqxdh.DRKey) (hdr : SignalPqxdh.HandshakeHdr)
    (sg : SessionGhost) (ss : SessionState (List (BitVec 8)))
    (pqspkPtr : BitVec 64) (opkId : BitVec 32)
    (s0 s : State) : Prop where
  ctrl : InInitiateExt img ext s0 s 0x1484
  trace : s.trace = s0.trace
  files : s.fs.files = x.F
  x8 : s0.readReg64 .x8 = x.ret
  bundleEq : bundleEOf? x.bundle = some be
  trustedOk : StoresGhost.opened.identity.trusted cliIo.rd x.F x.peer.val x.bundle.idKey = .ok true
  kpOk : StoresGhost.opened.identity.keyPair cliIo.rd x.F = .ok kp
  ekPairEq :
    let ekKP := keyPairOf P.C ⟨(padCoins x.coins).toList.take 32, by simp; decide⟩
    ekASk = ekKP.privateKey.bytes.toList ∧ ekAPk = ekKP.publicKey.bytes.toList
  opkIdEq : ∀ p, x.bundle.opk = some p → opkId = p.1
  keysOk : SignalPqxdh.Model.initiateKeys (modelPrims X P)
    (initiateInput P ⟨kp.privateKey.bytes, 0#32⟩ be (padCoins x.coins)) = some (dk, hdr)
  initSessOk : initializeInitiatorSession P.C (pqxdhSpqrSession P)
    ⟨(keyPairOf P.C kp.privateKey.bytes).publicKey⟩ ⟨⟨be.idPub⟩⟩ ⟨be.spkPub⟩
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

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate
