/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Defs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageDecrypt.RatchetDecryptCodeSym
public import LibsignalBinary.Proofs.Cli.TripleRatchet.CliRatchetCodeSymA
public import LibsignalBinary.Proofs.Cli.PublicApi.StoreSession.CoinsTapePlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.Record.DefsPlaced
public import LibsignalBinary.Proofs.Cli.TripleRatchet.FromRecordCallees.DropsPlaced
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic

/-!
# Relocatable CLI `MessageDecrypt` Seam States and Segment Specifications

Relocatable (`[LibsignalPlacement]`) seam program counters, intermediate states, callee contracts,
and twelve-segment specifications for `session_message_decrypt_signal_with_stores` on `lsProg_463`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoVerification.CliRatchet.DecPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64
open ProofLib
open CryptoVerification.RustHeap
open CryptoGames.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalSession
open CryptoGames
open CryptoGames.LibsignalSessionApi
open CryptoVerification.LibsignalPublicApi.StoreSession
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt hiding lsStringCloneSym lsExpectFailedSym wsEntryPCPlaced loadPolledPCPlaced keyReadyPCPlaced saveCallPCPlaced untrustedPCPlaced trustedPCPlaced storeCallPCPlaced errJoinPCPlaced resultFinalPCPlaced decStoreExtraPlaced wsStack_split_extra_placed wsStack_join_extra_placed wsCalleeStack_join_extra_placed wsCalleeStack_split_extra_placed wsMetaPlaced wsFixedVPlaced wsEnvPlaced satisfies_decVtablesAtV_placed LoadPolledStateVPlaced wsRegionFrameVPlaced RegionSomeStateVPlaced regionNonePrePlaced RegionNoneStateVPlaced PostSomeStateVPlaced PostNoneStateVPlaced KeyReadyStateVPlaced TrustedStateVPlaced StoreCallStateVPlaced ErrJoinStateVPlaced ResultFinalStateVPlaced withStoresDecPlacedSpecV withStoresDecPlacedSpecV_pre_addrOk DecSegVPlaced PublicApiDecHooksPlaced DecHypsVPlaced DecFsCtxPlaced RemoteIdentityKeyPlacedOk DropSessionStructureLocal2PlacedOk SegLoadSpecVPlaced SegDispatchSpecVPlaced SegRegionSomeSpecVPlaced SegRegionNoneSpecVPlaced SegPostSomeSpecVPlaced SegPostNoneSpecVPlaced SegTrustSpecVPlaced SegUntrustedSpecVPlaced SegSaveSpecVPlaced SegStoreSpecVPlaced SegErrTeardownSpecVPlaced SegWriteSpecVPlaced

set_option maxRecDepth 200000
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
theorem lsProg_463_eq_record_lsProg_463 [LibsignalPlacement] (H : LibsignalHooks) :
    lsProg_463 H = CryptoVerification.Cli.LibsignalTripleRatchet.Record.lsProg_463 H := rfl

theorem ls_hook_ok_463 [LibsignalPlacement] {α : Type} {H : LibsignalHooks} {sym : String}
    {spec : Spec α} (hmem : sym ∈ libsignalSessionExterns := by decide)
    (h : HookSat H sym spec) :
    subroutine_ok (lsProg_463 H) (lsmpl.ρ sym) spec := by
  obtain ⟨k, hlt, hk⟩ := List.getElem_of_mem hmem
  exact ls_hook_ok (k := k) (by rw [List.getElem?_eq_getElem hlt, hk]) h


/-- Mangled ELF symbol for `<alloc::string::String as core::clone::Clone>::clone`. -/
abbrev lsStringCloneSym : String :=
  "_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"

/-- Mangled ELF symbol for `core::option::expect_failed`. -/
abbrev lsExpectFailedSym : String :=
  "_RNvNtCskxtBwYRO61I_4core6option13expect_failed"

/-- Entry PC `(blkPl_463).base` (`+0x0`). -/
abbrev wsEntryPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base

/-- Seam PC `+0x8c` after the `load_session` poll returns. -/
abbrev loadPolledPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 140#64

/-- Seam PC `+0x1fcc` before `is_trusted_identity`. -/
abbrev keyReadyPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 8140#64

/-- Seam PC `+0x2150` at the `save_identity` shim call. -/
abbrev saveCallPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 8528#64

/-- Seam PC `+0x21b0` on the untrusted-identity branch. -/
abbrev untrustedPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 8624#64

/-- Trust-branch target PC (`+0x2150` if `t = true`, `+0x21b0` if `t = false`). -/
abbrev trustedPCPlaced [LibsignalPlacement] (t : Bool) : BitVec 64 :=
  if t then saveCallPCPlaced else untrustedPCPlaced

/-- Seam PC `+0x2388` at the `store_session` shim call. -/
abbrev storeCallPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 9096#64

/-- Error-join PC: `+0x2294` (`pt = true`) or `+0x22a8` (`pt = false`). -/
abbrev errJoinPCPlaced [LibsignalPlacement] (pt : Bool) : BitVec 64 :=
  if pt then (blkPl_463).base + 8852#64 else (blkPl_463).base + 8872#64

/-- Seam PC `+0x24d4` at the final 48-byte result write. -/
abbrev resultFinalPCPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_463).base + 9428#64

/-- Store invariants and callee stack slack threaded across middle seams. -/
def decStoreExtraPlaced {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) : SepProp :=
  ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
    memRegion (s0.sp - BitVec.ofNat 64 (wsStackV kit ikit)) (wsCalleeStackV kit ikit - wsCalleeStack)

theorem wsStack_split_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      stackAt s0.sp (wsStackV kit ikit) ⊢
      stackAt s0.sp wsStack ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsStackV kit ikit := by
    have : wsStack = wsCalleeStack + wsFrame := rfl
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + wsFrame := rfl
    omega
  rw [← hsum, stackAt_split_bottom s0.sp wsStack (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum]
  unfold decStoreExtraPlaced
  refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hbound (Entails.of_eq rfl)))
  exact Entails.of_eq (by ac_rfl)

theorem wsStack_join_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    stackAt s0.sp wsStack ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
        stackAt s0.sp (wsStackV kit ikit) := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsStackV kit ikit := by
    have : wsStack = wsCalleeStack + wsFrame := rfl
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + wsFrame := rfl
    omega
  unfold decStoreExtraPlaced
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbound
  rw [← hsum, stackAt_split_bottom s0.sp wsStack (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum]
  exact Entails.of_eq (by ac_rfl)

theorem wsCalleeStack_join_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State) :
    stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0 ⊢
      ⌜wsStackV kit ikit ≤ s0.sp.toNat⌝ ∗
        kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
        stackAt (s0.sp - 0xee0#64) (wsCalleeStackV kit ikit) := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have hsum : wsCalleeStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsCalleeStackV kit ikit := by omega
  unfold decStoreExtraPlaced
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; intro hbound
  have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hsub : (s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit) =
      s0.sp - BitVec.ofNat 64 (wsStackV kit ikit) := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    bv_omega
  rw [← hsum, stackAt_split_bottom (s0.sp - 0xee0#64) wsCalleeStack
        (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum, hsub]
  exact Entails.pure_right hbound (Entails.of_eq (by ac_rfl))

theorem wsCalleeStack_split_extra_placed {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (st : kit.StoreState) (ist : ikit.IdState) (s0 : State)
    (hbound : wsStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt (s0.readReg64 .x3) st ∗ ikit.identityAt (s0.readReg64 .x5) ist ∗
      stackAt (s0.sp - 0xee0#64) (wsCalleeStackV kit ikit) ⊢
      stackAt (s0.sp - 0xee0#64) wsCalleeStack ∗ decStoreExtraPlaced kit ikit st ist s0 := by
  have hle := wsCalleeStack_le_V kit ikit
  have hlt := s0.sp.isLt
  have h2 : wsCalleeStackV kit ikit ≤ wsStackV kit ikit := Nat.le_add_right _ _
  have hsum : wsCalleeStack + (wsCalleeStackV kit ikit - wsCalleeStack) = wsCalleeStackV kit ikit := by omega
  have hsub : (s0.sp - 0xee0#64) - BitVec.ofNat 64 (wsCalleeStackV kit ikit) =
      s0.sp - BitVec.ofNat 64 (wsStackV kit ikit) := by
    have : wsStackV kit ikit = wsCalleeStackV kit ikit + 0xee0 := rfl
    bv_omega
  rw [← hsum, stackAt_split_bottom (s0.sp - 0xee0#64) wsCalleeStack
        (wsCalleeStackV kit ikit - wsCalleeStack) (by omega), hsum, hsub]
  unfold decStoreExtraPlaced
  refine Entails.trans ?_ (sepConj_mono_right (Entails.pure_right hbound (Entails.of_eq rfl)))
  exact Entails.of_eq (by ac_rfl)

/-- Machine invariants preserved at every post-prologue seam under `[LibsignalPlacement]`. -/
def wsMetaPlaced [LibsignalPlacement] (x : DecryptGhost) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp - 0xee0#64 ∧ s0.spAligned = true ∧ s.spAligned = true ∧
    s.readReg64 .x29 = s0.sp - 96#64 ∧ s.readReg64 .x27 = x.ret ∧
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem ∧ calleeSavedVRegs s = calleeSavedVRegs s0

/-- Saved registers, argument cells, and vtables preserved across all post-prologue seams. -/
def wsFixedVPlaced {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (sp : BitVec 64) : SepProp :=
  wsSavedRegs s0.sp s0 ∗ wsArgCellsV kit ikit x s0 sp ∗ decVtablesAtV kit ikit ∗
  memRegion (sp + 0xa0#64) 0x40 ∗
  memRegion (sp + 0x2c8#64) 8 ∗ memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80

/-- Borrowed inputs, callee stack, and allocator pool preserved across seams. -/
def wsEnvPlaced [LibsignalPlacement] (A : RustAlloc) (x : DecryptGhost) (sp : BitVec 64) : SepProp :=
  signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ FromRecordCallees.lsLogOff ∗ stackAt sp wsCalleeStack ∗ A.pool

/-- Establishes `decVtablesAtV kit ikit` from `SessionOnlyVtablesPlacedOk` and `IdentityVtablesPlacedOk`. -/
theorem satisfies_decVtablesAtV_placed [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {m : Memory} {P : SepProp}
    (hvt : SessionOnlyVtablesPlacedOk kit) (hivt : IdentityVtablesPlacedOk ikit)
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ decVtablesAtV kit ikit ∗ P := by
  unfold decVtablesAtV decLoadVtableAtV decStoreVtableAtV decSaveVtableAtV decTrustVtableAtV
  simp only [sepConj_assoc]
  exact hvt.loadSlot hro (hvt.loadFutDrop hro (hvt.loadFutSize hro (hvt.loadFutAlign hro
    (hvt.loadFutPoll hro (hvt.storeSlot hro (hvt.storeFutDrop hro (hvt.storeFutSize hro
      (hvt.storeFutAlign hro (hvt.storeFutPoll hro (hivt.saveSlot hro (hivt.saveFutDrop hro
        (hivt.saveFutSize hro (hivt.saveFutAlign hro (hivt.saveFutPoll hro (hivt.trustSlot hro
          (hivt.trustFutDrop hro (hivt.trustFutSize hro (hivt.trustFutAlign hro
            (hivt.trustFutPoll hro hP)))))))))))))))))))

/-- Relocatable seam state at `+0x8c` after `load_session`. -/
def LoadPolledStateVPlaced [LibsignalPlacement] {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = loadPolledPCPlaced ∧ wsMetaPlaced x s0 s ∧ wsStack ≤ s0.sp.toNat ∧
  s.readReg64 .x19 = sp + 0x5f0#64 ∧
  kit.loadRel st0 x.rem.val ans.loadSession ∧
  s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
  (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
    (∃∗ box : BitVec 64, ⌜box ≠ 0#64⌝ ∗ ((sp + 0x2d0#64) ↦₆₄ box) ∗
      ((sp + 0x2d8#64) ↦₆₄ (0#64 + kit.loadFutVtOff)) ∗
      A.live box kit.loadBoxSize 8 ∗
      kit.loadBoxAt box (s0.readReg64 .x3) x.remA 1#8) ∗
    loadPollPlacedOutAtS Scope A (sp + 0x5f0#64) ans.loadSession ∗
    memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗
    memRegion (sp + 0x300#64) 0x1b0 ∗ memRegion (sp + 0x4b0#64) 0x140 ∗
    memRegion (sp + 0x760#64) 0x6a0 ∗ memRegion x.ret 48 ∗ cliTapeAt ctl x.cur x.rest ∗
    decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Public-API stack and store frame surrounding `recordDecryptPlacedSpec`. -/
def wsRegionFrameVPlaced {A : RustAlloc} {b : BitVec 64}
    (kit : SessionStoreSpec A b) (ikit : IdentityStoreSpec A b)
    (x : DecryptGhost) (s0 : State) (prevCap prevPtr : BitVec 64) : SepProp :=
  let sp := s0.sp - 0xee0#64
  wsSavedRegs s0.sp s0 ∗ wsArgCellsV kit ikit x s0 sp ∗ decVtablesAtV kit ikit ∗
    memRegion (sp + 0xa0#64) 0x40 ∗ memRegion (sp + 0x2c8#64) 8 ∗
    memRegion (sp + 0x2e0#64) 0x20 ∗ memRegion (sp + 0xe00#64) 0x80 ∗
    ((sp + 0x120#64) ↦₆₄ prevCap) ∗ prevBufAt A prevCap prevPtr ∗
    memRegion (sp + 0x290#64) 0x38 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
    memRegion (sp + 0x300#64) 0x1b0 ∗
    memRegion (sp - BitVec.ofNat 64 wsCalleeStack) (wsCalleeStack - rootStack) ∗
    memRegion x.ret 48

/-- Relocatable seam state at `recEntryPlaced` (`+0x1a8`) with `currentSession = some _`. -/
def RegionSomeStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State) : Prop :=
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8))) (G : SessionGhost)
    (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl parse S).pre (recGhostOf x prevPtr G ses.state) s ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Relocatable precondition at `+0x1a8` when `currentSession = none`. -/
def regionNonePrePlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64) (x : DecryptGhost)
    (prevPtr : BitVec 64) (s : State) : SepProp :=
  ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s.mem ∧ s.spAligned = true ∧ s.readReg64 .x27 = x.ret ∧
    s.readReg64 .x19 = x.remA ∧ s.readReg64 .x23 = s.sp + 0x5f0#64 ∧
    s.readReg64 .x24 = s.sp + 0xca0#64 ∧ rootStack ≤ s.sp.toNat⌝ ∗
  memRegion s.sp 0xa0 ∗ ((s.sp + 0xe0#64) ↦₆₄ x.msgA) ∗ ((s.sp + 0xf0#64) ↦₆₄ x.locA) ∗
  ((s.sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((s.sp + 0x130#64) ↦₆₄ 0#64) ∗
  ((s.sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (s.sp + 0x140#64) 336 ∗
  memRegion (s.sp + 0x4b0#64) 0x950 ∗
  protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
  stackAt s.sp rootStack ∗ A.pool

/-- Relocatable seam state at `recEntryPlaced` (`+0x1a8`) when `currentSession = none`. -/
def RegionNoneStateVPlaced [LibsignalPlacement] {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ regionNonePrePlaced A ctl x prevPtr s ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Relocatable seam state at `recExitPlaced` (`+0x1f50`) exiting `RegionSomeStateVPlaced`. -/
def PostSomeStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ (s1 : State) (rec : SessionRecord (List (BitVec 8))) (ses : Session (List (BitVec 8)))
    (G : SessionGhost) (prevCap prevPtr : BitVec 64),
    s1.sp = s0.sp - 0xee0#64 ∧
    s1.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = some ses ∧ sessionModelRel G ses ∧
    (s.mem ⊨ (CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl parse S).post (recGhostOf x prevPtr G ses.state) s1 s ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Relocatable seam state at `recExitPlaced` (`+0x1f50`) exiting `RegionNoneStateVPlaced`. -/
def PostNoneStateVPlaced [LibsignalPlacement] {A : RustAlloc} (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced ∧ wsMetaPlaced x s0 s ∧
  s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 = recordResultTag (.error (.invalidMessage .whisper .decryptionFailed)) ∧
  ∃ (rec : SessionRecord (List (BitVec 8))) (prevCap prevPtr : BitVec 64),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    rec.currentSession = none ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ memRegion sp 0xa0 ∗ wsMsgCells x sp ∗
      ((sp + 0x128#64) ↦₆₄ prevPtr) ∗ ((sp + 0x130#64) ↦₆₄ 0#64) ∗
      ((sp + 0x138#64) ↦₆₄ noneCap) ∗ memRegion (sp + 0x140#64) 336 ∗
      recordResultAt A (sp + 0x4b0#64) (.error (.invalidMessage .whisper .decryptionFailed)) ∗
      memRegion (sp + 0x4e0#64) 0x920 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ cliTapeAt ctl x.cur x.rest ∗ FromRecordCallees.lsLogOff ∗
      stackAt sp rootStack ∗ A.pool ∗
      wsRegionFrameVPlaced kit ikit x s0 prevCap prevPtr ∗ decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Relocatable seam state at `+0x1fcc` before `is_trusted_identity`. -/
def KeyReadyStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = keyReadyPCPlaced ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧
    s.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val ans.loadSession ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0xca0#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x9a0 ∗ memRegion (sp + 0xcc0#64) 0x140 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st0 ist0 s0 ∗ R)

/-- Relocatable seam state at `trustedPCPlaced t` after `is_trusted_identity`. -/
def TrustedStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (t : Bool)
    (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = trustedPCPlaced t ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x19 = sp + 0x2a8#64 ∧ s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok t ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity) ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ ((sp + 0x2a8#64) ↦ₛ k.publicKey.bytes.toList) ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st0 (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity) s0 ∗ R)

/-- Relocatable seam state at `+0x2388` before `store_session`. -/
def StoreCallStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = storeCallPCPlaced ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x22 = sp + 0x294#64 ∧
  ∃ (rec rec' : SessionRecord (List (BitVec 8))) (pt : List (BitVec 8)) (ses : Session (List (BitVec 8)))
    (k : IdentityKey) (c : IdentityChange),
    ans.loadSession = .ok (some rec) ∧ kit.ScopeAt Scope st0 x.rem.val rec ∧
    decryptRecord C S parse x rec = .ok (pt, rec') ∧ rec'.currentSession = some ses ∧
    ses.state.remoteIdentity = some k ∧ ans.isTrustedIdentity = .ok true ∧
    ans.saveIdentity = .ok c ∧
    ikit.trustRel ist0 x.rem.val k .receiving ans.isTrustedIdentity ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
      x.rem.val k ans.saveIdentity ∧
    s.trace = s0.trace ++ (kit.loadEvs encRecord x.rem.val ans.loadSession ++
      ikit.trustEvs x.rem.val k .receiving ans.isTrustedIdentity ++
      ikit.saveEvs x.rem.val k ans.saveIdentity) ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x120#64) g rec') ∗
      vecU8 A (sp + 0x290#64) pt ∗ memRegion (sp + 0x2a8#64) 0x20 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗ memRegion (sp + 0x300#64) 0xb00 ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit st0
        (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .receiving ans.isTrustedIdentity)
          x.rem.val k ans.saveIdentity) s0 ∗ R)

/-- Relocatable seam state at `errJoinPCPlaced pt` on error paths. -/
def ErrJoinStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = errJoinPCPlaced pt ∧ wsMetaPlaced x s0 s ∧ s.readReg64 .x26 = sp + 0xa0#64 ∧
  s.readReg64 .x28 ≠ pendingTag ∧
  ∃ (ans : StoreAnswers (List (BitVec 8)) Unit) (cs : Option (SessionGhost × SessionState (List (BitVec 8)))),
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ p, (x.model C S parse ans).1 ≠ .ok p) ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      droppableRecordAt A (sp + 0x120#64) cs ∗
      (if pt then ∃∗ p : List (BitVec 8), vecU8 A (sp + 0x290#64) p
       else memRegion (sp + 0x290#64) 24) ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x580#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x2a8#64) 0x20 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x300#64) 0x280 ∗ memRegion (sp + 0x5a4#64) 0x85c ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

/-- Relocatable seam state at `+0x24d4` before writing the final `Result`. -/
def ResultFinalStateVPlaced [LibsignalPlacement] (C : Crypto) {A : RustAlloc} (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State) : Prop :=
  let sp := s0.sp - 0xee0#64
  s.pc = resultFinalPCPlaced ∧ wsMetaPlaced x s0 s ∧
  ∃ ans : StoreAnswers (List (BitVec 8)) Unit,
    (x.model C S parse ans).1 ≠ .error .panic ∧
    (∀ r, ans.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
    kit.callsRel st0 ans (x.model C S parse ans).2 ∧
    ikit.idCallsRel ist0 ans (x.model C S parse ans).2 ∧
    s.trace = s0.trace ++ ikit.traceOfWith kit encRecord ans (x.model C S parse ans).2 ∧
    (s.mem ⊨ wsFixedVPlaced kit ikit x s0 sp ∗ wsEnvPlaced A x sp ∗ wsMsgCells x sp ∗
      StagedRes A (s.readReg64 .x28) (s.readReg64 .x20) (s.readReg64 .x21) (sp + 0x300#64)
        (x.model C S parse ans).1 ∗
      memRegion sp 0xa0 ∗ memRegion (sp + 0x120#64) 0x1a8 ∗ memRegion (sp + 0x2d0#64) 0x10 ∗
      memRegion (sp + 0x324#64) 0xadc ∗
      memRegion x.ret 48 ∗ cliTapeAfter ctl x.cur x.rest (x.draws C ans) ∗
      decStoreExtraPlaced kit ikit
        (kit.storeFinal st0 ans (x.model C S parse ans).2)
        (ikit.idFinal ist0 ans (x.model C S parse ans).2) s0 ∗ R)

/-- Relocatable `[LibsignalPlacement]` specification of `session_message_decrypt_signal_with_stores`
(Block `463`) parameterized by `kit`, `ikit`, `st0`, `ist0`, and `Scope`. -/
def withStoresDecPlacedSpecV [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Spec DecryptGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.msgA ∧ s.readReg64 .x1 = x.remA ∧ s.readReg64 .x2 = x.locA ∧
          s.readReg64 .x4 = kit.ss_vt ∧ s.readReg64 .x6 = ikit.id_vt ∧
          s.readReg64 .x8 = x.ret ∧ wsStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt (s.readReg64 .x3) st0 ∗
        ikit.identityAt (s.readReg64 .x5) ist0 ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 48 ∗ cliTapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s.sp (wsStackV kit ikit) ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S parse answers).1 ≠ .error .panic ∧
            (∀ r, answers.loadSession = .ok (some r) → kit.ScopeAt Scope st0 x.rem.val r) ∧
            kit.callsRel st0 answers (x.model C S parse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S parse answers).2 ∧
            sf.trace = s0.trace ++ ikit.traceOfWith kit encRecord answers (x.model C S parse answers).2⌝ ∗
          kit.storeAt (s0.readReg64 .x3)
            (kit.storeFinal st0 answers (x.model C S parse answers).2) ∗
          ikit.identityAt (s0.readReg64 .x5)
            (ikit.idFinal ist0 answers (x.model C S parse answers).2) ∗
          apiDecResultAt A x.ret (x.model C S parse answers).1 ∗
          signalMessageAt A x.msgG x.msgA x.msg ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ cliTapeAfter ctl x.cur x.rest (x.draws C answers) ∗
          FromRecordCallees.lsLogOff ∗ decVtablesAtV kit ikit ∗ stackAt s0.sp (wsStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
           (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S parse answers).1 = .error .panic ∨ x.recvPanics S answers))⌝ ∗
        anyHeap }

theorem withStoresDecPlacedSpecV_pre_addrOk [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {kit : SessionStoreSpec A 0#64} {ikit : IdentityStoreSpec A 0#64}
    {st0 : kit.StoreState} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {x : DecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (withStoresDecPlacedSpecV C A ctl uuidTryParse S encRecord kit ikit st0 ist0 Scope).pre x s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  have ⟨_, hp⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.1.2.2.2.2.2.2.2

/-- Step relation for a relocatable `MessageDecrypt` segment on `lsProg_463 H`. -/
def DecSegVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (x : DecryptGhost) (R : SepProp) (s0 s : State)
    (Out : State → Prop) : Prop :=
  (lsProg_463 H).CodeLoaded s.mem →
  ∃ s', Steps (lsProg_463 H) s s' ∧
    (Out s' ∨
      SubroutineOutcome (withStoresDecPlacedSpecV C A ctl parse S encRecord kit ikit st0 ist0 Scope)
        x R s0 s')

/-- External allocator, shim, `memcpy`, and `String::clone` contracts on `H : LibsignalHooks`. -/
structure PublicApiDecHooksPlaced (A : RustAlloc) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimSpec
  alloc : HookSat H lsRustAllocSym (rustAllocSpec A)
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  memcpy : HookSat H "memcpy" sessionMemcpyRegionSpec
  stringClone : HookSat H lsStringCloneSym (stringCloneSpec A)
  handleError : H lsHandleErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

/-- Store-kit and hook hypotheses shared by all relocatable `MessageDecrypt` segments. -/
structure DecHypsVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks)
    (ss : SessionStoreSpec A 0#64)
    (id : IdentityStoreSpec A 0#64)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop where
  hooks : PublicApiDecHooksPlaced A H
  kit : SessionOnlyKitPlacedOkSE ss Scope encRecord H
  ikit : IdentityStoreKitPlacedOkI id H
  scopeIn : ∀ r, Scope r → RecordInScope r
  recOk : DecModelRecOk ss C S parse Scope

/-- Filesystem invariant carrier over `lsProg_463 H`. -/
abbrev DecFsCtxPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (H : LibsignalHooks) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (lsProg_463 H) s0 s

/-- Relocatable `<SessionState>::remote_identity_key` (Block `29`) lifted to `lsProg_463 H`. -/
abbrev RemoteIdentityKeyPlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_463 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (Getters.remoteIdentityKeyPlacedSpec A))

/-- Relocatable `drop_glue::<SessionStructure> [local#2]` (Block `442`) lifted to `lsProg_463 H`. -/
abbrev DropSessionStructureLocal2PlacedOk [LibsignalPlacement] (A : RustAlloc) (H : LibsignalHooks) : Prop :=
  subroutine_ok (lsProg_463 H) (lsmpl.base 442)
    (StoreKit.withLsRoCl lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A))

/-- Relocatable `SegLoad` specification (`+0x0 → +0x8c`). -/
def SegLoadSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 : State),
    DecFsCtxPlaced kit ikit H s0 s0 →
    s0.pc = wsEntryPCPlaced → s0.status = .Running → s0.spAligned = true →
    (s0.mem ⊨ (withStoresDecPlacedSpecV C A ctl parse S encRecord kit ikit st0 ist0 Scope).pre x s0 ∗ R) →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s0
      (fun s' => ∃ ans, LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s')

/-- Relocatable `SegDispatch` specification (`+0x8c → +0x1a8 / +0x24d4`). -/
def SegDispatchSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    LoadPolledStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => RegionSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        RegionNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s')

/-- Relocatable `SegRegionSome` specification (`+0x1a8 → +0x1f50`). -/
def SegRegionSomeSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (Q : List (BitVec 8) → Prop),
  region_ok (lsProg_463 H) CryptoVerification.Cli.LibsignalTripleRatchet.Record.recEntryPlaced CryptoVerification.Cli.LibsignalTripleRatchet.Record.recExitPlaced
    ((CryptoVerification.Cli.LibsignalTripleRatchet.Record.recordDecryptPlacedSpec C A ctl uuidTryParse S).withVRegs.restrictPre (Q ·.st.pqRatchetState)) →
  ScopePq kit st0 Scope Q →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => PostSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s')

/-- Relocatable `SegRegionNone` specification (`+0x1a8 → +0x1f50`). -/
def SegRegionNoneSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    RegionNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => PostNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s')

/-- Relocatable `SegPostSome` specification (`+0x1f50 → +0x1fcc / +0x22a8`). -/
def SegPostSomeSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  RemoteIdentityKeyPlacedOk A H →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostSomeStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => KeyReadyStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s' ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x false R s0 s')

/-- Relocatable `SegPostNone` specification (`+0x1f50 → +0x22a8`). -/
def SegPostNoneSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    PostNoneStateVPlaced ctl encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x false R s0 s')

/-- Relocatable `SegTrust` specification (`+0x1fcc → +0x2150 / +0x21b0 / +0x2294`). -/
def SegTrustSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    KeyReadyStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans' t, TrustedStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans' t R s0 s') ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

/-- Relocatable `SegUntrusted` specification (`+0x21b0 → +0x2294`). -/
def SegUntrustedSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    TrustedStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans false R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

/-- Relocatable `SegSave` specification (`+0x2150 → +0x2388 / +0x2294`). -/
def SegSaveSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    ikit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    TrustedStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans true R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => (∃ ans', StoreCallStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans' R s0 s') ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

/-- Relocatable `SegStore` specification (`+0x2388 → +0x24d4 / +0x2294`). -/
def SegStoreSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  DropSessionStructureLocal2PlacedOk A H →
  ∀ (x : DecryptGhost) (ans : StoreAnswers (List (BitVec 8)) Unit) (R : SepProp) (s0 s : State),
    kit.addrOk x.rem.val →
    DecFsCtxPlaced kit ikit H s0 s →
    StoreCallStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x ans R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s' ∨
        ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x true R s0 s')

/-- Relocatable `SegErrTeardown` specification (`+0x2294 / +0x22a8 → +0x24d4`). -/
def SegErrTeardownSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  DropSessionStructureLocal2PlacedOk A H →
  ∀ (x : DecryptGhost) (pt : Bool) (R : SepProp) (s0 s : State),
    ErrJoinStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x pt R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s
      (fun s' => ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s')

/-- Relocatable `SegWrite` specification (`+0x24d4 → +0x2510`). -/
def SegWriteSpecVPlaced [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (st0 : kit.StoreState) (ist0 : ikit.IdState) (Scope : SessionRecord (List (BitVec 8)) → Prop) : Prop :=
  DecHypsVPlaced C A parse S encRecord H kit ikit Scope →
  ∀ (x : DecryptGhost) (R : SepProp) (s0 s : State),
    ResultFinalStateVPlaced C ctl parse S encRecord kit ikit st0 ist0 Scope x R s0 s →
    DecSegVPlaced C A ctl parse S encRecord H kit ikit st0 ist0 Scope x R s0 s (fun _ => False)


end CryptoVerification.Cli.LibsignalPublicApi.MessageDecrypt
