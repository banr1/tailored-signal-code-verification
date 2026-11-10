/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PublicApiEncryptCodeSym
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Segs
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.UnackItems
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.KyberMap
public import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From.Frame
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.CalleeProofs.CmDrop
import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.PreKeySignalMessageNew.Compose
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Drops.Local2
import LibsignalBinary.Proofs.TripleRatchet.Getters.Drops.SignalProtocolError.Ext
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.OutgoingRatchet.From

/-!
# Relocatable `MessageEncrypt` Seam States and Segment Specifications

Relocatable `[LibsignalPlacement]` seam PCs, frame invariants, callee bundles, and segment
specifications for `session_message_encrypt_with_stores` (block `198`, `lsProg_198 H`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.LibsignalPublicApi.MessageEncrypt

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApi.Placed
open CryptoVerification.LibsignalPublicApi.StoreKit

/-! ## 1. Entry and Seam PCs on Block `198` -/

/-- Entry address of `session_message_encrypt_with_stores` (Block `198`) under `[LibsignalPlacement]`. -/
abbrev encEntryPlaced [LibsignalPlacement] : BitVec 64 := (blkPl_198).base

/-- Seam `Cur` (`+0x20c`): `load_session` returned `Ok(Some r)` with a current session; next `from_session_state`. -/
abbrev curPCPlaced [LibsignalPlacement] : BitVec 64 := encEntryPlaced + 0x20c#64
/-- Seam `Otr` (`+0x2c8`): `bl remote_identity_key` (block `29`). -/
abbrev otrPCPlaced [LibsignalPlacement] : BitVec 64 := encEntryPlaced + 0x2c8#64
/-- Seam `Key` (`+0x344`): `bl unacknowledged_pre_key_message_items` (block `36`). -/
abbrev keyPCPlaced [LibsignalPlacement] : BitVec 64 := encEntryPlaced + 0x344#64
/-- Seam `Cm` (`+0xa70`): join of the `SignalMessage` and `PreKeySignalMessage` branches; next `is_trusted_identity`. -/
abbrev cmPCPlaced [LibsignalPlacement] : BitVec 64 := encEntryPlaced + 0xa70#64
/-- Seam `Save` (`+0xbd4`): identity trusted; next `save_identity`. -/
abbrev savePCPlaced [LibsignalPlacement] : BitVec 64 := encEntryPlaced + 0xbd4#64
/-- Seam `Apply` (`+0xd9c`): identity saved; next OTR copy and `apply_to_session_state` (`+0xde4`). -/
abbrev applyPCPlaced [LibsignalPlacement] : BitVec 64 := encEntryPlaced + 0xd9c#64
/-- Seam `Stored` (`+0xe88`): `store_session` returned `Ok(())`; next record drop, result copy, and epilogue. -/
abbrev storedPCPlaced [LibsignalPlacement] : BitVec 64 := encEntryPlaced + 0xe88#64

/-! ## 2. Store-Extra Frame and Stack Split/Join Lemmas -/

/-- Store and stack resources framed across intermediate seams (`kit : SessionStoreSpec A 0#64`, `ikit : IdentityStoreSpec A 0#64`). -/
def encStoreExtraPlaced {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) : SepProp :=
  ⌜withStoresEncStackV kit ikit ≤ s0.sp.toNat⌝ ∗
    kit.storeAt x.ssA st ∗
    ikit.identityAt x.idA ist ∗
    memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
      (encSubStackV kit ikit - encSubStack)

theorem withStoresEncStack_split_extra_placed {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ⊢
      encStoreExtraPlaced kit st ikit ist x s0 ∗ stackAt s0.sp withStoresEncStack := by
  unfold encStoreExtraPlaced stackAt
  have hle := encSubStack_le_encSubStackV kit ikit
  have hw : withStoresEncStack = encSubStack + encFrameSize := by decide
  have hsum : (encSubStackV kit ikit - encSubStack) + withStoresEncStack = withStoresEncStackV kit ikit := by
    unfold withStoresEncStackV; omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hsplit :
      memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (withStoresEncStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 withStoresEncStack) withStoresEncStack := by
    refine memRegion_split'
      (b := s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
      (b' := s0.sp - BitVec.ofNat 64 withStoresEncStack)
      (n := encSubStackV kit ikit - encSubStack) (k := withStoresEncStack)
      hsum.symm ?_ (by omega)
    bv_omega
  rw [hsplit, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  exact Entails.pure_right hbound (Entails.refl _)

theorem withStoresEncStack_join_extra_placed {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State) :
    encStoreExtraPlaced kit st ikit ist x s0 ∗ stackAt s0.sp withStoresEncStack ⊢
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt s0.sp (withStoresEncStackV kit ikit) := by
  unfold encStoreExtraPlaced stackAt
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun hbound => ?_
  have hle := encSubStack_le_encSubStackV kit ikit
  have hw : withStoresEncStack = encSubStack + encFrameSize := by decide
  have hsum : (encSubStackV kit ikit - encSubStack) + withStoresEncStack = withStoresEncStackV kit ikit := by
    unfold withStoresEncStackV; omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hsplit :
      memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (withStoresEncStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - BitVec.ofNat 64 withStoresEncStack) withStoresEncStack := by
    refine memRegion_split'
      (b := s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit))
      (b' := s0.sp - BitVec.ofNat 64 withStoresEncStack)
      (n := encSubStackV kit ikit - encSubStack) (k := withStoresEncStack)
      hsum.symm ?_ (by omega)
    bv_omega
  rw [hsplit]
  exact Entails.refl _

theorem encSubStack_join_extra_placed {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    encStoreExtraPlaced kit st ikit ist x s0 ∗ stackAt (s0.sp - 0xbe0#64) encSubStack ⊢
      kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) := by
  unfold encStoreExtraPlaced stackAt
  rw [sepConj_assoc, sepConj_assoc, sepConj_assoc]
  refine Entails.pure_left fun _ => ?_
  have hle := encSubStack_le_encSubStackV kit ikit
  have hsum : (encSubStackV kit ikit - encSubStack) + encSubStack = encSubStackV kit ikit := by omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hbase : s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit) =
      s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit) := by
    unfold withStoresEncStackV encFrameSize at hbound ⊢
    bv_omega
  have hsplit :
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) encSubStack := by
    rw [hbase]
    refine memRegion_split'
      (b := s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
      (b' := s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack)
      (n := encSubStackV kit ikit - encSubStack) (k := encSubStack)
      hsum.symm ?_ (by unfold withStoresEncStackV encFrameSize at hbound; omega)
    unfold withStoresEncStackV encFrameSize at hbound
    bv_omega
  rw [hsplit]
  exact Entails.refl _

theorem encSubStack_split_extra_placed {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist : ikit.IdState)
    (x : WithStoresEncGhost) (s0 : State)
    (hbound : withStoresEncStackV kit ikit ≤ s0.sp.toNat) :
    kit.storeAt x.ssA st ∗ ikit.identityAt x.idA ist ∗ stackAt (s0.sp - 0xbe0#64) (encSubStackV kit ikit) ⊢
      encStoreExtraPlaced kit st ikit ist x s0 ∗ stackAt (s0.sp - 0xbe0#64) encSubStack := by
  unfold encStoreExtraPlaced stackAt
  have hle := encSubStack_le_encSubStackV kit ikit
  have hsum : (encSubStackV kit ikit - encSubStack) + encSubStack = encSubStackV kit ikit := by omega
  have hsp : s0.sp.toNat < 2 ^ 64 := s0.sp.isLt
  have hbase : s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit) =
      s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit) := by
    unfold withStoresEncStackV encFrameSize at hbound ⊢
    bv_omega
  have hsplit :
      memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit)) (encSubStackV kit ikit) =
        memRegion (s0.sp - BitVec.ofNat 64 (withStoresEncStackV kit ikit)) (encSubStackV kit ikit - encSubStack) ∗
          memRegion (s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack) encSubStack := by
    rw [hbase]
    refine memRegion_split'
      (b := s0.sp - 0xbe0#64 - BitVec.ofNat 64 (encSubStackV kit ikit))
      (b' := s0.sp - 0xbe0#64 - BitVec.ofNat 64 encSubStack)
      (n := encSubStackV kit ikit - encSubStack) (k := encSubStack)
      hsum.symm ?_ (by unfold withStoresEncStackV encFrameSize at hbound; omega)
    unfold withStoresEncStackV encFrameSize at hbound
    bv_omega
  rw [hsplit, sepConj_assoc, sepConj_assoc, sepConj_assoc]
  exact Entails.pure_right hbound (Entails.refl _)

/-! ## 3. Relocatable `_with_stores` Specification -/

/-- Relocatable `session_message_encrypt_with_stores` (Block `198`) contract parameterized by
    `kit : SessionStoreSpec A 0#64` and `ikit : IdentityStoreSpec A 0#64`. -/
def withStoresEncPlacedSpecV [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)) : Spec WithStoresEncGhost :=
  StoreKit.withLsCodeRoLoaded lsmpl
    { pre := fun x s =>
        ⌜s.readReg64 .x0 = x.ptA ∧ (s.readReg64 .x1).toNat = x.ptext.length ∧
          x.ptext.length < 2 ^ 32 ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
          x.locA ≠ 0#64 ∧
          s.readReg64 .x4 = x.ssA ∧ s.readReg64 .x5 = kit.ss_vt ∧
          s.readReg64 .x6 = x.idA ∧ s.readReg64 .x7 = ikit.id_vt ∧
          x.now.tvNsec.toNat < 10 ^ 9 ∧ s.readReg64 .x8 = x.ret ∧
          withStoresEncStackV kit ikit ≤ s.sp.toNat ∧
          kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val⌝ ∗
        kit.storeAt x.ssA st0 ∗ ikit.identityAt x.idA ist0 ∗
        nowAt s.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
        protocolAddressAt A x.loc x.locA ∗ memRegion x.ret 248 ∗ tapeAt ctl x.cur x.rest ∗
        FromRecordCallees.lsLogOff ∗ stackAt s.sp (withStoresEncStackV kit ikit) ∗ A.pool
      post := fun x s0 sf =>
        ∃∗ answers : StoreAnswers (List (BitVec 8)) Unit,
          ⌜(x.model C S uuidParse answers).1 ≠ .error .panic ∧
            kit.callsRel st0 answers (x.model C S uuidParse answers).2 ∧
            ikit.idCallsRel ist0 answers (x.model C S uuidParse answers).2 ∧
            sf.trace = s0.trace ++
              ikit.traceOfWith kit encRecord answers (x.model C S uuidParse answers).2⌝ ∗
          kit.storeAt x.ssA (kit.storeFinal st0 answers (x.model C S uuidParse answers).2) ∗
          ikit.identityAt x.idA (ikit.idFinal ist0 answers (x.model C S uuidParse answers).2) ∗
          apiEncResultAt A x.ret (x.model C S uuidParse answers).1 ∗
          nowAt s0.sp x.now ∗ (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗
          protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest (x.draws S answers) ∗
          FromRecordCallees.lsLogOff ∗ stackAt s0.sp (withStoresEncStackV kit ikit) ∗ A.pool
      onPanic := fun x s0 sf =>
        ⌜s0.trace <+: sf.trace ∧
          (allocFailedIn s0 sf ∨
            ∃ answers : StoreAnswers (List (BitVec 8)) Unit,
              kit.loadRel st0 x.rem.val answers.loadSession ∧
              s0.trace ++ kit.loadEvs encRecord x.rem.val answers.loadSession <+: sf.trace ∧
              ((x.model C S uuidParse answers).1 = .error .panic ∨ x.sendPanics S answers))⌝ ∗
          anyHeap }

theorem withStoresEncPlacedSpecV_pre_addrOk [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {C : Crypto} {ctl : BitVec 64} {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {x : WithStoresEncGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).pre x s0 ∗ R) :
    kit.addrOk x.rem.val ∧ ikit.addrOk x.rem.val := by
  have ⟨_, hp⟩ := StoreKit.extract_withLsCodeRoLoaded hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hp
  exact hp.1.2.2.2.2.2.2.2.2.2.2.2.2.2

/-! ## 4. Seam Metadata, Common Frame, and Seam States -/

/-- Relocatable machine invariants at every seam of Block `198`. -/
def encMidMetaPlaced [LibsignalPlacement] (x : WithStoresEncGhost) (s0 s : State) : Prop :=
  s.status = .Running ∧ s.sp = s0.sp - 0xbe0#64 ∧ s0.spAligned = true ∧ s.spAligned = true ∧
    s.readReg64 .x29 = s0.sp - 0x60#64 ∧ s.readReg64 .x19 = x.ret ∧
    StoreKit.LibsignalCodeRoLoaded lsmpl s.mem ∧ calleeSavedVRegs s = calleeSavedVRegs s0

/-- Relocatable borrowed inputs and environment unchanged across seams. -/
def encCommonPlaced [LibsignalPlacement] (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (draws : Nat) (s0 : State) : SepProp :=
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
    nowAt s0.sp x.now ∗ tapeAfter ctl x.cur x.rest draws ∗ FromRecordCallees.lsLogOff ∗
    stackAt (s0.sp - 0xbe0#64) encSubStack ∗ encSavedRegs s0.sp s0 ∗ A.pool

/-- Generic seam state on Block `198` under `[LibsignalPlacement]`. -/
def EncSeamVPlaced [LibsignalPlacement] (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (pc : BitVec 64) (evs : List TraceEvent) (draws : Nat)
    (regs : BitVec 64 → State → Prop) (slots scratch : BitVec 64 → SepProp) (R : SepProp)
    (s0 s : State) : Prop :=
  let sp := s0.sp - 0xbe0#64
  s.pc = pc ∧ encMidMetaPlaced x s0 s ∧ s.trace = s0.trace ++ evs ∧ regs sp s ∧
    x.ptext.length < 2 ^ 32 ∧ x.rest.length < 2 ^ 63 ∧ x.locA ≠ 0#64 ∧
    x.now.tvNsec.toNat < 10 ^ 9 ∧ withStoresEncStack ≤ s0.sp.toNat ∧
    (s.mem ⊨ slots sp ∗ scratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x draws s0 ∗ R)

def CurStateVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State) : Prop :=
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  EncSeamVPlaced kit.ss_vt ikit.id_vt A ctl x curPCPlaced
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) 0
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x21 = sp + 0x128#64 ∧
      s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
      s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => sessionRecordAt A (sp + 0x110#64) g r ∗ memRegion (sp + 0x280#64) 0x1e8 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8))
    curScratch
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R) s0 s

def OtrStateVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  EncSeamVPlaced kit.ss_vt ikit.id_vt A ctl x otrPCPlaced
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) 0
    (fun sp s => s.readReg64 .x0 = sp + 0x128#64 ∧ s.readReg64 .x8 = sp + 0x580#64 ∧
      s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x22 = sp + 0x8b8#64 ∧
      s.readReg64 .x23 = sp + 0x58#64 ∧ s.readReg64 .x24 = sp + 0x58#64 ∧
      s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
      s.readReg64 .x27 = sp + 0xc0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      memRegion (sp + 0x350#64) 0x118)
    curScratch
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R) s0 s

def KeyStateVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (ctl : BitVec 64)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (pqCap pqPtr : BitVec 64) (k : IdentityKey) (R : SepProp) (s0 s : State) : Prop :=
  r.currentSession = some sess ∧ kit.ScopeAt Scope st0 x.rem.val r ∧
  execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken) ∧
  taken.remoteIdentity = some k ∧
  EncSeamVPlaced kit.ss_vt ikit.id_vt A ctl x keyPCPlaced
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) 0
    (fun sp s => s.readReg64 .x0 = sp + 0x128#64 ∧ s.readReg64 .x8 = sp + 0x580#64 ∧
      s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x22 = sp + 0x8b8#64 ∧
      s.readReg64 .x23 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
      s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x27 = sp + 0xc0#64 ∧
      s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => takenSlots A sp sess taken ∗ otrAt A (sp + 0x288#64) pqCap pqPtr otr ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ memRegion (sp + 0x370#64) 0xf8)
    curScratch
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R) s0 s

def CmStateVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (C : Crypto)
    (ctl : BitVec 64) (uuidParse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (taken : SessionState (List (BitVec 8)))
    (k : IdentityKey) (m : CiphertextMessage) (otr' : OutgoingTripleRatchet (List (BitVec 8)))
    (pqCap' pqPtr' : BitVec 64) (R : SepProp) (s0 s : State) : Prop :=
  StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
  EncSeamVPlaced kit.ss_vt ikit.id_vt A ctl x cmPCPlaced
    (kit.loadEvs encRecord x.rem.val (.ok (some r))) (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
      s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => cmSlots A sp sess taken otr' pqCap' pqPtr' k m)
    cmScratch
    (encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R) s0 s

def SaveStateVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
    (s0 s : State) : Prop :=
  (StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
    ikit.trustRel ist0 x.rem.val k .sending (.ok true)) ∧
  EncSeamVPlaced kit.ss_vt ikit.id_vt A ctl x savePCPlaced
    (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
      ikit.trustEvs x.rem.val k .sending (.ok true))
    (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x22 = sp + 0x8b8#64 ∧
      s.readReg64 .x25 = sp + 0x580#64 ∧ s.readReg64 .x26 = sp + 0x9d0#64 ∧
      s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => cmSlots A sp sess taken otr' pqCap' pqPtr' k m)
    cmScratch
    (encStoreExtraPlaced kit st0 ikit (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x s0 ∗ R)
    s0 s

def ApplyStateVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
    (c : IdentityChange) (R : SepProp) (s0 s : State) : Prop :=
  (StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
    ikit.trustRel ist0 x.rem.val k .sending (.ok true) ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c)) ∧
  EncSeamVPlaced kit.ss_vt ikit.id_vt A ctl x applyPCPlaced
    (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
      ikit.trustEvs x.rem.val k .sending (.ok true) ++
      ikit.saveEvs x.rem.val k (.ok c))
    (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x20 = sp + 0x58#64 ∧ s.readReg64 .x25 = sp + 0x580#64 ∧
      s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => cmSlots A sp sess taken otr' pqCap' pqPtr' k m)
    cmScratch
    (encStoreExtraPlaced kit st0 ikit
      (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c))
      x s0 ∗ R) s0 s

def StoredStateVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop)
    (C : Crypto) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
    (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
    (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
    (s0 s : State) : Prop :=
  (StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S uuidParse x r sess otr taken k m otr' ∧
    ikit.trustRel ist0 x.rem.val k .sending (.ok true) ∧
    ikit.saveRel (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c) ∧
    kit.storeRel st0 x.rem.val (storedRecord sess otr' taken) (.ok ())) ∧
  EncSeamVPlaced kit.ss_vt ikit.id_vt A ctl x storedPCPlaced
    (kit.loadEvs encRecord x.rem.val (.ok (some r)) ++
      ikit.trustEvs x.rem.val k .sending (.ok true) ++
      ikit.saveEvs x.rem.val k (.ok c) ++
      kit.storeEvs encRecord x.rem.val (storedRecord sess otr' taken) (.ok ()))
    (S.draws otr.pqrState x.rest)
    (fun sp s => s.readReg64 .x26 = sp + 0x9d0#64 ∧ s.readReg64 .x28 = sp + 0x4a0#64)
    (fun sp => (∃∗ g : RecordGhost,
        sessionRecordAt A (sp + 0x110#64) g (storedRecord sess otr' taken)) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 200 ∗
      ((sp + 0x350#64) ↦ₛ k.publicKey.bytes.toList) ∗ apiEncResultAt A (sp + 0x370#64) (.ok m) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ memRegion (sp + 0x469#64) 1)
    cmScratch
    (encStoreExtraPlaced kit (kit.storeUpdate st0 x.rem.val (storedRecord sess otr' taken) (.ok ()))
      ikit (ikit.saveUpdate (ikit.trustUpdate ist0 x.rem.val k .sending (.ok true)) x.rem.val k (.ok c))
      x s0 ∗ R)
    s0 s

/-! ## 5. External Hooks and Callees on `lsProg_198 H` -/

/-- Mangled ELF symbol for `std::time::SystemTime::duration_since` (called at `+0x6c4`). -/
abbrev lsDurationSinceSym : String :=
  "_RNvMs5_NtCsfr5T3GFabw_3std4timeNtB5_10SystemTime14duration_since"

/-- Mangled ELF symbol for `<SystemTime as Add<Duration>>::add` (called at `+0x6f8` and in `unackItems`). -/
abbrev lsTimeAddSym : String := Pf.UnackItems.lsTimeAddSym

/-- Mangled ELF symbol for `<String as Clone>::clone`. -/
abbrev lsStringCloneSym : String :=
  "_RNvXs4_NtCs69KKACWg7bl_5alloc6stringNtB5_6StringNtNtCskxtBwYRO61I_4core5clone5Clone5clone"

/-- Mangled ELF symbol for `core::option::expect_failed`. -/
abbrev lsExpectFailedSym : String :=
  "_RNvNtCskxtBwYRO61I_4core6option13expect_failed"

/-- Mangled ELF symbol for `alloc::alloc::handle_alloc_error` (used in `kyberMap`). -/
abbrev lsHandleAllocErrorSym : String := Pf.KyberMap.lsHandleAllocErrorSym

/-- External hook contracts and panic stubs on `H : LibsignalHooks` used by Block `198`
    (`session_message_encrypt_with_stores`) and its 8 proved placed callees. -/
structure PublicApiEncHooksPlaced (A : RustAlloc) (H : LibsignalHooks) : Prop where
  shim : HookSat H lsRustNoAllocShimSym sessionShimSpec
  alloc : HookSat H lsRustAllocSym (rustAllocSpec A)
  dealloc : HookSat H lsRustDeallocSym (rustDeallocSpec A)
  realloc : HookSat H lsRustReallocSym (rustReallocSpec A)
  memcpy : HookSat H lsMemcpySym sessionMemcpyRegionSpec
  stringClone : HookSat H lsStringCloneSym (stringCloneSpec A)
  timeAdd : HookSat H lsTimeAddSym timeAddSpec
  durationSince : HookSat H lsDurationSinceSym durationSinceSpec
  handleError : H lsHandleErrorSym = some Rust.panicked
  handleAllocError : H lsHandleAllocErrorSym = some Rust.panicked
  expectFailed : H lsExpectFailedSym = some Rust.panicked

/-- Relocatable `OTR::encrypt::<HookRng>` raw spec (with `FromRecordCallees.lsLogOff` and without `Spec.inImage`). -/
def otrEncryptPlacedSpec [LibsignalPlacement] (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (uuidParse : UuidParser) (S : SpqrModel) : Spec OtrEncryptGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.o ∧ s.readReg64 .x2 = x.ptA ∧
      (s.readReg64 .x3).toNat = x.ptext.length ∧ x.ptext.length < 2 ^ 32 ∧
      s.readReg64 .x4 = (if x.loc.isSome then x.locA else 0#64) ∧
      (x.loc.isSome → x.locA ≠ 0#64) ∧ s.readReg64 .x5 = x.remA⌝ ∗
    otrAt A x.o x.pqCap x.pqPtr x.ot ∗ (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗
    protocolAddressAt A x.rem x.remA ∗ memRegion x.ret 120 ∗ tapeAt ctl x.cur x.rest ∗
    FromRecordCallees.lsLogOff ∗ stackAt s.sp rootStack ∗ A.pool
  post := fun x s0 sf =>
    ⌜(x.model C S uuidParse).1 ≠ .error .panic ∧ sf.trace = s0.trace⌝ ∗
    (∃∗ pqCap' : BitVec 64, ∃∗ pqPtr' : BitVec 64,
      otrAt A x.o pqCap' pqPtr' (x.model C S uuidParse).2) ∗
    signalMessageResultAt A (utf8 "encrypt") x.ret (x.model C S uuidParse).1 ∗
    (x.ptA ↦ₛ x.ptext) ∗ optAddrAt A x.locA x.loc ∗ protocolAddressAt A x.rem x.remA ∗
    tapeAfter ctl x.cur x.rest (S.draws x.ot.pqrState x.rest) ∗
    FromRecordCallees.lsLogOff ∗ stackAt s0.sp rootStack ∗ A.pool
  onPanic := fun x s0 sf =>
    ⌜((x.model C S uuidParse).1 = .error .panic ∨ S.sendPanics x.ot.pqrState x.rest ∨
        allocFailedIn s0 sf) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Relocatable `OTR::encrypt::<HookRng>` spec restricted to OTRs whose SPQR state satisfies `Q`. -/
def otrEncryptPlacedSpecQ [LibsignalPlacement] (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) : Spec OtrEncryptGhost :=
  { otrEncryptPlacedSpec C A ctl parse S with
    pre := fun x s => ⌜Q x.ot.pqrState⌝ ∗ (otrEncryptPlacedSpec C A ctl parse S).pre x s }

/-- Relocatable `OTR::encrypt::<HookRng>` spec for OTRs whose `(pqrState, rest)` satisfies `Q`, with `F` framed. -/
def otrEncryptPlacedSpecQF [LibsignalPlacement] (Q : List (BitVec 8) → List (BitVec 8) → Prop) (F : SepProp)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) : Spec OtrEncryptGhost :=
  { otrEncryptPlacedSpec C A ctl parse S with
    pre := fun x s => ⌜Q x.ot.pqrState x.rest⌝ ∗ F ∗ (otrEncryptPlacedSpec C A ctl parse S).pre x s
    post := fun x s0 sf => F ∗ (otrEncryptPlacedSpec C A ctl parse S).post x s0 sf }

theorem blkPl_198_ρ_otrEncryptName [LibsignalPlacement] :
    (blkPl_198).ρ otrEncryptName = libsignalSessionLib.fnAddr lsmpl otrEncryptName := by
  simp [otrEncryptName]

/-- Bundle of all 9 in-library callees invoked by Block `198` (`lsProg_198 H`) under `[LibsignalPlacement]`. -/
structure EncCalleesPlaced [LibsignalPlacement] (Q : List (BitVec 8) → Prop)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) (H : LibsignalHooks) : Prop where
  otrFrom : subroutine_ok (lsProg_198 H) (lsmpl.base 19)
    (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A))
  otrApply : subroutine_ok (lsProg_198 H) (lsmpl.base 20)
    (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrApplyPlacedSpec A))
  remoteIk : subroutine_ok (lsProg_198 H) (lsmpl.base 29)
    (StoreKit.withLsRoCl lsmpl (Getters.remoteIdentityKeyPlacedSpec A))
  otrEnc : subroutine_ok (lsProg_198 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
    (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQ Q C A ctl parse S))
  unack : subroutine_ok (lsProg_198 H) (lsmpl.base 36)
    (StoreKit.withLsRoCl lsmpl (Pf.UnackItems.unackItemsPlacedSpec A))
  kyber : subroutine_ok (lsProg_198 H) (lsmpl.base 127)
    (StoreKit.withLsRoCl lsmpl (kyberMapSpec A))
  psmNew : subroutine_ok (lsProg_198 H) (lsmpl.base 41)
    (StoreKit.withLsRoCl lsmpl (preKeyMsgNewSpec A))
  cmDrop : subroutine_ok (lsProg_198 H) (lsmpl.base 135)
    (StoreKit.withLsRoCl lsmpl (cmDropSpec A))
  dropSs : subroutine_ok (lsProg_198 H) (lsmpl.base 139)
    (StoreKit.withLsRoCl lsmpl (FromRecordCallees.dropSessionStructureLocal2Spec A))

private theorem subroutine_ok_withLsCodeRoLoaded_of_otrFromPlaced [LibsignalPlacement] {A : RustAlloc}
    {prog : Program} {entry : BitVec 64}
    (h : subroutine_ok prog entry (OutgoingRatchet.otrFromPlacedSpec A)) :
    subroutine_ok prog entry (StoreKit.withLsCodeRoLoaded lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A)) :=
  subroutine_ok_mono h
    (fun _ _ _ hp => by
      obtain ⟨hfr, hpre⟩ := StoreKit.extract_withLsCodeRoLoaded hp
      dsimp only [OutgoingRatchet.otrFromPlacedSpec, OutgoingRatchet.withLsRoLoaded, withLsCodeLoaded]
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      refine ⟨hfr.2, ?_⟩
      rw [sepConj_assoc, sepConj_left_comm, satisfies_pure_sepConj]
      exact ⟨hfr.1, hpre⟩)
    (fun _ _ _ _ hq => hq)

/-- Discharge all 8 proved in-library callees of `EncCalleesPlaced` from `PublicApiEncHooksPlaced A H`,
    leaving only `otrEnc` as an assumption. -/
theorem EncCalleesPlaced.of_otrEnc [LibsignalPlacement] {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {H : LibsignalHooks}
    (hhooks : PublicApiEncHooksPlaced A H)
    (hotrEnc : subroutine_ok (lsProg_198 H) (libsignalSessionLib.fnAddr lsmpl otrEncryptName)
      (StoreKit.withLsRoCl lsmpl (otrEncryptPlacedSpecQ Q C A ctl parse S))) :
    EncCalleesPlaced Q C A ctl parse S H where
  otrFrom :=
    StoreKit.ls_subroutine_ok_rocl_of_block (callerProg := lsProg_198 H)
      (subroutine_ok_withLsCodeRoLoaded_of_otrFromPlaced
        (OutgoingRatchet.otrFrom_placed_ok hhooks.dealloc
          (((Getters.instIsLsBlockProg_29 H).eq_blockProgram.trans
              (CryptoVerification.instIsLsBlockProg_29 H).eq_blockProgram.symm) ▸
            Getters.remote_identity_key_placed_ok A H)
          (((Getters.instIsLsBlockProg_5 H).eq_blockProgram.trans
              (CryptoVerification.instIsLsBlockProg_5 H).eq_blockProgram.symm) ▸
            Getters.drop_spe_placed_ok hhooks.dealloc)))
  otrApply :=
    StoreKit.ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_198 H)
      (OutgoingRatchet.otrApply_placed_ok hhooks.shim hhooks.alloc hhooks.dealloc hhooks.handleError)
  remoteIk :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (Getters.remote_identity_key_placed_ok A H)
  otrEnc := hotrEnc
  unack :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (Pf.UnackItems.unackItems_placed_ok hhooks.timeAdd)
  kyber :=
    StoreKit.ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_198 H)
      (Pf.KyberMap.kyberMap_placed_ok hhooks.shim hhooks.alloc hhooks.memcpy hhooks.handleAllocError)
  psmNew :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (PreKeySignalMessageNew.Compose.preKeyMsgNew_placed_ok hhooks.shim hhooks.alloc hhooks.dealloc
        hhooks.realloc hhooks.memcpy hhooks.handleError)
  cmDrop :=
    StoreKit.ls_subroutine_ok_rocl_of_plain (callerProg := lsProg_198 H)
      (Pf.CmDrop.cmDrop_placed_ok hhooks.dealloc)
  dropSs :=
    StoreKit.ls_subroutine_ok_rocl_of_cl (callerProg := lsProg_198 H)
      (FromRecordCallees.drop_session_structure_local2_placed_ok hhooks.dealloc)

/-! ## 6. Segment Environment, Exit Relation, and Segment Specifications -/

/-- Relocatable environment of every `MessageEncrypt` segment on `lsProg_198 H`. -/
structure EncEnvPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (_ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  hooks : PublicApiEncHooksPlaced A H
  kitOk : SessionOnlyKitPlacedOkSE kit Scope encRecord H
  ikitOk : IdentityStoreKitPlacedOkI ikit H
  callees : EncCalleesPlaced Q C A ctl parse S H
  vtables : SessionOnlyVtablesPlacedOk kit
  idVtables : IdentityVtablesPlacedOk ikit
  scopeIn : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → RecordInScopeEnc r
  scopeQ : ∀ {rem : AddrVal} (r : SessionRecord (List (BitVec 8))) (s : Session (List (BitVec 8))),
    kit.ScopeAt Scope st0 rem r → r.currentSession = some s → Q s.state.pqRatchetState
  recOk : ∀ {x : WithStoresEncGhost} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} {k : IdentityKey} {m : CiphertextMessage}
    {otr' : OutgoingTripleRatchet (List (BitVec 8))},
    StepsThroughEncrypt (kit.ScopeAt Scope st0 x.rem.val) C S parse x r sess otr taken k m otr' →
    kit.RecOk (storedRecord sess otr' taken)

theorem EncEnvPlaced.q_otr [LibsignalPlacement] {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop} {C : Crypto} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {H : LibsignalHooks}
    (env : EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord H)
    {rem : AddrVal} {r : SessionRecord (List (BitVec 8))}
    {sess : Session (List (BitVec 8))} {otr : OutgoingTripleRatchet (List (BitVec 8))}
    {taken : SessionState (List (BitVec 8))} (hcur : r.currentSession = some sess)
    (hsc : kit.ScopeAt Scope st0 rem r)
    (hfrom : execOk OutgoingTripleRatchet.fromSessionState sess.state = .ok (otr, taken)) :
    Q otr.pqrState :=
  fromSessionState_pqrState hfrom ▸ env.scopeQ r sess hsc hcur

/-- Segment exit relation on `lsProg_198 H` under `[LibsignalPlacement]`. -/
def SegExitPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (C : Crypto) (ctl : BitVec 64) (parse : UuidParser)
    (S : SpqrModel) (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) (x : WithStoresEncGhost) (R : SepProp) (s0 s : State)
    (next : State → Prop) : Prop :=
  (lsProg_198 H).CodeLoaded s.mem →
    ∃ sf, Steps (lsProg_198 H) s sf ∧
      (next sf ∨ SubroutineOutcome (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl parse S encRecord) x R s0 sf)

abbrev EncFsCtxPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (ikit : IdentityStoreSpec A 0#64)
    (H : LibsignalHooks) (s0 s : State) : Prop :=
  FsCtx (fun f => kit.envOk f ∧ ikit.envOk f) (kit.Quiet ∧ ikit.Quiet)
    (lsProg_198 H) s0 s

/-- Segment `segLoad` (entry → `Cur`). -/
def SegLoadSpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (R : SepProp) (s0 : State),
      EncFsCtxPlaced kit ikit H s0 s0 →
      s0.pc = encEntryPlaced → s0.status = .Running → s0.spAligned = true →
      (s0.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl parse S encRecord).pre x s0 ∗ R) →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s0
        (fun s => ∃ r g sess, CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s)

/-- Segment `segFrom` (`Cur` → `Otr`). -/
def SegFromSpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
      (sess : Session (List (BitVec 8))) (R : SepProp) (s0 s : State),
      CurStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r g sess R s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s
        (fun s' => ∃ otr taken pqCap pqPtr,
          OtrStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s')

/-- Segment `segIdentity` (`Otr` → `Key`). -/
def SegIdentitySpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (R : SepProp)
      (s0 s : State),
      OtrStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr R s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s
        (fun s' => ∃ k,
          KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s')

/-- Segment `segSignal` (`Key` → `Cm`, `pendingPreKey = none`). -/
def SegSignalSpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey = none →
      KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CmStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

/-- Segment `segPreKey` (`Key` → `Cm`, `pendingPreKey.isSome`). -/
def SegPreKeySpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (pqCap pqPtr : BitVec 64) (k : IdentityKey)
      (R : SepProp) (s0 s : State),
      sess.pendingPreKey.isSome →
      KeyStateVPlaced kit st0 ikit ist0 Scope ctl encRecord x r sess otr taken pqCap pqPtr k R s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s
        (fun s' => ∃ m otr' pqCap' pqPtr',
          CmStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
            pqCap' pqPtr' R s0 s')

/-- Segment `segTrust` (`Cm` → `Save`). -/
def SegTrustSpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtxPlaced kit ikit H s0 s →
      CmStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s
        (fun s' => SaveStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k
          m otr' pqCap' pqPtr' R s0 s')

/-- Segment `segSave` (`Save` → `Apply`). -/
def SegSaveSpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64) (R : SepProp)
      (s0 s : State),
      ikit.addrOk x.rem.val →
      EncFsCtxPlaced kit ikit H s0 s →
      SaveStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' pqCap'
        pqPtr' R s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s
        (fun s' => ∃ c, ApplyStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr
          taken k m otr' pqCap' pqPtr' c R s0 s')

/-- Segment `segApplyStore` (`Apply` → `Stored`). -/
def SegApplyStoreSpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (pqCap' pqPtr' : BitVec 64)
      (c : IdentityChange) (R : SepProp) (s0 s : State),
      kit.addrOk x.rem.val →
      EncFsCtxPlaced kit ikit H s0 s →
      ApplyStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr'
        pqCap' pqPtr' c R s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s
        (fun s' => StoredStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken
          k m otr' c R s0 s')

/-- Segment `segFinish` (`Stored` → outcome). -/
def SegFinishSpecVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop :=
  EncEnvPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H →
    ∀ (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8)))
      (sess : Session (List (BitVec 8))) (otr : OutgoingTripleRatchet (List (BitVec 8)))
      (taken : SessionState (List (BitVec 8))) (k : IdentityKey) (m : CiphertextMessage)
      (otr' : OutgoingTripleRatchet (List (BitVec 8))) (c : IdentityChange) (R : SepProp)
      (s0 s : State),
      StoredStateVPlaced kit st0 ikit ist0 Scope C ctl parse S encRecord x r sess otr taken k m otr' c R
        s0 s →
      SegExitPlaced kit st0 ikit ist0 C ctl parse S encRecord H x R s0 s (fun _ => False)

/-- All nine `MessageEncrypt` segments on `lsProg_198 H` under `[LibsignalPlacement]`. -/
structure EncSegsVPlaced [LibsignalPlacement] {A : RustAlloc}
    (kit : SessionStoreSpec A 0#64) (st0 : kit.StoreState)
    (ikit : IdentityStoreSpec A 0#64) (ist0 : ikit.IdState)
    (Scope : SessionRecord (List (BitVec 8)) → Prop) (Q : List (BitVec 8) → Prop)
    (C : Crypto) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8))
    (H : LibsignalHooks) : Prop where
  load : SegLoadSpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  fromS : SegFromSpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  identity : SegIdentitySpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  signal : SegSignalSpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  preKey : SegPreKeySpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  trust : SegTrustSpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  save : SegSaveSpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  applyStore : SegApplyStoreSpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H
  finish : SegFinishSpecVPlaced kit st0 ikit ist0 Scope Q C ctl parse S encRecord H

end CryptoVerification.LibsignalPublicApi.MessageEncrypt
