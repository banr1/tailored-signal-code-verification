/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
public import LibsignalBinary.Proofs.E2E.Pqxdh.WireEntries.RecvWireSameAccount
public import LibsignalBinary.Proofs.E2E.Pqxdh.Initiator.SessionStateCallees
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop

/-!
# Stage P3 Spatial Handoff and `initializeRecipientSession` Unpacking Helpers

Spatial re-slicing helpers for the `+0x1cd8#64` and `+0x34dc#64` Stage P3/P4 handoffs, together with
`bobSession344WithRegIdsBv8` unpacking lemmas for `initializeRecipientSession`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.E2E.Pqxdh.ResponderClosure

namespace P3P4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalTripleRatchet.Record.SegDecryptFacts
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

section TryDecryptPqDistinct

def tryDecryptRawSpecP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse : UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { tryDecryptRawSpec C A ctl uuidParse S img with
    pre := fun x s => ⌜x.st.pqRatchetState = [] ∧ s.readReg64 .x0 = x.ret ∧ s.readReg64 .x1 = x.ss ∧
        s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧ s.readReg64 .x4 = x.msgA ∧
        (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧ (x.st.remoteIdentity ≠ some
        x.st.localIdentity ∨ DistinctSid uuidParse x.loc.name.bytes x.rem.name.bytes) ∧ SeedsLen32
        x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s.sp.toNat⌝ ∗ sessionStateAt A x.ss
        x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
        signalMessageAt A x.msgG x.msgA x.msg ∗
      memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗ A.pool }
private def tryDecryptSpecPqP (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (uuidParse :
  UuidParser)
    (S : SpqrModel) (img : Obj.Image) : Spec TryDecryptGhost :=
  { tryDecryptSpec C A ctl uuidParse S img with
    pre := fun x s =>
      ⌜img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗ ⌜x.st.pqRatchetState = [] ∧ s.readReg64 .x0 =
      x.ret ∧ s.readReg64 .x1 = x.ss ∧ s.readReg64 .x2 = x.remA ∧ s.readReg64 .x3 = x.locA ∧
      s.readReg64 .x4 = x.msgA ∧ (s.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
      (x.st.remoteIdentity ≠ some x.st.localIdentity ∨ DistinctSid uuidParse x.loc.name.bytes
      x.rem.name.bytes) ∧ SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤
      s.sp.toNat⌝ ∗ sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
      protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗ memRegion x.ret 48
      ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s.sp rootStack ∗
      A.pool }

private theorem tapeAfter_zero_sa (ctl cur : BitVec 64) (rest : List (BitVec 8)) :
    tapeAt ctl cur rest ⊢ tapeAfter ctl cur rest 0 := by
  unfold tapeAt tapeAfter
  have hcur : cur + BitVec.ofNat 64 0 = cur := by bv_omega
  have hlen : rest.length - 0 = rest.length := Nat.sub_zero _
  rw [hcur, hlen]
  exact Entails.pure_left (fun _ => Entails.refl _)

private theorem seedsLen32_of_pre_pq_P {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost} {R : SepProp} {s0 : State} (hpre :
    s0.mem ⊨ (tryDecryptSpecPqP C A ctl uuidTryParse S img).pre x s0 ∗ R) : x.st.pqRatchetState = []
    ∧ SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  simp only [tryDecryptSpecPqP] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre⟩
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact ⟨hpre.1.1, hpre.1.2.2.2.2.2.2.2.2⟩

end TryDecryptPqDistinct

attribute [local irreducible] Program.fnOff

/-! ## 1. Spatial Bridging Helpers (`+0x1cd8#64` and `+0x34dc#64`) -/

theorem stackAt_root_eq_growOneSpe (sp : BitVec 64) :
    stackAt sp rootStack = memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack)
      ∗ stackAt sp growOneSpeStack :=
  stackAt_split_bottom sp growOneSpeStack (rootStack - growOneSpeStack) (by decide)

theorem stackAt_root_chainClone_eq_growOneSpe (sp : BitVec 64) :
    memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - chainCloneStack) ∗ stackAt sp
      chainCloneStack = memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
      memRegion (sp - BitVec.ofNat 64 growOneSpeStack) (growOneSpeStack - chainCloneStack) ∗ stackAt
      sp chainCloneStack := by
  rw [← stackAt_root_eq_chainClone sp, stackAt_root_eq_growOneSpe sp, stackAt_sub_eq sp
      growOneSpeStack chainCloneStack]

theorem sp3e0_104_240_eq_344 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 104 ∗ memRegion (sp + 0x448#64) 240 = memRegion (sp + 0x3e0#64) 344 :=
      by
  rw [ProofLib.memRegion_split' (b := sp + 0x3e0#64) (n := 104) (k := 240)
        (b' := sp + 0x448#64) rfl (by bv_omega) (by decide)]

theorem sp930_6words_entails_memRegion48 (sp w0 w1 w2 w3 w4 w5 : BitVec 64) :
    ((sp + 0x930#64) ↦₆₄ w0) ∗ ((sp + 0x938#64) ↦₆₄ w1) ∗ ((sp + 0x940#64) ↦₆₄ w2) ∗ ((sp +
    0x948#64) ↦₆₄ w3) ∗ ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ⊢ memRegion (sp +
    0x930#64) 48 := by
  have h := words6_entails_memRegion48 (sp + 0x930#64) w0 w1 w2 w3 w4 w5
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem sp960_6words_entails_memRegion48 (sp w6 w7 w8 w9 w10 w11 : BitVec 64) :
    ((sp + 0x960#64) ↦₆₄ w6) ∗ ((sp + 0x968#64) ↦₆₄ w7) ∗ ((sp + 0x970#64) ↦₆₄ w8) ∗ ((sp +
    0x978#64) ↦₆₄ w9) ∗ ((sp + 0x980#64) ↦₆₄ w10) ∗ ((sp + 0x988#64) ↦₆₄ w11) ⊢ memRegion (sp +
    0x960#64) 48 := by
  have h := words6_entails_memRegion48 (sp + 0x960#64) w6 w7 w8 w9 w10 w11
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

private theorem bv64_eq_append_halves (w : BitVec 64) :
    (w.extractLsb' 32 32 ++ w.extractLsb' 0 32) = w :=
  (_root_.BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' rfl).trans _root_.BitVec.extractLsb'_eq_self

/-- Re-slice 3 contiguous 64-bit words (`cap`, `ptr`, `len`) into the `4 + 8 + 8 + 4`-byte
layout expected by `stageP4_ok` (`ptextHead`, `ptextMid0`, `ptextMid1`, `ptextTail`). -/
theorem words3_eq_p4_ptext_slots (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 0x8#64) ↦₆₄ w1) ∗ ((a + 0x10#64) ↦₆₄ w2) = (a ↦₃₂ w0.extractLsb' 0 32) ∗ ((a
      + 0x4#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) ∗ ((a + 0xc#64) ↦₆₄
      (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) ∗ ((a + 0x14#64) ↦₃₂ w2.extractLsb' 32 32) :=
      by
  have hw0 : (a ↦₆₄ w0) = (a ↦₃₂ w0.extractLsb' 0 32) ∗ ((a + 4#64) ↦₃₂ w0.extractLsb' 32 32) := by
    rw [pointsTo32_pair, bv64_eq_append_halves]
  have hw1 : ((a + 0x8#64) ↦₆₄ w1) = ((a + 0x8#64) ↦₃₂ w1.extractLsb' 0 32) ∗ ((a + 0xc#64) ↦₃₂
      w1.extractLsb' 32 32) := by
    have h : a + 0xc#64 = a + 0x8#64 + 4#64 := by bv_omega
    rw [h, pointsTo32_pair, bv64_eq_append_halves]
  have hw2 : ((a + 0x10#64) ↦₆₄ w2) = ((a + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) ∗ ((a + 0x14#64) ↦₃₂
      w2.extractLsb' 32 32) := by
    have h : a + 0x14#64 = a + 0x10#64 + 4#64 := by bv_omega
    rw [h, pointsTo32_pair, bv64_eq_append_halves]
  have hm0 : ((a + 0x4#64) ↦₃₂ w0.extractLsb' 32 32) ∗ ((a + 0x8#64) ↦₃₂ w1.extractLsb' 0 32) = ((a
      + 0x4#64) ↦₆₄ (w1.extractLsb' 0 32 ++ w0.extractLsb' 32 32)) := by
    have h : a + 0x8#64 = a + 0x4#64 + 4#64 := by bv_omega
    rw [h, pointsTo32_pair]
  have hm1 : ((a + 0xc#64) ↦₃₂ w1.extractLsb' 32 32) ∗ ((a + 0x10#64) ↦₃₂ w2.extractLsb' 0 32) = ((a
      + 0xc#64) ↦₆₄ (w2.extractLsb' 0 32 ++ w1.extractLsb' 32 32)) := by
    have h : a + 0x10#64 = a + 0xc#64 + 4#64 := by bv_omega
    rw [h, pointsTo32_pair]
  rw [hw0, hw1, hw2, ← hm0, ← hm1]
  ac_rfl

theorem sp278_24_to_p4_slots (sp ptCap ptPtr ptLen : BitVec 64) :
    ((sp + 0x278#64) ↦₆₄ ptCap) ∗ ((sp + 0x280#64) ↦₆₄ ptPtr) ∗ ((sp + 0x288#64) ↦₆₄ ptLen) = ((sp +
      0x278#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗ ((sp + 0x27c#64) ↦₆₄ (ptPtr.extractLsb' 0 32 ++
      ptCap.extractLsb' 32 32)) ∗ ((sp + 0x284#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++ ptPtr.extractLsb'
      32 32)) ∗ ((sp + 0x28c#64) ↦₃₂ ptLen.extractLsb' 32 32) := by
  have h := words3_eq_p4_ptext_slots (sp + 0x278#64) ptCap ptPtr ptLen
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

theorem retPtr08_p4_slots_to_words3 (retPtr ptCap ptPtr ptLen : BitVec 64) :
    ((retPtr + 0x8#64) ↦₃₂ ptCap.extractLsb' 0 32) ∗ ((retPtr + 0xc#64) ↦₆₄ (ptPtr.extractLsb' 0 32
    ++ ptCap.extractLsb' 32 32)) ∗ ((retPtr + 0x14#64) ↦₆₄ (ptLen.extractLsb' 0 32 ++
    ptPtr.extractLsb' 32 32)) ∗ ((retPtr + 0x1c#64) ↦₃₂ ptLen.extractLsb' 32 32) = ((retPtr +
    0x8#64) ↦₆₄ ptCap) ∗ ((retPtr + 0x10#64) ↦₆₄ ptPtr) ∗ ((retPtr + 0x18#64) ↦₆₄ ptLen) := by
  have h := (words3_eq_p4_ptext_slots (retPtr + 0x8#64) ptCap ptPtr ptLen).symm
  simpa only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using h

/-- Frame preserved across `stageP3_sub5_dispatch_ok` after `stageP3_tryDecrypt_v4_nopanic_ok`. -/
def stageP3PostTryDecryptFrame (A : RustAlloc) (ctl : BitVec 64) (C : Crypto) (sp : BitVec 64)
    (coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr newLocIdPtr ctxPtr
     remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (sq3 sq4 sq5 : BitVec 128) (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (rest : List (BitVec
    8)) (st : SessionState (List (BitVec 8))) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg
    : SignalMessage) : SepProp :=
  ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  protocolAddressAt A rem remAddrPtr ∗
  protocolAddressAt A loc locAddrPtr ∗
  signalMessageAt A msgG whisperMsgPtr msg ∗
  tapeAfter ctl cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗
  memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - growOneSpeStack) ∗
  ((sp + 0x8#64) ↦₆₄ v08) ∗ ((sp + 0x10#64) ↦₆₄ v10) ∗ ((sp + 0x18#64) ↦₆₄ v18) ∗
  ((sp + 0x24#64) ↦₃₂ v24) ∗ ((sp + 0x28#64) ↦₃₂ v28) ∗ ((sp + 0x2c#64) ↦₃₂ v2c) ∗
  ((sp + 0x30#64) ↦₃₂ f248) ∗ ((sp + 0x34#64) ↦₃₂ f24c) ∗
  ((sp + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((sp + 0x40#64) ↦₆₄ 0#64) ∗
  ((sp + 0x48#64) ↦₆₄ c0) ∗ ((sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗
  ((sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
  ((sp + 0x68#64) ↦₆₄ 33#64) ∗ ((sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
  ((sp + 0x7c#64) ↦₃₂ 4#32) ∗ ((sp + 0x98#64) ↦₆₄ 32#64) ∗
  ((sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((sp + 0xb0#64) ↦₆₄ whisperMsgPtr) ∗
  ((sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗
  ((sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
  ((sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
  ((sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)

/-- Extra frame required at `+0x1778#64` beyond `stageP3_clone_and_tryDecrypt_v4_ok`'s precondition
to execute `stageP3_sub5_dispatch_ok`. -/
def stageP3Sub5ExtraPre (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr : BitVec 64)
    (b_2c0 : BitVec 8) : SepProp :=
  ((s.sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
  ((s.sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗ ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((s.sp + 0x3c8#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x3d0#64) ↦₆₄ initErrsPtr) ∗
  ((s.sp + 0x3d8#64) ↦₆₄ 0#64) ∗ memRegion (s.sp + 0x448#64) 240 ∗
  ((coroPtr + 0xe0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0xe8#64) ↦₆₄ prevStatesPtr) ∗
  ((coroPtr + 0xf0#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  memRegion outPtr 48 ∗ memRegion (s.sp + 0x250#64) 20 ∗ memRegion (s.sp + 0x370#64) 36 ∗
  decryptPrekeySavedRegsAt (s.sp + 0xcd0#64) s0

theorem postTryDecrypt_entails_dispatchPre (A : RustAlloc) (img : Obj.Image) (C : Crypto)
    (ctl : BitVec 64) (S : SpqrModel) (s0 s : State) (coroPtr outPtr initErrsPtr prevStatesPtr
     v08 v10 v18 c0 newRootKeyPtr newRemIdPtr newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr
     cur : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 : BitVec 128) (v24 v28 v2c f248 f24c prevCounter : BitVec 32) (b_2c0 :
    BitVec 8) (rest : List (BitVec 8)) (G' recG : SessionGhost) (st : SessionState (List (BitVec
    8))) (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage) : (sessionStateAt A
    (s.sp + 0xa90#64) G' (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 ∗ vecResultAt
    A (s.sp + 0x270#64) (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 ∗
    sessionStateAt A (coroPtr + 0xf8#64) recG st ∗ protocolAddressAt A rem remAddrPtr ∗
    protocolAddressAt A loc locAddrPtr ∗ signalMessageAt A msgG whisperMsgPtr msg ∗ tapeAfter ctl
    cur rest (decryptDraws C st msg.senderRatchetKey rest) ∗ logOff img ∗ stackAt s.sp rootStack ∗
    A.pool ∗ memRegion (s.sp + 0x3e0#64) 104 ∗ ((s.sp + 0x8#64) ↦₆₄ v08) ∗ ((s.sp + 0x10#64) ↦₆₄
    v10) ∗ ((s.sp + 0x18#64) ↦₆₄ v18) ∗ ((s.sp + 0x24#64) ↦₃₂ v24) ∗ ((s.sp + 0x28#64) ↦₃₂ v28) ∗
    ((s.sp + 0x2c#64) ↦₃₂ v2c) ∗ ((s.sp + 0x30#64) ↦₃₂ f248) ∗ ((s.sp + 0x34#64) ↦₃₂ f24c) ∗ ((s.sp
    + 0x38#64) ↦₆₄ 0xffffffffffffffff#64) ∗ ((s.sp + 0x40#64) ↦₆₄ 0#64) ∗ ((s.sp + 0x48#64) ↦₆₄ c0)
    ∗ ((s.sp + 0x50#64) ↦₆₄ newRootKeyPtr) ∗ ((s.sp + 0x5c#64) ↦₃₂ prevCounter) ∗ ((s.sp + 0x60#64)
    ↦₆₄ newRemIdPtr) ∗ ((s.sp + 0x68#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗ ((s.sp +
    0x7c#64) ↦₃₂ 4#32) ∗ ((s.sp + 0x98#64) ↦₆₄ 32#64) ∗ ((s.sp + 0xa0#64) ↦₆₄ locAddrPtr) ∗ ((s.sp +
    0xb0#64) ↦₆₄ whisperMsgPtr) ∗ ((s.sp + 0xb8#64) ↦₃₂ 4#32) ∗ ((s.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
    ((s.sp + 0xd0#64) ↦₆₄ 33#64) ∗ ((s.sp + 0x3a0#64) ↦₆₄ remAddrPtr) ∗ ((s.sp + 0x3ac#64) ↦₈ 3#8) ∗
    ((s.sp + 0x930#64) ↦₆₄ sq0.extractLsb' 0 64) ∗ ((s.sp + 0x938#64) ↦₆₄ sq0.extractLsb' 64 64) ∗
    ((s.sp + 0x940#64) ↦₆₄ sq1.extractLsb' 0 64) ∗ ((s.sp + 0x948#64) ↦₆₄ sq1.extractLsb' 64 64) ∗
    ((s.sp + 0x950#64) ↦₆₄ sq2.extractLsb' 0 64) ∗ ((s.sp + 0x958#64) ↦₆₄ sq2.extractLsb' 64 64) ∗
    ((s.sp + 0x960#64) ↦₆₄ sq3.extractLsb' 0 64) ∗ ((s.sp + 0x968#64) ↦₆₄ sq3.extractLsb' 64 64) ∗
    ((s.sp + 0x970#64) ↦₆₄ sq4.extractLsb' 0 64) ∗ ((s.sp + 0x978#64) ↦₆₄ sq4.extractLsb' 64 64) ∗
    ((s.sp + 0x980#64) ↦₆₄ sq5.extractLsb' 0 64) ∗ ((s.sp + 0x988#64) ↦₆₄ sq5.extractLsb' 64 64)) ∗
    stageP3Sub5ExtraPre s0 s coroPtr outPtr initErrsPtr prevStatesPtr b_2c0 ⊢ stageP3DispatchPre A
    img.base s0 s coroPtr outPtr initErrsPtr prevStatesPtr
      (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).1 b_2c0 G' recG
      (pqxdhTryDecryptModel C S uuidTryParse rem loc msg rest st).2 st ∗ stageP3PostTryDecryptFrame
      A ctl C s.sp coroPtr v08 v10 v18 c0 newRootKeyPtr newRemIdPtr
      newLocIdPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur sq3 sq4 sq5 v24 v28 v2c f248 f24c
      prevCounter rest st rem loc msgG msg := by
  unfold stageP3Sub5ExtraPre stageP3DispatchPre stageP3PostTryDecryptFrame
  rw [logOff_eq_5b810 img, stackAt_root_eq_growOneSpe s.sp, ← sp3e0_104_240_eq_344 s.sp]
  have h930 := sp930_6words_entails_memRegion48 s.sp
    (sq0.extractLsb' 0 64) (sq0.extractLsb' 64 64) (sq1.extractLsb' 0 64) (sq1.extractLsb' 64 64)
    (sq2.extractLsb' 0 64) (sq2.extractLsb' 64 64)
  exact entails_replace_sub h930 (by sep_focus) (eq_of_sep_emp (by sep_focus))

/-! ## 2. `bobSession344WithRegIdsBv8` Layout Definitions -/

/-- Middle 280 bytes (`+0x38..+0x150`) of `bobSession344Bv8`. -/
def bobSession280MidBv8 (rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) : List (BitVec 8) :=
  unpack64 rootKeyBoxPtr ++ unpack64 32#64 ++
  unpack64 0#64 ++ unpack64 8#64 ++ unpack64 0#64 ++
  unpack64 33#64 ++ unpack64 baseKeyBoxPtr ++ unpack64 33#64 ++
  unpack64 spqrCap ++ unpack64 spqrBufPtr ++ unpack64 0#64 ++
  Initiator.senderChainBytes100 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ++
  unpack32 pad_f4 ++ unpack64 0xffffffffffffffff#64 ++
  unpack64 c0 ++ unpack64 c1 ++ unpack64 c2 ++ unpack64 c3 ++ unpack64 c4 ++
  unpack64 0xffffffffffffffff#64 ++
  unpack64 d0 ++ unpack64 d1 ++ unpack64 d2 ++
  unpack64 4#64

@[simp]
theorem bobSession280MidBv8_length (p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64) :
    (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2).length = 280 := by
  unfold bobSession280MidBv8 Initiator.senderChainBytes100
  simp only [List.length_append, unpack64_length, unpack32_length]

/-- 344-byte `SessionState` with `remoteRegId` at `+0x150` and `localRegId` at `+0x154`. -/
def bobSession344WithRegIdsBv8 (localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr
    spqrCap spqrBufPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) : List (BitVec 8) :=
  unpack64 33#64 ++ unpack64 localIkBoxPtr ++ unpack64 33#64 ++
  unpack64 33#64 ++ unpack64 remoteIkBoxPtr ++ unpack64 33#64 ++
  unpack64 32#64 ++
  bobSession280MidBv8 rootKeyBoxPtr baseKeyBoxPtr spqrCap spqrBufPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
  unpack32 remoteRegId ++ unpack32 localRegId

@[simp]
theorem bobSession344WithRegIdsBv8_length (p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) :
    (bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
      remoteRegId localRegId).length = 344 := by
  unfold bobSession344WithRegIdsBv8
  simp only [List.length_append, unpack64_length, unpack32_length, bobSession280MidBv8_length]

theorem bobSession344WithRegIds_fold (a p1 p2 p3 p4 c5 p5 p6 p7 p8 : BitVec 64)
    (pad_f4 : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 : BitVec 64)
    (remoteRegId localRegId : BitVec 32) :
    (a ↦₆₄ 33#64) ∗ ((a + 0x8#64) ↦₆₄ p1) ∗ ((a + 0x10#64) ↦₆₄ 33#64) ∗
    ((a + 0x18#64) ↦₆₄ 33#64) ∗ ((a + 0x20#64) ↦₆₄ p2) ∗ ((a + 0x28#64) ↦₆₄ 33#64) ∗
    ((a + 0x30#64) ↦₆₄ 32#64) ∗
    ((a + 0x38#64) ↦ₛ bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ∗
    ((a + 0x150#64) ↦₃₂ remoteRegId) ∗ ((a + 0x154#64) ↦₃₂ localRegId) =
      (a ↦ₛ bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        remoteRegId localRegId) := by
  have hfold :
      bobSession344WithRegIdsBv8 p1 p2 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
        remoteRegId localRegId =
      unpack64 33#64 ++ (unpack64 p1 ++ (unpack64 33#64 ++
      (unpack64 33#64 ++ (unpack64 p2 ++ (unpack64 33#64 ++
      (unpack64 32#64 ++ (bobSession280MidBv8 p3 p4 c5 p5 p6 p7 p8 pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 ++
      (unpack32 remoteRegId ++ unpack32 localRegId)))))))) := by
    unfold bobSession344WithRegIdsBv8
    simp only [List.append_assoc]
  rw [hfold,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, unpack64_length,
      pointsToBytes_append, bobSession280MidBv8_length,
      pointsToBytes_append, unpack32_length,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
      ← pointsTo64_eq_pointsToBytes,
      ← pointsTo32_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 3. `bobSession344WithRegIdsBv8` Unpacking and `initializeRecipientSession` Bridge -/

def mkBobSenderChainGhost (ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64)
    (spkPubBytes spkPrivBytes : List (BitVec 8)) : SenderChainGhost :=
  { srk := ⟨33#64, ratchetPubBoxPtr, spkPubBytes⟩, priv := ⟨32#64, ratchetPrivBoxPtr, spkPrivBytes⟩,
    mkCap := 0#64, mkPtr := 8#64, ck := ⟨32#64, chainKeyBoxPtr⟩ }

theorem vecGhostAt_of_box {A : RustAlloc} (hdrPtr boxPtr cap : BitVec 64) (n : Nat) (bs : List
  (BitVec 8))
    (hptr : boxPtr ≠ 0#64) (hcap0 : cap ≠ 0) (hcap : cap.toNat = n) (hcap2 : BitVec.ofNat 64 n =
    cap) (hlen : bs.length = n) (hlt : n < 2 ^ 63) : (hdrPtr ↦₆₄ cap) ∗ ((hdrPtr + 8#64) ↦₆₄ boxPtr)
    ∗ ((hdrPtr + 16#64) ↦₆₄ cap) ∗ A.live boxPtr n 1 ∗ (boxPtr ↦ₛ bs) ⊢ vecGhostAt A ⟨cap, boxPtr,
    bs⟩ hdrPtr := by
  unfold vecGhostAt vecU8At vecHeader
  simp only [hlen, hcap, hcap2, hcap0, ↓reduceIte, Nat.sub_self, ProofLib.memRegion_zero,
    sepConj_emp]
  exact Entails.trans (Entails.of_eq (by ac_rfl))
    (sepConj_mono_right (Entails.pure_right ⟨Nat.le_refl _, hlt, hptr⟩ (Entails.refl _)))

theorem bobSenderChain_entails_optSenderChainAt {A : RustAlloc}
    (coroPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64) (spkPubBytes
    spkPrivBytes chainKeyBytes : List (BitVec 8)) (pad_f4 : BitVec 32) (sc : SenderChain) (hrat_pub
    : ratchetPubBoxPtr ≠ 0#64) (hrat_priv : ratchetPrivBoxPtr ≠ 0#64) (hck_ptr : chainKeyBoxPtr ≠
    0#64) (hspk_pub_len : spkPubBytes.length = 33) (hspk_priv_len : spkPrivBytes.length = 32)
    (hspk_deser : PublicKey.deserialize spkPubBytes = .ok sc.ratchetKey.publicKey) (hspk_priv_eq :
    spkPrivBytes = sc.ratchetKey.privateKey.bytes.toList) (hspk_clamp : Ratchet.clampScalar
    sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) (hck_eq : chainKeyBytes =
    keyToBytes32 sc.chainKey.key) (hck_idx : sc.chainKey.index = 0#32) :
    (Initiator.senderChainFieldsAt (coroPtr + 0xf8#64) ratchetPubBoxPtr ratchetPrivBoxPtr
    chainKeyBoxPtr 0#32 ∗ ((coroPtr + 0x1ec#64) ↦₃₂ pad_f4) ∗ (ratchetPubBoxPtr ↦ₛ spkPubBytes) ∗
    A.live ratchetPubBoxPtr 33 1 ∗ (ratchetPrivBoxPtr ↦ₛ spkPrivBytes) ∗ A.live ratchetPrivBoxPtr 32
    1 ∗ (chainKeyBoxPtr ↦ₛ chainKeyBytes) ∗ A.live chainKeyBoxPtr 32 1) ⊢ optSenderChainAt A
    (coroPtr + 0x188#64)
      (some (mkBobSenderChainGhost ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spkPubBytes
      spkPrivBytes)) (some sc) := by
  have hsub0 : ∀ a b : BitVec 64, coroPtr + a + b = coroPtr + (a + b) := fun a b => by bv_omega
  have hsrk := vecGhostAt_of_box (A := A) (coroPtr + 0x188#64) ratchetPubBoxPtr 33#64 33 spkPubBytes
    hrat_pub (by decide) rfl rfl hspk_pub_len (by decide)
  have hpriv := vecGhostAt_of_box (A := A) (coroPtr + 0x1a0#64) ratchetPrivBoxPtr 32#64 32
    spkPrivBytes
    hrat_priv (by decide) rfl rfl hspk_priv_len (by decide)
  have hck_vec := vecGhostAt_of_box (A := A) (coroPtr + 0x1d0#64) chainKeyBoxPtr 32#64 32
    (keyToBytes32 sc.chainKey.key) hck_ptr (by decide) rfl rfl (length_keyToBytes32 _) (by decide)
  have hmk :
      ((coroPtr + 0x1b8#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x1c0#64) ↦₆₄ 8#64) ∗ ((coroPtr + 0x1c8#64) ↦₆₄
      0#64) ⊢ vecAt A 104 8 (messageKeyAt A) (coroPtr + 0x1b8#64) 0#64 8#64 [] := by
    unfold vecAt vecHeader vecBuf
    simp only [hsub0, BitVec.reduceAdd, List.length_nil, ↓reduceIte]
    rw [← sepConj_emp (((coroPtr + 0x1b8#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x1c0#64) ↦₆₄ 8#64) ∗ ((coroPtr
      + 0x1c8#64) ↦₆₄ 0#64))]
    exact Entails.trans (Entails.of_eq (by ac_rfl))
      (sepConj_mono_right (Entails.pure_right ⟨by decide, by decide, by decide⟩ (Entails.refl _)))
  have hpad := pointsTo32_entails_memRegion (coroPtr + 0x1ec#64) pad_f4
  unfold optSenderChainAt optChainKeyAt mkBobSenderChainGhost Initiator.senderChainFieldsAt
  refine Entails.pure_right ⟨hspk_deser, hspk_priv_eq, hspk_clamp, hspk_pub_len⟩ ?_
  rw [hck_eq, ← hck_idx]
  simp only [hsub0, BitVec.reduceAdd] at hsrk hpriv hck_vec ⊢
  refine Entails.trans (entails_replace_sub hsrk (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hpriv (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hmk (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub hck_vec (by sep_focus) rfl) ?_
  exact entails_replace_sub hpad (by sep_focus) (eq_of_sep_emp (by unfold vecGhostAt; sep_focus))

theorem bobSession280Mid_entails_fields (coroPtr rootKeyBoxPtr baseKeyBoxPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr : BitVec 64) (pad_f4 : BitVec 32) (c0 c1 c2 c3
    c4 d0 d1 d2 : BitVec 64) : ((coroPtr + 0x130#64) ↦ₛ bobSession280MidBv8 rootKeyBoxPtr
    baseKeyBoxPtr 0#64 1#64
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2) ⊢ ((coroPtr
      + 0x130#64) ↦₆₄ rootKeyBoxPtr) ∗ ((coroPtr + 0x138#64) ↦₆₄ 32#64) ∗ ((coroPtr + 0x140#64) ↦₆₄
      0#64) ∗ ((coroPtr + 0x148#64) ↦₆₄ 8#64) ∗ ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗ ((coroPtr +
      0x158#64) ↦₆₄ 33#64) ∗ ((coroPtr + 0x160#64) ↦₆₄ baseKeyBoxPtr) ∗ ((coroPtr + 0x168#64) ↦₆₄
      33#64) ∗ ((coroPtr + 0x170#64) ↦₆₄ 0#64) ∗ ((coroPtr + 0x178#64) ↦₆₄ 1#64) ∗ ((coroPtr +
      0x180#64) ↦₆₄ 0#64) ∗ Initiator.senderChainFieldsAt (coroPtr + 0xf8#64) ratchetPubBoxPtr
      ratchetPrivBoxPtr chainKeyBoxPtr 0#32 ∗ ((coroPtr + 0x1ec#64) ↦₃₂ pad_f4) ∗ ((coroPtr +
      0x1f0#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x1f8#64) 40 ∗ ((coroPtr +
      0x220#64) ↦₆₄ 0xffffffffffffffff#64) ∗ memRegion (coroPtr + 0x228#64) 24 ∗ ((coroPtr +
      0x240#64) ↦₃₂ 4#32) ∗ ((coroPtr + 0x244#64) ↦₃₂ 0#32) := by
  have h4 : unpack64 4#64 = unpack32 4#32 ++ unpack32 0#32 := by decide
  have hsc_addr : (coroPtr + 0xf8#64) + 0x90#64 = coroPtr + 0x188#64 := by bv_omega
  have hsc_eq :
      Initiator.senderChainFieldsAt (coroPtr + 0xf8#64) ratchetPubBoxPtr ratchetPrivBoxPtr
      chainKeyBoxPtr 0#32 = ((coroPtr + 0x188#64) ↦ₛ Initiator.senderChainBytes100 ratchetPubBoxPtr
      ratchetPrivBoxPtr chainKeyBoxPtr 0#32) := by
    rw [Initiator.senderChainFieldsAt_eq_pointsToBytes, hsc_addr]
  rw [hsc_eq]; unfold bobSession280MidBv8; rw [h4]
  simp only [List.append_assoc, pointsToBytes_append, unpack64_length, unpack32_length,
    Initiator.senderChainBytes100_length, BitVec.add_assoc, BitVec.reduceAdd, ←
    pointsTo64_eq_pointsToBytes, ← pointsTo32_eq_pointsToBytes, sepConj_assoc]
  have hc40 :
      ((coroPtr + 0x1f8#64) ↦₆₄ c0) ∗ ((coroPtr + 0x200#64) ↦₆₄ c1) ∗ ((coroPtr + 0x208#64) ↦₆₄ c2)
      ∗ ((coroPtr + 0x210#64) ↦₆₄ c3) ∗ ((coroPtr + 0x218#64) ↦₆₄ c4) ⊢ memRegion (coroPtr +
      0x1f8#64) 40 := by
    rw [(ProofLib.memRegion_cells (coroPtr + 0x1f8#64) 5 (by decide) : memRegion (coroPtr +
      0x1f8#64) 40 = cells (coroPtr + 0x1f8#64) 5)]
    simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right c0 (Entails.sepExists_right c1
      (Entails.sepExists_right c2 (Entails.sepExists_right c3 (Entails.sepExists_right c4
      (Entails.refl _)))))
  have hd24 :
      ((coroPtr + 0x228#64) ↦₆₄ d0) ∗ ((coroPtr + 0x230#64) ↦₆₄ d1) ∗ ((coroPtr + 0x238#64) ↦₆₄ d2)
      ⊢ memRegion (coroPtr + 0x228#64) 24 := by
    rw [(ProofLib.memRegion_cells (coroPtr + 0x228#64) 3 (by decide) : memRegion (coroPtr +
      0x228#64) 24 = cells (coroPtr + 0x228#64) 3)]
    simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.sepExists_right d0 (Entails.sepExists_right d1 (Entails.sepExists_right d2
      (Entails.refl _)))
  refine Entails.trans (entails_replace_sub hc40 (by sep_focus) rfl) ?_
  exact entails_replace_sub hd24 (by sep_focus) (eq_of_sep_emp (by sep_focus))

def stageP3InitSessionPre (A : RustAlloc) (sp coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
    baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr u_38 u_40 u_48 u_50 u_60
    u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (pad_f4 remoteRegId localRegId u_30 u_34 u_5c u_7c : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 :
    BitVec 64) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes spkPubBytes spkPrivBytes
    chainKeyBytes : List (BitVec 8)) : SepProp :=
  A.pool ∗ stackAt sp chainCloneStack ∗ memRegion (sp + 0x3e0#64) 104 ∗
  ((coroPtr + 0xf8#64) ↦ₛ bobSession344WithRegIdsBv8 localIkBoxPtr remoteIkBoxPtr
    rootKeyBoxPtr baseKeyBoxPtr 0#64 1#64 ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4
    c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId) ∗
  (localIkBoxPtr ↦ₛ locIdBytes) ∗ A.live localIkBoxPtr 33 1 ∗
  (remoteIkBoxPtr ↦ₛ remIdBytes) ∗ A.live remoteIkBoxPtr 33 1 ∗
  (rootKeyBoxPtr ↦ₛ rootKeyBytes) ∗ A.live rootKeyBoxPtr 32 1 ∗
  (baseKeyBoxPtr ↦ₛ aliceBaseBytes) ∗ A.live baseKeyBoxPtr 33 1 ∗
  (ratchetPubBoxPtr ↦ₛ spkPubBytes) ∗ A.live ratchetPubBoxPtr 33 1 ∗
  (ratchetPrivBoxPtr ↦ₛ spkPrivBytes) ∗ A.live ratchetPrivBoxPtr 32 1 ∗
  (chainKeyBoxPtr ↦ₛ chainKeyBytes) ∗ A.live chainKeyBoxPtr 32 1 ∗
  ((sp + 0x30#64) ↦₃₂ u_30) ∗ ((sp + 0x34#64) ↦₃₂ u_34) ∗ ((sp + 0x38#64) ↦₆₄ u_38) ∗ ((sp +
    0x40#64) ↦₆₄ u_40) ∗
  ((sp + 0x48#64) ↦₆₄ u_48) ∗ ((sp + 0x50#64) ↦₆₄ u_50) ∗ ((sp + 0x5c#64) ↦₃₂ u_5c) ∗ ((sp +
    0x60#64) ↦₆₄ u_60) ∗
  ((sp + 0x68#64) ↦₆₄ u_68) ∗ ((sp + 0x70#64) ↦₆₄ u_70) ∗ ((sp + 0x7c#64) ↦₃₂ u_7c) ∗ ((sp +
    0x98#64) ↦₆₄ u_98) ∗
  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗ ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  ((sp + 0x930#64) ↦₆₄ u930) ∗ ((sp + 0x938#64) ↦₆₄ u938) ∗ ((sp + 0x940#64) ↦₆₄ u940) ∗ ((sp +
    0x948#64) ↦₆₄ u948) ∗
  ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960) ∗ ((sp +
    0x968#64) ↦₆₄ u968) ∗
  ((sp + 0x970#64) ↦₆₄ u970) ∗ ((sp + 0x978#64) ↦₆₄ u978) ∗ ((sp + 0x980#64) ↦₆₄ u980) ∗ ((sp +
    0x988#64) ↦₆₄ u988)

theorem stageP3InitSessionPre_entails_clonePre {A : RustAlloc}
    (sp coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
     baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr u_38 u_40 u_48 u_50 u_60
     u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 : BitVec 64)
    (pad_f4 remoteRegId localRegId u_30 u_34 u_5c u_7c : BitVec 32) (c0 c1 c2 c3 c4 d0 d1 d2 :
    BitVec 64) (locIdBytes remIdBytes rootKeyBytes aliceBaseBytes spkPubBytes spkPrivBytes
    chainKeyBytes : List (BitVec 8)) (sc : SenderChain) (hrat_pub : ratchetPubBoxPtr ≠ 0#64)
    (hrat_priv : ratchetPrivBoxPtr ≠ 0#64) (hck_ptr : chainKeyBoxPtr ≠ 0#64) (hspk_pub_len :
    spkPubBytes.length = 33) (hspk_priv_len : spkPrivBytes.length = 32) (hspk_deser :
    PublicKey.deserialize spkPubBytes = .ok sc.ratchetKey.publicKey) (hspk_priv_eq : spkPrivBytes =
    sc.ratchetKey.privateKey.bytes.toList) (hspk_clamp : Ratchet.clampScalar
    sc.ratchetKey.privateKey.bytes = sc.ratchetKey.privateKey.bytes) (hck_eq : chainKeyBytes =
    keyToBytes32 sc.chainKey.key) (hck_idx : sc.chainKey.index = 0#32) : stageP3InitSessionPre A sp
    coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr
      baseKeyBoxPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr ctxPtr u_38 u_40 u_48 u_50
      u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978 u980 u988 pad_f4
      remoteRegId localRegId u_30 u_34 u_5c u_7c c0 c1 c2 c3 c4 d0 d1 d2 locIdBytes remIdBytes
      rootKeyBytes aliceBaseBytes spkPubBytes spkPrivBytes chainKeyBytes ⊢ stageP3ClonePre A sp
      coroPtr localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr ctxPtr
      u_38 u_40 u_48 u_50 u_60 u_68 u_70 u_98 u_d0 u930 u938 u940 u948 u950 u958 u960 u968 u970 u978
      u980 u988 0#32 remoteRegId localRegId u_30 u_34 u_5c u_7c (mkBobSenderChainGhost
      ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spkPubBytes spkPrivBytes) sc locIdBytes
      remIdBytes rootKeyBytes aliceBaseBytes ∗ bobCoroRestAt A coroPtr localIkBoxPtr remoteIkBoxPtr
      rootKeyBoxPtr baseKeyBoxPtr := by
  have hfold := (bobSession344WithRegIds_fold (coroPtr + 0xf8#64)
    localIkBoxPtr remoteIkBoxPtr rootKeyBoxPtr baseKeyBoxPtr 0#64 1#64 ratchetPubBoxPtr
    ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2 remoteRegId localRegId).symm
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hfold
  unfold stageP3InitSessionPre stageP3ClonePre bobCoroRestAt; rw [hfold]
  have hmid := bobSession280Mid_entails_fields coroPtr rootKeyBoxPtr baseKeyBoxPtr
    ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr pad_f4 c0 c1 c2 c3 c4 d0 d1 d2
  have hsc := bobSenderChain_entails_optSenderChainAt (A := A)
    coroPtr ratchetPubBoxPtr ratchetPrivBoxPtr chainKeyBoxPtr spkPubBytes spkPrivBytes chainKeyBytes
    pad_f4 sc hrat_pub hrat_priv hck_ptr hspk_pub_len hspk_priv_len hspk_deser hspk_priv_eq
    hspk_clamp hck_eq hck_idx
  refine Entails.trans (entails_replace_sub hmid (by sep_focus) rfl) ?_
  exact entails_replace_sub hsc (by sep_focus) (eq_of_sep_emp (by sep_focus))

end P3P4

end CryptoVerification.E2E.Pqxdh.ResponderClosure
