/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.Defs
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionLenAux.StepsBack
import LibsignalBinary.Proofs.SignalSession.Cli.Run.Proofs.Initiate.StoreCallees.SerializeExt.SessionLenAux.StepsChains
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

@[expose] public section

set_option autoImplicit false

/-!
# `<SessionStructure as prost::Message>::encoded_len`

Sums the protobuf field lengths of a 344-byte `SessionStructure` (`sessionStateAt`):
scalar `u32`/`bytes` fields, `sender_chain` (`+0x90`) and `receiver_chains` (`+0x48`) via
`Chain::encoded_len`, and inlined `PendingPreKey` (`+0xf8`) and `PendingKyberPreKey` (`+0x128`).
-/

namespace CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
open CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet hiding stackAt_split_cells memRegion_eight allocFailedIn_of_eq memRegion_cells
open CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt.SessionLenAux

private def pendingTailLen (opt : Option TailVecGhost) : Prop :=
  match opt with | none => True | some g => g.tail.length = 24

private def kyberTailLen (opt : Option TailVecGhost) : Prop :=
  match opt with | none => True | some g => g.tail.length = 8

private def tailLensPure (G : SessionGhost) : SepProp :=
  ⌜pendingTailLen G.pending⌝ ∗ ⌜kyberTailLen G.kyber⌝

private theorem optTailVecAt_pending_eq' (A : RustAlloc) (a : BitVec 64)
    (opt : Option TailVecGhost) (m : Option PendingPreKey) :
    PendingRel opt m →
    optTailVecAt A 48 a opt = ⌜pendingTailLen opt⌝ ∗ pendingUnpacked A a opt m := by
  intro hrel
  rw [optTailVecAt_pending_eq A a opt m hrel]
  cases opt <;> rfl

private theorem optTailVecAt_kyber_eq' (A : RustAlloc) (a : BitVec 64)
    (opt : Option TailVecGhost) (m : Option PendingKyberPreKey) :
    KyberRel opt m →
    optTailVecAt A 32 a opt = ⌜kyberTailLen opt⌝ ∗ kyberUnpacked A a opt m := by
  intro hrel
  rw [optTailVecAt_kyber_eq A a opt m hrel]
  cases opt <;> rfl

/-- Fully unpacked heap body of `sessionStateAt` with `pendingUnpacked` and `kyberUnpacked`. -/
private def sessionFullUnpacked (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8))) : SepProp :=
  tags1to5Cells ss G s ∗
  optSenderChainAt A (ss + 144#64) G.sender s.state.senderChain ∗
  (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
   ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip s.state.receiverChains).length) ∗
   vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip s.state.receiverChains)) ∗
  pendingUnpacked A (ss + 248#64) G.pending s.pendingPreKey ∗
  tags10to15Cells ss s ∗
  kyberUnpacked A (ss + 296#64) G.kyber s.pendingKyberPreKey ∗
  sessionUnused A ss G s ∗
  tailLensPure G

private theorem sessionBodyUnpacked_eq (A : RustAlloc) (ss : BitVec 64) (G : SessionGhost)
    (s : Session (List (BitVec 8)))
    (hpending : PendingRel G.pending s.pendingPreKey)
    (hkyber : KyberRel G.kyber s.pendingKyberPreKey) :
    sessionBodyUnpacked A ss G s = sessionFullUnpacked A ss G s := by
  unfold sessionBodyUnpacked sessionFullUnpacked tailLensPure
  rw [optTailVecAt_pending_eq' A (ss + 248#64) G.pending s.pendingPreKey hpending,
      optTailVecAt_kyber_eq' A (ss + 296#64) G.kyber s.pendingKyberPreKey hkyber]
  ac_rfl

private theorem sp_sub64_aligned {sp : BitVec 64} (h : sp &&& 15#64 = 0#64) :
    ((sp - 64#64) &&& 15#64 == 0#64) = true := by
  have hmod : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    rw [BitVec.toNat_and, show (15#64).toNat = 2 ^ 4 - 1 from rfl,
        Nat.and_two_pow_sub_one_eq_mod]
  have h0 : sp.toNat % 16 = 0 := by
    have := congrArg BitVec.toNat h
    simpa [hmod] using this
  rw [beq_iff_eq]
  apply BitVec.eq_of_toNat_eq
  have := sp.isLt
  simp only [hmod, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub]
  omega

/-- `<SessionStructure as prost::Message>::encoded_len` satisfies `sessionLenSpec`,
given `Chain::encoded_len` (`chainLenSpec`). -/
theorem sessionLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State))
    (hchain : OkAtExt b ext chainLenName (chainLenSpec A)) :
    OkAtExt b ext sessionLenName (sessionLenSpec A) := by
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, G, m⟩ R s0 hpc0 hrun0 hpre hsp0
  have halign0 : s0.sp &&& 15#64 = 0#64 := by
    simp only [State.spAligned, beq_iff_eq] at hsp0; exact hsp0
  have halign0_b : (s0.sp &&& 15#64 == 0#64) = true := hsp0
  dsimp only [sessionLenSpec, sessionStateReprAt, sessionStateAt] at hpre
  rw [stackAt_sessionLen_eq] at hpre
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨v64, v56, v48, v40, v32, v24, v16, v8, ⟨hx0, hfit⟩,
    ⟨hpending, hkyber, halice, hrem_id, hloc_id⟩,
    ⟨hlik, hrik, hchains, hpendsome, hreg_len, hlik33, hrik33⟩, hpre⟩
  have hbody :
      (vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        vecU8At A (ss + 0x30#64) G.root.cap G.root.ptr (HMAC.keyToBytes32 m.state.rootKey) ∗
        vecAt A 104 8 (chainAt A) (ss + 0x48#64) G.chainsCap G.chainsPtr
          (G.chains.zip m.state.receiverChains) ∗
        vecGhostAt A G.alice (ss + 0x60#64) ∗
        vecU8At A (ss + 0x78#64) G.pq.cap G.pq.ptr m.state.pqRatchetState ∗
        optSenderChainAt A (ss + 0x90#64) G.sender m.state.senderChain ∗
        optTailVecAt A 48 (ss + 0xf8#64) G.pending ∗
        optTailVecAt A 32 (ss + 0x128#64) G.kyber ∗
        ((ss + 0x148#64) ↦₃₂ m.state.sessionVersion) ∗ ((ss + 0x14c#64) ↦₃₂ m.state.previousCounter) ∗
        ((ss + 0x150#64) ↦ₛ G.regIds)) =
      sessionFullUnpacked A ss G m := by
    rw [sessionStateAt_body_eq A ss G m halice hreg_len hrem_id hloc_id,
        sessionBodyUnpacked_eq A ss G m hpending hkyber]
  let P0 : SepProp :=
    sessionFullUnpacked A ss G m ∗
    stackAt (s0.sp - 64#64) chainLenStack ∗
    frameCells s0.sp v64 v56 v48 v40 v32 v24 v16 v8 ∗ R
  have hpre' : s0.mem ⊨ P0 := by
    dsimp only [P0]
    rw [← hbody]
    convert hpre using 1; ac_rfl
  have hfit_eq := encSessionMem_length_eq G m
  refine ⟨P0, emp, by rw [sepConj_emp]; exact hpre', ?_⟩
  let FrSave : SepProp :=
    frameCells s0.sp (s0.readReg64 .fp) (s0.readReg64 .lr)
      (s0.readReg64 .x24) (s0.readReg64 .x23)
      (s0.readReg64 .x22) (s0.readReg64 .x21)
      (s0.readReg64 .x20) (s0.readReg64 .x19)
  let P : SepProp :=
    sessionFullUnpacked A ss G m ∗
    stackAt (s0.sp - 64#64) chainLenStack ∗
    FrSave ∗ R
  have hP0 : P0 = (tags1to5Cells ss G m ∗ frameCells s0.sp v64 v56 v48 v40 v32 v24 v16 v8) ∗
      (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ R) := by
    dsimp only [P0, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f1 b ext ss s0.sp v64 v56 v48 v40 v32 v24 v16 v8 G m
    (by omega) hpc0 hrun0 rfl halign0 hx0 hP0 ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hx19_1 hx8_1 hx9_1 hcs1
  have hP_f1 : ((tags1to5Cells ss G m ∗ FrSave) ∗
      (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ R)) = P := by
    dsimp only [P, FrSave, sessionFullUnpacked]; ac_rfl
  rw [hP_f1]
  have hP_1to5 : P = tags1to5Cells ss G m ∗
      (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f2 b ext ss G m
    (uint32Field 1 m.state.sessionVersion).length
    (by omega) hpc1 hrun1 hx19_1 hx8_1 hx9_1 hP_1to5 ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hx19_2 hx8_2 hx9_2 hcs2
  refine step_sessLen_f3 b ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length)
    (by omega) hpc2 hrun2 hx19_2 hx8_2 hx9_2 hP_1to5 ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hx19_3 hx8_3 hcs3
  refine step_sessLen_f4 b ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length)
    (by omega) hpc3 hrun3 hx19_3 hx8_3 hP_1to5 ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hx19_4 hx20_4 hcs4
  have hsp4' : s4.sp = s0.sp - 64#64 := by reg_chain
  have hsp4_align : s4.spAligned = true := by
    simp only [State.spAligned, hsp4']
    exact sp_sub64_aligned halign0
  have hP_f5 : P = (optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
      stackAt s4.sp chainLenStack) ∗
      (tags1to5Cells ss G m ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗ FrSave ∗ R) := by
    rw [hsp4']; dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f5 b A ext hchain ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length)
    (by omega) (by omega) hpc4 hrun4 hsp4_align hx19_4 hx20_4 hP_f5 ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hx19_5 hx21_5 hcs5
  have hsp5' : s5.sp = s0.sp - 64#64 := by reg_chain
  have hsp5_align : s5.spAligned = true := by simpa only [State.spAligned, hsp5] using hsp4_align
  have hP_f6 : P = (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
      ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
      vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains) ∗
      stackAt s5.sp chainLenStack) ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗ FrSave ∗ R) := by
    rw [hsp5']; dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f6 b A ext hchain ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length)
    (by omega) hpc5 hrun5 hsp5_align hx19_5 hx21_5 hP_f6 ?_
  intro s6 hpc6 hrun6 hsp6 htr6 hx19_6 hx8_6 hcs6
  have hP_f7 : P = pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       tags10to15Cells ss m ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f7 b A ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains))
    hpending (by omega) hpc6 hrun6 hx19_6 hx8_6 hP_f7 ?_
  intro s7 hpc7 hrun7 hsp7 htr7 hx19_7 hx8_7 hcs7
  have hP_10to15 : P = tags10to15Cells ss m ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f8 b ext ss m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length)
    (by omega) hpc7 hrun7 hx19_7 hx8_7 hP_10to15 ?_
  intro s8 hpc8 hrun8 hsp8 htr8 hx19_8 hx8_8 hcs8
  refine step_sessLen_f9 b ext ss m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length)
    (by omega) hpc8 hrun8 hx19_8 hx8_8 hP_10to15 ?_
  intro s9 hpc9 hrun9 hsp9 htr9 hx19_9 hx8_9 hcs9
  refine step_sessLen_f10 b ext ss m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length +
     (uint32Field 11 m.localRegistrationId).length)
    (by omega) hpc9 hrun9 hx19_9 hx8_9 hP_10to15 ?_
  intro s10 hpc10 hrun10 hsp10 htr10 hx19_10 hx8_10 hcs10
  have hP_f11 : P = kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       tags10to15Cells ss m ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ FrSave ∗ R) := by
    dsimp only [P, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f11 b A ext ss G m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length +
     (uint32Field 11 m.localRegistrationId).length +
     (bytesField 13 m.aliceBaseKey).length)
    hkyber (by omega) hpc10 hrun10 hx19_10 hx8_10 hP_f11 ?_
  intro s11 hpc11 hrun11 hsp11 htr11 hx19_11 hx8_11 hcs11
  have hP_f12 : P = (tags10to15Cells ss m ∗ FrSave) ∗
      (tags1to5Cells ss G m ∗
       optSenderChainAt A (ss + 144#64) G.sender m.state.senderChain ∗
       (((ss + 80#64) ↦₆₄ G.chainsPtr) ∗
        ((ss + 88#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip m.state.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip m.state.receiverChains)) ∗
       pendingUnpacked A (ss + 248#64) G.pending m.pendingPreKey ∗
       kyberUnpacked A (ss + 296#64) G.kyber m.pendingKyberPreKey ∗
       sessionUnused A ss G m ∗ tailLensPure G ∗
       stackAt (s0.sp - 64#64) chainLenStack ∗ R) := by
    dsimp only [P, FrSave, sessionFullUnpacked]; ac_rfl
  refine step_sessLen_f12 b ext ss s0.sp m
    ((uint32Field 1 m.state.sessionVersion).length + (bytesField 2 G.localIk.bytes).length +
     (bytesField 3 G.remoteIk.bytes).length +
     (bytesField 4 (HMAC.keyToBytes32 m.state.rootKey)).length +
     (uint32Field 5 m.state.previousCounter).length +
     (encSenderFieldMem G.sender m.state.senderChain).length +
     chainsTotalLen (G.chains.zip m.state.receiverChains) +
     (encPendingFieldMem G.pending m.pendingPreKey).length +
     (uint32Field 10 m.remoteRegistrationId).length +
     (uint32Field 11 m.localRegistrationId).length +
     (bytesField 13 m.aliceBaseKey).length +
     (msgField 14 (m.pendingKyberPreKey.map encPendingKyber)).length)
    (by omega) hpc11 hrun11 (by reg_chain) halign0_b hx19_11 hx8_11 (by reg_chain) hP_f12 ?_
  intro sf hpcf hrunf hspf htrf hx0_f hcsf
  rw [← hfit_eq] at hx0_f
  refine ⟨?_, hspf, hcsf⟩
  intro hm_f
  rw [sepConj_emp] at hm_f
  dsimp only [sessionLenSpec, sessionStateReprAt, sessionStateAt]
  rw [stackAt_sessionLen_eq]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists,
    sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨s0.readReg64 .fp, s0.readReg64 .lr, s0.readReg64 .x24, s0.readReg64 .x23,
    s0.readReg64 .x22, s0.readReg64 .x21, s0.readReg64 .x20, s0.readReg64 .x19,
    ⟨hx0_f, by reg_chain⟩,
    ⟨hpending, hkyber, halice, hrem_id, hloc_id⟩,
    ⟨hlik, hrik, hchains, hpendsome, hreg_len, hlik33, hrik33⟩, ?_⟩
  have hm_f' : sf.mem ⊨ P := hm_f
  dsimp only [P, FrSave] at hm_f'
  rw [← hbody] at hm_f'
  convert hm_f' using 1; ac_rfl

end CryptoVerification.SignalSession.Cli.RunProofs.Initiate.SerializeExt
