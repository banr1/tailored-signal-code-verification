/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2OkPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsBPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Bridge
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Steps
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP2a
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.TripleRatchet.Getters.Identity
import LibsignalBinary.Proofs.TripleRatchet.Glue
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.ChainLookup.IdentityKeys
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.PublicKeyTryFrom

/-!
# Relocatable Stage P2 Matched-Session Entry Bridge (`+0x0868 → +0x094c`)

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2Bridge` on Block `518`
(`lsProg_518 ext`, `(blkPl_518).base = lsmpl.base 518`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Glue
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

theorem blackBoxHook_withPanics_placed [LibsignalPlacement] {ext : String → Option (State → State)}
    (h_bb : ext "subtle::black_box::<u8>" = some blackBoxHook) :
    Rust.withPanics ext "subtle::black_box::<u8>" = some blackBoxHook :=
  blackBoxHook_withPanics h_bb

theorem processPrekeyActive10At_eq_placed [LibsignalPlacement]
    (coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt : BitVec 64) :
    processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt =
    ((coroPtr + 0x3f8#64) ↦₆₄ kyberStorePtr) ∗
    ((coroPtr + 0x400#64) ↦₆₄ kyberStoreVt) ∗
    ((coroPtr + 0x408#64) ↦₆₄ preKeyStorePtr) ∗
    ((coroPtr + 0x410#64) ↦₆₄ preKeyStoreVt) ∗
    ((coroPtr + 0x418#64) ↦₆₄ idStorePtr) ∗
    ((coroPtr + 0x420#64) ↦₆₄ idStoreVt) ∗
    ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
    ((coroPtr + 0x470#64) ↦₆₄ remoteAddrPtr) ∗
    ((coroPtr + 0x478#64) ↦₆₄ localAddrPtr) ∗
    ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) :=
  processPrekeyActive10At_eq coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
    kyberStorePtr kyberStoreVt

def stageP2Matched0868PrePlaced [LibsignalPlacement] (A : RustAlloc)
    (sp coroPtr msgPtr : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) : SepProp :=
  cells (coroPtr + 0x3f8#64) 6 ∗
  cells (coroPtr + 0x468#64) 4 ∗
  ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
  ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
  ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
  sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
  memRegion (sp + 0x3e0#64) 34 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  A.pool ∗
  stackAt sp rootStack

def stageP2Matched094cPostPlaced [LibsignalPlacement] (A : RustAlloc)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (sess : Session (List (BitVec 8))) : SepProp :=
  ∃∗ recG : SessionGhost,
    ⌜g.cur = some recG ∧ SessionExtraRel recG sess⌝ ∗
    processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      kyberStorePtr kyberStoreVt ∗
    ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
    ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
    ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
    prevSessionsEmptyAt A coroPtr g ∗
    sessionStateAt A (coroPtr + 0xf8#64) recG sess.state ∗
    Getters.remoteIdentityOkAt (sp + 0x3e0#64) sess.state.remoteIdentity ∗
    (lsLogFilterAddr ↦₆₄ 0#64) ∗
    A.pool ∗
    stackAt sp rootStack

private theorem stack_root_to_pkSerialize_m2_placed (sp : BitVec 64) (hsp : rootStack ≤ sp.toNat) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - publicKeySerializeStack) ∗
        stackAt sp publicKeySerializeStack :=
  stackAt_split_of_le sp rootStack publicKeySerializeStack (by decide)
    (Nat.le_trans hsp (Nat.le_of_lt sp.isLt))

private theorem stack_root_to_remoteIk_m2_placed (sp : BitVec 64) (hsp : rootStack ≤ sp.toNat) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - Getters.remoteIdentityKeyStack) ∗
        stackAt sp Getters.remoteIdentityKeyStack :=
  stackAt_split_of_le sp rootStack Getters.remoteIdentityKeyStack (by decide)
    (Nat.le_trans hsp (Nat.le_of_lt sp.isLt))

private theorem boxU8Buf_pk_serialize_entails_placed (A : RustAlloc) (ptr : BitVec 64) (pk : PublicKey) :
    boxU8Buf A ptr pk.serialize ⊢ A.live ptr 33 1 ∗ (ptr ↦ₛ pk.serialize) := by
  have hne : pk.serialize ≠ [] := by simp [PublicKey.serialize]
  have hlen : pk.serialize.length = 33 := by simp [PublicKey.serialize]
  unfold boxU8Buf
  simp only [hne, ↓reduceIte, hlen]
  exact Entails.pure_left fun _ => Entails.refl _

private theorem sessionStateAt_split_remoteIk_placed (A : RustAlloc) (ss : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    ∃ R_ss : SepProp,
      (sessionStateAt A ss G st ⊢
        ⌜G.localIk.cap.toNat < 2 ^ 63 ∧
          (match st.remoteIdentity with
           | none => G.remoteIk.bytes = []
           | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey)⌝ ∗
        (ss ↦₆₄ G.localIk.cap) ∗
        vecGhostAt A G.remoteIk (ss + 0x18#64) ∗
        R_ss) ∧
      ((ss ↦₆₄ G.localIk.cap) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_ss ⊢
        sessionStateAt A ss G st) := by
  have hloc :
      ∃ R_loc : SepProp,
        (vecGhostAt A G.localIk ss ⊢
          ⌜G.localIk.cap.toNat < 2 ^ 63⌝ ∗ (ss ↦₆₄ G.localIk.cap) ∗ R_loc) ∧
        ((ss ↦₆₄ G.localIk.cap) ∗ R_loc ⊢ vecGhostAt A G.localIk ss) := by
    unfold vecGhostAt vecU8At vecHeader
    refine ⟨((ss + 8#64) ↦₆₄ G.localIk.ptr) ∗
            ((ss + 16#64) ↦₆₄ BitVec.ofNat 64 G.localIk.bytes.length) ∗
            ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧
              G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0#64⌝ ∗
            (if G.localIk.cap = 0#64 then emp
             else A.live G.localIk.ptr G.localIk.cap.toNat 1 ∗
               (G.localIk.ptr ↦ₛ G.localIk.bytes) ∗
               memRegion (G.localIk.ptr + BitVec.ofNat 64 G.localIk.bytes.length)
                 (G.localIk.cap.toNat - G.localIk.bytes.length)), ?_, ?_⟩
    · simp only [sepConj_assoc]
      refine Entails.trans (Entails.of_eq (by sep_focus : _ =
        ⌜G.localIk.bytes.length ≤ G.localIk.cap.toNat ∧
          G.localIk.cap.toNat < 2 ^ 63 ∧ G.localIk.ptr ≠ 0#64⌝ ∗ _)) ?_
      refine Entails.pure_left fun hp => Entails.pure_right hp.2.1
        (Entails.trans (Entails.of_eq (by ac_rfl))
          (Entails.of_eq (by simp only [pure_sepConj_of_true hp, sepConj_assoc]; ac_rfl)))
    · simp only [sepConj_assoc]
      exact Entails.of_eq (by ac_rfl)
  obtain ⟨R_loc, hloc_f, hloc_b⟩ := hloc
  let P_pure : Prop :=
    PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧ (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)
  let R_rest : SepProp :=
    vecU8At A (ss + asm64% ssRootKeyOff) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecAt A (asm% chainSize) (asm% chainAlign) (chainAt A) (ss + asm64% ssReceiverChainsOff)
      G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
    vecGhostAt A G.alice (ss + asm64% ssAliceBaseKeyOff) ∗
    vecU8At A (ss + asm64% ssPqRatchetStateOff) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (ss + asm64% ssSenderChainOff) G.sender st.senderChain ∗
    optTailVecAt A (asm% pendingPreKeySize) (ss + asm64% ssPendingPreKeyOff) G.pending ∗
    optTailVecAt A (asm% pendingKyberPreKeySize) (ss + asm64% ssPendingKyberPreKeyOff) G.kyber ∗
    ((ss + asm64% ssSessionVersionOff) ↦₃₂ st.sessionVersion) ∗
    ((ss + asm64% ssPreviousCounterOff) ↦₃₂ st.previousCounter) ∗
    ((ss + asm64% ssRegistrationIdsOff) ↦ₛ G.regIds)
  have hss_eq : sessionStateAt A ss G st =
      ⌜P_pure⌝ ∗ vecGhostAt A G.localIk ss ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_rest := by
    unfold sessionStateAt P_pure R_rest
    rfl
  refine ⟨⌜P_pure⌝ ∗ R_loc ∗ R_rest, ?_, ?_⟩
  · rw [hss_eq]
    refine Entails.pure_left fun hp => ?_
    refine Entails.trans (sepConj_mono_left hloc_f) ?_
    simp only [sepConj_assoc]
    refine Entails.pure_left fun hcap => Entails.pure_right ⟨hcap, hp.2.1⟩ ?_
    simp only [pure_sepConj_of_true hp, sepConj_assoc]
    exact Entails.of_eq (by ac_rfl)
  · rw [hss_eq]
    refine Entails.trans (Entails.of_eq (by ac_rfl :
      (ss ↦₆₄ G.localIk.cap) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ (⌜P_pure⌝ ∗ R_loc ∗ R_rest) =
      ⌜P_pure⌝ ∗ ((ss ↦₆₄ G.localIk.cap) ∗ R_loc) ∗ vecGhostAt A G.remoteIk (ss + 0x18#64) ∗ R_rest)) ?_
    exact sepConj_mono_right (sepConj_mono_left hloc_b)

private theorem memRegion_3e0_34_split_16_18_placed (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 34 =
      memRegion (sp + 0x3e0#64) 16 ∗ memRegion (sp + 0x3f0#64) 18 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 16 18 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem memRegion_3e0_34_restore_placed (sp : BitVec 64) (w0 : BitVec 64) (b8 : BitVec 8) :
    ((sp + 0x3e0#64) ↦₆₄ w0) ∗ ((sp + 0x3e8#64) ↦₈ b8) ∗
    memRegion (sp + 0x3e9#64) 7 ∗ memRegion (sp + 0x3f0#64) 18 ⊢
      memRegion (sp + 0x3e0#64) 34 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 8 26 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64) 1 25 (by decide),
      ProofLib.memRegion_split (sp + 0x3e0#64 + 8#64 + 1#64) 7 18 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo8_entails_memRegion _ _) (Entails.refl _))

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` Stage P2 matched prefix Part A
(`(blkPl_518).base + 0x0868 → +0x08c0`). -/
theorem stageP2_matched_0868_to_08c0_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (s0 s : State)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = msgVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x8c0#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
       sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
       memRegion (sp + 0x3e0#64) 34 ∗
       A.pool ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
            idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
            kyberStorePtr kyberStoreVt ∗
          ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
          ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
          ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
          sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
          A.live (sf.readReg64 .x21) 33 1 ∗
          ((sf.readReg64 .x21) ↦ₛ baseKey.serialize) ∗
          ((sp + 0x3e0#64) ↦₆₄ 0#64) ∗
          ((sp + 0x3e8#64) ↦₈ 1#8) ∗
          memRegion (sp + 0x3e9#64) 7 ∗
          memRegion (sp + 0x3f0#64) 18 ∗
          A.pool ∗
          stackAt sp rootStack) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x26 = 33#64 ∧
        sf.readReg64 .x28 = sp + 0xa90#64 ∧
        sf.readReg64 .x29 = sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  have h1a := p2_seg1a_placed_wp ext s coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt msgVerByte b_4f1
    hpc hrun hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24
  refine bind_sepWP_lscro_steps_m2_placed hcro h1a (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx19_1, _, hx22_1, hx23_1, hx24_1, hx25_1,
    _, _, hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have htr01 : s0.trace <+: s1.trace := htr1_s ▸ htr
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkSerialize_m2_placed sp hsp_root)) (by sep_focus) ?_
  refine call_lscro_oom_steps_m2_placed
    (spec := publicKeySerializeSpec A)
    (x := ⟨msgPtr + 0xa8#64, baseKey⟩)
    (P_spec := ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗ A.pool ∗
      stackAt sp publicKeySerializeStack)
    hcro1 htr01 (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hser)
    hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [publicKeySerializeSpec]
      rw [hsp1]
      exact Entails.pure_right hx0_1 (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
  dsimp only [publicKeySerializeSpec]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx1_2, htr2_1⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkSerialize_m2_placed sp hsp_root).symm) (by sep_focus) ?_
  let serPtr := s2.readReg64 .x0
  refine SepWPp.weaken_frame (boxU8Buf_pk_serialize_entails_placed A serPtr baseKey) (by sep_focus) ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, hx22_cs2, hx23_cs2, hx24_cs2, hx25_cs2,
    _, _, hx28_cs2, hx29_cs2, hvregs_cs2⟩
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx22_2 : s2.readReg64 .x22 = spkStorePtr := hx22_cs2.trans hx22_1
  have hx23_2 : s2.readReg64 .x23 = coroPtr + 0xe0#64 := hx23_cs2.trans hx23_1
  have hx24_2 : s2.readReg64 .x24 = spkStoreVt := hx24_cs2.trans hx24_1
  have hx25_2 : s2.readReg64 .x25 = msgVerByte.zeroExtend 64 := hx25_cs2.trans hx25_1
  have h1b := p2_seg1b_placed_wp ext s2 coroPtr serPtr spkStorePtr spkStoreVt msgVerByte
    hpc2 hrun2 rfl hx1_2 hx19_2 hx22_2 hx23_2 hx24_2 hx25_2
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h1b (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hx19_3, hx21_3,
    _, _, _, _, hx26_3, _, hx28_3, hx29_3, hx30_3, hvregs3⟩
  have hsp3 : s3.sp = sp := hsp3_2.trans hsp2
  have hsp3_al : s3.spAligned = true := by simpa only [State.spAligned, hsp3_2] using hsp2_al
  rw [hsp2] at hx8_3
  conv => arg 4; rw [memRegion_3e0_34_split_16_18_placed sp]
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_promoteMatch sp hroot_le)) (by sep_focus) ?_
  have hlen33 : baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  have hprom := StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (promote_matching_session_match_placed_ok_at (A := A) (callerProg := lsProg_518 (Rust.withPanics ext)) h_bb)
  have hφ_prom :
      s3.readReg64 .x0 = coroPtr + 0xe0#64 ∧
      s3.readReg64 .x1 = msgVerByte.zeroExtend 64 ∧
      s3.readReg64 .x2 = serPtr ∧
      s3.readReg64 .x3 = 33#64 ∧
      s3.readReg64 .x8 = sp + 0x3e0#64 ∧
      r.currentSession = some sess ∧
      sess.state.version = msgVerByte.zeroExtend 32 ∧
      sess.aliceBaseKey = baseKey.serialize ∧
      baseKey.serialize.length = 33 :=
    ⟨hx0_3, hx1_3, hx2_3, hx3_3, hx8_3, hcur, hver, halice, hlen33⟩
  refine call_lscro_nopanic_m2_placed
    (spec := promoteMatchingSessionMatchSpec A)
    (x := ⟨coroPtr + 0xe0#64, msgVerByte, serPtr, baseKey.serialize, sp + 0x3e0#64, g, r, sess⟩)
    (T := sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
      (serPtr ↦ₛ baseKey.serialize) ∗
      memRegion (sp + 0x3e0#64) 16 ∗
      stackAt sp promoteMatchingSessionMatchStack)
    hcro3 hprom hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [promoteMatchingSessionMatchSpec]; rw [hsp3])
    hφ_prom
    (by sep_focus)
    (hpan_false := fun _ => rfl)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [promoteMatchingSessionMatchSpec]
  rw [hsp3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_promoteMatch sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, _, _, hx26_cs4, _, hx28_cs4, hx29_cs4, hvregs_cs4⟩
  have hx21_4 : s4.readReg64 .x21 = serPtr := hx21_cs4.trans hx21_3
  refine SepWPp.done hpc4 hrun4 ⟨?_, hsp4_3.trans hsp3,
    htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)),
    hx19_cs4.trans hx19_3,
    hx26_cs4.trans hx26_3,
    hx28_cs4.trans (hx28_3.trans (hx28_cs2.trans (hx28_1.trans hx28))),
    hx29_cs4.trans (hx29_3.trans (hx29_cs2.trans (hx29_1.trans hx29))),
    hvregs_cs4.trans (hvregs3.trans (hvregs_cs2.trans hvregs1)),
    hcro4⟩
  rw [hx21_4]
  exact Entails.of_eq (by ac_rfl)

private theorem p2_call_dealloc_33_placed_wp [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (s : State) (serPtr : BitVec 64)
    (hpc : s.pc = lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = serPtr)
    (hx1 : s.readReg64 .x1 = 33#64)
    (hx2 : s.readReg64 .x2 = 1#64)
    (hx30 : s.readReg64 .x30 = (blkPl_518).base + 0x930#64) :
    SepWP (lsProg_518 (Rust.withPanics ext))
      ((blkPl_518).base + 0x930#64) s
      (A.live serPtr 33 1 ∗ memRegion serPtr 33 ∗ A.pool ∗ stackAt s.sp allocHookStack)
      (fun s1 P_f =>
        (P_f ⊢ A.pool ∗ stackAt s.sp allocHookStack) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = serPtr := hx0
  have hx1' : s.readReg64 (Reg.gpr 1#5) = 33#64 := hx1
  have hx2' : s.readReg64 (Reg.gpr 2#5) = 1#64 := hx2
  have hx30' : s.readReg64 (Reg.gpr 30#5) = (blkPl_518).base + 0x930#64 := hx30
  wp_call hdealloc (serPtr, 33, 1)
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 800000 in
/-- Relocatable `[LibsignalPlacement]` Stage P2 matched prefix Part B
(`(blkPl_518).base + 0x08c0 → +0x094c`). -/
theorem stageP2_matched_08c0_to_094c_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (s : State)
    (sp coroPtr serPtr : BitVec 64)
    (serBytes : List (BitVec 8))
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess)
    (hlen33 : serBytes.length = 33)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x8c0#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = serPtr)
    (hx26 : s.readReg64 .x26 = 33#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x94c#64) s
      (((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
       sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
       A.live serPtr 33 1 ∗
       (serPtr ↦ₛ serBytes) ∗
       ((sp + 0x3e0#64) ↦₆₄ 0#64) ∗
       ((sp + 0x3e8#64) ↦₈ 1#8) ∗
       memRegion (sp + 0x3e9#64) 7 ∗
       memRegion (sp + 0x3f0#64) 18 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ recG : SessionGhost,
            ⌜g.cur = some recG ∧ SessionExtraRel recG sess⌝ ∗
            ((coroPtr + 0x480#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            prevSessionsEmptyAt A coroPtr g ∗
            sessionStateAt A (coroPtr + 0xf8#64) recG sess.state ∗
            Getters.remoteIdentityOkAt (sp + 0x3e0#64) sess.state.remoteIdentity ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool ∗
            stackAt sp rootStack) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x21 = sp + 0x370#64 ∧
        sf.readReg64 .x25 = sp + 0x210#64 ∧
        sf.readReg64 .x28 = sp + 0xa90#64 ∧
        sf.readReg64 .x29 = sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      Qp := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  have h2a := p2_matched_to_dealloc_placed_wp ext s coroPtr serPtr
    hpc hrun hsp_align hx19 hx21 hx26
  rw [hsp_eq] at h2a
  refine bind_sepWP_lscro_steps_m2_placed hcro h2a (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx0_1, hx1_1, hx2_1, hx19_1, _, _, _,
    hx25_1, _, _, hx28_1, hx29_1, hx30_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hser_mem : (serPtr ↦ₛ serBytes) ⊢ memRegion serPtr 33 := by
    rw [← hlen33]; exact ProofLib.pointsToBytes_entails_memRegion serPtr serBytes
  refine SepWPp.weaken_frame hser_mem (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_alloc sp hroot_le)) (by sep_focus) ?_
  have hde := p2_call_dealloc_33_placed_wp ext hdealloc s1 serPtr
    hpc1 hrun1 hsp1_align hx0_1 hx1_1 hx2_1 hx30_1
  rw [hsp1] at hde
  refine bind_sepWP_lscro_steps_m2_placed hcro1 hde (by sep_focus)
    fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, hx19_2, hx25_2, hx28_2, hx29_2, hvregs2⟩
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_alloc sp hroot_le).symm) (by sep_focus) ?_
  have hsp2 : s2.sp = sp := hsp2_1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (memRegion_3e0_34_restore_placed sp 0#64 1#8) (by sep_focus) ?_
  refine SepWPp.weaken_frame (sessionRecordAt_some_eq_prev_sess A coroPtr g r sess hcur)
    (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun recG => SepWPp.pure_elim fun hgc => ?_
  have hsess_eq : sessionStateReprAt A (coroPtr + 0xf8#64) recG sess =
      ⌜SessionExtraRel recG sess⌝ ∗ sessionStateAt A (coroPtr + 0xf8#64) recG sess.state := rfl
  conv => arg 4; rw [hsess_eq]
  sep_norm
  refine SepWPp.pure_left_frame (φ := SessionExtraRel recG sess) (by sep_focus) fun hextra => ?_
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := sessionStateAt_split_remoteIk_placed A (coroPtr + 0xf8#64) recG sess.state
  refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun ⟨hcap_lt, hrem_wf⟩ => ?_
  have h2b := p2_matched_to_remote_ik_placed_wp ext s2 coroPtr recG.localIk.cap hcap_lt
    hpc2 hrun2 (hx19_2.trans hx19_1)
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h2b (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hx0_3, hx8_3, hx19_3, hx21_3, _, _,
    hx25_3, _, _, hx28_3, hx29_3, hx30_3, hvregs3⟩
  have hsp3 : s3.sp = sp := hsp3_2.trans hsp2
  have hsp3_al : s3.spAligned = true := by
    simpa only [State.spAligned, hsp3_2] using hsp2_align
  rw [hsp2] at hx8_3 hx21_3
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_remoteIk_m2_placed sp hsp_root)) (by sep_focus) ?_
  have hrem_ok := StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_518 (Rust.withPanics ext))
      (entry := lsmpl.base 29)
      (CryptoVerification.LibsignalTripleRatchet.Decrypt.ChainLookup.remote_identity_key_placed_ok A
        (Rust.withPanics ext))
      (by decide))
  have hφ_rem :
      s3.readReg64 .x0 = coroPtr + 0xf8#64 ∧
      s3.readReg64 .x8 = sp + 0x3e0#64 ∧
      (match sess.state.remoteIdentity with
       | none => recG.remoteIk.bytes = []
       | some ik => PublicKey.deserialize recG.remoteIk.bytes = .ok ik.publicKey) :=
    ⟨hx0_3, hx8_3, hrem_wf⟩
  refine call_lscro_nopanic_m2_placed
    (spec := Getters.remoteIdentityKeyPlacedSpec A)
    (x := ⟨coroPtr + 0xf8#64, recG.remoteIk, sess.state.remoteIdentity, sp + 0x3e0#64⟩)
    (T := vecGhostAt A recG.remoteIk ((coroPtr + 0xf8#64) + 0x18#64) ∗
      memRegion (sp + 0x3e0#64) 34 ∗
      (lsLogFilterAddr ↦₆₄ 0#64) ∗
      stackAt sp Getters.remoteIdentityKeyStack)
    hcro3 hrem_ok hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [Getters.remoteIdentityKeyPlacedSpec]; rw [hsp3]; ac_rfl)
    hφ_rem
    (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus)
    (hpan_false := fun _ => rfl)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [Getters.remoteIdentityKeyPlacedSpec]
  rw [hsp3]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_remoteIk_m2_placed sp hsp_root).symm) (by sep_focus) ?_
  have hss_bwd' :
      ((coroPtr + 0xf8#64) ↦₆₄ recG.localIk.cap) ∗
      vecGhostAt A recG.remoteIk (coroPtr + 0x110#64) ∗ R_ss ⊢
      sessionStateAt A (coroPtr + 0xf8#64) recG sess.state := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using hss_bwd
  refine SepWPp.weaken_frame hss_bwd' (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, _, hx21_cs4, _, _, _, hx25_cs4, _, _, hx28_cs4, hx29_cs4, hvregs_cs4⟩
  refine SepWPp.done hpc4 hrun4 ⟨?_, hsp4_3.trans hsp3,
    htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)),
    hx19_cs4.trans hx19_3,
    hx21_cs4.trans hx21_3,
    hx25_cs4.trans (hx25_3.trans (hx25_2.trans hx25_1)),
    hx28_cs4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))),
    hx29_cs4.trans (hx29_3.trans (hx29_2.trans (hx29_1.trans hx29))),
    hvregs_cs4.trans (hvregs3.trans (hvregs2.trans hvregs1)),
    hcro4⟩
  refine Entails.sepExists_right recG (Entails.pure_right ⟨hgc, hextra⟩ ?_)
  exact Entails.of_eq (by ac_rfl)

private theorem bind_sepWPp_steps_frame_dep_placed
    {prog : Program} {mid ret : BitVec 64} {s0 s : State}
    {P P_stage F : SepProp} {P_stage_post : State → SepProp} {Q_regs : State → Prop}
    {Q : State → SepProp → Prop}
    (hstage : SepWPp prog mid s P_stage
      (fun sm P_m => (P_m ⊢ P_stage_post sm) ∧ Q_regs sm)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0))
    (hP : P = P_stage ∗ F)
    (hnext : ∀ sm : State, Steps prog s sm → sm.pc = mid → sm.status = .Running →
      Q_regs sm →
      SepWPp prog ret sm (P_stage_post sm ∗ F) Q
        (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)) :
    SepWPp prog ret s P Q (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpcm, hrunm, P_m, hmm, hent, hregs⟩ | ⟨hpan, P_m, hmm, hpanm⟩ | ⟨_, hoom⟩⟩ :=
    hstage (F ∗ R) hm hL
  · have hmm' : sm.mem ⊨ (P_stage_post sm ∗ F) ∗ R := by
      rw [sepConj_assoc]
      exact Arm64.Satisfies.mono (sepConj_mono_left hent) hmm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hsteps hpcm hrunm hregs R hmm' (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hmm
    exact ⟨sm, hsteps, Or.inr (Or.inl ⟨hpan, P_m ∗ F, hmm, fun R' hmR' => by
      rw [sepConj_assoc] at hmR'
      have h1 := hpanm (F ∗ R') hmR'
      rw [← sepConj_assoc] at h1
      exact allowPanic_frame id h1⟩)⟩
  · exact (not_satisfies_false_sepConj hoom).elim

set_option maxHeartbeats 600000 in
/-- Relocatable `[LibsignalPlacement]` full Stage P2 matched prefix
(`(blkPl_518).base + 0x0868 → +0x094c`) on `lsProg_518 (Rust.withPanics ext)`. -/
theorem stageP2_matched_0868_to_094c_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hser : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 205)
      (withLsCodeLoaded lsmpl (publicKeySerializeSpec A)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym = some blackBoxHook)
    (s0 s : State)
    (sp coroPtr msgPtr remoteAddrPtr localAddrPtr
      idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
      spkStorePtr spkStoreVt kyberStorePtr kyberStoreVt : BitVec 64)
    (msgVerByte b_4f1 : BitVec 8)
    (baseKey : PublicKey)
    (g : RecordGhost) (r : SessionRecord (List (BitVec 8))) (sess : Session (List (BitVec 8)))
    (hcur : r.currentSession = some sess)
    (hver : sess.state.version = msgVerByte.zeroExtend 32)
    (halice : sess.aliceBaseKey = baseKey.serialize)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x868#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx8 : s.readReg64 .x8 = kyberStorePtr)
    (hx9 : s.readReg64 .x9 = msgPtr)
    (hx10 : s.readReg64 .x10 = kyberStoreVt)
    (hx11 : s.readReg64 .x11 = preKeyStorePtr)
    (hx12 : s.readReg64 .x12 = remoteAddrPtr)
    (hx13 : s.readReg64 .x13 = preKeyStoreVt)
    (hx14 : s.readReg64 .x14 = localAddrPtr)
    (hx15 : s.readReg64 .x15 = idStorePtr)
    (hx16 : s.readReg64 .x16 = idStoreVt)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx22 : s.readReg64 .x22 = spkStorePtr)
    (hx23 : s.readReg64 .x23 = coroPtr + 0xe0#64)
    (hx24 : s.readReg64 .x24 = spkStoreVt)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64)
    (hx29 : s.readReg64 .x29 = sp + 0xc70#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x94c#64) s
      (cells (coroPtr + 0x3f8#64) 6 ∗
       cells (coroPtr + 0x468#64) 4 ∗
       ((coroPtr + 0x4f1#64) ↦₈ b_4f1) ∗
       ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
       ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
       sessionRecordAt A (coroPtr + 0xe0#64) g r ∗
       memRegion (sp + 0x3e0#64) 34 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       A.pool ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ recG : SessionGhost,
            ⌜g.cur = some recG ∧ SessionExtraRel recG sess⌝ ∗
            processPrekeyActive10At coroPtr msgPtr remoteAddrPtr localAddrPtr
              idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt
              kyberStorePtr kyberStoreVt ∗
            ((coroPtr + 0x4f1#64) ↦₈ 0#8) ∗
            ((msgPtr + 0xa8#64) ↦ₛ baseKey.bytes.toList) ∗
            ((msgPtr + 0xf0#64) ↦₈ msgVerByte) ∗
            prevSessionsEmptyAt A coroPtr g ∗
            sessionStateAt A (coroPtr + 0xf8#64) recG sess.state ∗
            Getters.remoteIdentityOkAt (sp + 0x3e0#64) sess.state.remoteIdentity ∗
            (lsLogFilterAddr ↦₆₄ 0#64) ∗
            A.pool ∗
            stackAt sp rootStack) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x21 = sp + 0x370#64 ∧
        sf.readReg64 .x25 = sp + 0x210#64 ∧
        sf.readReg64 .x28 = sp + 0xa90#64 ∧
        sf.readReg64 .x29 = sp + 0xc70#64 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  have hpartA := stageP2_matched_0868_to_08c0_placed hser h_bb s0 s sp coroPtr msgPtr remoteAddrPtr localAddrPtr
    idStorePtr idStoreVt preKeyStorePtr preKeyStoreVt spkStorePtr spkStoreVt
    kyberStorePtr kyberStoreVt msgVerByte b_4f1 baseKey g r sess
    hcur hver halice hcro htr hsp_eq hsp_root hpc hrun hsp_align
    hx8 hx9 hx10 hx11 hx12 hx13 hx14 hx15 hx16 hx19 hx22 hx23 hx24 hx28 hx29
  refine bind_sepWPp_steps_frame_dep_placed hpartA (by sep_focus)
    fun sm _ hpcm hrunm hregsm => ?_
  rcases hregsm with ⟨hspm, htrm, hx19m, hx26m, hx28m, hx29m, hvregsm, hcrom⟩
  have hspm_align : (sm.sp &&& 15#64 == 0#64) = true := by rw [hspm, ← hsp_eq]; exact hsp_align
  have hlen33 : baseKey.serialize.length = 33 := by simp [PublicKey.serialize]
  conv => arg 4; rw [processPrekeyActive10At_eq]
  simp only [sepConj_assoc]
  have hpartB := stageP2_matched_08c0_to_094c_placed
    (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)
    hdealloc sm sp coroPtr (sm.readReg64 .x21) baseKey.serialize g r sess
    hcur hlen33 hcrom hspm hsp_root hpcm hrunm hspm_align
    hx19m rfl hx26m hx28m hx29m
  refine SepWPp.bind_sepWPp_steps_frame hpartB (by sep_focus)
    fun sf _ hpcf hrunf hregsf => ?_
  rcases hregsf with ⟨hspf, htrf, hx19f, hx21f, hx25f, hx28f, hx29f, hvregsf, hcrof⟩
  sep_norm
  refine SepWPp.exists_elim fun recG => SepWPp.pure_elim fun ⟨hgc, hextra⟩ => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, hspf, htrf.trans htrm,
    hx19f, hx21f, hx25f, hx28f, hx29f, hvregsf.trans hvregsm, hcrof⟩
  refine Entails.sepExists_right recG (Entails.pure_right ⟨hgc, hextra⟩ ?_)
  rw [processPrekeyActive10At_eq]
  exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
end
