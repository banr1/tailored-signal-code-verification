/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Base
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.ChainKeyField
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.PrologueSenderRatchetKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.SepLogic.WPp

/-!
# Per-element `MessageKey` encoding body in `encode::<Chain, Vec<u8>>` (`+0x2a8..+0x29c`)
-/

@[expose] public section

set_option maxHeartbeats 400000
set_option maxRecDepth 200000

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open EncodeVarintNorm
open scoped BigOperators

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Loop register invariant and `messageKeyAt` split -/

def MkLoopRegs (s : State) (v cur endPtr : BitVec 64) : Prop :=
  s.readReg64 .x19 = v ∧
  s.readReg64 .x20 = cur ∧
  s.readReg64 .x24 = endPtr ∧
  s.readReg64 .x25 = 0x22#64 ∧
  s.readReg64 .x26 = 0x08#64

theorem MkLoopRegs.of_calleeSaved {s1 s2 : State} {v cur endPtr : BitVec 64}
    (h1 : MkLoopRegs s1 v cur endPtr) (hcs : CalleeSavedPreserved s1 s2) :
    MkLoopRegs s2 v cur endPtr :=
  ⟨hcs.1.trans h1.1, hcs.2.1.trans h1.2.1, hcs.2.2.2.2.2.1.trans h1.2.2.1,
   hcs.2.2.2.2.2.2.1.trans h1.2.2.2.1, hcs.2.2.2.2.2.2.2.1.trans h1.2.2.2.2⟩

theorem bytesField5_nonempty_eq {bs : List (BitVec 8)} (hne : bs ≠ []) :
    [0x2a#8] ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs = bytesField 5 bs :=
  bytesField_nonempty_eq 5 0x2a#8 bs hne (by decide +kernel)

theorem lenField4_encMessageKey_eq (mk : MessageKeyGenerator) (hseed : mk.seed ≠ []) :
    [0x22#8] ++ encodeVarint (BitVec.ofNat 64 (encMessageKey mk).length) ++
      uint32Field 1 mk.counter ++
      ([0x2a#8] ++ encodeVarint (BitVec.ofNat 64 mk.seed.length) ++ mk.seed) =
      lenField 4 (encMessageKey mk) := by
  rw [bytesField5_nonempty_eq hseed]
  unfold lenField encMessageKey
  have hk : encodeKey 4 .lengthDelimited = [0x22#8] := by decide +kernel
  rw [hk]
  simp [List.append_assoc]

theorem lenField4_encMessageKey_len_parts (mk : MessageKeyGenerator) (hseed : mk.seed ≠ []) :
    1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey mk).length)).length +
      (uint32Field 1 mk.counter).length +
      1 + (encodeVarint (BitVec.ofNat 64 mk.seed.length)).length + mk.seed.length =
      (lenField 4 (encMessageKey mk)).length := by
  have h := congrArg List.length (lenField4_encMessageKey_eq mk hseed)
  simp only [List.length_append, List.length_singleton] at h
  omega

/-- Portion of `messageKeyAt A gk cur` not read during the `message_keys` encoding loop body. -/
def mkUnusedAt (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator) (cur : BitVec 64) :
    SepProp :=
  ⌜gk.2.seed ≠ []⌝ ∗
    (cur ↦₆₄ gk.1.cipher.cap) ∗ ((cur + 8#64) ↦₆₄ gk.1.cipher.ptr) ∗
    vecU8Buf A gk.1.cipher.cap gk.1.cipher.ptr [] ∗
    ((cur + 24#64) ↦₆₄ gk.1.mac.cap) ∗ ((cur + 32#64) ↦₆₄ gk.1.mac.ptr) ∗
    vecU8Buf A gk.1.mac.cap gk.1.mac.ptr [] ∗
    ((cur + 48#64) ↦₆₄ gk.1.iv.cap) ∗ ((cur + 56#64) ↦₆₄ gk.1.iv.ptr) ∗
    vecU8Buf A gk.1.iv.cap gk.1.iv.ptr [] ∗
    ((cur + 72#64) ↦₆₄ gk.1.seed.cap) ∗
    memRegion (cur + 100#64) 4

theorem messageKeyAt_eq_cells (A : RustAlloc) (gk : MessageKeyGhost × MessageKeyGenerator)
    (cur : BitVec 64) :
    messageKeyAt A gk cur =
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      mkUnusedAt A gk cur := by
  unfold messageKeyAt mkUnusedAt
  have h32 : (cur + 24#64) + 8#64 = cur + 32#64 := by rw [BitVec.add_assoc]; rfl
  have h40 : (cur + 24#64) + 16#64 = cur + 40#64 := by rw [BitVec.add_assoc]; rfl
  have h56 : (cur + 48#64) + 8#64 = cur + 56#64 := by rw [BitVec.add_assoc]; rfl
  have h64 : (cur + 48#64) + 16#64 = cur + 64#64 := by rw [BitVec.add_assoc]; rfl
  have h80 : (cur + 72#64) + 8#64 = cur + 80#64 := by rw [BitVec.add_assoc]; rfl
  have h88 : (cur + 72#64) + 16#64 = cur + 88#64 := by rw [BitVec.add_assoc]; rfl
  rw [vecU8At_eq_cells_buf A cur,
      vecU8At_eq_cells_buf A (cur + 24#64),
      vecU8At_eq_cells_buf A (cur + 48#64),
      vecU8At_eq_cells_buf A (cur + 72#64),
      h32, h40, h56, h64, h80, h88]
  simp only [List.length_nil]
  ac_rfl

theorem sepWPp_extract_messageKey_seed_ne_nil {A : RustAlloc}
    {gk : MessageKeyGhost × MessageKeyGenerator} {cur : BitVec 64}
    {prog : Program} {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = messageKeyAt A gk cur ∗ F)
    (h : gk.2.seed ≠ [] → SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hhm : s.mem ⊨ ⌜gk.2.seed ≠ []⌝ ∗
      ((vecU8At A cur gk.1.cipher.cap gk.1.cipher.ptr [] ∗
        vecU8At A (cur + 24#64) gk.1.mac.cap gk.1.mac.ptr [] ∗
        vecU8At A (cur + 48#64) gk.1.iv.cap gk.1.iv.ptr [] ∗
        vecU8At A (cur + 72#64) gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
        ((cur + 96#64) ↦₃₂ gk.2.counter) ∗ memRegion (cur + 100#64) 4) ∗ F ∗ R) := by
    convert hm using 1
    rw [hP]
    unfold messageKeyAt
    ac_rfl
  rw [satisfies_pure_sepConj] at hhm
  exact h hhm.1 R hm hL

/-! ## `MessageKey::encoded_len` call wrapper -/

theorem step_encChain_msgKeyLen (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hMK : OkAt b C ctl abs msgKeyLenName (msgKeyLenSpec A))
    (cur sp0 ret_pc : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = cur)
    (hP : P = (messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encMessageKey gk.2).length →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  rw [msgKeyLen_fnAddr_eq_encChain] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPp.call (x := MsgKeyLenGhost.mk cur gk)
    (F := memRegion (sp0 - 96#64 - 8544#64) 8528 ∗ F)
    hMK hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_msgKeyLen (sp0 - 96#64)] at hm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [msgKeyLenSpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine sepWPp_congr_pre ?_ (hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m)
    rw [stackAt_sub_to_msgKeyLen (sp0 - 96#64)]
    ac_rfl

/-! ## Outer tag `0x22` and element length varint (`+680..+728`) -/

theorem step_encChain_mk_tag_len (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hMK : OkAt b C ctl abs msgKeyLenName (msgKeyLenSpec A))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v cur endPtr curCap curPtr sp0 : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    (curBs : List (BitVec 8))
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 728#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap1 ptr1
          ((curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 680 728
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1244 1272
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hcur_snoc_lt : (curBs ++ [0x22#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x22#8 hlt]
    refine step_encChain_msgKeyLen b C A ctl abs hMK cur sp0 (entry + bv% (720)) gk
      (x := x)
      (F := vecU8At A v curCap curPtr (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v curCap curPtr sp0 (entry + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hregs2)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 b C A ctl abs hDR v curCap curPtr sp0 (entry + bv% (1264))
      curBs hcap_eq (by omega)
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::chain::MessageKey as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x22#8 hnew_gt]
    refine step_encChain_msgKeyLen b C A ctl abs hMK cur sp0 (entry + bv% (720)) gk
      (x := x)
      (F := vecU8At A v newCap p' (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v newCap p' sp0 (entry + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hspm htrm hregs2)

/-! ## `index` field (`uint32Field 1 gk.2.counter`, `+728..+776`) -/

theorem step_encChain_mk_counter (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v cur endPtr cap1 ptr1 sp0 : BitVec 64) (cnt : BitVec 32) (bs1 : List (BitVec 8))
    (hcur_lt : bs1.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 728#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      ((cur + 96#64) ↦₃₂ cnt) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 776#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ uint32Field 1 cnt) ∗
          ((cur + 96#64) ↦₃₂ cnt) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 728 776
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1272 1308
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  by_cases hcnt : cnt = 0#32
  · have hcnt_beq : (cnt == 0#32) = true := by simp [hcnt]
    apply SepWPp.of_sepWP (mid := entry + bv% (776))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hu0 : bs1 ++ uint32Field 1 cnt = bs1 := by simp [hcnt, uint32Field1_zero_eq]
    rw [← hu0]
    exact hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *]⟩
  · have hcnt_beq : (cnt == 0#32) = false := beq_eq_false_iff_ne.mpr hcnt
    have hu_eq : (bs1 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 cnt) =
        bs1 ++ uint32Field 1 cnt := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hcnt]
    have hcur_snoc_lt : (bs1 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A v cap1 ptr1 bs1]
    refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := (v ↦₆₄ cap1) ∗ ((v + 8#64) ↦₆₄ ptr1) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        ((cur + 96#64) ↦₃₂ cnt) ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by ac_rfl) fun hle => ?_
    by_cases hlt : bs1.length < cap1.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A cap1 ptr1 bs1 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A cap1 ptr1 bs1 0x08#8 hlt]
      refine step_encChain_encodeVarint b C A ctl abs hEV
        (BitVec.zeroExtend 64 cnt) v cap1 ptr1 sp0 (entry + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hregsm)
    · have hcap_eq : cap1.toNat = bs1.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      refine step_encChain_reserve1 b C A ctl abs hDR v cap1 ptr1 sp0 (entry + bv% (1296))
        bs1 hcap_eq (by omega)
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
      have hregsr : MkLoopRegs sr v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
      have hx19r : sr.readReg64 .x19 = v := hregsr.1
      have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
      have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
      have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
      have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
      have hx21r : sr.readReg64 .x21 = BitVec.zeroExtend 64 cnt :=
        hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A newCap p' bs1 hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      rw [vecU8Buf_snoc_eq A newCap p' bs1 0x08#8 hnew_gt]
      refine step_encChain_encodeVarint b C A ctl abs hEV
        (BitVec.zeroExtend 64 cnt) v newCap p' sp0 (entry + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hspm htrm hregsm)

/-! ## Empty fields 2–4 and `seed` tag/length (`+776..+1148`) -/

theorem bv_len_beq_zero_false {bs : List (BitVec 8)} (hpos : 0 < bs.length) (hlt : bs.length < 2 ^ 32) :
    (BitVec.ofNat 64 bs.length == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  omega

theorem ule_false_of_ult_true {x y : BitVec 64} (h : y.ult x = true) :
    x.ule y = false := by
  simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at *
  omega

theorem step_encChain_mk_seed_tag (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v cur endPtr cap2 ptr2 seedPtr sp0 : BitVec 64) (bs2 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hbs2_lt : bs2.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 776#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 1148#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length →
      sm.readReg64 .x22 = seedPtr →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap3 ptr3
          ((bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 seedBs.length)) ∗
          ((cur + 16#64) ↦₆₄ 0#64) ∗
          ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗
          ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 776 784
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 880 888
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 984 992
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1088 1148
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1620 1648
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hseed_nz := bv_len_beq_zero_false hseed_pos hseed_lt
  have hbs2_snoc_lt : (bs2 ++ [0x2a#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hbs2_lt
  rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2]
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : bs2.length < cap2.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x2a#8 hlt]
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 seedBs.length) v cap2 ptr2 sp0 (entry + bv% (1148)) (bs2 ++ [0x2a#8])
      hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hregsm hx21m hx22m)
  · have hcap_eq : cap2.toNat = bs2.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 b C A ctl abs hDR v cap2 ptr2 sp0 (entry + bv% (1640))
      bs2 hcap_eq (by omega)
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A newCap p' bs2 hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' bs2 0x2a#8 hnew_gt]
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 seedBs.length) v newCap p' sp0 (entry + bv% (1148)) (bs2 ++ [0x2a#8])
      hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hspm htrm hregsm hx21m hx22m)

/-! ## `seed` reserve and `memcpy` (`+1148..+668`) -/

theorem step_encChain_mk_seed_copy (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v cur endPtr cap3 ptr3 seedCap seedPtr sp0 : BitVec 64)
    (bs3 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hsum_lt : bs3.length + seedBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 1148#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 seedBs.length)
    (hx22 : s.readReg64 .x22 = seedPtr)
    (hP : P = (vecU8At A v cap3 ptr3 bs3 ∗
      vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap4 ptr4 (bs3 ++ seedBs) ∗
          vecU8Buf A seedCap seedPtr seedBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1148 1212
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 640 668
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hbs3_lt : bs3.length < 2 ^ 32 := by omega
  have hlen_add := bv_len_add_slice bs3 seedBs
  rw [vecU8At_eq_cells_buf A v cap3 ptr3 bs3]
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := seedCap) (ptr := seedPtr) (bs := seedBs)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A cap3 ptr3 bs3 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hseed_le => ?_
  by_cases hfit : bs3.length + seedBs.length ≤ cap3.toNat
  · have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = false :=
      (spare_ult_iff hle hbs3_lt hseed_lt).2.mpr hfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = true :=
      ule_of_ult_false hult
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy b C A ctl abs cap3 ptr3 seedPtr sp0 (entry + bv% (660))
      bs3 seedBs hseed_pos hfit hseed_lt
      (x := x)
      (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre ?_
      (hnext _ cap3 ptr3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl
  · have hnfit : cap3.toNat - bs3.length < seedBs.length := by omega
    have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = true :=
      (spare_ult_iff hle hbs3_lt hseed_lt).1.mpr hnfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = false :=
      ule_false_of_ult_true hult
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice b C A ctl abs hDR v cap3 ptr3 sp0 (entry + bv% (1192))
      bs3 seedBs.length hle hnfit hbs3_lt hseed_lt
      (x := x) (F := vecU8Buf A seedCap seedPtr seedBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_fit hult_false
    have hule_true := ule_of_ult_false hult_false
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy b C A ctl abs newCap p' seedPtr sp0 (entry + bv% (660))
      bs3 seedBs hseed_pos hnew_fit hseed_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregsr.1], by simp only [arm64_norm, hregsr.2.1],
         by simp only [arm64_norm, hregsr.2.2.1], by simp only [arm64_norm, hregsr.2.2.2.1],
         by simp only [arm64_norm, hregsr.2.2.2.2]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl

/-! ## Combined per-element loop body (`+680..+668`) -/

theorem step_encChain_mk_elem (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hMK : OkAt b C ctl abs msgKeyLenName (msgKeyLenSpec A))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (curBs : List (BitVec 8))
    (hbound : curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 680#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 668#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v capOut ptrOut (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_messageKey_seed_ne_nil (A := A) (gk := gk) (cur := cur)
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hseed => ?_
  have hseed_pos : 0 < gk.2.seed.length := List.length_pos_of_ne_nil hseed
  have hparts := lenField4_encMessageKey_len_parts gk.2 hseed
  have hcur_lt : curBs.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_tag_len b C A ctl abs hMK hEV hDR
    v cur endPtr curCap curPtr sp0 gk curBs hcur_lt
    (x := x) (F := F) hpc hrun hsp halign htr hregs
    (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hsp1 htr1 hregs1
  set bs1 := (curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)
  have hbs1_len : bs1.length =
      curBs.length + 1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length := by
    simp only [bs1, List.length_append, List.length_singleton]
  have hbs1_lt : bs1.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_counter b C A ctl abs hEV hDR
    v cur endPtr cap1 ptr1 sp0 gk.2.counter bs1 hbs1_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc1 hrun1 hsp1 halign htr1 hregs1
    (by rw [messageKeyAt_eq_cells A gk cur]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hsp2 htr2 hregs2
  set bs2 := bs1 ++ uint32Field 1 gk.2.counter
  have hbs2_len : bs2.length = bs1.length + (uint32Field 1 gk.2.counter).length := by
    simp only [bs2, List.length_append]
  have hbs2_lt : bs2.length + 1 < 2 ^ 32 := by omega
  have hseed_lt : gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_tag b C A ctl abs hEV hDR
    v cur endPtr cap2 ptr2 gk.1.seed.ptr sp0 bs2 gk.2.seed hseed_pos hseed_lt hbs2_lt
    (x := x)
    (F := ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc2 hrun2 hsp2 halign htr2 hregs2 (by ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hsp3 htr3 hregs3 hx21_3 hx22_3
  set bs3 := (bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 gk.2.seed.length)
  have hbs3_len : bs3.length =
      bs2.length + 1 + (encodeVarint (BitVec.ofNat 64 gk.2.seed.length)).length := by
    simp only [bs3, List.length_append, List.length_singleton]
  have hsum_lt : bs3.length + gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_copy b C A ctl abs hDR
    v cur endPtr cap3 ptr3 gk.1.seed.cap gk.1.seed.ptr sp0 bs3 gk.2.seed
    hseed_pos hseed_lt hsum_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      mkUnusedAt A gk cur ∗ F)
    hpc3 hrun3 hsp3 halign htr3 hregs3 hx21_3 hx22_3 (by ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hregs4
  have hbs4_eq : bs3 ++ gk.2.seed = curBs ++ lenField 4 (encMessageKey gk.2) := by
    rw [← lenField4_encMessageKey_eq gk.2 hseed]
    simp [bs3, bs2, bs1, List.append_assoc]
  refine sepWPp_congr_pre ?_ (hnext s4 cap4 ptr4 hpc4 hrun4 hsp4 htr4 hregs4)
  rw [hbs4_eq, messageKeyAt_eq_cells A gk cur]
  ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `12`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_encChain_msgKeyLen_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hMK : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (cur sp0 ret_pc : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 118)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = cur)
    (hP : P = (messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encMessageKey gk.2).length →
      SepWPp (lsProg_12 H) ret sm
        ((messageKeyAt A gk cur ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  have hMK' : subroutine_ok (lsProg_12 H) (blkPl_118).base
      (withLsCodeLoaded lsmpl (msgKeyLenSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hMK
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPp_call_lscl (x := MsgKeyLenGhost.mk cur gk)
    (F := memRegion (sp0 - 96#64 - 8544#64) 8528 ∗ F)
    hMK' hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_msgKeyLen (sp0 - 96#64)] at hm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hx0, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [msgKeyLenSpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [msgKeyLenSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    refine sepWPp_congr_pre ?_
      (hnext sm hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m)
    rw [stackAt_sub_to_msgKeyLen (sp0 - 96#64)]
    ac_rfl

theorem step_encChain_mk_tag_len_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hMK : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (v cur endPtr curCap curPtr sp0 : BitVec 64) (gk : MessageKeyGhost × MessageKeyGenerator)
    (curBs : List (BitVec 8))
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_12).base + 728#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap1 ptr1
          ((curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hcur_snoc_lt : (curBs ++ [0x22#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hcur_lt
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 118)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x22#8 hlt]
    refine step_encChain_msgKeyLen_placed A H hMK cur sp0 ((blkPl_12).base + bv% (720)) gk
      (x := x)
      (F := vecU8At A v curCap curPtr (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply sepWPp_of_sepWP_lscl hcl1 (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v curCap curPtr sp0 ((blkPl_12).base + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hclm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hclm hspm htrm hregs2)
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0
    refine step_encChain_reserve1_placed A H hDR v curCap curPtr sp0 ((blkPl_12).base + bv% (1264))
      curBs hcap_eq (by omega)
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hlen1 := bv_len_add_one curBs 0x22#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hclr (mid := lsmpl.base 118)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl0'
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x22#8 hnew_gt]
    refine step_encChain_msgKeyLen_placed A H hMK cur sp0 ((blkPl_12).base + bv% (720)) gk
      (x := x)
      (F := vecU8At A v newCap p' (curBs ++ [0x22#8]) ∗ A.pool ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl0'
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro s1 hpc1 hrun1 hcl1 hsp1 htr1 hcs1 hx0_1
    have hregs1 : MkLoopRegs s1 v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcs1
    have hx19_1 : s1.readReg64 .x19 = v := hregs1.1
    apply sepWPp_of_sepWP_lscl hcl1 (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 (encMessageKey gk.2).length) v newCap p' sp0 ((blkPl_12).base + bv% (728))
      (curBs ++ [0x22#8]) hcur_snoc_lt
      (x := x) (F := messageKeyAt A gk cur ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by ac_rfl) ?_
    intro sm cap1 ptr1 hpcm hrunm hclm hspm htrm hcsm
    have hregs2 : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregs1.1], by simp only [arm64_norm, hregs1.2.1],
         by simp only [arm64_norm, hregs1.2.2.1], by simp only [arm64_norm, hregs1.2.2.2.1],
         by simp only [arm64_norm, hregs1.2.2.2.2]⟩ hcsm
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap1 ptr1 hpcm hrunm hclm hspm htrm hregs2)

theorem step_encChain_mk_counter_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (v cur endPtr cap1 ptr1 sp0 : BitVec 64) (cnt : BitVec 32) (bs1 : List (BitVec 8))
    (hcur_lt : bs1.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 728#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap1 ptr1 bs1 ∗
      ((cur + 96#64) ↦₃₂ cnt) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_12).base + 776#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2 (bs1 ++ uint32Field 1 cnt) ∗
          ((cur + 96#64) ↦₃₂ cnt) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  by_cases hcnt : cnt = 0#32
  · have hcnt_beq : (cnt == 0#32) = true := by simp [hcnt]
    apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_12).base + bv% (776))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    have hu0 : bs1 ++ uint32Field 1 cnt = bs1 := by simp [hcnt, uint32Field1_zero_eq]
    rw [← hu0]
    exact hnext _ cap1 ptr1 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *]⟩
  · have hcnt_beq : (cnt == 0#32) = false := beq_eq_false_iff_ne.mpr hcnt
    have hu_eq : (bs1 ++ [0x08#8]) ++ encodeVarint (BitVec.zeroExtend 64 cnt) =
        bs1 ++ uint32Field 1 cnt := by
      rw [List.append_assoc, uint32Field1_nonzero_eq hcnt]
    have hcur_snoc_lt : (bs1 ++ [0x08#8]).length < 2 ^ 32 := by
      rw [List.length_append, List.length_singleton]; exact hcur_lt
    rw [vecU8At_eq_cells_buf A v cap1 ptr1 bs1]
    refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap1) (ptr := ptr1) (bs := bs1)
      (F := (v ↦₆₄ cap1) ∗ ((v + 8#64) ↦₆₄ ptr1) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs1.length) ∗
        ((cur + 96#64) ↦₃₂ cnt) ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by ac_rfl) fun hle => ?_
    by_cases hlt : bs1.length < cap1.toNat
    · have hbeq := cap_beq_len_false hlt
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A cap1 ptr1 bs1 hlt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      rw [vecU8Buf_snoc_eq A cap1 ptr1 bs1 0x08#8 hlt]
      refine step_encChain_encodeVarint_placed A H hEV
        (BitVec.zeroExtend 64 cnt) v cap1 ptr1 sp0 ((blkPl_12).base + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hclm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hclm hspm htrm hregsm)
    · have hcap_eq : cap1.toNat = bs1.length := by omega
      have hcap_bv := cap_eq_ofNat_len hcap_eq
      apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl1
      refine step_encChain_reserve1_placed A H hDR v cap1 ptr1 sp0 ((blkPl_12).base + bv% (1296))
        bs1 hcap_eq (by omega)
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by ac_rfl) ?_
      intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt
      have hregsr : MkLoopRegs sr v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
      have hx19r : sr.readReg64 .x19 = v := hregsr.1
      have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
      have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
      have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
      have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
      have hx21r : sr.readReg64 .x21 = BitVec.zeroExtend 64 cnt :=
        hcsr.2.2.1.trans (by simp only [arm64_norm, *])
      have hlen1 := bv_len_add_one bs1 0x08#8
      rw [vecU8Buf_eq_open_one A newCap p' bs1 hnew_gt]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun y => ?_
      apply sepWPp_of_sepWP_lscl hclr (mid := lsmpl.base 10)
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      intro hcl2
      rw [vecU8Buf_snoc_eq A newCap p' bs1 0x08#8 hnew_gt]
      refine step_encChain_encodeVarint_placed A H hEV
        (BitVec.zeroExtend 64 cnt) v newCap p' sp0 ((blkPl_12).base + bv% (776)) (bs1 ++ [0x08#8])
        hcur_snoc_lt
        (x := x) (F := ((cur + 96#64) ↦₃₂ cnt) ∗ F)
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) halign
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
      intro sm cap2 ptr2 hpcm hrunm hclm hspm htrm hcsm
      have hregsm : MkLoopRegs sm v cur endPtr :=
        MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
          by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
      rw [hu_eq]
      refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap2 ptr2 hpcm hrunm hclm hspm htrm hregsm)

theorem step_encChain_mk_seed_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (v cur endPtr cap2 ptr2 seedPtr sp0 : BitVec 64) (bs2 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hbs2_lt : bs2.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 776#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v cap2 ptr2 bs2 ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_12).base + 1148#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length →
      sm.readReg64 .x22 = seedPtr →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3
          ((bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 seedBs.length)) ∗
          ((cur + 16#64) ↦₆₄ 0#64) ∗
          ((cur + 40#64) ↦₆₄ 0#64) ∗
          ((cur + 64#64) ↦₆₄ 0#64) ∗
          ((cur + 80#64) ↦₆₄ seedPtr) ∗
          ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hseed_nz := bv_len_beq_zero_false hseed_pos hseed_lt
  have hbs2_snoc_lt : (bs2 ++ [0x2a#8]).length < 2 ^ 32 := by
    rw [List.length_append, List.length_singleton]; exact hbs2_lt
  rw [vecU8At_eq_cells_buf A v cap2 ptr2 bs2]
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bs2)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs2.length) ∗
      ((cur + 16#64) ↦₆₄ 0#64) ∗
      ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗
      ((cur + 80#64) ↦₆₄ seedPtr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  by_cases hlt : bs2.length < cap2.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A cap2 ptr2 bs2 hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [vecU8Buf_snoc_eq A cap2 ptr2 bs2 0x2a#8 hlt]
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 seedBs.length) v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1148))
      (bs2 ++ [0x2a#8]) hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hclm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hclm hspm htrm hregsm hx21m hx22m)
  · have hcap_eq : cap2.toNat = bs2.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine step_encChain_reserve1_placed A H hDR v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1640))
      bs2 hcap_eq (by omega)
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx20r : sr.readReg64 .x20 = cur := hregsr.2.1
    have hx24r : sr.readReg64 .x24 = endPtr := hregsr.2.2.1
    have hx25r : sr.readReg64 .x25 = 0x22#64 := hregsr.2.2.2.1
    have hx26r : sr.readReg64 .x26 = 0x08#64 := hregsr.2.2.2.2
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one bs2 0x2a#8
    rw [vecU8Buf_eq_open_one A newCap p' bs2 hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hclr (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    rw [vecU8Buf_snoc_eq A newCap p' bs2 0x2a#8 hnew_gt]
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 seedBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (1148))
      (bs2 ++ [0x2a#8]) hbs2_snoc_lt
      (x := x)
      (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
        ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ seedPtr) ∗
        ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 seedBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap3 ptr3 hpcm hrunm hclm hspm htrm hcsm
    have hregsm : MkLoopRegs sm v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsm
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22m : sm.readReg64 .x22 = seedPtr :=
      hcsm.2.2.2.1.trans (by simp only [arm64_norm, *])
    refine sepWPp_congr_pre (by ac_rfl) (hnext sm cap3 ptr3 hpcm hrunm hclm hspm htrm hregsm hx21m hx22m)

theorem step_encChain_mk_seed_copy_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (v cur endPtr cap3 ptr3 seedCap seedPtr sp0 : BitVec 64)
    (bs3 seedBs : List (BitVec 8))
    (hseed_pos : 0 < seedBs.length) (hseed_lt : seedBs.length < 2 ^ 32)
    (hsum_lt : bs3.length + seedBs.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 1148#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 seedBs.length)
    (hx22 : s.readReg64 .x22 = seedPtr)
    (hP : P = (vecU8At A v cap3 ptr3 bs3 ∗
      vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap4 ptr4 : BitVec 64),
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap4 ptr4 (bs3 ++ seedBs) ∗
          vecU8Buf A seedCap seedPtr seedBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  rcases hregs with ⟨hx19, hx20, hx24, hx25, hx26⟩
  have hbs3_lt : bs3.length < 2 ^ 32 := by omega
  have hlen_add := bv_len_add_slice bs3 seedBs
  rw [vecU8At_eq_cells_buf A v cap3 ptr3 bs3]
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap3) (ptr := ptr3) (bs := bs3)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A seedCap seedPtr seedBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := seedCap) (ptr := seedPtr) (bs := seedBs)
    (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
      vecU8Buf A cap3 ptr3 bs3 ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hseed_le => ?_
  by_cases hfit : bs3.length + seedBs.length ≤ cap3.toNat
  · have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = false :=
      (spare_ult_iff hle hbs3_lt hseed_lt).2.mpr hfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = true :=
      ule_of_ult_false hult
    apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy_placed A H hmc cap3 ptr3 seedPtr sp0 ((blkPl_12).base + bv% (660))
      bs3 seedBs hseed_pos hfit hseed_lt
      (x := x)
      (F := (v ↦₆₄ cap3) ∗ ((v + 8#64) ↦₆₄ ptr3) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hclc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclc (mid := (blkPl_12).base + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    refine sepWPp_congr_pre ?_
      (hnext _ cap3 ptr3 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl
  · have hnfit : cap3.toNat - bs3.length < seedBs.length := by omega
    have hult : (cap3 - BitVec.ofNat 64 bs3.length).ult (BitVec.ofNat 64 seedBs.length) = true :=
      (spare_ult_iff hle hbs3_lt hseed_lt).1.mpr hnfit
    have hule : (BitVec.ofNat 64 seedBs.length).ule (cap3 - BitVec.ofNat 64 bs3.length) = false :=
      ule_false_of_ult_true hult
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine step_encChain_reserveSlice_placed A H hDR v cap3 ptr3 sp0 ((blkPl_12).base + bv% (1192))
      bs3 seedBs.length hle hnfit hbs3_lt hseed_lt
      (x := x) (F := vecU8Buf A seedCap seedPtr seedBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_fit hult_false
    have hule_true := ule_of_ult_false hult_false
    have hregsr : MkLoopRegs sr v cur endPtr :=
      MkLoopRegs.of_calleeSaved ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
        by simp only [arm64_norm, *], by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩ hcsr
    have hx19r : sr.readReg64 .x19 = v := hregsr.1
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = seedPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclr (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    rw [vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    refine step_encChain_memcpy_placed A H hmc newCap p' seedPtr sp0 ((blkPl_12).base + bv% (660))
      bs3 seedBs hseed_pos hnew_fit hseed_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bs3.length) ∗
        vecReadRest A seedCap seedPtr seedBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sc hpcc hrunc hclc hspc htrc hcsc
    have hregsc : MkLoopRegs sc v cur endPtr :=
      MkLoopRegs.of_calleeSaved
        ⟨by simp only [arm64_norm, hregsr.1], by simp only [arm64_norm, hregsr.2.1],
         by simp only [arm64_norm, hregsr.2.2.1], by simp only [arm64_norm, hregsr.2.2.2.1],
         by simp only [arm64_norm, hregsr.2.2.2.2]⟩ hcsc
    have hx19c : sc.readReg64 .x19 = v := hregsc.1
    have hx21c : sc.readReg64 .x21 = BitVec.ofNat 64 seedBs.length :=
      hcsc.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23c : sc.readReg64 .x23 = BitVec.ofNat 64 bs3.length :=
      hcsc.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclc (mid := (blkPl_12).base + bv% (668))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl3
    refine sepWPp_congr_pre ?_
      (hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        ⟨by simp only [arm64_norm, hregsc.1], by simp only [arm64_norm, hregsc.2.1],
         by simp only [arm64_norm, hregsc.2.2.1], by simp only [arm64_norm, hregsc.2.2.2.1],
         by simp only [arm64_norm, hregsc.2.2.2.2]⟩)
    rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A seedCap seedPtr seedBs hseed_pos hseed_le]
    ac_rfl

theorem step_encChain_mk_elem_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hMK : subroutine_ok (lsProg_118 H) (blkPl_118).base (withLsCodeLoaded lsmpl (msgKeyLenSpec A)))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (v cur endPtr curCap curPtr sp0 : BitVec 64)
    (gk : MessageKeyGhost × MessageKeyGenerator) (curBs : List (BitVec 8))
    (hbound : curBs.length + (lenField 4 (encMessageKey gk.2)).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 680#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hregs : MkLoopRegs s v cur endPtr)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗
      messageKeyAt A gk cur ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (capOut ptrOut : BitVec 64),
      sm.pc = (blkPl_12).base + 668#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      MkLoopRegs sm v cur endPtr →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v capOut ptrOut (curBs ++ lenField 4 (encMessageKey gk.2)) ∗
          messageKeyAt A gk cur ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_messageKey_seed_ne_nil (A := A) (gk := gk) (cur := cur)
    (F := vecU8At A v curCap curPtr curBs ∗ A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hseed => ?_
  have hseed_pos : 0 < gk.2.seed.length := List.length_pos_of_ne_nil hseed
  have hparts := lenField4_encMessageKey_len_parts gk.2 hseed
  have hcur_lt : curBs.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_tag_len_placed A H hMK hEV hDR
    v cur endPtr curCap curPtr sp0 gk curBs hcur_lt
    (x := x) (F := F) hpc hrun hcl hsp halign htr hregs
    (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
  intro s1 cap1 ptr1 hpc1 hrun1 hcl1 hsp1 htr1 hregs1
  set bs1 := (curBs ++ [0x22#8]) ++ encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)
  have hbs1_len : bs1.length =
      curBs.length + 1 + (encodeVarint (BitVec.ofNat 64 (encMessageKey gk.2).length)).length := by
    simp only [bs1, List.length_append, List.length_singleton]
  have hbs1_lt : bs1.length + 1 < 2 ^ 32 := by omega
  refine step_encChain_mk_counter_placed A H hEV hDR
    v cur endPtr cap1 ptr1 sp0 gk.2.counter bs1 hbs1_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc1 hrun1 hcl1 hsp1 halign htr1 hregs1
    (by rw [messageKeyAt_eq_cells A gk cur]; ac_rfl) ?_
  intro s2 cap2 ptr2 hpc2 hrun2 hcl2 hsp2 htr2 hregs2
  set bs2 := bs1 ++ uint32Field 1 gk.2.counter
  have hbs2_len : bs2.length = bs1.length + (uint32Field 1 gk.2.counter).length := by
    simp only [bs2, List.length_append]
  have hbs2_lt : bs2.length + 1 < 2 ^ 32 := by omega
  have hseed_lt : gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_tag_placed A H hEV hDR
    v cur endPtr cap2 ptr2 gk.1.seed.ptr sp0 bs2 gk.2.seed hseed_pos hseed_lt hbs2_lt
    (x := x)
    (F := ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed ∗
      mkUnusedAt A gk cur ∗ F)
    hpc2 hrun2 hcl2 hsp2 halign htr2 hregs2 (by ac_rfl) ?_
  intro s3 cap3 ptr3 hpc3 hrun3 hcl3 hsp3 htr3 hregs3 hx21_3 hx22_3
  set bs3 := (bs2 ++ [0x2a#8]) ++ encodeVarint (BitVec.ofNat 64 gk.2.seed.length)
  have hbs3_len : bs3.length =
      bs2.length + 1 + (encodeVarint (BitVec.ofNat 64 gk.2.seed.length)).length := by
    simp only [bs3, List.length_append, List.length_singleton]
  have hsum_lt : bs3.length + gk.2.seed.length < 2 ^ 32 := by omega
  refine step_encChain_mk_seed_copy_placed A H hDR hmc
    v cur endPtr cap3 ptr3 gk.1.seed.cap gk.1.seed.ptr sp0 bs3 gk.2.seed
    hseed_pos hseed_lt hsum_lt
    (x := x)
    (F := ((cur + 16#64) ↦₆₄ 0#64) ∗ ((cur + 40#64) ↦₆₄ 0#64) ∗
      ((cur + 64#64) ↦₆₄ 0#64) ∗ ((cur + 80#64) ↦₆₄ gk.1.seed.ptr) ∗
      ((cur + 88#64) ↦₆₄ BitVec.ofNat 64 gk.2.seed.length) ∗
      ((cur + 96#64) ↦₃₂ gk.2.counter) ∗
      mkUnusedAt A gk cur ∗ F)
    hpc3 hrun3 hcl3 hsp3 halign htr3 hregs3 hx21_3 hx22_3 (by ac_rfl) ?_
  intro s4 cap4 ptr4 hpc4 hrun4 hcl4 hsp4 htr4 hregs4
  have hbs4_eq : bs3 ++ gk.2.seed = curBs ++ lenField 4 (encMessageKey gk.2) := by
    rw [← lenField4_encMessageKey_eq gk.2 hseed]
    simp [bs3, bs2, bs1, List.append_assoc]
  refine sepWPp_congr_pre ?_ (hnext s4 cap4 ptr4 hpc4 hrun4 hcl4 hsp4 htr4 hregs4)
  rw [hbs4_eq, messageKeyAt_eq_cells A gk cur]
  ac_rfl

end Placed

end CryptoVerification.E2E.Record.Serialization



