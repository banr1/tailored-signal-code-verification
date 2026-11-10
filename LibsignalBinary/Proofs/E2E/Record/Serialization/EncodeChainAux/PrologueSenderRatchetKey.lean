/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Base
public import LibsignalBinary.Proofs.E2E.Record.RecordPlacedCodeSymF
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.E2E.Record.Serialization.EncodeChainAux.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Prost.EncodeVarintBase
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.E2E.Record.Serialization

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.E2E.Record
open CryptoVerification.LibsignalProtoCodec CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.E2E.Record
open EncodeVarintNorm

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

/-! ## Pure tag and length helpers -/

theorem encChain_tag_orr_eq {tag : Nat} (htag : tag = 6 ∨ tag = 7) :
    ((2#32 ||| ((BitVec.ofNat 64 tag).truncate 32 <<< (3 : Nat))).zeroExtend 64) =
      BitVec.ofNat 64 (tag * 8 + 2) := by
  rcases htag with rfl | rfl <;> decide

theorem encChain_encodeKey_eq {tag : Nat} (htag : tag = 6 ∨ tag = 7) :
    encodeVarint (BitVec.ofNat 64 (tag * 8 + 2)) = encodeKey tag .lengthDelimited := by
  rcases htag with rfl | rfl <;> decide +kernel

theorem encChain_encodeKey_len {tag : Nat} (htag : tag = 6 ∨ tag = 7) :
    (encodeKey tag .lengthDelimited).length = 1 := by
  rcases htag with rfl | rfl <;> decide +kernel

theorem encChainMem_len_lt {x : EncodeChainGhost}
    (hlen : x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32) :
    (encChainMem x.gc).length < 2 ^ 32 := by
  simp only [lenField, List.length_append] at hlen
  omega

theorem bytesField_len_le_encChainMem_srk (gc : ChainGhost × ReceiverChain) :
    (bytesField 1 gc.1.srk.bytes).length ≤ (encChainMem gc).length := by
  simp only [encChainMem, List.length_append]
  omega

theorem bytesField_len_le_encChainMem_priv (gc : ChainGhost × ReceiverChain) :
    (bytesField 1 gc.1.srk.bytes).length + (bytesField 2 gc.1.priv.bytes).length ≤
      (encChainMem gc).length := by
  simp only [encChainMem, List.length_append]
  omega

theorem bytesField_nonempty_eq (tag : Nat) (tagByte : BitVec 8) (bs : List (BitVec 8))
    (hne : bs ≠ [])
    (htag : [tagByte] = encodeKey tag .lengthDelimited) :
    [tagByte] ++ encodeVarint (BitVec.ofNat 64 bs.length) ++ bs = bytesField tag bs := by
  simp only [bytesField, hne, ↓reduceIte, lenField, htag, List.append_assoc]

/-! ## `Chain::encoded_len` call wrapper -/

theorem step_encChain_chainLen (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hchain : OkAt b C ctl abs chainLenName (chainLenSpec A))
    (sp0 ret_pc : BitVec 64)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = x.a)
    (hlen : (encChainMem x.gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  rw [chainLen_fnAddr_eq] at hpc
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine SepWPp.call (x := ChainLenGhost.mk x.a x.gc)
    (F := memRegion (sp0 - 96#64 - 8544#64) 8464 ∗ F)
    hchain hpc hrun hsp_aligned hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_chainLen (sp0 - 96#64)] at hm
    simp only [chainLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [chainLenSpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hcsm
    rw [hsp] at hspm
    simp only [chainLenSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    have hGoalEq :
        (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) chainLenStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 8464 ∗ F) =
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_chainLen (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m

/-! ## Prologue, outer tag, and payload length (`+0x000..+0x044`) -/

@[local arm64_norm]
theorem bv_add_neg96 (sp0 : BitVec 64) :
    sp0 + bv% (2 ^ 64 - 96) = sp0 - 96#64 := by bv_omega

theorem step_encChain_prologue (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (tag : Nat) (a v sp0 w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (htag : tag = 6 ∨ tag = 7)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
      ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
      ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
      ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
      ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 52#64 →
      sm.readReg64 .x0 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm (encChainSavedRegs sp0 s ∗ F) Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 0 48
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  have horr := encChain_tag_orr_eq htag
  apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  have hSavedEq :
      (((sp0 - 96#64) ↦₆₄ s.readReg64 (Reg.gpr 29#5)) ∗
        ((sp0 - 88#64) ↦₆₄ s.readReg64 (Reg.gpr 30#5)) ∗
        ((sp0 - 80#64) ↦₆₄ s.readReg64 (Reg.gpr 28#5)) ∗
        ((sp0 - 72#64) ↦₆₄ s.readReg64 (Reg.gpr 27#5)) ∗
        ((sp0 - 64#64) ↦₆₄ s.readReg64 (Reg.gpr 26#5)) ∗
        ((sp0 - 56#64) ↦₆₄ s.readReg64 (Reg.gpr 25#5)) ∗
        ((sp0 - 48#64) ↦₆₄ s.readReg64 (Reg.gpr 24#5)) ∗
        ((sp0 - 40#64) ↦₆₄ s.readReg64 (Reg.gpr 23#5)) ∗
        ((sp0 - 32#64) ↦₆₄ s.readReg64 (Reg.gpr 22#5)) ∗
        ((sp0 - 24#64) ↦₆₄ s.readReg64 (Reg.gpr 21#5)) ∗
        ((sp0 - 16#64) ↦₆₄ s.readReg64 (Reg.gpr 20#5)) ∗
        ((sp0 - 8#64) ↦₆₄ s.readReg64 (Reg.gpr 19#5))) ∗ F =
      encChainSavedRegs sp0 s ∗ F := rfl
  rw [hSavedEq]
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rcases htag with rfl | rfl <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

theorem step_encChain_to_chainLen (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (a v : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 52#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>") →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 60#64 →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 52 56
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<libsignal_protocol::proto::storage::session_structure::Chain as prost::message::Message>::encoded_len" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_to_lenVarint (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (a v lenVal : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 60#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = lenVal)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")) →
      sm.status = .Running →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 68#64 →
      sm.readReg64 .x0 = lenVal →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm P Q Qp) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q Qp := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 60 64
  generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

theorem step_encChain_seg0 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hchain : OkAt b C ctl abs chainLenName (chainLenSpec A))
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 : State} {Q : State → SepProp → Prop}
    (hpc : s0.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 68#64 →
      sm.status = .Running →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        (vecU8At A x.v cap1 ptr1
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A x.gc x.a ∗ A.pool ∗
          stackAt (s0.sp - 96#64) encChainSubStack ∗
          encChainSavedRegs s0.sp s0)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s0
      ((encodeChainSpec A).pre x s0) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  dsimp only [encodeChainSpec]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, htag, hlen⟩ => ?_
  rw [stackAt_encodeChainStack_split s0.sp]
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w96 => SepWPp.exists_elim fun w88 =>
    SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 => ?_
  refine step_encChain_prologue b C ctl abs x.tag x.a x.v s0.sp
    w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 htag
    (F := protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗
      A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStack)
    hpc hrun rfl halign hx0 hx1 hx2 (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx19_1 hx20_1
  refine step_encChain_encodeVarint b C A ctl abs hEV
    (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr s0.sp
    ((tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 52#64) x.bs
    (by simp only [lenField, List.length_append] at hlen; omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hsp1 halign htr1 hlr1 hx0_1 hx1_1 (by ac_rfl) ?_
  intro s2 cap0 ptr0 hpc2 hrun2 hsp2 htr2 hcs2
  refine step_encChain_to_chainLen b C ctl abs x.a x.v
    hpc2 hrun2 (by reg_chain) (by reg_chain) ?_
  intro s3 hpc3 hrun3 hsp3 htr3 hlr3 hx0_3 hx19_3 hx20_3
  refine step_encChain_chainLen b C A ctl abs hchain s0.sp
    ((tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 60#64)
    (x := x)
    (F := vecU8At A x.v cap0 ptr0 (x.bs ++ encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))) ∗
      A.pool ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 (hsp3.trans hsp2) halign (trVRegs_trans htr3 htr2) hlr3 hx0_3 (encChainMem_len_lt hlen)
    (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hcs4 hx0_4
  rw [encChain_encodeKey_eq htag]
  refine step_encChain_to_lenVarint b C ctl abs x.a x.v
    (BitVec.ofNat 64 (encChainMem x.gc).length)
    hpc4 hrun4 hx0_4 (by reg_chain) (by reg_chain) ?_
  intro s5 hpc5 hrun5 hsp5 htr5 hlr5 hx0_5 hx1_5 hx19_5 hx20_5
  refine step_encChain_encodeVarint b C A ctl abs hEV
    (BitVec.ofNat 64 (encChainMem x.gc).length) x.v cap0 ptr0 s0.sp
    ((tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 68#64)
    (x.bs ++ encodeKey x.tag .lengthDelimited)
    (by
      have := encChain_encodeKey_len htag
      simp only [lenField, List.length_append] at hlen ⊢
      omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc5 hrun5 (hsp5.trans hsp4) halign (trVRegs_trans htr5 htr4) hlr5 hx0_5 hx1_5
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 hcs6
  have hGoalEq :
      ((vecU8At A x.v cap1 ptr1
        ((x.bs ++ encodeKey x.tag .lengthDelimited) ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStack) ∗
        protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0) =
      (vecU8At A x.v cap1 ptr1
        (x.bs ++ encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        protoChainAt A x.gc x.a ∗ A.pool ∗
        stackAt (s0.sp - 96#64) encChainSubStack ∗
        encChainSavedRegs s0.sp s0) := by ac_rfl
  rw [hGoalEq]
  exact hnext s6 cap1 ptr1 hpc6 hrun6 hsp6 htr6 (by reg_chain) (by reg_chain) hlen

/-! ## `bytesField` length bounds -/

theorem bytes_len_le_bytesField (tag : Nat) (bs : List (BitVec 8)) :
    bs.length ≤ (bytesField tag bs).length := by
  by_cases h : bs = []
  · subst h; simp [bytesField]
  · simp only [bytesField, h, ↓reduceIte, lenField, List.length_append]
    omega

theorem bv_ofNat_beq_zero_false {n : Nat} (hpos : 0 < n) (hlt : n < 2 ^ 32) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  rw [beq_eq_false_iff_ne]
  intro heq
  have h1 := congrArg BitVec.toNat heq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at h1
  simp at h1
  omega

theorem bv_len_add_slice (bs sliceBs : List (BitVec 8)) :
    BitVec.ofNat 64 bs.length + BitVec.ofNat 64 sliceBs.length =
      BitVec.ofNat 64 (bs ++ sliceBs).length := by
  simp only [List.length_append, BitVec.ofNat_add]

/-! ## Tag 1 (`sender_ratchet_key`, `+0x044..+0x0b0`) -/

theorem step_encChain_seg1_tag (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v a curCap curPtr srkPtr sp0 : BitVec 64) (curBs srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 128#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length →
      sm.readReg64 .x22 = srkPtr →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 68 124
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1676 1700
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hsrk_nz := bv_ofNat_beq_zero_false hsrk_pos hsrk_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x0a#8 hlt]
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 srkBs.length) v curCap curPtr sp0 (entry + bv% (128)) (curBs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 b C A ctl abs hDR v curCap curPtr sp0 (entry + bv% (1696))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x0a#8 hnew_gt]
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 srkBs.length) v newCap p' sp0 (entry + bv% (128)) (curBs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem ule_of_ult_false {x y : BitVec 64} (h : y.ult x = false) : x.ule y = true := by
  simp only [BitVec.ult, BitVec.ule, decide_eq_true_eq, decide_eq_false_iff_not] at *
  omega

theorem step_encChain_seg1_copy (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v a cap2 ptr2 srkCap srkPtr sp0 : BitVec 64) (bsMid srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 128#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 srkBs.length)
    (hx22 : s.readReg64 .x22 = srkPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 128 172
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1704 1744
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle2 => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := srkCap) (ptr := srkPtr) (bs := srkBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hsrk_le => ?_
  have hlen_add := bv_len_add_slice bsMid srkBs
  by_cases hfit : bsMid.length + srkBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).2.mpr hfit
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy b C A ctl abs cap2 ptr2 srkPtr sp0 (entry + bv% (168))
      bsMid srkBs hsrk_pos hfit hsrk_lt
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A cap2 ptr2 (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs)) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < srkBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).1.mpr hrem
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice b C A ctl abs hDR v cap2 ptr2 sp0 (entry + bv% (1728))
      bsMid srkBs.length hle2 hrem hmid_lt hsrk_lt
      (x := x)
      (F := vecU8Buf A srkCap srkPtr srkBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy b C A ctl abs newCap p' srkPtr sp0 (entry + bv% (168))
      bsMid srkBs hsrk_pos hnew_ge hsrk_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A newCap p' (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs)) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_seg1 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v a curCap curPtr sp0 : BitVec 64) (srk : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 1 srk.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 68#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A srk a ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 176#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : srk.bytes = []
  · encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 68 72
    generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
    examples_hide_fetches
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    have hlen0 : BitVec.ofNat 64 srk.bytes.length = 0#64 := by simp [hnil]
    apply SepWPp.of_sepWP (mid := entry + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hbf0 : curBs ++ bytesField 1 srk.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hsrk_pos : 0 < srk.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length) ++ srk.bytes =
        bytesField 1 srk.bytes :=
      bytesField_nonempty_eq 1 0x0a#8 srk.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length + srk.bytes.length =
        (bytesField 1 srk.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srk.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    refine step_encChain_seg1_tag b C A ctl abs hEV hDR
      v a curCap curPtr srk.ptr sp0 curBs srk.bytes
      hsrk_pos (by omega) (by omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ vecU8Buf A srk.cap srk.ptr srk.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length))]
    refine step_encChain_seg1_copy b C A ctl abs hDR
      v a cap2 ptr2 srk.cap srk.ptr sp0
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) srk.bytes
      hsrk_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes =
        curBs ++ bytesField 1 srk.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes) ∗
          vecU8Buf A srk.cap srk.ptr srk.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2

/-! ## Tag 2 (`sender_ratchet_key_private`, `+0x0b0..+0x11c`) -/

theorem vecU8At_add24_eq_cells_buf (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A (a + 24#64) cap ptr bs =
      ((a + 24#64) ↦₆₄ cap) ∗ ((a + 32#64) ↦₆₄ ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        vecU8Buf A cap ptr bs := by
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by rw [BitVec.add_assoc]; rfl
  have h40 : (a + 24#64) + 16#64 = a + 40#64 := by rw [BitVec.add_assoc]; rfl
  rw [vecU8At_eq_cells_buf, h32, h40]

theorem step_encChain_seg2_tag (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v a curCap curPtr privPtr sp0 : BitVec 64) (curBs privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 236#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length →
      sm.readReg64 .x22 = privPtr →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 176 232
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1780 1804
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hpriv_nz := bv_ofNat_beq_zero_false hpriv_pos hpriv_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x12#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x12#8 hlt]
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 privBs.length) v curCap curPtr sp0 (entry + bv% (236)) (curBs ++ [0x12#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserve1 b C A ctl abs hDR v curCap curPtr sp0 (entry + bv% (1800))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x12#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (2 ^ 64 + (ls_off% "prost::encoding::varint::encode_varint::<alloc::vec::Vec<u8>> [local#1]") - (ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>")))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x12#8 hnew_gt]
    refine step_encChain_encodeVarint b C A ctl abs hEV
      (BitVec.ofNat 64 privBs.length) v newCap p' sp0 (entry + bv% (236)) (curBs ++ [0x12#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg2_copy (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v a cap2 ptr2 privCap privPtr sp0 : BitVec 64) (bsMid privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 236#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 privBs.length)
    (hx22 : s.readReg64 .x22 = privPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A privCap privPtr privBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 236 280
  encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 1808 1848
  generalize_entry hentry : (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
  examples_hide_fetches
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A privCap privPtr privBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle2 => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := privCap) (ptr := privPtr) (bs := privBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hpriv_le => ?_
  have hlen_add := bv_len_add_slice bsMid privBs
  by_cases hfit : bsMid.length + privBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).2.mpr hfit
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
    refine step_encChain_memcpy b C A ctl abs cap2 ptr2 privPtr sp0 (entry + bv% (276))
      bsMid privBs hpriv_pos hfit hpriv_lt
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A privCap privPtr privBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A cap2 ptr2 (bsMid ++ privBs) ∗ (privPtr ↦ₛ privBs)) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ privBs).length) ∗
          vecReadRest A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < privBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).1.mpr hrem
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#1]" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine step_encChain_reserveSlice b C A ctl abs hDR v cap2 ptr2 sp0 (entry + bv% (1832))
      bsMid privBs.length hle2 hrem hmid_lt hpriv_lt
      (x := x)
      (F := vecU8Buf A privCap privPtr privBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "memcpy" - ls_off% "prost::encoding::message::encode::<libsignal_protocol::proto::storage::session_structure::Chain, alloc::vec::Vec<u8>>"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    rw [vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
    refine step_encChain_memcpy b C A ctl abs newCap p' privPtr sp0 (entry + bv% (276))
      bsMid privBs hpriv_pos hnew_ge hpriv_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A privCap privPtr privBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply SepWPp.of_sepWP (mid := entry + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hGoalEq :
        ((vecU8Buf A newCap p' (bsMid ++ privBs) ∗ (privPtr ↦ₛ privBs)) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ privBs).length) ∗
          vecReadRest A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_seg2 (b : BitVec 64) (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (hEV : Prost.EncodeVarintOk b C A ctl abs)
    (hDR : OkAt b C ctl abs doReserveName (doReserveSpec A))
    (v a curCap curPtr sp0 : BitVec 64) (priv : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 2 priv.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 176#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A priv (a + 24#64) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName + 284#64 →
      sm.status = .Running →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (tripleRatchetProgAt b C ctl abs) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 2 priv.bytes) ∗ vecGhostAt A priv (a + 24#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (tripleRatchetProgAt b C ctl abs) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : priv.bytes = []
  · encChain_fetches_range b (Rust.withPanics (tripleRatchetExterns C ctl abs)) 176 180
    generalize_entry (tripleRatchetProgAt b C ctl abs).fnAddr encodeChainName = entry
    examples_hide_fetches
    unfold vecGhostAt
    rw [vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    have hlen0 : BitVec.ofNat 64 priv.bytes.length = 0#64 := by simp [hnil]
    apply SepWPp.of_sepWP (mid := entry + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    have hbf0 : curBs ++ bytesField 2 priv.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hpriv_pos : 0 < priv.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x12#8] ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length) ++ priv.bytes =
        bytesField 2 priv.bytes :=
      bytesField_nonempty_eq 2 0x12#8 priv.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length + priv.bytes.length =
        (bytesField 2 priv.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 priv.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    refine step_encChain_seg2_tag b C A ctl abs hEV hDR
      v a curCap curPtr priv.ptr sp0 curBs priv.bytes
      hpriv_pos (by omega) (by omega)
      (x := x)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ vecU8Buf A priv.cap priv.ptr priv.bytes ∗ F)
      hpc hrun hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length))]
    refine step_encChain_seg2_copy b C A ctl abs hDR
      v a cap2 ptr2 priv.cap priv.ptr sp0
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) priv.bytes
      hpriv_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F)
      hpc1 hrun1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes =
        curBs ++ bytesField 2 priv.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes) ∗
          vecU8Buf A priv.cap priv.ptr priv.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 2 priv.bytes) ∗ vecGhostAt A priv (a + 24#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hsp2 htr2 hx19_2 hx20_2

/-! ## Relocatable `[LibsignalPlacement]` proofs (block `12`) -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem step_encChain_chainLen_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base (withLsCodeLoaded lsmpl (chainLenSpec A)))
    (sp0 ret_pc : BitVec 64)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = lsmpl.base 88)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hlr : s.readReg64 .lr = ret_pc)
    (hx0 : s.readReg64 .x0 = x.a)
    (hlen : (encChainMem x.gc).length < 2 ^ 32)
    (hP : P = (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State),
      sm.pc = ret_pc →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      CalleeSavedPreserved s sm →
      sm.readReg64 .x0 = BitVec.ofNat 64 (encChainMem x.gc).length →
      SepWPp (lsProg_12 H) ret sm
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  have hchain' : subroutine_ok (lsProg_12 H) (blkPl_88).base
      (withLsCodeLoaded lsmpl (chainLenSpec A)) :=
    ls_subroutine_ok_of_block (callerProg := lsProg_12 H) hchain
  have hsp_aligned : s.spAligned = true := by
    simp only [State.spAligned, hsp, beq_iff_eq]
    exact sp_sub_96_aligned halign
  refine sepWPp_call_lscl (x := ChainLenGhost.mk x.a x.gc)
    (F := memRegion (sp0 - 96#64 - 8544#64) 8464 ∗ F)
    hchain' hpc hrun hsp_aligned hcl hlr ?_ ?_ ?_ ?_
  · intro R' hm
    rw [hP, stackAt_sub_to_chainLen (sp0 - 96#64)] at hm
    simp only [chainLenSpec, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hlen⟩, ?_⟩
    convert hm using 1; ac_rfl
  · intro sf code R' _ hm
    exact not_satisfies_false_sepConj hm
  · intro sf _ hm
    simp only [chainLenSpec, sepConj_assoc] at hm
    exact False.elim (not_satisfies_false_sepConj hm)
  · intro sm hpcm hrunm hspm hclm hcsm
    rw [hsp] at hspm
    simp only [chainLenSpec, hsp, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨hx0m, htrm⟩ => ?_
    have hGoalEq :
        (protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) chainLenStack ∗
          memRegion (sp0 - 96#64 - 8544#64) 8464 ∗ F) =
        ((protoChainAt A x.gc x.a ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [stackAt_sub_to_chainLen (sp0 - 96#64)]
      ac_rfl
    rw [hGoalEq]
    exact hnext sm hpcm hrunm hclm hspm (trVRegs_of_call htrm hcsm htr) hcsm hx0m

theorem step_encChain_prologue_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (tag : Nat) (a v sp0 w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 : BitVec 64)
    (htag : tag = 6 ∨ tag = 7)
    {ret : BitVec 64} {s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0)
    (halign : sp0 &&& 15#64 = 0#64)
    (hx0 : s.readReg64 .x0 = BitVec.ofNat 64 tag)
    (hx1 : s.readReg64 .x1 = a)
    (hx2 : s.readReg64 .x2 = v)
    (hP : P = (((sp0 - 96#64) ↦₆₄ w96) ∗ ((sp0 - 88#64) ↦₆₄ w88) ∗
      ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
      ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
      ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
      ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) ∗ F)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 10 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 52#64 →
      sm.readReg64 .x0 = BitVec.ofNat 64 (tag * 8 + 2) →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (lsProg_12 H) ret sm (encChainSavedRegs sp0 s ∗ F) Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  subst hP
  have horr := encChain_tag_orr_eq htag
  apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 10)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclm
  have hSavedEq :
      (((sp0 - 96#64) ↦₆₄ s.readReg64 (Reg.gpr 29#5)) ∗
        ((sp0 - 88#64) ↦₆₄ s.readReg64 (Reg.gpr 30#5)) ∗
        ((sp0 - 80#64) ↦₆₄ s.readReg64 (Reg.gpr 28#5)) ∗
        ((sp0 - 72#64) ↦₆₄ s.readReg64 (Reg.gpr 27#5)) ∗
        ((sp0 - 64#64) ↦₆₄ s.readReg64 (Reg.gpr 26#5)) ∗
        ((sp0 - 56#64) ↦₆₄ s.readReg64 (Reg.gpr 25#5)) ∗
        ((sp0 - 48#64) ↦₆₄ s.readReg64 (Reg.gpr 24#5)) ∗
        ((sp0 - 40#64) ↦₆₄ s.readReg64 (Reg.gpr 23#5)) ∗
        ((sp0 - 32#64) ↦₆₄ s.readReg64 (Reg.gpr 22#5)) ∗
        ((sp0 - 24#64) ↦₆₄ s.readReg64 (Reg.gpr 21#5)) ∗
        ((sp0 - 16#64) ↦₆₄ s.readReg64 (Reg.gpr 20#5)) ∗
        ((sp0 - 8#64) ↦₆₄ s.readReg64 (Reg.gpr 19#5))) ∗ F =
      encChainSavedRegs sp0 s ∗ F := rfl
  rw [hSavedEq]
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by rcases htag with rfl | rfl <;> simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

theorem step_encChain_to_chainLen_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (a v : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 52#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 88 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 60#64 →
      sm.readReg64 .x0 = a →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (lsProg_12 H) ret sm P Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 88)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclm
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_to_lenVarint_placed [LibsignalPlacement]
    (H : String → Option (State → State))
    (a v lenVal : BitVec 64)
    {ret : BitVec 64} {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 60#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hx0 : s.readReg64 .x0 = lenVal)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hnext : ∀ sm : State,
      sm.pc = lsmpl.base 10 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = s.sp →
      sm.trace = s.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s →
      sm.readReg64 .lr = (blkPl_12).base + 68#64 →
      sm.readReg64 .x0 = lenVal →
      sm.readReg64 .x1 = v →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (lsProg_12 H) ret sm P Q Qp) :
    SepWPp (lsProg_12 H) ret s P Q Qp := by
  apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 10)
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  intro hclm
  exact hnext _ (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])

theorem step_encChain_seg0_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hchain : subroutine_ok (lsProg_88 H) (blkPl_88).base (withLsCodeLoaded lsmpl (chainLenSpec A)))
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 : State} {Q : State → SepProp → Prop}
    (hpc : s0.pc = (blkPl_12).base)
    (hrun : s0.status = .Running)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hnext : ∀ (sm : State) (cap1 ptr1 : BitVec 64),
      sm.pc = (blkPl_12).base + 68#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = s0.sp - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = x.v →
      sm.readReg64 .x20 = x.a →
      x.bs.length + (lenField x.tag (encChainMem x.gc)).length < 2 ^ 32 →
      SepWPp (lsProg_12 H) ret sm
        (vecU8At A x.v cap1 ptr1
          (x.bs ++ encodeKey x.tag .lengthDelimited ++
            encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
          protoChainAt A x.gc x.a ∗ A.pool ∗
          stackAt (s0.sp - 96#64) encChainSubStack ∗
          encChainSavedRegs s0.sp s0)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s0
      ((withLsCodeLoaded lsmpl (encodeChainSpec A)).pre x s0) Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  dsimp only [withLsCodeLoaded, encodeChainSpec]
  rw [sepConj_comm _ ⌜LibsignalCodeLoaded lsmpl s0.mem⌝]
  refine SepWPp.pure_elim fun hcl0 => ?_
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, htag, hlen⟩ => ?_
  rw [stackAt_encodeChainStack_split s0.sp]
  simp only [sepExists_sepConj_right]
  refine SepWPp.exists_elim fun w96 => SepWPp.exists_elim fun w88 =>
    SepWPp.exists_elim fun w80 => SepWPp.exists_elim fun w72 =>
    SepWPp.exists_elim fun w64 => SepWPp.exists_elim fun w56 =>
    SepWPp.exists_elim fun w48 => SepWPp.exists_elim fun w40 =>
    SepWPp.exists_elim fun w32 => SepWPp.exists_elim fun w24 =>
    SepWPp.exists_elim fun w16 => SepWPp.exists_elim fun w8 => ?_
  refine step_encChain_prologue_placed H x.tag x.a x.v s0.sp
    w96 w88 w80 w72 w64 w56 w48 w40 w32 w24 w16 w8 htag
    (F := protoChainAt A x.gc x.a ∗ vecU8At A x.v x.cap x.ptr x.bs ∗
      A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStack)
    hpc hrun hcl0 rfl halign hx0 hx1 hx2 (by ac_rfl) ?_
  intro s1 hpc1 hrun1 hcl1 hsp1 htr1 hlr1 hx0_1 hx1_1 hx19_1 hx20_1
  refine step_encChain_encodeVarint_placed A H hEV
    (BitVec.ofNat 64 (x.tag * 8 + 2)) x.v x.cap x.ptr s0.sp
    ((blkPl_12).base + 52#64) x.bs
    (by simp only [lenField, List.length_append] at hlen; omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc1 hrun1 hcl1 hsp1 halign htr1 hlr1 hx0_1 hx1_1 (by ac_rfl) ?_
  intro s2 cap0 ptr0 hpc2 hrun2 hcl2 hsp2 htr2 hcs2
  refine step_encChain_to_chainLen_placed H x.a x.v
    hpc2 hrun2 hcl2 (by reg_chain) (by reg_chain) ?_
  intro s3 hpc3 hrun3 hcl3 hsp3 htr3 hlr3 hx0_3 hx19_3 hx20_3
  refine step_encChain_chainLen_placed A H hchain s0.sp
    ((blkPl_12).base + 60#64)
    (x := x)
    (F := vecU8At A x.v cap0 ptr0 (x.bs ++ encodeVarint (BitVec.ofNat 64 (x.tag * 8 + 2))) ∗
      A.pool ∗ encChainSavedRegs s0.sp s0)
    hpc3 hrun3 hcl3 (hsp3.trans hsp2) halign (trVRegs_trans htr3 htr2) hlr3 hx0_3
    (encChainMem_len_lt hlen) (by ac_rfl) ?_
  intro s4 hpc4 hrun4 hcl4 hsp4 htr4 hcs4 hx0_4
  rw [encChain_encodeKey_eq htag]
  refine step_encChain_to_lenVarint_placed H x.a x.v
    (BitVec.ofNat 64 (encChainMem x.gc).length)
    hpc4 hrun4 hcl4 hx0_4 (by reg_chain) (by reg_chain) ?_
  intro s5 hpc5 hrun5 hcl5 hsp5 htr5 hlr5 hx0_5 hx1_5 hx19_5 hx20_5
  refine step_encChain_encodeVarint_placed A H hEV
    (BitVec.ofNat 64 (encChainMem x.gc).length) x.v cap0 ptr0 s0.sp
    ((blkPl_12).base + 68#64)
    (x.bs ++ encodeKey x.tag .lengthDelimited)
    (by
      have := encChain_encodeKey_len htag
      simp only [lenField, List.length_append] at hlen ⊢
      omega)
    (x := x) (F := protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0)
    hpc5 hrun5 hcl5 (hsp5.trans hsp4) halign (trVRegs_trans htr5 htr4) hlr5 hx0_5 hx1_5
    (by ac_rfl) ?_
  intro s6 cap1 ptr1 hpc6 hrun6 hcl6 hsp6 htr6 hcs6
  have hGoalEq :
      ((vecU8At A x.v cap1 ptr1
        ((x.bs ++ encodeKey x.tag .lengthDelimited) ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        A.pool ∗ stackAt (s0.sp - 96#64) encChainSubStack) ∗
        protoChainAt A x.gc x.a ∗ encChainSavedRegs s0.sp s0) =
      (vecU8At A x.v cap1 ptr1
        (x.bs ++ encodeKey x.tag .lengthDelimited ++
          encodeVarint (BitVec.ofNat 64 (encChainMem x.gc).length)) ∗
        protoChainAt A x.gc x.a ∗ A.pool ∗
        stackAt (s0.sp - 96#64) encChainSubStack ∗
        encChainSavedRegs s0.sp s0) := by ac_rfl
  rw [hGoalEq]
  exact hnext s6 cap1 ptr1 hpc6 hrun6 hcl6 hsp6 htr6 (by reg_chain) (by reg_chain) hlen

theorem step_encChain_seg1_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (v a curCap curPtr srkPtr sp0 : BitVec 64) (curBs srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_12).base + 128#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length →
      sm.readReg64 .x22 = srkPtr →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hsrk_nz := bv_ofNat_beq_zero_false hsrk_pos hsrk_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x0a#8 hlt]
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 srkBs.length) v curCap curPtr sp0 ((blkPl_12).base + bv% (128))
      (curBs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hclm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hclm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine step_encChain_reserve1_placed A H hDR v curCap curPtr sp0 ((blkPl_12).base + bv% (1696))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x0a#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hclr (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x0a#8 hnew_gt]
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 srkBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (128))
      (curBs ++ [0x0a#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hclm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srkBs.length)) ∗
          ((a + 8#64) ↦₆₄ srkPtr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srkBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hclm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg1_copy_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (v a cap2 ptr2 srkCap srkPtr sp0 : BitVec 64) (bsMid srkBs : List (BitVec 8))
    (hsrk_pos : 0 < srkBs.length)
    (hsrk_lt : srkBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 128#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 srkBs.length)
    (hx22 : s.readReg64 .x22 = srkPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A srkCap srkPtr srkBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle2 => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := srkCap) (ptr := srkPtr) (bs := srkBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hsrk_le => ?_
  have hlen_add := bv_len_add_slice bsMid srkBs
  by_cases hfit : bsMid.length + srkBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).2.mpr hfit
    apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy_placed A H hmc cap2 ptr2 srkPtr sp0 ((blkPl_12).base + bv% (168))
      bsMid srkBs hsrk_pos hfit hsrk_lt
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hclm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclm (mid := (blkPl_12).base + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    have hGoalEq :
        ((vecU8Buf A cap2 ptr2 (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs)) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < srkBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 srkBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hsrk_lt).1.mpr hrem
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine step_encChain_reserveSlice_placed A H hDR v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1728))
      bsMid srkBs.length hle2 hrem hmid_lt hsrk_lt
      (x := x)
      (F := vecU8Buf A srkCap srkPtr srkBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = srkPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclr (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    rw [vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
    refine step_encChain_memcpy_placed A H hmc newCap p' srkPtr sp0 ((blkPl_12).base + bv% (168))
      bsMid srkBs hsrk_pos hnew_ge hsrk_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A srkCap srkPtr srkBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hclm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 srkBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclm (mid := (blkPl_12).base + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl3
    have hGoalEq :
        ((vecU8Buf A newCap p' (bsMid ++ srkBs) ∗ (srkPtr ↦ₛ srkBs)) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ srkBs).length) ∗
          vecReadRest A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ srkBs) ∗
          vecU8Buf A srkCap srkPtr srkBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A srkCap srkPtr srkBs hsrk_pos hsrk_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_seg1_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (v a curCap curPtr sp0 : BitVec 64) (srk : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 1 srk.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 68#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A srk a ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_12).base + 176#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : srk.bytes = []
  · unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    have hlen0 : BitVec.ofNat 64 srk.bytes.length = 0#64 := by simp [hnil]
    apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_12).base + bv% (176))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclm
    have hbf0 : curBs ++ bytesField 1 srk.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hsrk_pos : 0 < srk.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x0a#8] ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length) ++ srk.bytes =
        bytesField 1 srk.bytes :=
      bytesField_nonempty_eq 1 0x0a#8 srk.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 srk.bytes.length)).length + srk.bytes.length =
        (bytesField 1 srk.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 srk.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
    refine step_encChain_seg1_tag_placed A H hEV hDR
      v a curCap curPtr srk.ptr sp0 curBs srk.bytes
      hsrk_pos (by omega) (by omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ vecU8Buf A srk.cap srk.ptr srk.bytes ∗ F)
      hpc hrun hcl hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length))]
    refine step_encChain_seg1_copy_placed A H hDR hmc
      v a cap2 ptr2 srk.cap srk.ptr sp0
      ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) srk.bytes
      hsrk_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F)
      hpc1 hrun1 hcl1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes =
        curBs ++ bytesField 1 srk.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x0a#8]) ++ encodeVarint (BitVec.ofNat 64 srk.bytes.length)) ++ srk.bytes) ∗
          vecU8Buf A srk.cap srk.ptr srk.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          (a ↦₆₄ srk.cap) ∗ ((a + 8#64) ↦₆₄ srk.ptr) ∗
          ((a + 16#64) ↦₆₄ BitVec.ofNat 64 srk.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 1 srk.bytes) ∗ vecGhostAt A srk a ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_eq_cells_buf A a srk.cap srk.ptr srk.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2

theorem step_encChain_seg2_tag_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (v a curCap curPtr privPtr sp0 : BitVec 64) (curBs privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hcur_lt : curBs.length + 1 < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 176#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = ((v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      vecU8Buf A curCap curPtr curBs ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap2 ptr2 : BitVec 64),
      sm.pc = (blkPl_12).base + 236#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length →
      sm.readReg64 .x22 = privPtr →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := curCap) (ptr := curPtr) (bs := curBs)
    (F := (v ↦₆₄ curCap) ∗ ((v + 8#64) ↦₆₄ curPtr) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 curBs.length) ∗
      ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle => ?_
  have hpriv_nz := bv_ofNat_beq_zero_false hpriv_pos hpriv_lt
  by_cases hlt : curBs.length < curCap.toNat
  · have hbeq := cap_beq_len_false hlt
    have hlen1 := bv_len_add_one curBs 0x12#8
    rw [vecU8Buf_eq_open_one A curCap curPtr curBs hlt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [vecU8Buf_snoc_eq A curCap curPtr curBs 0x12#8 hlt]
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 privBs.length) v curCap curPtr sp0 ((blkPl_12).base + bv% (236))
      (curBs ++ [0x12#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hclm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hclm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))
  · have hcap_eq : curCap.toNat = curBs.length := by omega
    have hcap_bv := cap_eq_ofNat_len hcap_eq
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine step_encChain_reserve1_placed A H hDR v curCap curPtr sp0 ((blkPl_12).base + bv% (1800))
      curBs hcap_eq (by omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_gt
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    have hlen1 := bv_len_add_one curBs 0x12#8
    rw [vecU8Buf_eq_open_one A newCap p' curBs hnew_gt]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun y => ?_
    apply sepWPp_of_sepWP_lscl hclr (mid := lsmpl.base 10)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    rw [vecU8Buf_snoc_eq A newCap p' curBs 0x12#8 hnew_gt]
    refine step_encChain_encodeVarint_placed A H hEV
      (BitVec.ofNat 64 privBs.length) v newCap p' sp0 ((blkPl_12).base + bv% (236))
      (curBs ++ [0x12#8])
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by rw [vecU8At_eq_cells_buf]; ac_rfl) ?_
    intro sm cap2 ptr2 hpcm hrunm hclm hspm htrm hcsm
    have hGoalEq :
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗ F) =
        ((vecU8At A v cap2 ptr2
          ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 privBs.length)) ∗
          ((a + 32#64) ↦₆₄ privPtr) ∗ ((a + 40#64) ↦₆₄ BitVec.ofNat 64 privBs.length) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by ac_rfl
    rw [hGoalEq]
    exact hnext sm cap2 ptr2 hpcm hrunm hclm hspm htrm
      (hcsm.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.1.trans (by simp only [arm64_norm, *]))
      (hcsm.2.2.2.1.trans (by simp only [arm64_norm, *]))

theorem step_encChain_seg2_copy_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (v a cap2 ptr2 privCap privPtr sp0 : BitVec 64) (bsMid privBs : List (BitVec 8))
    (hpriv_pos : 0 < privBs.length)
    (hpriv_lt : privBs.length < 2 ^ 32)
    (hmid_lt : bsMid.length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 236#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 privBs.length)
    (hx22 : s.readReg64 .x22 = privPtr)
    (hP : P = ((v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      vecU8Buf A privCap privPtr privBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap3 ptr3 : BitVec 64),
      sm.pc = (blkPl_12).base + 284#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap3 ptr3 (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := cap2) (ptr := ptr2) (bs := bsMid)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A privCap privPtr privBs ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hle2 => ?_
  refine sepWPp_extract_vecU8Buf_le (A := A) (cap := privCap) (ptr := privPtr) (bs := privBs)
    (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
      ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
      vecU8Buf A cap2 ptr2 bsMid ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
    (by ac_rfl) fun hpriv_le => ?_
  have hlen_add := bv_len_add_slice bsMid privBs
  by_cases hfit : bsMid.length + privBs.length ≤ cap2.toNat
  · have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = false :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).2.mpr hfit
    apply sepWPp_of_sepWP_lscl hcl (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    rw [vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
    refine step_encChain_memcpy_placed A H hmc cap2 ptr2 privPtr sp0 ((blkPl_12).base + bv% (276))
      bsMid privBs hpriv_pos hfit hpriv_lt
      (x := x)
      (F := (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A privCap privPtr privBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hclm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclm (mid := (blkPl_12).base + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    have hGoalEq :
        ((vecU8Buf A cap2 ptr2 (bsMid ++ privBs) ∗ (privPtr ↦ₛ privBs)) ∗
          (v ↦₆₄ cap2) ∗ ((v + 8#64) ↦₆₄ ptr2) ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ privBs).length) ∗
          vecReadRest A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v cap2 ptr2 (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ cap2 ptr2 (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hrem : cap2.toNat - bsMid.length < privBs.length := by omega
    have hult : (cap2 - BitVec.ofNat 64 bsMid.length).ult (BitVec.ofNat 64 privBs.length) = true :=
      (spare_ult_iff hle2 hmid_lt hpriv_lt).1.mpr hrem
    apply sepWPp_of_sepWP_lscl hcl (mid := lsmpl.base 13)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl1
    refine step_encChain_reserveSlice_placed A H hDR v cap2 ptr2 sp0 ((blkPl_12).base + bv% (1832))
      bsMid privBs.length hle2 hrem hmid_lt hpriv_lt
      (x := x)
      (F := vecU8Buf A privCap privPtr privBs ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl1
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sr newCap p' hpcr hrunr hclr hspr htrr hcsr hnew_ge hult_false
    have hule_true := ule_of_ult_false hult_false
    have hx19r : sr.readReg64 .x19 = v := hcsr.1.trans (by simp only [arm64_norm, *])
    have hx20r : sr.readReg64 .x20 = a := hcsr.2.1.trans (by simp only [arm64_norm, *])
    have hx21r : sr.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsr.2.2.1.trans (by simp only [arm64_norm, *])
    have hx22r : sr.readReg64 .x22 = privPtr :=
      hcsr.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclr (mid := lsρ lsMemcpySym)
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl2
    rw [vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
    refine step_encChain_memcpy_placed A H hmc newCap p' privPtr sp0 ((blkPl_12).base + bv% (276))
      bsMid privBs hpriv_pos hnew_ge hpriv_lt
      (x := x)
      (F := (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
        ((v + 16#64) ↦₆₄ BitVec.ofNat 64 bsMid.length) ∗
        vecReadRest A privCap privPtr privBs ∗
        A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F)
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl2
      (by simp only [arm64_norm, *]) halign
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by ac_rfl) ?_
    intro sm hpcm hrunm hclm hspm htrm hcsm
    have hx19m : sm.readReg64 .x19 = v := hcsm.1.trans (by simp only [arm64_norm, *])
    have hx20m : sm.readReg64 .x20 = a := hcsm.2.1.trans (by simp only [arm64_norm, *])
    have hx21m : sm.readReg64 .x21 = BitVec.ofNat 64 privBs.length :=
      hcsm.2.2.1.trans (by simp only [arm64_norm, *])
    have hx23m : sm.readReg64 .x23 = BitVec.ofNat 64 bsMid.length :=
      hcsm.2.2.2.2.1.trans (by simp only [arm64_norm, *])
    apply sepWPp_of_sepWP_lscl hclm (mid := (blkPl_12).base + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hcl3
    have hGoalEq :
        ((vecU8Buf A newCap p' (bsMid ++ privBs) ∗ (privPtr ↦ₛ privBs)) ∗
          (v ↦₆₄ newCap) ∗ ((v + 8#64) ↦₆₄ p') ∗
          ((v + 16#64) ↦₆₄ BitVec.ofNat 64 (bsMid ++ privBs).length) ∗
          vecReadRest A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack ∗ F) =
        ((vecU8At A v newCap p' (bsMid ++ privBs) ∗
          vecU8Buf A privCap privPtr privBs ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      rw [vecU8At_eq_cells_buf, vecU8Buf_eq_open_bytes A privCap privPtr privBs hpriv_pos hpriv_le]
      ac_rfl
    rw [hGoalEq]
    exact hnext _ newCap p' (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hcl3
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])

theorem step_encChain_seg2_placed [LibsignalPlacement] (A : RustAlloc)
    (H : String → Option (State → State))
    (hEV : subroutine_ok ((blkPC_10).rebase (blkPl_10).base H) (blkPl_10).base
      (withLsCodeLoaded lsmpl (encodeVarintSpec A)))
    (hDR : subroutine_ok ((blkPC_13).rebase (blkPl_13).base H) (blkPl_13).base
      (withLsCodeLoaded lsmpl (doReserveSpec A)))
    (hmc : HookSat H lsMemcpySym framelessMemcpySpec)
    (v a curCap curPtr sp0 : BitVec 64) (priv : VecGhost) (curBs : List (BitVec 8))
    (hbound : curBs.length + (bytesField 2 priv.bytes).length < 2 ^ 32)
    {x : EncodeChainGhost} {R : SepProp}
    {ret : BitVec 64} {s0 s : State} {P F : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_12).base + 176#64)
    (hrun : s.status = .Running)
    (hcl : LibsignalCodeLoaded lsmpl s.mem)
    (hsp : s.sp = sp0 - 96#64)
    (halign : sp0 &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace ∧ calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = v)
    (hx20 : s.readReg64 .x20 = a)
    (hP : P = (vecU8At A v curCap curPtr curBs ∗ vecGhostAt A priv (a + 24#64) ∗
      A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
    (hnext : ∀ (sm : State) (cap' ptr' : BitVec 64),
      sm.pc = (blkPl_12).base + 284#64 →
      sm.status = .Running →
      LibsignalCodeLoaded lsmpl sm.mem →
      sm.sp = sp0 - 96#64 →
      sm.trace = s0.trace ∧ calleeSavedVRegs sm = calleeSavedVRegs s0 →
      sm.readReg64 .x19 = v →
      sm.readReg64 .x20 = a →
      SepWPp (lsProg_12 H) ret sm
        ((vecU8At A v cap' ptr' (curBs ++ bytesField 2 priv.bytes) ∗ vecGhostAt A priv (a + 24#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R))) :
    SepWPp (lsProg_12 H) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (encodeChainSpec A).onPanic x s0 sf ∗ R)) := by
  subst hP
  by_cases hnil : priv.bytes = []
  · unfold vecGhostAt
    rw [vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    have hlen0 : BitVec.ofNat 64 priv.bytes.length = 0#64 := by simp [hnil]
    apply sepWPp_of_sepWP_lscl hcl (mid := (blkPl_12).base + bv% (284))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    intro hclm
    have hbf0 : curBs ++ bytesField 2 priv.bytes = curBs := by simp [bytesField, hnil]
    rw [← vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes, ← hbf0]
    exact hnext _ curCap curPtr (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *]) hclm
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  · have hpriv_pos : 0 < priv.bytes.length := List.length_pos_iff.mpr hnil
    have hbf_eq : [0x12#8] ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length) ++ priv.bytes =
        bytesField 2 priv.bytes :=
      bytesField_nonempty_eq 2 0x12#8 priv.bytes hnil (by decide +kernel)
    have hbf_len : 1 + (encodeVarint (BitVec.ofNat 64 priv.bytes.length)).length + priv.bytes.length =
        (bytesField 2 priv.bytes).length := by
      have h := congrArg List.length hbf_eq
      simp only [List.length_append, List.length_singleton] at h
      omega
    have ⟨hvar_pos, _⟩ := encodeVarint_length_bounds (BitVec.ofNat 64 priv.bytes.length)
    unfold vecGhostAt
    rw [vecU8At_eq_cells_buf A v curCap curPtr curBs,
        vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
    refine step_encChain_seg2_tag_placed A H hEV hDR
      v a curCap curPtr priv.ptr sp0 curBs priv.bytes
      hpriv_pos (by omega) (by omega)
      (x := x)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ vecU8Buf A priv.cap priv.ptr priv.bytes ∗ F)
      hpc hrun hcl hsp halign htr hx19 hx20 (by ac_rfl) ?_
    intro s1 cap2 ptr2 hpc1 hrun1 hcl1 hsp1 htr1 hx19_1 hx20_1 hx21_1 hx22_1
    rw [vecU8At_eq_cells_buf A v cap2 ptr2
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length))]
    refine step_encChain_seg2_copy_placed A H hDR hmc
      v a cap2 ptr2 priv.cap priv.ptr sp0
      ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) priv.bytes
      hpriv_pos (by omega)
      (by simp only [List.length_append, List.length_singleton]; omega)
      (x := x)
      (F := ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
        ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F)
      hpc1 hrun1 hcl1 hsp1 halign htr1 hx19_1 hx20_1 hx21_1 hx22_1 (by ac_rfl) ?_
    intro s2 cap3 ptr3 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2
    have hlist : ((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes =
        curBs ++ bytesField 2 priv.bytes := by
      rw [← hbf_eq]; simp [List.append_assoc]
    have hGoalEq :
        ((vecU8At A v cap3 ptr3
          (((curBs ++ [0x12#8]) ++ encodeVarint (BitVec.ofNat 64 priv.bytes.length)) ++ priv.bytes) ∗
          vecU8Buf A priv.cap priv.ptr priv.bytes ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗
          ((a + 24#64) ↦₆₄ priv.cap) ∗ ((a + 32#64) ↦₆₄ priv.ptr) ∗
          ((a + 40#64) ↦₆₄ BitVec.ofNat 64 priv.bytes.length) ∗ F) =
        ((vecU8At A v cap3 ptr3 (curBs ++ bytesField 2 priv.bytes) ∗ vecGhostAt A priv (a + 24#64) ∗
          A.pool ∗ stackAt (sp0 - 96#64) encChainSubStack) ∗ F) := by
      unfold vecGhostAt
      rw [hlist, vecU8At_add24_eq_cells_buf A a priv.cap priv.ptr priv.bytes]
      ac_rfl
    rw [hGoalEq]
    exact hnext s2 cap3 ptr3 hpc2 hrun2 hcl2 hsp2 htr2 hx19_2 hx20_2

end Placed

end CryptoVerification.E2E.Record.Serialization

