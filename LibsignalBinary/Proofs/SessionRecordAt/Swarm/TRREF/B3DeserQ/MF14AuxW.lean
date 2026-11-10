/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF14Aux.Pure
public import LibsignalBinary.Proofs.SessionRecordAt.Swarm.TRREF.B3DeserQ.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# W-Stack Helpers and Specifications for `SessionStructure::merge_field` on Tag 14

Defines the `SP2Ext` specifications, layout-independent decode/rodata/callee helpers, and stack
frame decompositions for `SessionStructure::merge_field` on protobuf tag 14
(`pending_kyber_pre_key` at `ss + 0x128`, `kyberAt14` / `prostSSGXNoPqAt_x14`) at
`mergeFieldStackX = 32768` with slice length `< 2 ^ 62`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.TRREF.B3DeserQ

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification CryptoVerification.E2E.Record
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)
open Proofs.libsignal.Hooks2

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

theorem L1_MF14AuxW : True := trivial

/-! ## Decode, step, call, stack, and payload helpers -/

gen_decodes CryptoVerification.libsignalSessionCode_tree mf14W
  [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 60),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 368) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 440),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1208) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1252),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1320) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1436),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1440) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1676),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1680) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1724),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1880) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1904),
   (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2328) →
     (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2356)]

theorem mergeField_fnOff_mf14W :
    CryptoVerification.libsignalSessionCode.fnOff mergeFieldName =
      num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") :=
  ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"

set_option allowUnsafeReducibility true in
attribute [local semireducible] SepWP in
theorem step_ldr8_ro_mf14 {prog : Program} {target_pc : BitVec 64}
    {s : State} {P : SepProp} {post : State → SepProp → Prop}
    {pc pc' : BitVec 64} {rt : Reg} {addr : AddrMode}
    {ea : BitVec 64} {wb : Option (Reg × BitVec 64)} {v : BitVec 8}
    {r : Reg} {v64 : BitVec 64}
    (hpc : s.pc = pc)
    (hrun : s.status = .Running)
    (hfetch : prog.fetch pc = some (.ldr .W32 .B8 false rt addr))
    (hsp : checkAddrSPAligned s addr = true)
    (haddr : evalAddrMode s addr = (ea, wb))
    (hread : s.mem.read8 ea = v)
    (hcan : s.mem.canRead ea 1 = true)
    (hexec : ((applyWriteback s wb).writeReg .W32 rt (v.zeroExtend 64)).setPC (pc + 4#64) =
      (s.writeReg64 r v64).setPC pc')
    (hnext : SepWP prog target_pc ((s.writeReg64 r v64).setPC pc') P post) :
    SepWP prog target_pc s P post := by
  intro R hm
  have hfetch' : prog.fetch s.pc = some (.ldr .W32 .B8 false rt addr) := hpc.symm ▸ hfetch
  apply reaches_pc_step hrun hfetch'
  have hstep : execInst (.ldr .W32 .B8 false rt addr) s = (s.writeReg64 r v64).setPC pc' := by
    rw [← hexec]
    cases wb <;> simp [execInst, execInstWithSvc, execLdr, Memory.readSized, State.writeReg,
      applyWriteback, State.advancePC, State.setPC, hsp, haddr, hread, hcan, MemWidth.bytes, hpc]
  rw [Program.evalInst_of_isSvc0Instr_false _ _ _ rfl, hstep]
  apply hnext R
  exact hm

theorem adrp_rodata_mf14W (b : BitVec 64) (hb : b &&& 4095#64 = 0#64) :
    (b + bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") + 40#64 &&&
      bv% (2 ^ 64 - 4096)) +
      bv% (ls_bytes% "0082775f19328d6db5d6cb6d" -
        page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 40)) =
      b + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
  bv_arith

theorem of_sepWP_frozen_mf14 {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P (fun sm Pm =>
      img.FrozenLoaded sm → sm.symtab = img.symtab → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  ProofLib.SepWPp.of_sepWP_frozen hfl hsym h

theorem call_alloc_mf14 {α β : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s s0 : State} {P R : SepProp} {Q : State → SepProp → Prop} {y : β}
    (hcall : subroutine_ok prog entry spec)
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)))
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)) := by
  refine ProofLib.SepWPp.call_frame_frozen hcall hfl hsym hpc hrun hsp hlr hspec hφ hP
    (fun sf code R' _ hex => by rw [hexit] at hex; exact not_satisfies_false_sepConj hex)
    (fun sm _ hm' => ?_)
    hnext
    (fun sf R' _ hpost => by rw [hoom] at hpost; exact (not_satisfies_false_sepConj hpost).elim)
  rw [hpan] at hm'
  dsimp only [allocPanic]
  exact allowPanic_frame (fun h => by simpa only [allocFailedIn, htr] using h) hm'

theorem stackAt_split_top_mf14 (sp : BitVec 64) (n d : Nat) (h : n + d ≤ 2 ^ 64) :
    stackAt sp (n + d) = stackAt (sp - BitVec.ofNat 64 d) n ∗
      memRegion (sp - BitVec.ofNat 64 d) d := by
  simp only [stackAt]
  rw [memRegion_split' (n := n) (k := d) rfl rfl h]
  have e1 : sp - BitVec.ofNat 64 (n + d) = sp - BitVec.ofNat 64 d - BitVec.ofNat 64 n := by
    rw [BitVec.sub_sub, ← BitVec.ofNat_add, Nat.add_comm]
  have e2 : sp - BitVec.ofNat 64 (n + d) + BitVec.ofNat 64 n = sp - BitVec.ofNat 64 d := by
    rw [e1, BitVec.sub_add_cancel]
  rw [e2, e1]

theorem stackAt_split_bottom_mf14 (sp : BitVec 64) (N n d : Nat) (hN : N = n + d := by decide)
    (h : n + d ≤ 2 ^ 64 := by decide) :
    stackAt sp N = memRegion (sp - BitVec.ofNat 64 N) d ∗ stackAt sp n := by
  subst hN
  simp only [stackAt]
  rw [show n + d = d + n by omega,
    memRegion_split' (n := d) (k := n) (by omega) rfl (by omega)]
  congr 2
  rw [BitVec.ofNat_add, BitVec.add_comm (BitVec.ofNat 64 d), ← BitVec.sub_sub,
    BitVec.sub_add_cancel]

theorem memRegion160_split_mf14 (sp0 : BitVec 64) :
    memRegion (sp0 - 240#64) 160 =
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗ memRegion (sp0 - 208#64) 128 := by
  rw [memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 232#64) (n := 8) (k := 152)
        rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 232#64) (b' := sp0 - 208#64) (n := 24) (k := 128)
        rfl (by bv_lin) (by decide)]

theorem memRegion160_fold_mf14 (sp0 : BitVec 64) :
    memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗ memRegion (sp0 - 208#64) 128 =
      memRegion (sp0 - 240#64) 160 :=
  (memRegion160_split_mf14 sp0).symm

theorem pointsTo64_zero_split32_mf14 (sp0 : BitVec 64) :
    ((sp0 - 232#64) ↦₆₄ 0#64) =
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) := by
  have hs := pointsTo64_split32 (sp0 - 232#64) 0#64
  have ha : (sp0 - 232#64) + 4#64 = sp0 - 228#64 := by bv_omega
  simpa [ha] using hs

theorem cells24_entails_memRegion24_mf14 (sp0 w1 w2 : BitVec 64) :
    ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ w1) ∗ ((sp0 - 216#64) ↦₆₄ w2) ⊢
    memRegion (sp0 - 232#64) 24 := by
  rw [← sepConj_assoc, ← pointsTo64_zero_split32_mf14 sp0]
  rw [memRegion_split' (b := sp0 - 232#64) (b' := sp0 - 224#64) (n := 8) (k := 16)
        rfl (by bv_lin) (by decide),
      memRegion_split' (b := sp0 - 224#64) (b' := sp0 - 216#64) (n := 8) (k := 8)
        rfl (by bv_lin) (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  exact sepConj_mono (Entails.sepExists_right 0#64 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

theorem sliceCursorAt_kyber_unfold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1574 + tail.length)) ∗
      (ptr ↦ₛ (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) := by
  unfold Prost.sliceCursorAt
  rw [kyber_payload_tail_length hct, kyber_payload_tail_eq hct]

theorem bytes_kyber_split_mf14 (ptr : BitVec 64) (ib : List (BitVec 8)) :
    (ptr ↦ₛ (164#8 :: 12#8 :: 18#8 :: ib)) =
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ ib) := by
  simp only [pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + 1#64 = ptr + 3#64 by bv_lin]

theorem sliceCursorAfter_inner_unfold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAfter slot (ptr + 3#64) (innerBytes ct tail) tail =
      (slot ↦₆₄ (ptr + 1574#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) := by
  unfold Prost.sliceCursorAfter
  have hsub : (innerBytes ct tail).length - tail.length = 1571 := by
    rw [innerBytes_length hct]; omega
  have hadd : ptr + 3#64 + BitVec.ofNat 64 1571 = ptr + 1574#64 := by bv_lin
  rw [hsub, hadd]

theorem sliceCursorAt_inner_fold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1571 + tail.length)) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAt slot (ptr + 3#64) (innerBytes ct tail) := by
  unfold Prost.sliceCursorAt
  rw [innerBytes_length hct]

theorem sliceCursorAfter_kyber_fold_mf14 (slot ptr : BitVec 64) {ct : List (BitVec 8)}
    (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 1574#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter
  have hsub : ((GenFieldX.kyber 0#32 ct).payload ++ tail).length - tail.length = 1574 := by
    rw [kyber_payload_tail_length hct]; omega
  rw [hsub, kyber_payload_tail_eq hct, bytes_kyber_split_mf14]

theorem decode_kyber_result_mf14 {ct : List (BitVec 8)} (_hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A0 ret (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)
      (decodeVarint (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail)) =
      (ret ↦₆₄ 0#64) ∗ ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 1572) ∗
        ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber]
  dsimp only [Prost.varintSliceResultAt]
  have : (164#8 :: 12#8 :: 18#8 :: innerBytes ct tail).length -
      (18#8 :: innerBytes ct tail).length = 2 := by
    simp only [List.length_cons]; omega
  rw [this]

def kyberPtr2 (ptr : BitVec 64) (i : BitVec 32) : BitVec 64 :=
  ptr + 3#64 + BitVec.ofNat 64 (encodeVarint (i.setWidth 64)).length

theorem sliceCursorAt_kyber_ne_unfold_mf14 (slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAt slot ptr ((GenFieldX.kyber i ct).payload ++ tail) =
      (slot ↦₆₄ ptr) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      (ptr ↦ₛ (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) := by
  unfold Prost.sliceCursorAt
  rw [kyber_ne_payload_tail_length hi hct, kyber_ne_payload_tail_eq hi hct]

theorem bytes_kyber_ne_split_mf14 (ptr : BitVec 64) (i : BitVec 32) (ib : List (BitVec 8)) :
    (ptr ↦ₛ (kyberB0 i :: 12#8 :: 8#8 :: ib)) =
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ ib) := by
  simp only [pointsToBytes_cons,
    show ptr + 1#64 + 1#64 = ptr + 2#64 by bv_lin,
    show ptr + 2#64 + 1#64 = ptr + 3#64 by bv_lin]

theorem decode_kyber_ne_result_mf14 (i : BitVec 32) {ct : List (BitVec 8)} (_hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ret : BitVec 64) :
    Prost.varintSliceResultAt A0 ret (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)
      (decodeVarint (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail)) =
      (ret ↦₆₄ 0#64) ∗
        ((ret + 8#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((ret + 16#64) ↦₆₄ 2#64) := by
  rw [decodeVarint_kyber_ne]
  dsimp only [Prost.varintSliceResultAt]
  have : (kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail).length -
      (8#8 :: kyberIdBytes i ct tail).length = 2 := by
    simp only [List.length_cons]; omega
  rw [this]

theorem sliceCursorAt_kyberId_fold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) =
      Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) := by
  unfold Prost.sliceCursorAt
  rw [kyberIdBytes_length i hct]

theorem sliceCursorAfter_kyberId_unfold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAfter slot (ptr + 3#64) (kyberIdBytes i ct tail)
        (18#8 :: innerBytes ct tail) =
      (slot ↦₆₄ kyberPtr2 ptr i) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + tail.length)) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) := by
  unfold Prost.sliceCursorAfter kyberIdBytes kyberPtr2
  have hsub : (encodeVarint (i.setWidth 64) ++ 18#8 :: innerBytes ct tail).length -
      (18#8 :: innerBytes ct tail).length = (encodeVarint (i.setWidth 64)).length := by
    rw [List.length_append]; omega
  have hlen : (18#8 :: innerBytes ct tail).length = 1572 + tail.length := by
    rw [List.length_cons, innerBytes_length hct]; omega
  rw [hsub, hlen, pointsToBytes_append, pointsToBytes_cons]

theorem sliceCursorAt_inner_ne_fold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (kyberPtr2 ptr i + 1#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1571 + tail.length)) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAt slot (kyberPtr2 ptr i + 1#64) (innerBytes ct tail) := by
  unfold Prost.sliceCursorAt
  rw [innerBytes_length hct]

theorem sliceCursorAfter_inner_ne_unfold_mf14 (slot ptr : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    Prost.sliceCursorAfter slot (kyberPtr2 ptr i + 1#64) (innerBytes ct tail) tail =
      (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) := by
  unfold Prost.sliceCursorAfter
  have hsub : (innerBytes ct tail).length - tail.length = 1571 := by
    rw [innerBytes_length hct]; omega
  have hadd : kyberPtr2 ptr i + 1#64 + BitVec.ofNat 64 1571 = kyberPtr2 ptr i + 1572#64 := by bv_lin
  rw [hsub, hadd]

theorem sliceCursorAfter_kyber_ne_fold_mf14 (slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) :
    (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) =
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail := by
  unfold Prost.sliceCursorAfter
  have hsub : ((GenFieldX.kyber i ct).payload ++ tail).length - tail.length =
      1575 + (encodeVarint (i.setWidth 64)).length := by
    rw [kyber_ne_payload_tail_length hi hct]; omega
  have hptr : ptr + BitVec.ofNat 64 (1575 + (encodeVarint (i.setWidth 64)).length) =
      kyberPtr2 ptr i + 1572#64 := by
    unfold kyberPtr2
    rw [BitVec.ofNat_add]
    bv_lin
  rw [hsub, hptr, kyber_ne_payload_tail_eq hi hct, bytes_kyber_ne_split_mf14]
  unfold kyberIdBytes
  rw [pointsToBytes_append, pointsToBytes_cons, ← kyberPtr2]

/-! ## Tag-14 field slice (`kyberAt14`), `restX14NoPq`, and `prostSSGXNoPqAt_x14` -/

/-- Standalone 32-byte `pending_kyber_pre_key: Option<PendingKyberPreKey>` slice at `ss + 0x128`. -/
def kyberAt14 (A : RustAlloc) (ss : BitVec 64)
    (kyber : Option (BitVec 32 × List (BitVec 8))) : SepProp :=
  match kyber with
  | none => ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24
  | some (i, ct) => vecU8 A (ss + 0x128#64) ct ∗ ((ss + 0x140#64) ↦₃₂ i) ∗
      memRegion (ss + 0x144#64) 4

/-- `prostSSGXNoPqAt_x14` without the pending Kyber pre-key @0x128 (32 bytes): unchanged by tag 14. -/
def restX14NoPq (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    ((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
    ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ ((ss + 0x154#64) ↦₃₂ v.ext.locReg)

theorem prostSSGXAt_eq_noPq_sep_emptyPq_x14 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A ss v = prostSSGXNoPqAt_x14 A ss v ∗ vecU8 A (ss + 0x78#64) v.ext.pq := by
  unfold prostSSGXAt prostSSGXNoPqAt_x14
  ac_rfl

theorem restX14_eq_noPq_sep_emptyPq_x14 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    restX14 A ss v = restX14NoPq A ss v ∗ vecU8 A (ss + 0x78#64) v.ext.pq := by
  unfold restX14 restX14NoPq
  ac_rfl

theorem prostSSGXNoPqAt_x14_eq_kyber_sep_rest (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXNoPqAt_x14 A ss v = kyberAt14 A ss v.ext.kyber ∗ restX14NoPq A ss v := by
  unfold prostSSGXNoPqAt_x14 kyberAt14 restX14NoPq
  cases v.ext.kyber with
  | none =>
    dsimp only [kyberAt]
    ac_rfl
  | some p =>
    rcases p with ⟨i, ct⟩
    dsimp only [kyberAt]
    ac_rfl

theorem restX14NoPq_apply_kyber (A : RustAlloc) (ss : BitVec 64) (v : SSGX) (i : BitVec 32)
    (ct : List (BitVec 8)) : restX14NoPq A ss (v.apply (.kyber i ct)) = restX14NoPq A ss v := rfl

theorem kyberAt14_none_unfold (A : RustAlloc) (ss : BitVec 64) (v : SSGX)
    (hk : v.ext.kyber = none) :
    kyberAt14 A ss v.ext.kyber =
      ((ss + 0x128#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w130 : BitVec 64, (ss + 0x130#64) ↦₆₄ w130) ∗
      (∃∗ w138 : BitVec 64, (ss + 0x138#64) ↦₆₄ w138) ∗
      (∃∗ w140 : BitVec 32, (ss + 0x140#64) ↦₃₂ w140) ∗
      memRegion (ss + 0x144#64) 4 := by
  unfold kyberAt14
  rw [hk, memRegion_24_split_kyber ss]
  dsimp only [noneCap]

theorem kyberAt14_some_fold (A : RustAlloc) (ss cap' ptr' : BitVec 64) (v : SSGX)
    (i : BitVec 32) (ct : List (BitVec 8)) :
    vecU8At A (ss + 0x128#64) cap' ptr' ct ∗
      ((ss + 0x140#64) ↦₃₂ i) ∗ memRegion (ss + 0x144#64) 4 ⊢
      kyberAt14 A ss (v.apply (.kyber i ct)).ext.kyber := by
  have hv : vecU8At A (ss + 0x128#64) cap' ptr' ct ⊢ vecU8 A (ss + 0x128#64) ct := by
    unfold vecU8
    exact Entails.trans
      (Entails.sepExists_intro (P := fun ptr => vecU8At A (ss + 0x128#64) cap' ptr ct) ptr')
      (Entails.sepExists_intro (P := fun cap => ∃∗ ptr, vecU8At A (ss + 0x128#64) cap ptr ct) cap')
  refine Entails.trans (sepConj_mono_left hv) ?_
  unfold kyberAt14 SSGX.apply
  dsimp only
  apply Entails.of_eq
  ac_rfl

/-! ## W-stack specifications for `merge_field` on tag 14 -/

def mergeField14KyberSpecAtW (img : Obj.Image) (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      kyberAt14 A0 x.ss x.v.ext.kyber ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      kyberAt14 A0 x.ss (x.v.apply x.fld).ext.kyber ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField14KyberOkAtW (img : Obj.Image) (ext : String → Option (State → State))
    (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField14KyberSpecAtW img P)

def mergeField14SpecAtW (img : Obj.Image) (P : GenFieldX → Prop) : Spec MergeFieldXGhost where
  pre := fun x s =>
    ⌜s.readReg64 .x0 = x.ss ∧ (s.readReg64 .x1).setWidth 32 = BitVec.ofNat 32 x.fld.tag ∧
      (s.readReg64 .x2).setWidth 8 = BitVec.ofNat 8 x.fld.wt.toNat ∧ s.readReg64 .x3 = x.bufRef ∧
      (s.readReg64 .x4).setWidth 32 = 99#32 ∧ P x.fld ∧ x.fld.Ok ∧ x.fld.Fresh x.v ∧
      (x.fld.payload ++ x.tail).length < 2 ^ 62 ∧
      img.FrozenLoaded s ∧ s.symtab = img.symtab⌝ ∗
      prostSSGXNoPqAt_x14 A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s.sp mergeFieldStackX
  post := fun x s0 sf =>
    ⌜sf.trace = s0.trace ∧ sf.readReg64 .x0 = 0#64⌝ ∗
      prostSSGXNoPqAt_x14 A0 x.ss (x.v.apply x.fld) ∗
      (x.bufRef ↦₆₄ x.slot) ∗
      Prost.sliceCursorAfter x.slot x.ptr (x.fld.payload ++ x.tail) x.tail ∗
      stackAt s0.sp mergeFieldStackX
  onPanic := allocPanic

def MergeField14OkAtW (img : Obj.Image) (ext : String → Option (State → State))
    (P : GenFieldX → Prop) : Prop :=
  OkAtX img.base ext mergeFieldName (mergeField14SpecAtW img P)

theorem mergeField14OkAtW_of_kyber {img : Obj.Image}
    {ext : String → Option (State → State)} {P : GenFieldX → Prop}
    (hP14 : ∀ fl, P fl → fl.tag = 14)
    (hP : MergeField14KyberOkAtW img ext P) :
    MergeField14OkAtW img ext P := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  simp only [mergeField14SpecAtW, prostSSGXNoPqAt_x14_eq_kyber_sep_rest,
    sepConj_assoc, satisfies_pure_sepConj] at hpre
  obtain ⟨h0, hm⟩ := hpre
  obtain ⟨i, ct, hfl⟩ := (genFieldX_tag_eq_14_iff x.fld).mp (hP14 x.fld h0.2.2.2.2.2.1)
  have hpre' : s0.mem ⊨ (mergeField14KyberSpecAtW img P).pre x s0 ∗
      (restX14NoPq A0 x.ss x.v ∗ R) := by
    simp only [mergeField14KyberSpecAtW, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨h0, ?_⟩
    convert hm using 1; ac_rfl
  refine hP.mono_outcome x (restX14NoPq A0 x.ss x.v ∗ R) s0 hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, _, hpost⟩ | ⟨_, hpost⟩
  · left
    refine ⟨hret, hcc, ?_⟩
    simp only [mergeField14SpecAtW, prostSSGXNoPqAt_x14_eq_kyber_sep_rest,
      hfl, restX14NoPq_apply_kyber]
    simp only [mergeField14KyberSpecAtW, hfl] at hpost
    convert hpost using 1; ac_rfl
  · right; left
    refine ⟨hpan, ?_⟩
    dsimp only [mergeField14SpecAtW, mergeField14KyberSpecAtW] at hpost ⊢
    rw [← sepConj_assoc] at hpost
    exact allowPanic_frame id hpost
  · exact (allowPanic_not_exited hpost).elim
  · exact (allowPanic_not_exited hpost).elim

theorem okAtX_of_eq_pre_post_mf14 {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)} {name : String} {s1 s2 : Spec α}
    (h1 : OkAtX b ext name s1) (hpre : ∀ x s, s2.pre x s = s1.pre x s)
    (hpost : ∀ x s0 sf, s1.post x s0 sf = s2.post x s0 sf)
    (hpan : s1.onPanic = s2.onPanic) (hex : s1.onExit = s2.onExit)
    (hoom : s1.onOom = s2.onOom) : OkAtX b ext name s2 := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hp hal => ?_
  rw [hpre x s0] at hp
  refine h1.mono_outcome x R s0 hpc hrun hp hal fun sf hout => ?_
  rcases hout with ⟨hr, hc, hq⟩ | ⟨hp', hq⟩ | ⟨c, he, hq⟩ | ⟨ho, hq⟩
  · exact Or.inl ⟨hr, hc, hpost x s0 sf ▸ hq⟩
  · exact Or.inr (Or.inl ⟨hp', hpan ▸ hq⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨c, he, hex ▸ hq⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨ho, hoom ▸ hq⟩))

theorem okAtX_of_imp_frame_mf14 {α β : Type} {b : BitVec 64} {ext : String → Option (State → State)}
    {name : String} {specField : Spec α} {specFull : Spec β} (hField : OkAtX b ext name specField)
    (h_exit : ∀ (g : α) (code : BitVec 64) (s0 sf : State), specField.onExit g code s0 sf = ⌜False⌝)
    (h_panic : ∀ (g : α) (x : β) (s0 sf : State) (F R : SepProp),
      (sf.mem ⊨ specField.onPanic g s0 sf ∗ (F ∗ R)) → (sf.mem ⊨ specFull.onPanic x s0 sf ∗ R))
    (h_step : ∀ (x : β) (s0 : State) (R : SepProp), (s0.mem ⊨ specFull.pre x s0 ∗ R) →
      ∃ (g : α) (F : SepProp), (s0.mem ⊨ specField.pre g s0 ∗ (F ∗ R)) ∧
        (∀ sf : State, (sf.mem ⊨ specField.post g s0 sf ∗ (F ∗ R)) →
          (sf.mem ⊨ specFull.post x s0 sf ∗ R)))
    (h_oom : ∀ (g : α) (s0 sf : State), specField.onOom g s0 sf = ⌜False⌝) :
    OkAtX b ext name specFull := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  obtain ⟨g, F, hpre', hpost_imp⟩ := h_step x s0 R hpre
  refine hField.mono_outcome g (F ∗ R) s0 hpc hrun hpre' hal fun sf h_out => ?_
  rcases h_out with ⟨hret, hcc, hpost⟩ | ⟨hpan, hpanic⟩ | ⟨code, _, hexit⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost_imp sf hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, h_panic g x s0 sf F R hpanic⟩)
  · rw [h_exit g code s0 sf, satisfies_pure_sepConj] at hexit; exact False.elim hexit.1
  · rw [h_oom g s0 sf, satisfies_pure_sepConj] at hoom; exact False.elim hoom.1

theorem allocPanic_frame_mf14 {α β : Type} (g : α) (x : β) (s0 sf : State) (F R : SepProp)
    (hm : sf.mem ⊨ allocPanic g s0 sf ∗ (F ∗ R)) :
    sf.mem ⊨ allocPanic x s0 sf ∗ R := by
  dsimp only [allocPanic] at hm ⊢
  have hm' : sf.mem ⊨ ((⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R := by
    rw [sepConj_assoc]; exact hm
  exact allowPanic_frame id hm'

/-! ## Arithmetic helpers under `< 2 ^ 62` -/

theorem bv_ofNat_add_eq_mf14W (a b n : Nat) (_h : a + b + n < 2 ^ 62) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 (b + n) = BitVec.ofNat 64 (a + b + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem len_sub_mf14W {a b n : Nat} (hb : b ≤ a) (_h : a + n < 2 ^ 62) :
    BitVec.ofNat 64 (a + n) - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b + n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem wt_and_ff_eq_mf14W (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    r2.truncate 32 &&& 255#32 = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_and, BitVec.toNat_setWidth,
    BitVec.toNat_ofNat] at h ⊢
  change (r2.toNat % 4294967296 &&& (2 ^ 8 - 1)) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem wt_and_ff_64_eq_mf14W (r2 : BitVec 64) (hx2 : r2.setWidth 8 = 2#8) :
    BitVec.truncate 32 (BitVec.zeroExtend 64 (BitVec.truncate 32 r2) &&& 255#64) = 2#32 := by
  apply BitVec.eq_of_toNat_eq
  have h := congrArg BitVec.toNat hx2
  simp only [BitVec.truncate_eq_setWidth,
    BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat] at h ⊢
  change (((r2.toNat % 4294967296) % 18446744073709551616 &&& (2 ^ 8 - 1)) % 4294967296) = 2
  rw [Nat.and_two_pow_sub_one_eq_mod]
  omega

/-! ## W-stack decomposition (`mergeFieldStackX = 32768`, `mergeFieldSubStackX = 32528`) -/

theorem stackAt_mergeField_split_mf14W (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      memRegion (sp0 - 240#64) 160 ∗
      cells (sp0 - 80#64) 10 := by
  have htop := stackAt_split_top_mf14 sp0 mergeFieldSubStackX 240 (by decide)
  change stackAt sp0 mergeFieldStackX =
    stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ memRegion (sp0 - 240#64) 240 at htop
  rw [htop,
      memRegion_split' (b := sp0 - 240#64) (b' := sp0 - 80#64) (n := 160) (k := 80)
        rfl (by bv_lin) (by decide),
      show (80 : Nat) = 8 * 10 by rfl,
      LibsignalTripleRatchet.memRegion_cells (sp0 - 80#64) 10 (by decide)]

theorem stackAt_sub_to_decode_mf14W (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 7872 ∗ stackAt sp Prost.X.decodeVarintSliceStackW :=
  stackAt_split_bottom_mf14 sp mergeFieldSubStackX Prost.X.decodeVarintSliceStackW 7872

theorem stackAt_sub_to_int32Merge_mf14W (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 7792 ∗ stackAt sp Prost.X.int32MergeStackW :=
  stackAt_split_bottom_mf14 sp mergeFieldSubStackX Prost.X.int32MergeStackW 7792

theorem stackAt_sub_to_bytesMerge_mf14W (sp : BitVec 64) :
    stackAt sp mergeFieldSubStackX =
      memRegion (sp - 32528#64) 7648 ∗ stackAt sp Prost.X.bytesMergeStackW :=
  stackAt_split_bottom_mf14 sp mergeFieldSubStackX Prost.X.bytesMergeStackW 7648

theorem decode_to_int32Merge_stack_mf14W (sp : BitVec 64) :
    memRegion (sp - 32528#64) 7872 ∗ stackAt sp Prost.X.decodeVarintSliceStackW =
      memRegion (sp - 32528#64) 7792 ∗ stackAt sp Prost.X.int32MergeStackW := by
  rw [← stackAt_sub_to_decode_mf14W, stackAt_sub_to_int32Merge_mf14W]

theorem decode_to_bytesMerge_stack_mf14W (sp : BitVec 64) :
    memRegion (sp - 32528#64) 7872 ∗ stackAt sp Prost.X.decodeVarintSliceStackW =
      memRegion (sp - 32528#64) 7648 ∗ stackAt sp Prost.X.bytesMergeStackW := by
  rw [← stackAt_sub_to_decode_mf14W, stackAt_sub_to_bytesMerge_mf14W]

theorem int32Merge_to_bytesMerge_stack_mf14W (sp : BitVec 64) :
    memRegion (sp - 32528#64) 7792 ∗ stackAt sp Prost.X.int32MergeStackW =
      memRegion (sp - 32528#64) 7648 ∗ stackAt sp Prost.X.bytesMergeStackW := by
  rw [← stackAt_sub_to_int32Merge_mf14W, stackAt_sub_to_bytesMerge_mf14W]

theorem stackAt_mergeField_unfold_mf14W (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStackX =
      ∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64,
      ∃∗ v8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
        memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗
        memRegion (sp0 - 208#64) 128 ∗
        memRegion (sp0 - 240#64 - 32528#64) 7872 ∗
        stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW := by
  have h1 : stackAt sp0 mergeFieldStackX =
      cells (sp0 - 80#64) 10 ∗
      (memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 232#64) 24 ∗
        memRegion (sp0 - 208#64) 128 ∗
        memRegion (sp0 - 240#64 - 32528#64) 7872 ∗
        stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW) := by
    rw [stackAt_mergeField_split_mf14W sp0, memRegion160_split_mf14 sp0,
      stackAt_sub_to_decode_mf14W (sp0 - 240#64)]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin,
    sepConj_assoc]

theorem stackAt_mergeField_fold_mf14W (sp0 v80 v72 v64 v56 v48 v40 v32 v24 v16 v8 : BitVec 64) :
    ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
      ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
      ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
      ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
      ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
      memRegion (sp0 - 240#64) 160 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ⊢
      stackAt sp0 mergeFieldStackX := by
  have h1 : stackAt sp0 mergeFieldStackX =
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX) ∗
      cells (sp0 - 80#64) 10 := by
    rw [stackAt_mergeField_split_mf14W sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, ← sepExists_sepConj_left,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin]
  refine Entails.trans (Q :=
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStackX) ∗
    (((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
     ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
     ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
     ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
     ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8)))
    (by apply Entails.of_eq; ac_rfl) ?_
  refine sepConj_mono_right ?_
  refine sepConj_mono (Entails.sepExists_intro v80) ?_
  refine sepConj_mono (Entails.sepExists_intro v72) ?_
  refine sepConj_mono (Entails.sepExists_intro v64) ?_
  refine sepConj_mono (Entails.sepExists_intro v56) ?_
  refine sepConj_mono (Entails.sepExists_intro v48) ?_
  refine sepConj_mono (Entails.sepExists_intro v40) ?_
  refine sepConj_mono (Entails.sepExists_intro v32) ?_
  refine sepConj_mono (Entails.sepExists_intro v24) ?_
  refine sepConj_mono (Entails.sepExists_intro v16) ?_
  exact Entails.sepExists_intro v8

/-! ## Rodata jump table and callee offsets on `SP2Ext` -/

theorem rodata_jump_tag14_mf14W {img : Obj.Image} {s : State}
    (hLoads : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    s.mem.read8 (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) = 0x4c#8 ∧
      s.mem.canRead (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) 1 = true := by
  have hhb := loads_rodata_holdsBytes hLoads hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 13)) (n := 1) (bs := [0x4c#8])
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel) rfl
    (by rfl_kernel)
  exact ⟨(holdsBytes_cons_iff.mp hhb).1.1, (memSlice_of_holdsBytes_ro hhb).1⟩

theorem decodeVarintSlice_ok_sub_mf14W {img : Obj.Image}
    {ext : String → Option (State → State)}
    (h : Prost.X.DecodeVarintSliceOkW img A0 ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64))
      ((Prost.X.decodeVarintSliceSpecW A0).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::varint::decode_varint_slice") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr Prost.decodeVarintSliceName := by
    dsimp only [SP2Ext]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::varint::decode_varint_slice")]
    bv_omega
  rw [heq]; exact h

theorem int32Merge_ok_sub_mf14W {img : Obj.Image}
    {ext : String → Option (State → State)}
    (h : Prost.X.Int32MergeOkW img A0 ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64))
      ((Prost.X.int32MergeSpecW A0).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr Prost.int32MergeName := by
    dsimp only [SP2Ext]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

theorem bytesMerge_ok_sub_mf14W {img : Obj.Image}
    {ext : String → Option (State → State)}
    (h : Prost.X.BytesMergeOkW img A0 ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64))
      (Prost.X.bytesMergeSpecW A0 img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr Prost.bytesMergeName := by
    dsimp only [SP2Ext]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

theorem int32Merge_ok_sub_mf14WA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.X.Int32MergeOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64))
      ((Prost.X.int32MergeSpecW A).inImage img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::int32::merge::<&mut &[u8]>") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr Prost.int32MergeName := by
    dsimp only [SP2Ext]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::int32::merge::<&mut &[u8]>")]
    bv_omega
  rw [heq]; exact h

theorem bytesMerge_ok_sub_mf14WA {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : Prost.X.BytesMergeOkW img A ext) :
    subroutine_ok (SP2Ext img.base ext)
      ((SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64))
      (Prost.X.bytesMergeSpecW A img) := by
  have heq : (SP2Ext img.base ext).fnAddr mergeFieldName +
        bv% ((2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") -
          (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) % 2 ^ 64) =
      (SP2Ext img.base ext).fnAddr Prost.bytesMergeName := by
    dsimp only [SP2Ext]
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"),
      (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
    bv_omega
  rw [heq]; exact h

/-! ## `call_alloc` wrappers for `.inImage img` specifications -/

theorem call_alloc_inImage_mf14W {α β : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s s0 : State} {P R : SepProp} {Q : State → SepProp → Prop} {y : β}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)))
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)) := by
  exact call_alloc_mf14 (spec := spec.inImage img)
    (φ := (img.FrozenLoaded s ∧ s.symtab = img.symtab) ∧ φ)
    hcall hfl hsym hpc hrun hsp hlr
    (by dsimp only [Spec.inImage]; rw [hspec, pure_sepConj_pure_assoc])
    ⟨⟨hfl, hsym⟩, hφ⟩ hP hexit hpan htr hnext
    (hoom := fun sf => by dsimp only [Spec.inImage]; exact hoom sf)

theorem call_alloc_entails_inImage_mf14W {α β : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {φ : Prop}
    {T F : SepProp} {s s0 : State} {P R : SepProp} {Q : State → SepProp → Prop} {y : β}
    (hcall : subroutine_ok prog entry (spec.inImage img))
    (hfl : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P ⊢ T ∗ F)
    (hexit : ∀ sf code, spec.onExit x code s sf = ⌜False⌝)
    (hpan : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (htr : s.trace = s0.trace)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → CalleeSavedPreserved s sf →
      img.FrozenLoaded sf → sf.symtab = img.symtab →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)))
    (hoom : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ allocPanic y s0 sf ∗ R)) := by
  intro R' hm hL
  exact call_alloc_inImage_mf14W hcall hfl hsym hpc hrun hsp hlr hspec hφ rfl hexit hpan htr hnext
    (hoom := hoom) R'
    (Satisfies.mono (sepConj_mono_left hP) hm) hL

/-! ## Postcondition and frame helpers (`i = 0#32` and `i ≠ 0#32`) -/

theorem post_of_decode_mf14W {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.decodeVarintSliceSpecW A0).post
        ⟨sp0 - 232#64, ptr, 164#8 :: 12#8 :: 18#8 :: innerBytes ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr := by
  dsimp only [Prost.X.decodeVarintSliceSpecW]
  rw [decode_kyber_result_mf14 hct, hsp, bytes_kyber_split_mf14, pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega,
    show A0.pool = emp from rfl, emp_sepConj]
  simp only [sepConj_assoc]

theorem post_of_bytesMerge_mf14W (ss bufRef slot ptr sp0 : BitVec 64)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.bytesMergeRawSpecW A0).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, ptr + 3#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_inner hct tail]
  dsimp only
  rw [hsp, sliceCursorAfter_inner_unfold_mf14 slot ptr hct tail,
      stackAt_sub_to_bytesMerge_mf14W (sp0 - 240#64), hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

theorem final_post_entails_kyber_mf14W (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ 0#32) ∗ memRegion (ss + 324#64) 4 ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    kyberAt14 A0 ss (v.apply (GenFieldX.kyber 0#32 ct)).ext.kyber ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber 0#32 ct).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_kyber_fold_mf14 slot ptr hct tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 324#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (ptr + 1574#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ 164#8) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 18#8) ∗
      ((ptr + 3#64) ↦ₛ innerBytes ct tail)) ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 1572) ∗ ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (kyberAt14_some_fold A0 ss cap' ptr' v 0#32 ct) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14W sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

theorem post_of_decode_ne_mf14W (i : BitVec 32) {ct : List (BitVec 8)} (hct : ct.length = 1569)
    (tail : List (BitVec 8)) (ptr sp0 : BitVec 64) (sm sf : State)
    (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.decodeVarintSliceSpecW A0).post
        ⟨sp0 - 232#64, ptr, kyberB0 i :: 12#8 :: 8#8 :: kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
        ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
        ((sp0 - 216#64) ↦₆₄ 2#64) ∗
        (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
        ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
        stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr := by
  dsimp only [Prost.X.decodeVarintSliceSpecW]
  rw [decode_kyber_ne_result_mf14 i hct, hsp, bytes_kyber_ne_split_mf14,
      pointsTo64_zero_split32_mf14,
    show sp0 - 232#64 + 8#64 = sp0 - 224#64 by bv_omega,
    show sp0 - 232#64 + 16#64 = sp0 - 216#64 by bv_omega,
    show A0.pool = emp from rfl, emp_sepConj]
  simp only [sepConj_assoc]

theorem pre_to_int32Merge_ne_mf14W (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8)) (Fr : SepProp) :
    ((ss + 320#64) ↦₃₂ 0#32) ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (ptr + 3#64)) ∗
      ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + (encodeVarint (i.setWidth 64)).length +
        tail.length)) ∗
      ((ptr + 3#64) ↦ₛ kyberIdBytes i ct tail) ∗
      memRegion (sp0 - 240#64 - 32528#64) 7872 ∗
      stackAt (sp0 - 240#64) Prost.X.decodeVarintSliceStackW ∗ Fr ⊢
    (memRegion (ss + 320#64) 4 ∗ (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAt slot (ptr + 3#64) (kyberIdBytes i ct tail) ∗ A0.pool ∗
      stackAt (sp0 - 240#64) Prost.X.int32MergeStackW) ∗
    (memRegion (sp0 - 240#64 - 32528#64) 7792 ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  rw [← sliceCursorAt_kyberId_fold_mf14 slot ptr i hct tail, hpool, emp_sepConj]
  have hpt32 : ((ss + 320#64) ↦₃₂ 0#32) ⊢ memRegion (ss + 320#64) 4 := by
    rw [ProofLib.memRegion_four]
    exact Entails.sepExists_right 0#32 (Entails.refl _)
  refine Entails.trans (sepConj_mono_left hpt32) ?_
  apply Entails.of_eq
  rw [← sepConj_assoc (memRegion (sp0 - 240#64 - 32528#64) 7872),
      decode_to_int32Merge_stack_mf14W (sp0 - 240#64)]
  ac_rfl

theorem post_of_int32Merge_ne_mf14W (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.int32MergeSpecW A0).post
        ⟨.varint, ss + 320#64, bufRef, slot, ptr + 3#64, kyberIdBytes i ct tail⟩ sm sf ∗ Fr =
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        ((ss + 320#64) ↦₃₂ i) ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ kyberPtr2 ptr i) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 (1572 + tail.length)) ∗
        ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
        (kyberPtr2 ptr i ↦₈ 18#8) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) Prost.X.int32MergeStackW ∗ Fr := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.X.int32MergeSpecW]
  rw [mergeUint32_kyberIdBytes i tail]
  dsimp only
  rw [hsp, sliceCursorAfter_kyberId_unfold_mf14 slot ptr i hct tail, hpool, emp_sepConj]
  simp only [sepConj_assoc]
  ac_rfl

theorem post_of_bytesMerge_ne_mf14W (ss bufRef slot ptr sp0 : BitVec 64) (i : BitVec 32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sm sf : State) (hsp : sm.sp = sp0 - 240#64) (Fr : SepProp) :
    (Prost.X.bytesMergeRawSpecW A0).post
        ⟨.lengthDelimited, ss + 296#64, 0#64, 1#64, [], bufRef, slot, kyberPtr2 ptr i + 1#64,
          innerBytes ct tail⟩ sm sf ∗
      (memRegion (sp0 - 240#64 - 32528#64) 7648 ∗ Fr) =
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜sf.trace = sm.trace⌝ ∗ ⌜sf.readReg64 .x0 = 0#64⌝ ∗
        vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
        (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
        ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
        stackAt (sp0 - 240#64) mergeFieldSubStackX ∗ Fr) := by
  have hpool : A0.pool = emp := rfl
  dsimp only [Prost.X.bytesMergeRawSpecW]
  rw [mergeBytes_inner hct tail]
  dsimp only
  rw [hsp, sliceCursorAfter_inner_ne_unfold_mf14 slot ptr i hct tail,
      stackAt_sub_to_bytesMerge_mf14W (sp0 - 240#64), hpool, emp_sepConj]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine congrArg sepExists (funext fun cap' => congrArg sepExists (funext fun ptr' => ?_))
  ac_rfl

theorem final_post_entails_ne_kyber_mf14W (ss cap' ptr' : BitVec 64) (v : SSGX)
    (bufRef slot ptr : BitVec 64) {i : BitVec 32} (hi : i ≠ 0#32)
    {ct : List (BitVec 8)} (hct : ct.length = 1569) (tail : List (BitVec 8))
    (sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19 : BitVec 64) :
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ (bufRef ↦₆₄ slot) ∗
      (slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail) ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX ∗
      ((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((ss + 320#64) ↦₃₂ i) ∗ memRegion (ss + 324#64) 4 ∗
      ((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128) ⊢
    kyberAt14 A0 ss (v.apply (GenFieldX.kyber i ct)).ext.kyber ∗
      (bufRef ↦₆₄ slot) ∗
      Prost.sliceCursorAfter slot ptr ((GenFieldX.kyber i ct).payload ++ tail) tail ∗
      stackAt sp0 mergeFieldStackX := by
  rw [← sliceCursorAfter_kyber_ne_fold_mf14 slot ptr hi hct tail]
  refine Entails.trans (Q :=
    (vecU8At A0 (ss + 296#64) cap' ptr' ct ∗ ((ss + 320#64) ↦₃₂ i) ∗
      memRegion (ss + 324#64) 4) ∗
    (bufRef ↦₆₄ slot) ∗
    ((slot ↦₆₄ (kyberPtr2 ptr i + 1572#64)) ∗ ((slot + 8#64) ↦₆₄ BitVec.ofNat 64 tail.length) ∗
      (ptr ↦₈ kyberB0 i) ∗ ((ptr + 1#64) ↦₈ 12#8) ∗ ((ptr + 2#64) ↦₈ 8#8) ∗
      ((ptr + 3#64) ↦ₛ encodeVarint (i.setWidth 64)) ∗
      (kyberPtr2 ptr i ↦₈ 18#8) ∗
      ((kyberPtr2 ptr i + 1#64) ↦ₛ innerBytes ct tail)) ∗
    ((((sp0 - 232#64) ↦₃₂ 0#32) ∗ ((sp0 - 228#64) ↦₃₂ 0#32) ∗
      ((sp0 - 224#64) ↦₆₄ BitVec.ofNat 64 (1573 + (encodeVarint (i.setWidth 64)).length)) ∗
      ((sp0 - 216#64) ↦₆₄ 2#64)) ∗
      (((sp0 - 80#64) ↦₆₄ r29) ∗ ((sp0 - 72#64) ↦₆₄ r30) ∗
      ((sp0 - 64#64) ↦₆₄ r25) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
      ((sp0 - 48#64) ↦₆₄ r24) ∗ ((sp0 - 40#64) ↦₆₄ r23) ∗
      ((sp0 - 32#64) ↦₆₄ r22) ∗ ((sp0 - 24#64) ↦₆₄ r21) ∗
      ((sp0 - 16#64) ↦₆₄ r20) ∗ ((sp0 - 8#64) ↦₆₄ r19) ∗
      memRegion (sp0 - 240#64) 8 ∗ memRegion (sp0 - 208#64) 128 ∗
      stackAt (sp0 - 240#64) mergeFieldSubStackX)))
    (Entails.of_eq (by ac_rfl)) ?_
  refine sepConj_mono (kyberAt14_some_fold A0 ss cap' ptr' v i ct) ?_
  refine sepConj_mono_right (sepConj_mono_right ?_)
  refine Entails.trans (sepConj_mono (cells24_entails_memRegion24_mf14 sp0 _ _)
    (Entails.refl _)) ?_
  refine Entails.trans ?_ (stackAt_mergeField_fold_mf14W sp0 r29 r30 r25 w56 r24 r23 r22 r21 r20 r19)
  rw [← memRegion160_fold_mf14]
  exact Entails.of_eq (by ac_rfl)

theorem sat_pure_true_mf14W {m : Memory} {φ : Prop} {X R : SepProp} (hφ : φ)
    (h : m ⊨ (X ∗ emp) ∗ R) : m ⊨ (⌜φ⌝ ∗ X) ∗ R := by
  rw [sepConj_emp] at h
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hφ, h⟩

end Symbolic.Swarm.TRREF.B3DeserQ
