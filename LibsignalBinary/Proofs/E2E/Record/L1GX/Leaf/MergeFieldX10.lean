/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.L1GX.Defs
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge
import ProofLib.SepLogic.WPp

/-!
# `SessionStructure::merge_field` on tag 10 (`remote_registration_id`)

Proves `mergeFieldX10_ok` (`0x581c`, arm `+0x398` calling `uint32::merge` into `ss + 0x150`),
along with shared varint-field helpers reused by `MergeFieldX11`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX10

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem genFieldX_tag_eq_10_iff (fl : GenFieldX) :
    fl.tag = 10 ↔ ∃ v, fl = .remReg v := by
  cases fl with
  | base f => cases f <;> simp [GenFieldX.tag, GenField.tag]
  | pendingId i k => simp [GenFieldX.tag]
  | pendingSpk i k spk => simp [GenFieldX.tag]
  | remReg v => simp [GenFieldX.tag]
  | locReg v => simp [GenFieldX.tag]
  | abk b => simp [GenFieldX.tag]
  | kyber i ct => simp [GenFieldX.tag]
  | pq b => simp [GenFieldX.tag]

private theorem rodata_0x79025_byte0_eq_mf10 :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 9) - num% (ls_xref% 0x2440 0x2444))).take 1 = [214#8] := by
  rfl_kernel

private theorem holdsBytes_rodata_0x79025_mf10 {s : State}
    (hF : sessionImg0.FrozenLoaded s) :
    Arm64.Obj.HoldsBytes s.mem (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 9)) [214#8] (fun _ => .ro) :=
  loads_rodata_holdsBytes E2E.Record.loads_sessionImg0 hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 9)) (n := 1) (bs := [214#8])
    (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel))
    (by rfl_kernel)
    (by rfl_kernel)
    rfl
    rodata_0x79025_byte0_eq_mf10

private theorem sepWPp_intro_rodata_0x79025_mf10 {prog : Program} {ret : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : sessionImg0.FrozenLoaded s)
    (h : SepWPp prog ret s (((sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 9)) ↦₈ᵣ 214#8) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  refine h R ?_ hL
  rw [sepConj_assoc, ← pointsToBytesRO_singleton]
  exact Satisfies.of_holdsBytes_ro (holdsBytes_rodata_0x79025_mf10 hF) (by decide) hm

gen_decodes CryptoVerification.libsignalSessionCode_tree mf1011
  [0x581c → 0x5858, 0x5b88 → 0x5b9c, 0x5bb4 → 0x5bc8, 0x5f74 → 0x5f8c]

theorem drop_left_sepWPp_mf1011 {prog : Program} {ret : BitVec 64}
    {s : State} {Drop P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s P Q Qp) :
    SepWPp prog ret s (Drop ∗ P) Q Qp := by
  intro R hm hL
  rw [sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

theorem int32Merge_ok_sub_mf1011 {b : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (h : Prost.Int32MergeOk b C A ctl abs) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + 18446744073709540264#64)
      (Prost.int32MergeSpec A) := by
  have heq : (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + 18446744073709540264#64 =
      (tripleRatchetProgAt b C ctl abs).fnAddr Prost.int32MergeName := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase,
      libsignalSessionCode_fnOff_0x581c, libsignalSessionCode_fnOff_0x2bc4]
    bv_omega
  rw [heq]; exact h

def prostSSGXRest_mf10 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) : SepProp :=
  vecU8 A ss v.base.lik ∗ vecU8 A (ss + 0x18#64) v.base.rik ∗ vecU8 A (ss + 0x30#64) v.base.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.base.recv ∗
    vecU8 A (ss + 0x60#64) v.ext.abk ∗ vecU8 A (ss + 0x78#64) v.ext.pq ∗
    (match v.base.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    (match v.base.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A (ss + 0xf8#64) k ∗
         pidAt ss v.ext.pid (((ss + 0x118#64) ↦₆₄ 0#64) ∗
           ((ss + 0x120#64) ↦₃₂ v.ext.spkId) ∗ memRegion (ss + 0x124#64) 4)) ∗
    kyberAt A ss v.ext.kyber
      (((ss + 0x148#64) ↦₃₂ v.base.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.base.prevCounter) ∗
        ((ss + 0x154#64) ↦₃₂ v.ext.locReg))

theorem prostSSGXAt_eq_remReg_sep_rest_mf10 (A : RustAlloc) (ss : BitVec 64) (v : SSGX) :
    prostSSGXAt A ss v = ((ss + 0x150#64) ↦₃₂ v.ext.remReg) ∗ prostSSGXRest_mf10 A ss v := by
  unfold prostSSGXAt prostSSGXRest_mf10
  rcases v.ext.kyber with _ | ⟨i, ct⟩ <;> simp only [kyberAt] <;> ac_rfl

theorem stackAt_mergeField_split_mf1011 (sp : BitVec 64) :
    stackAt sp mergeFieldStack =
      memRegion (sp - 16384#64) 7792 ∗
        stackAt (sp - 240#64) Prost.int32MergeStack ∗
        memRegion (sp - 240#64) 160 ∗
        memRegion (sp - 56#64) 8 ∗
        (∃∗ w19 : BitVec 64, ∃∗ w20 : BitVec 64, ∃∗ w21 : BitVec 64, ∃∗ w22 : BitVec 64,
         ∃∗ w23 : BitVec 64, ∃∗ w24 : BitVec 64, ∃∗ w25 : BitVec 64,
         ∃∗ w30 : BitVec 64, ∃∗ w29 : BitVec 64,
          ((sp - 80#64) ↦₆₄ w29) ∗ ((sp - 72#64) ↦₆₄ w30) ∗
          ((sp - 64#64) ↦₆₄ w25) ∗
          ((sp - 48#64) ↦₆₄ w24) ∗ ((sp - 40#64) ↦₆₄ w23) ∗
          ((sp - 32#64) ↦₆₄ w22) ∗ ((sp - 24#64) ↦₆₄ w21) ∗
          ((sp - 16#64) ↦₆₄ w20) ∗ ((sp - 8#64) ↦₆₄ w19)) := by
  have h0 := LibsignalTripleRatchet.stackAt_split_cells sp 16144 30 (by decide)
  rw [← ProofLib.memRegion_cells (sp - BitVec.ofNat 64 (8 * 30)) 30 (by decide)] at h0
  change stackAt sp mergeFieldStack = stackAt (sp - 240#64) 16144 ∗
      memRegion (sp - 240#64) 240 at h0
  have hsub := ProofLib.stackAt_split_bottom (sp - 240#64) Prost.int32MergeStack 7792 (by decide)
  change stackAt (sp - 240#64) 16144 =
    memRegion (sp - 240#64 - 16144#64) 7792 ∗ stackAt (sp - 240#64) Prost.int32MergeStack at hsub
  have hsub_addr : sp - 240#64 - 16144#64 = sp - 16384#64 := by bv_omega
  rw [hsub_addr] at hsub
  have s1 := Prost.memRegion_split (sp - 240#64) 160 80 (by decide)
  rw [bv_sub_add_lit sp 240 160] at s1
  have s2 := Prost.memRegion_split (sp - 80#64) 8 72 (by decide)
  rw [bv_sub_add_lit sp 80 8] at s2
  have s3 := Prost.memRegion_split (sp - 72#64) 8 64 (by decide)
  rw [bv_sub_add_lit sp 72 8] at s3
  have s4 := Prost.memRegion_split (sp - 64#64) 8 56 (by decide)
  rw [bv_sub_add_lit sp 64 8] at s4
  have s5 := Prost.memRegion_split (sp - 56#64) 8 48 (by decide)
  rw [bv_sub_add_lit sp 56 8] at s5
  have s6 := Prost.memRegion_split (sp - 48#64) 8 40 (by decide)
  rw [bv_sub_add_lit sp 48 8] at s6
  have s7 := Prost.memRegion_split (sp - 40#64) 8 32 (by decide)
  rw [bv_sub_add_lit sp 40 8] at s7
  have s8 := Prost.memRegion_split (sp - 32#64) 8 24 (by decide)
  rw [bv_sub_add_lit sp 32 8] at s8
  have s9 := Prost.memRegion_split (sp - 24#64) 8 16 (by decide)
  rw [bv_sub_add_lit sp 24 8] at s9
  have s10 := Prost.memRegion_split (sp - 16#64) 8 8 (by decide)
  rw [bv_sub_add_lit sp 16 8] at s10
  rw [h0, hsub, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10,
    Prost.memRegion_eight (sp - 80#64), Prost.memRegion_eight (sp - 72#64),
    Prost.memRegion_eight (sp - 64#64),
    Prost.memRegion_eight (sp - 48#64), Prost.memRegion_eight (sp - 40#64),
    Prost.memRegion_eight (sp - 32#64), Prost.memRegion_eight (sp - 24#64),
    Prost.memRegion_eight (sp - 16#64), Prost.memRegion_eight (sp - 8#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  ac_rfl

theorem adrp_0x4601c_eq_mf1011 (base entry : BitVec 64)
    (halign : base &&& 0xfff#64 = 0#64) (hentry : base + 22556#64 = entry) :
    (entry + 40#64 &&& 18446744073709547520#64) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" - 0x5000) = base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
  subst hentry
  rw [BitVec.add_assoc base 22556#64 40#64, adrp_page_of_aligned halign, BitVec.add_assoc]
  rfl

theorem setWidth8_zext64_trunc32_mf1011 (v : BitVec 64) :
    BitVec.setWidth 8 (BitVec.zeroExtend 64 (BitVec.truncate 32 v)) = BitVec.setWidth 8 v := by
  change BitVec.setWidth 8 (BitVec.setWidth 64 (BitVec.setWidth 32 v)) = BitVec.setWidth 8 v
  rw [BitVec.setWidth_setWidth_of_le (BitVec.setWidth 32 v) (by decide),
    BitVec.setWidth_setWidth_of_le v (by decide)]

theorem int64_raw_toBitVec_mf1011 (n : Nat) (h : n < 18446744073709551616) :
    ({ toUInt64 := { toBitVec := { toFin := ⟨n, h⟩ } } } : Int64).toBitVec = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  change n = n % 18446744073709551616
  exact (Nat.mod_eq_of_lt h).symm

theorem allowPanic_call_mf1011 {s_call s0 sf : State} {F R : SepProp}
    (htr : s_call.trace = s0.trace)
    (hm : sf.mem ⊨ ((⌜allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R := by
  have h1 : allocFailedIn s_call sf ∧ s_call.trace <+: sf.trace →
      allocFailedIn s0 sf ∧ s0.trace <+: sf.trace := by
    unfold allocFailedIn
    rw [htr]
    exact id
  exact allowPanic_frame h1 hm

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero int64_raw_toBitVec_mf1011

theorem mergeFieldX10_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) : MergeFieldXOk C ctl (fun fl => fl.tag = 10) abs := by
  unfold MergeFieldXOk Serialization.OkAt mergeFieldXSpec
  have hInt32 := int32Merge_ok_sub_mf1011 hC.2.1
  have halign : sessionImg0.base &&& 0xfff#64 = 0#64 :=
    base_aligned_of_loads E2E.Record.loads_sessionImg0
  have hentry_eq : sessionImg0.base + 22556#64 =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr mergeFieldName := by
    rw [Program.fnAddr_rebase, libsignalSessionCode_fnOff_0x581c]
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
    (b := sessionImg0.base) (H := H)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x581c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 4)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5820
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 8)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5824
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 12)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5828
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 16)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x582c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 20)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5830
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 24)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5834
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 28)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5838
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 32)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x583c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 36)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5840
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 40)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5844
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 44)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5848
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 48)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x584c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 52)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5850
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 56)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5854
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 60)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5858
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 920)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5bb4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 924)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5bb8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 928)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5bbc
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 932)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5bc0
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 936)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5bc4
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 940)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5bc8
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1880)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5f74
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1884)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5f78
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1888)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5f7c
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1892)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5f80
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1896)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5f84
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1900)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5f88
  have := CryptoVerification.libsignalSessionCode_fetch_fnAddr
    (b := sessionImg0.base) (H := H) (k := 1904)
    libsignalSessionCode_fnOff_0x581c (by decide) mf1011_decode_0x5f8c
  apply subroutine_ok_of_sepWPp
  intro ⟨ss, v_ss, fld, bufRef, slot, ptr, tail⟩ R s0 hpc hrun hpre hsp_align
  refine ⟨_, R, hpre, ?_⟩
  clear hpre
  dsimp only
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0, hx1, hx2, hx3, hx4, htag, hf_ok, hf_fresh, h_len, h_loaded,
      h_sym⟩ => ?_
  obtain ⟨v_fld, h_fld⟩ := (genFieldX_tag_eq_10_iff fld).mp htag
  subst h_fld
  change BitVec.setWidth 32 (s0.readReg64 Reg.x1) = 10#32 at hx1
  change BitVec.setWidth 8 (s0.readReg64 Reg.x2) = 0#8 at hx2
  dsimp only [tripleRatchetProgAt] at hInt32 hentry_eq hpc ⊢
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr mergeFieldName = entry
  generalize_entry (libsignalSessionCode.rebase sessionImg0.base
    (Rust.withPanics (tripleRatchetExterns C ctl abs))) = prog
    reverting [Program.fetch, subroutine_ok]
  examples_hide_fetches
  refine sepWPp_intro_rodata_0x79025_mf10 h_loaded ?_
  conv =>
    arg 4
    rw [prostSSGXAt_eq_remReg_sep_rest_mf10 A0 ss v_ss, stackAt_mergeField_split_mf1011 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun w19 => ?_
  refine SepWPp.exists_elim fun w20 => ?_
  refine SepWPp.exists_elim fun w21 => ?_
  refine SepWPp.exists_elim fun w22 => ?_
  refine SepWPp.exists_elim fun w23 => ?_
  refine SepWPp.exists_elim fun w24 => ?_
  refine SepWPp.exists_elim fun w25 => ?_
  refine SepWPp.exists_elim fun w30 => ?_
  refine SepWPp.exists_elim fun w29 => ?_
  apply SepWPp.of_sepWP (mid := entry + 18446744073709540264#64)
  wp_steps
  rw [adrp_0x4601c_eq_mf1011 sessionImg0.base entry halign hentry_eq]
  wp_steps
  apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
  apply drop_left_sepWPp_mf1011
  refine SepWPp.call
    (x := Prost.Int32MergeGhost.mk .varint (ss +
      336#64) bufRef slot ptr ((GenFieldX.remReg v_fld).payload ++ tail))
    (ret_pc := entry + 936#64)
    (F := prostSSGXRest_mf10 A0 ss v_ss ∗
      memRegion (s0.sp - 16384#64) 7792 ∗
      memRegion (s0.sp - 240#64) 160 ∗
      memRegion (s0.sp - 56#64) 8 ∗
      (s0.sp - 80#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5) ∗
      (s0.sp - 72#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5) ∗
      (s0.sp - 64#64) ↦₆₄ s0.readReg64 (Reg.gpr 25#5) ∗
      (s0.sp - 48#64) ↦₆₄ s0.readReg64 (Reg.gpr 24#5) ∗
      (s0.sp - 40#64) ↦₆₄ s0.readReg64 (Reg.gpr 23#5) ∗
      (s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 22#5) ∗
      (s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 21#5) ∗
      (s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 20#5) ∗
      (s0.sp - 8#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5))
    hInt32
    (by simp only [arm64_norm, *])
    (by simp only [arm64_norm, *])
    (by simp only [State.spAligned, arm64_norm] at hsp_align ⊢; exact hsp_align)
    (by simp only [arm64_norm, *])
    ?_ ?_ ?_ ?_
  · intro R' hm
    have hpool : A0.pool = emp := rfl
    simp only [Prost.int32MergeSpec, hpool, emp_sepConj, Prost.memRegion_four (ss + 336#64),
      arm64_norm, setWidth8_zext64_trunc32_mf1011, sepExists_sepConj_left, sepExists_sepConj_right,
      sepConj_assoc, satisfies_pure_sepConj, satisfies_sepExists]
    refine ⟨v_ss.ext.remReg, ⟨hx2, Nat.lt_of_lt_of_le h_len (by decide)⟩, ?_⟩
    convert hm using 1
    · ac_rfl
    · rfl
  · intro sf code R' _ hm
    exact allowPanic_not_exited hm
  · intro sf _ hm
    exact allowPanic_call_mf1011 rfl hm
  · intro sm hpcm hrunm hspm hcsm
    obtain ⟨-, -, -, -, -, -, -, hx26m, hx27m, hx28m, -, hvregsm⟩ := hcsm
    simp only [arm64_norm] at hspm hx26m hx27m hx28m hvregsm
    have hsm_align : sm.spAligned = true := by
      simp only [State.spAligned, hspm, arm64_norm] at hsp_align ⊢
      exact hsp_align
    have hpool : A0.pool = emp := rfl
    simp only [Prost.int32MergeSpec, GenFieldX.payload, mergeUint32_encode, hpool, emp_sepConj,
      arm64_norm, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨htrm, hx0m⟩ => ?_
    apply SepWPp.of_sepWP (mid := s0.readReg64 (Reg.gpr 30#5))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply SepWPp.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    refine ⟨?_, by simp only [arm64_norm, *],
      ⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *],
       by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩⟩
    intro hm
    refine ⟨⟨by simp only [arm64_norm, *], by simp only [arm64_norm, *]⟩, ?_⟩
    rw [show v_ss.apply (GenFieldX.remReg v_fld) = { v_ss with ext := { v_ss.ext with remReg :=
      v_fld } } from rfl,
      prostSSGXAt_eq_remReg_sep_rest_mf10 A0 ss { v_ss with ext := { v_ss.ext with remReg :=
        v_fld } },
      show prostSSGXRest_mf10 A0 ss { v_ss with ext := { v_ss.ext with remReg :=
        v_fld } } = prostSSGXRest_mf10 A0 ss v_ss from rfl,
      stackAt_mergeField_split_mf1011 s0.sp]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, satisfies_sepExists]
    refine ⟨s0.readReg64 (Reg.gpr 19#5), s0.readReg64 (Reg.gpr 20#5),
      s0.readReg64 (Reg.gpr 21#5), s0.readReg64 (Reg.gpr 22#5),
      s0.readReg64 (Reg.gpr 23#5), s0.readReg64 (Reg.gpr 24#5),
      s0.readReg64 (Reg.gpr 25#5), s0.readReg64 (Reg.gpr 30#5),
      s0.readReg64 (Reg.gpr 29#5), ?_⟩
    convert hm using 1
    ac_rfl

end CryptoVerification.E2E.Record.L1GX.Leaf.MergeFieldX10
