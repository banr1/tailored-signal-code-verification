/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.Post
public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.VarintKey
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.ResponderStoreCodeSym
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFields
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.SepLogic.WPp

/-!
# `PreKeyRecord::deserialize` Decode Loop and Prologue

Verifies the `PreKeyRecordStructure` protobuf decode loop (`+0x070 .. +0x07c`), prologue
(`+0x000 → +0x224`), and relocatable `[LibsignalPlacement]` post-loop / varint CPS helpers on
Block `65`.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecs
open CryptoVerification.RecordCodecsBinary

/-! ## Loop header `+0x070..+0x07c` and loop induction over `fuel` -/

theorem loopHeader_070_empty_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hok : out = .ok ⟨m⟩)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr [] m)
      (pkEpiloguePost img A s0 sp' x19 ptr [] out)
      (tryFromQp s0) := by
  have hexit := @post_ok_23c_wp img A ext s0
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 112 16
  dsimp only [tripleRatchetProgAtExt] at hexit hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  unfold pkLoopMem sliceCursorAt
  simp only [sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (572)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hexit (sp' := sp') (x19 := x19) (ptr := ptr) (m := m) (bs := []) (out := out) hok
      ⟨by simpa [arm64_norm] using hregs.sp,
       by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hF1, hsym1, by simp [htr, arm64_norm],
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp [hrun, arm64_norm])
      (by simpa [arm64_norm] using hregs.x19_eq)
      (by simpa [arm64_norm] using hregs.x20))
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length)
  have hof := preKeyStructLoopOf_entails_of A (sp' + 56#64) ([] : List (BitVec 8)).length m
  rw [← sepConj_assoc ((sp' + 40#64) ↦₆₄ ptr) ((sp' + 40#64 + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length)]
  refine Entails.trans
    (sepConj_mono h16
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left hof))))) ?_
  apply entails_of_eq; ac_rfl

theorem loopHeader_070_cons_cps {img : Obj.Image}
    {ext : String → Option (State → State)}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State,
      s1.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x080#64 →
      s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 →
      s1.readReg64 .x23 = sp' + 40#64 →
      s1.readReg64 .x21 = sp' + 48#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      s1.spAligned = true → img.FrozenLoaded s1 → s1.symtab = img.symtab →
      s1.trace = s0.trace →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
        (sliceCursorAt (sp' + 40#64) ptr (b0 :: bs1) ∗
          ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ F) Q Qp) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (sliceCursorAt (sp' + 40#64) ptr (b0 :: bs1) ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ F) Q Qp := by
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 112 16
  dsimp only [tripleRatchetProgAtExt] at hcont hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  unfold sliceCursorAt
  simp only [sepConj_assoc]
  refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (128)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
  intro hF1 hsym1
  refine Wire.SepWPp.mono_pre ?_
    (hcont _
      (by simp [arm64_norm])
      (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp,
       by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22,
       by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hF1 hsym1 (by simpa [arm64_norm] using htr))
  unfold sliceCursorAt
  apply entails_of_eq; ac_rfl

def pkLoopOut : Option PreKeyRecordStructure → Except SignalProtocolError PreKeyRecord
  | some m => .ok ⟨m⟩
  | none => .error .invalidProtobufEncoding

theorem decodeLoop_080_step_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : PreKeyRecordStructure},
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64 →
      s.status = .Running →
      PkLoopRegs s0 sp' x19 s →
      s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
        (pkLoopMem A sp' x19 ptr bs m)
        (pkEpiloguePost img A s0 sp' x19 ptr bs
          (pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField fuel m bs)))
        (tryFromQp s0))
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x080#64)
    (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64)
    (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1)
    (hlen : (b0 :: bs1).length < 2 ^ 63) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
      (pkLoopMem A sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePost img A s0 sp' x19 ptr (b0 :: bs1)
        (pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1))))
      (tryFromQp s0) := by
  refine decodeKey_080_cps hC d hpc hrun hregs hx23 hx21 hx2 hsp hF hsym htr hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hF1 hsym1 htr1 hx8_1 hx1_1 => ?_)
    (fun hdk_none => by simp [decodeFieldsLoop, pkLoopOut, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  unfold pkAfterVarintMem
  refine pkAdvanceCursor ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left
        (preKeyStructLoopOf_mono A (sp' + 56#64) (m := rest1.length) (n := (b0 :: bs1).length) m
          (by omega)))))) ?_
  change Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s1
    (pkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest1.length)) rest1 m) _ _
  refine mergeField_0fc_cps hC d hpc1 hrun1 hregs1 hx8_1 hx1_1 htag_ge htag_lt
    hsp1 hF1 hsym1 htr1 (by omega)
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 hsp2 hF2 hsym2 htr2 => ?_)
    (fun hmf_none => by simp [decodeFieldsLoop, pkLoopOut, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := pkMergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  unfold pkAfterVarintMem
  refine pkAdvanceCursor ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : decodeFieldsLoop PreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1) =
      decodeFieldsLoop PreKeyRecordStructure.mergeField fuel m' rest2 := by
    simp [decodeFieldsLoop, hdk, hmf]
  rw [hloop_eq]
  exact ih hpc2 hrun2 hregs2 hsp2 hF2 hsym2 htr2 (by omega) (by omega)

theorem decodeLoop_070_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {s0 : State} {sp' x19 : BitVec 64} :
    ∀ (fuel : ℕ) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : PreKeyRecordStructure},
      s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x070#64 →
      s.status = .Running →
      PkLoopRegs s0 sp' x19 s →
      s.spAligned = true → img.FrozenLoaded s → s.symtab = img.symtab →
      s.trace = s0.trace →
      bs.length ≤ fuel →
      bs.length < 2 ^ 63 →
      Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
        ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s
        (pkLoopMem A sp' x19 ptr bs m)
        (pkEpiloguePost img A s0 sp' x19 ptr bs
          (pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField fuel m bs)))
        (tryFromQp s0)
  | 0, s, ptr, bs, m, hpc, hrun, hregs, hsp, hF, hsym, htr, hfuel, _ => by
    cases bs with
    | nil => exact loopHeader_070_empty_wp rfl hpc hrun hregs hsp hF hsym htr
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hpc, hrun, hregs, hsp, hF, hsym, htr, hfuel, hlen => by
    cases bs with
    | nil => exact loopHeader_070_empty_wp rfl hpc hrun hregs hsp hF hsym htr
    | cons b0 bs1 =>
      unfold pkLoopMem
      refine loopHeader_070_cons_cps hpc hrun hregs hsp hF hsym htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx23_1 hx21_1 hx2_1 hsp1 hF1 hsym1 htr1
      exact decodeLoop_080_step_wp hC d (decodeLoop_070_wp hC d fuel)
        hpc1 hrun1 hregs1 hx23_1 hx21_1 hx2_1 hsp1 hF1 hsym1 htr1 hfuel hlen

/-! ## Prologue unpacking helpers and full `+0x000 → +0x224` segment -/

theorem pkMemRegion64_unpack (a : BitVec 64) :
    memRegion a 64 ⊢
      ∃∗ c0 : BitVec 64, ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64, ∃∗ c7 : BitVec 64,
        (a ↦₆₄ c0) ∗ ((a + 8#64) ↦₆₄ c1) ∗ ((a + 16#64) ↦₆₄ c2) ∗ ((a + 24#64) ↦₆₄ c3) ∗
        ((a + 32#64) ↦₆₄ c4) ∗ ((a + 40#64) ↦₆₄ c5) ∗ ((a + 48#64) ↦₆₄ c6) ∗ ((a + 56#64) ↦₆₄ c7) := by
  rw [ProofLib.memRegion_split a 8 56 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun c7 => Entails.sepExists_elim fun c6 =>
    Entails.sepExists_elim fun c5 => Entails.sepExists_elim fun c4 =>
    Entails.sepExists_elim fun c3 => Entails.sepExists_elim fun c2 =>
    Entails.sepExists_elim fun c1 => Entails.sepExists_elim fun c0 => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro c0)
  refine Entails.trans ?_ (Entails.sepExists_intro c1)
  refine Entails.trans ?_ (Entails.sepExists_intro c2)
  refine Entails.trans ?_ (Entails.sepExists_intro c3)
  refine Entails.trans ?_ (Entails.sepExists_intro c4)
  refine Entails.trans ?_ (Entails.sepExists_intro c5)
  refine Entails.trans ?_ (Entails.sepExists_intro c6)
  refine Entails.trans ?_ (Entails.sepExists_intro c7)
  exact Entails.refl _

theorem pkStruct56_unpack_init (a : BitVec 64) :
    memRegion a 56 ⊢
      ∃∗ s0w : BitVec 64, ∃∗ s1w : BitVec 64, ∃∗ s2w : BitVec 64,
      ∃∗ s3w : BitVec 64, ∃∗ s4w : BitVec 64, ∃∗ s5w : BitVec 64,
      ∃∗ s6w : BitVec 32,
        (a ↦₆₄ s0w) ∗ ((a + 8#64) ↦₆₄ s1w) ∗ ((a + 16#64) ↦₆₄ s2w) ∗
        ((a + 24#64) ↦₆₄ s3w) ∗ ((a + 32#64) ↦₆₄ s4w) ∗ ((a + 40#64) ↦₆₄ s5w) ∗
        ((a + 48#64) ↦₃₂ s6w) ∗ memRegion (a + 52#64) 4 := by
  rw [ProofLib.memRegion_split a 8 48 (by decide),
    ProofLib.memRegion_split (a + 8#64) 8 40 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64) 8 32 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64) 8 24 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64) 8 16 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 8 8 (by decide),
    ProofLib.memRegion_split (a + 8#64 + 8#64 + 8#64 + 8#64 + 8#64 + 8#64) 4 4 (by decide),
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_eight, ProofLib.memRegion_eight, ProofLib.memRegion_eight,
    ProofLib.memRegion_four]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right]
  refine Entails.sepExists_elim fun s6w => Entails.sepExists_elim fun s5w =>
    Entails.sepExists_elim fun s4w => Entails.sepExists_elim fun s3w =>
    Entails.sepExists_elim fun s2w => Entails.sepExists_elim fun s1w =>
    Entails.sepExists_elim fun s0w => ?_
  refine Entails.trans ?_ (Entails.sepExists_intro s0w)
  refine Entails.trans ?_ (Entails.sepExists_intro s1w)
  refine Entails.trans ?_ (Entails.sepExists_intro s2w)
  refine Entails.trans ?_ (Entails.sepExists_intro s3w)
  refine Entails.trans ?_ (Entails.sepExists_intro s4w)
  refine Entails.trans ?_ (Entails.sepExists_intro s5w)
  refine Entails.trans ?_ (Entails.sepExists_intro s6w)
  exact Entails.refl _

theorem pkEmptyHeaders_entails_loopOf (A : RustAlloc) (sp' : BitVec 64) (n : ℕ) :
    vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗
      vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗
      ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4 ⊢
      preKeyStructLoopOf A (sp' + 56#64) n PreKeyRecordStructure.empty := by
  have hz2 := emp_entails_two_vecU8Buf_zero A
  refine Entails.trans ?_
    (preKeyStructAt_entails_loopOf A ⟨⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩⟩ (sp' + 56#64) n
      PreKeyRecordStructure.empty ⟨Or.inl (by decide), Or.inl (by decide)⟩)
  rw [preKeyStructAt_split_pub A ⟨⟨0#64, 1#64⟩, ⟨0#64, 1#64⟩⟩ sp' PreKeyRecordStructure.empty]
  dsimp only [PreKeyRecordStructure.empty]
  rw [vecU8At_eq_header_buf A (sp' + 56#64) 0#64 1#64 [],
    vecU8At_eq_header_buf A (sp' + 80#64) 0#64 1#64 []]
  rw [← emp_sepConj (vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗
    vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗
    ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4)]
  refine Entails.trans (sepConj_mono_left hz2) ?_
  apply entails_of_eq; ac_rfl

theorem prologue_000_to_224_wp {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32)
    (hpc : s0.pc = (tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
    (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true)
    (hF : img.FrozenLoaded s0) (hsym : s0.symtab = img.symtab)
    (hx0 : s0.readReg64 .x0 = x.bytesA)
    (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName + 0x224#64) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sm Pm =>
        PkEpilogueState img s0 (s0.sp - 224#64) sm ∧
        (Pm ⊢ pkEpilogueMem A (s0.sp - 224#64) x.ret x.bytesA x.bytes
            (PreKeyRecord.deserialize x.bytes) ∗
          pkCalleeSavedAt (s0.sp - 224#64) s0 ∗
          memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack)
            (pkSubStack - skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 224#64
  have hstk1 := pkStack_smallRoot_split s0.sp
  have hstk2 := pkSubStack_split sp'
  have h160 : memRegion sp' 160 =
      memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 := by
    rw [show (160 : Nat) = 40 + (16 + (56 + 48)) by decide,
      ProofLib.memRegion_split sp' 40 120 (by decide),
      ProofLib.memRegion_split (sp' + 40#64) 16 104 (by decide),
      ProofLib.memRegion_split (sp' + 40#64 + 16#64) 56 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h16 : memRegion (sp' + 40#64) 16 =
      (∃∗ u0 : BitVec 64, (sp' + 40#64) ↦₆₄ u0) ∗
      (∃∗ u1 : BitVec 64, (sp' + 48#64) ↦₆₄ u1) := by
    rw [ProofLib.memRegion_split (sp' + 40#64) 8 8 (by decide),
      ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Wire.SepWPp.mono_pre
    (P' := memRegion (sp' + 160#64) 64 ∗
      memRegion (sp' + 56#64) 56 ∗
      memRegion (sp' + 40#64) 16 ∗
      (memRegion sp' 40 ∗ memRegion (sp' + 112#64) 48 ∗
        memRegion x.ret 56 ∗ (x.bytesA ↦ₛ x.bytes) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)))
    (by
      rw [hstk1]
      dsimp only [sp'] at hstk2 h160 ⊢
      rw [hstk2, h160]
      apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion64_unpack (sp' + 160#64))
      (sepConj_mono (pkStruct56_unpack_init (sp' + 56#64)) (Entails.refl _))) ?_
  rw [h16]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun u1 => Wire.SepWPp.exists_pre fun u0 =>
    Wire.SepWPp.exists_pre fun s6w => Wire.SepWPp.exists_pre fun s5w =>
    Wire.SepWPp.exists_pre fun s4w => Wire.SepWPp.exists_pre fun s3w =>
    Wire.SepWPp.exists_pre fun s2w => Wire.SepWPp.exists_pre fun s1w =>
    Wire.SepWPp.exists_pre fun s0w =>
    Wire.SepWPp.exists_pre fun c7 => Wire.SepWPp.exists_pre fun c6 =>
    Wire.SepWPp.exists_pre fun c5 => Wire.SepWPp.exists_pre fun c4 =>
    Wire.SepWPp.exists_pre fun c3 => Wire.SepWPp.exists_pre fun c2 =>
    Wire.SepWPp.exists_pre fun c1 => Wire.SepWPp.exists_pre fun c0 => ?_
  have hfast := @fast_empty_174_wp img A ext s0
  have hloop := @decodeLoop_080_step_wp img A ext hC d s0
  have hih := @decodeLoop_070_wp img A ext hC d s0 sp' x.ret
  code_fetches_from CryptoVerification.libsignalSessionCode
    CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers.pkDec
    img.base (Rust.withPanics ext) pkDec_fnOff pkDecOff 0 92
  dsimp only [tripleRatchetProgAtExt] at hfast hloop hih hpc ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr preKeyDeserializeName = entry
  examples_hide_fetches
  dsimp only [sp']
  have h0 : s0.readReg64 (Reg.gpr 0#5) = x.bytesA := hx0
  have h1 : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 x.bytes.length := hx1
  have h8 : s0.readReg64 (Reg.gpr 8#5) = x.ret := hx8
  cases hbs : x.bytes with
  | nil =>
    have h1_nil : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by simpa [hbs] using h1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (372)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    have hoff40 : s0.sp - 184#64 = s0.sp - 224#64 + 40#64 := by bv_omega
    set F_saved := pkCalleeSavedAt sp' s0 ∗
      memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)
    have h16_pack := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) x.bytesA 0#64
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion sp' 40 ∗
        memRegion (sp' + 40#64) 16 ∗
        vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗
        vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗
        ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4 ∗
        memRegion (sp' + 112#64) 48 ∗
        ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x.ret 56 ∗
        (x.bytesA ↦ₛ ([] : List (BitVec 8))) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗
        F_saved)
      (by
        dsimp only [F_saved, pkCalleeSavedAt, vecHeader, sp'] at h16_pack ⊢
        simp only [arm64_norm, sepConj_assoc] at h16_pack ⊢
        rw [← sepConj_assoc ((s0.sp - 224#64 + 40#64) ↦₆₄ x.bytesA) ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64)]
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_left h16_pack))))))))))))))))) ?_
        apply entails_of_eq; rw [hoff40]; ac_rfl) ?_
    exact Wire.SepWPp.frame_tryFrom
      (hfast (sp' := sp') (x19 := x.ret) (ptr := x.bytesA)
        (out := PreKeyRecord.deserialize []) rfl
        ⟨by simp [sp', arm64_norm],
         by simpa [State.spAligned, arm64_norm] using hsp,
         hF1, hsym1, by simp [arm64_norm],
         ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
          by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simp [arm64_norm])
        (by simp [hrun, arm64_norm])
        (by simp [arm64_norm])
        (by simp [sp', arm64_norm]; bv_omega))
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)
  | cons b0 bs1 =>
    have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by simp [hbs, List.length_cons] at hlt ⊢; omega
    obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen63
    have h1_cons : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (b0 :: bs1).length := by
      simpa [hbs] using h1
    refine Wire.SepWPp.of_sepWP_frozen hF hsym (mid := entry + bv% (128)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_
    intro hF1 hsym1
    have hoff40 : s0.sp - 184#64 = s0.sp - 224#64 + 40#64 := by bv_omega
    set F_saved := pkCalleeSavedAt sp' s0 ∗
      memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)
    have hloop0 := pkEmptyHeaders_entails_loopOf A sp' (b0 :: bs1).length
    refine Wire.SepWPp.mono_pre
      (P' := pkLoopMem A sp' x.ret x.bytesA (b0 :: bs1) PreKeyRecordStructure.empty ∗ F_saved)
      (by
        unfold pkLoopMem sliceCursorAt
        dsimp only [F_saved, pkCalleeSavedAt, vecHeader, sp'] at hloop0 ⊢
        simp only [arm64_norm, sepConj_assoc] at hloop0 ⊢
        have hloop0L : (((((((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64 ∗ (s0.sp - 224#64 + 64#64) ↦₆₄ 1#64) ∗
            (s0.sp - 224#64 + 72#64) ↦₆₄ 0#64) ∗ (s0.sp - 224#64 + 80#64) ↦₆₄ 0#64) ∗
            (s0.sp - 224#64 + 88#64) ↦₆₄ 1#64) ∗ (s0.sp - 224#64 + 96#64) ↦₆₄ 0#64) ∗
            (s0.sp - 224#64 + 104#64) ↦₃₂ 0#32) ∗ memRegion (s0.sp - 224#64 + 108#64) 4 ⊢
            preKeyStructLoopOf A (s0.sp - 224#64 + 56#64) (b0 :: bs1).length PreKeyRecordStructure.empty := by
          simpa only [sepConj_assoc] using hloop0
        rw [← sepConj_assoc ((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64),
          ← sepConj_assoc (((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗ _),
          ← sepConj_assoc ((((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗ _) ∗ _),
          ← sepConj_assoc (((((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _),
          ← sepConj_assoc ((((((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _) ∗ _),
          ← sepConj_assoc (((((((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _) ∗ _) ∗ _),
          ← sepConj_assoc ((((((((s0.sp - 224#64 + 56#64) ↦₆₄ 0#64) ∗ _) ∗ _) ∗ _) ∗ _) ∗ _) ∗ _)]
        refine Entails.trans
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono hloop0L (Entails.refl _)))))))))) ?_
        apply entails_of_eq; rw [hoff40]; ac_rfl) ?_
    have hdes : PreKeyRecord.deserialize (b0 :: bs1) =
        pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField (bs1.length + 1)
          PreKeyRecordStructure.empty (b0 :: bs1)) := by
      rw [pkDeserialize_eq_of_decodeLoop (b0 :: bs1)]
      simp only [List.length_cons]
      cases decodeFieldsLoop PreKeyRecordStructure.mergeField (bs1.length + 1)
        PreKeyRecordStructure.empty (b0 :: bs1) <;> rfl
    rw [hdes]
    exact Wire.SepWPp.frame_tryFrom
      (hloop (sp' := sp') (x19 := x.ret) (ptr := x.bytesA)
        (fuel := bs1.length) (b0 := b0) (bs1 := bs1) (m := PreKeyRecordStructure.empty)
        (hih bs1.length)
        (by simp [arm64_norm])
        (by simp [hrun, arm64_norm])
        ⟨by simp [sp', arm64_norm],
         by simp [sp', arm64_norm]; bv_omega,
         by simp [arm64_norm],
         by simp [sp', arm64_norm]; bv_omega,
         by simp [arm64_norm],
         ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm],
          by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simp [sp', arm64_norm]; bv_omega)
        (by simp [sp', arm64_norm]; bv_omega)
        (by simp [arm64_norm])
        (by simpa [State.spAligned, arm64_norm] using hsp)
        hF1 hsym1
        (by simp [arm64_norm])
        (by simp)
        hlen63)
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)

/-! ## Relocatable `[LibsignalPlacement]` Ok-Post, Error Stubs, and Varint/Key CPS (Block `65`) -/

section Placed
open CryptoVerification.RecordCodecs.Placed

theorem post_ok_23c_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64}
    {m : PreKeyRecordStructure} {bs : List (BitVec 8)}
    {out : Except SignalProtocolError PreKeyRecord} (hok : out = .ok ⟨m⟩)
    (hst : PkEpilogueStatePlaced s0 sp' s)
    (hpc : s.pc = (blkPl_65).base + bv% (572)) (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = x19) (hx20 : s.readReg64 .x20 = sp' + 56#64) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗ preKeyStructOf A (sp' + 56#64) m ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x19 56 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  rcases hst with ⟨hsp_eq, hsp, hcrl, htr, hsaved⟩
  unfold preKeyStructOf; simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine Wire.SepWPp.exists_pre fun g => ?_
  rw [preKeyStructAt_split_pub A g sp' m,
    vecU8At_eq_header_buf A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey,
    vecU8At_eq_header_buf A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey]; simp only [sepConj_assoc]
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion40_unpack sp')
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_left (memRegion_four_entails (sp' + 108#64)))))))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun pad32 => Wire.SepWPp.exists_pre fun w0 =>
    Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w2 => Wire.SepWPp.exists_pre fun w3 => ?_
  have hpub_bounds : vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ⊢
      ⌜g.pub.cap.toNat < 2 ^ 63⌝ ∗ vecU8Buf A g.pub.cap g.pub.ptr m.publicKey := by
    unfold vecU8Buf; refine Entails.pure_left fun h => ?_
    rw [pure_true_emp h, pure_true_emp h.2.1, emp_sepConj, emp_sepConj]; exact Entails.refl _
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hpub_bounds)))))))) ?_
  simp only [sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun hpub_lt => ?_
  have ⟨hc1, hc2⟩ := cmn_one_ne_of_lt g.pub.cap hpub_lt
  have hp104 : ((sp' + 104#64) ↦₃₂ m.id) ∗ ((sp' + 108#64) ↦₃₂ pad32) =
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) := by
    simpa [BitVec.add_assoc, BitVec.reduceAdd] using pointsTo32_pair (sp' + 104#64) m.id pad32
  refine Wire.SepWPp.mono_pre
    (P' := (sp' ↦₆₄ w0) ∗ ((sp' + 8#64) ↦₆₄ w1) ∗ ((sp' + 16#64) ↦₆₄ w2) ∗ ((sp' + 24#64) ↦₆₄ w3) ∗
      memRegion (sp' + 32#64) 8 ∗ memRegion (sp' + 40#64) 16 ∗
      ((sp' + 56#64) ↦₆₄ g.pub.cap) ∗ ((sp' + 64#64) ↦₆₄ g.pub.ptr) ∗
      ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((sp' + 80#64) ↦₆₄ g.priv.cap) ∗ ((sp' + 88#64) ↦₆₄ g.priv.ptr) ∗
      ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) ∗ vecU8Buf A g.pub.cap g.pub.ptr m.publicKey ∗
      vecU8Buf A g.priv.cap g.priv.ptr m.privateKey ∗ memRegion (sp' + 112#64) 48 ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ memRegion x19 56 ∗
      (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (by dsimp only [vecHeader]; rw [← sepConj_assoc ((sp' + 104#64) ↦₃₂ m.id), hp104]
        simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]; apply entails_of_eq; ac_rfl) ?_
  have h19 : s.readReg64 (Reg.gpr 19#5) = x19 := hx19
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hx20
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (400)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (pack_tail_190_placed_wp (g := g) (m := m) (w0 := w0) (w1 := w1) (pad32 := pad32) hok
      ⟨by simp [hsp_eq, arm64_norm], by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp, hcrl1,
       by simp [htr, arm64_norm], ⟨by simpa [arm64_norm] using hsaved.x24, by simpa [arm64_norm] using hsaved.x25,
        by simpa [arm64_norm] using hsaved.x26, by simpa [arm64_norm] using hsaved.x27, by simpa [arm64_norm] using hsaved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [h19, arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp [arm64_norm]) (by simp [arm64_norm]))
  simp only [arm64_norm]
  have h56 : ((sp' + 56#64) ↦₆₄ g.pub.cap) ∗ ((sp' + 64#64) ↦₆₄ g.pub.ptr) ∗
      ((sp' + 72#64) ↦₆₄ BitVec.ofNat 64 m.publicKey.length) ∗
      ((sp' + 80#64) ↦₆₄ g.priv.cap) ∗ ((sp' + 88#64) ↦₆₄ g.priv.ptr) ∗
      ((sp' + 96#64) ↦₆₄ BitVec.ofNat 64 m.privateKey.length) ∗
      ((sp' + 104#64) ↦₆₄ (pad32 ++ m.id)) ⊢ memRegion (sp' + 56#64) 56 := by
    rw [← hp104]; simpa [vecHeader, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc] using
      pkStruct56_pack sp' g.pub.cap g.pub.ptr (BitVec.ofNat 64 m.publicKey.length)
        g.priv.cap g.priv.ptr (BitVec.ofNat 64 m.privateKey.length) m.id pad32
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h56)))))))
  apply entails_of_eq; ac_rfl

theorem decodeErrorFrom_1c8_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr kind : BitVec 64}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (blkPl_65).base + bv% (456)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hkind : KindNoHeap kind) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗
        preKeyStructOf A (sp' + 56#64) mErr ∗ memRegion sp' 40 ∗ memRegion x19 56 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 261) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro (sp' + 112#64, kind) (pk_decodeErrorFrom_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (464)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ kind) ∗ memRegion (sp' + 120#64) 40 ∗ A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := KindNoHeap kind)
    (by simp [decodeErrorFromSpecWithStack, hsp_eq, arm64_norm]) hkind (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  dsimp only [decodeErrorFromSpecWithStack]; rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun ⟨_hx0_ne, htr2⟩ => ?_
  refine Wire.SepWPp.mono_pre ?_
    (post_err_1d0_placed_wp d (err := s2.readReg64 .x0) (mErr := mErr) herr
      ⟨hregs2.sp, hsp2_align, hcrl2, (by simp [htr2, htr, arm64_norm]), hregs2.saved⟩
      hpc2 hrun2 rfl hregs2.x19_eq hregs2.x22)
  refine Entails.trans ?_ (pkErrMem_of_structOf A sp' x19 ptr (s2.readReg64 .x0) 0 mErr bs)
  apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl

theorem decodeErrorFrom_1c4_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr w0 : BitVec 64}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (blkPl_65).base + bv% (452)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hkind : KindNoHeap (s.readReg64 .x8)) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ w0) ∗ memRegion (sp' + 120#64) 40 ∗
        preKeyStructOf A (sp' + 56#64) mErr ∗ memRegion sp' 40 ∗ memRegion x19 56 ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (456)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (decodeErrorFrom_1c8_placed_wp d (kind := s.readReg64 .x8) (mErr := mErr) herr
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcrl1 (by simpa [arm64_norm] using htr) hkind)
  apply entails_of_eq; simp only [arm64_norm]

theorem decodeErrorPush_2cc_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr err : BitVec 64} {n : ℕ}
    {bs : List (BitVec 8)} {mErr : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (herr : out = .error .invalidProtobufEncoding)
    (hpc : s.pc = (blkPl_65).base + bv% (716)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = sp' + 112#64) (herr_ne : err ≠ 0#64) (hn : n < 2 ^ 32) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (memRegion (sp' + 40#64) 16 ∗ (ptr ↦ₛ bs) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        ((sp' + 112#64) ↦₆₄ err) ∗ memRegion (sp' + 120#64) 40 ∗
        decodeErrorAtStackLen A err n ∗ preKeyStructOf A (sp' + 56#64) mErr ∗
        memRegion sp' 40 ∗ memRegion x19 56 ∗ A.pool ∗ stackAt sp' (skipFieldStackX 100))
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h0 : s.readReg64 (Reg.gpr 0#5) = sp' + 112#64 := hx0
  have hstack := stackAt_sub_split sp' (2 * extHookStack) (skipFieldStackX 100)
  simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 257) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro (sp' + 112#64, err, n) (pk_decodeErrorPush_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (720)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 112#64) ↦₆₄ err) ∗ decodeErrorAtStackLen A err n ∗ A.pool ∗ stackAt sp' (2 * extHookStack))
    (φ := err ≠ 0#64 ∧ n < 4294967296)
    (by simp [decodeErrorPushExternSpecWithStack, hsp_eq, h0, arm64_norm]) ⟨herr_ne, hn⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  dsimp only [decodeErrorPushExternSpecWithStack]; rw [sepConj_assoc]
  refine Wire.SepWPp.pure_pre fun htr2 => ?_
  simp only [sepExists_sepConj_left, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun err' => Wire.SepWPp.pure_pre fun _herr' => ?_
  refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
  refine Wire.SepWPp.mono_pre ?_
    (post_err_1d0_placed_wp d (err := err') (mErr := mErr) herr
      ⟨by simpa [arm64_norm] using hregs2.sp, by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
       hcrl3, by simpa [arm64_norm] using htr2.trans htr,
       ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
        by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
        by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
      (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22))
  have hscr := pkPointsTo112_memRegion40_entails_memRegion48 sp' err'
  refine Entails.trans ?_ (pkErrMem_of_structOf A sp' x19 ptr err' (n + 1) mErr bs)
  refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
  apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl

theorem decodeVarintSlow_15c_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (348)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have hstack := stackAt_sub_split sp' (64 + 2 * extHookStack) (skipFieldStackX 100)
  unfold pkLoopMem sliceCursorAt; simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 293) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro (sp' + 184#64, sp' + 40#64, ptr, bs) (pk_varintSlow_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (356)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ ((sp' + 40#64) ↦₆₄ ptr) ∗
      ((sp' + 40#64 + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗ (ptr ↦ₛ bs) ∗
      A.pool ∗ stackAt sp' (64 + 2 * extHookStack))
    (φ := bs.length < 2 ^ 64)
    (by simp [decodeVarintSlowSpecWithStack, hsp_eq, arm64_norm]) (by omega) (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  dsimp only [decodeVarintSlowSpecWithStack]
  rw [VarintBridge.decodeVarint_eq_varintSlow bs]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [Option.map]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hlen_sub : bs.length - (bs.length - rest.length) = rest.length := by rw [hrest, List.length_drop]; omega
    rw [hlen_sub, sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_2, hx1_2⟩ => ?_
    have hx0_2' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_2
    have hx1_2' : s2.readReg64 (Reg.gpr 1#5) = key := hx1_2
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (224)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (hcont key rest _ hd (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp [arm64_norm]))
    apply entails_of_eq; unfold pkAfterVarintMem sliceCursorAfter
    simp only [hstack, hsp_eq, arm64_norm]; ac_rfl
  | none =>
    dsimp only [Option.map]; rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun ⟨hx0_1, _hx1_ne⟩ => ?_
    have hx0_1' : s2.readReg64 (Reg.gpr 0#5) = 1#64 := hx0_1
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (post_err_1d0_placed_wp d (err := s2.readReg64 (Reg.gpr 1#5)) (mErr := m) (hnone hd)
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hcrl3, by simpa [arm64_norm] using htr2.trans htr,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
        (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22))
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 40#64)
      (ptr + BitVec.ofNat 64 (min 10 bs.length)) (BitVec.ofNat 64 (bs.length - min 10 bs.length))
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_ (pkErrMem_of_loopOf A sp' x19 ptr (s2.readReg64 (Reg.gpr 1#5)) 0 bs.length m bs)
    refine Entails.trans ?_ (sepConj_mono_left hpair)
    apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl

theorem decodeVarintSlice_0ac_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (172)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63) (hpre_slice : VarintSlicePre bs)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h23 : s.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := hx23
  have h21 : s.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := hx21
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hx2_nat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hstack := stackAt_sub_split sp' decodeVarintSliceStackX (skipFieldStackX 100)
  unfold pkLoopMem sliceCursorAt; simp only [hstack, pkMemRegion48_split24 sp', sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 76) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro ⟨sp' + 112#64, ptr, bs⟩ (pk_varintSlice_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (180)) (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 112#64) 24 ∗ (ptr ↦ₛ bs) ∗ A.pool ∗ stackAt sp' decodeVarintSliceStackX)
    (φ := bs.length < 2 ^ 63 ∧ VarintSlicePre bs)
    (by simp [decodeVarintSliceSpecX, hsp_eq, h1, h2, hx2_nat, arm64_norm]) ⟨hlen, hpre_slice⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
  have h23_2 : s2.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := by simpa [arm64_norm, h23] using hcs2.2.2.2.2.1
  have h21_2 : s2.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := by simpa [arm64_norm, h21] using hcs2.2.2.1
  dsimp only [decodeVarintSliceSpecX]
  cases hd : decodeVarint bs with
  | some p =>
    rcases p with ⟨key, rest⟩
    dsimp only [varintSliceResultAt]
    obtain ⟨k, _, hkl, hrest⟩ := decodeVarint_suffix hd
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    have hlen64 : bs.length < 2 ^ 64 := by omega
    have hrest64 : rest.length < 2 ^ 64 := by omega
    have hsub64 : bs.length - rest.length < 2 ^ 64 := by omega
    have hsub_bv : BitVec.ofNat 64 bs.length - BitVec.ofNat 64 (bs.length - rest.length) =
        BitVec.ofNat 64 rest.length := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64, Nat.mod_eq_of_lt hrest64]; omega
    have hult_false :
        (BitVec.ofNat 64 bs.length).ult (BitVec.ofNat 64 (bs.length - rest.length)) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, Nat.mod_eq_of_lt hsub64,
        decide_eq_false_iff_not]; omega
    rw [pointsTo64_zero_split32 (sp' + 112#64)]; simp only [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (224)) ?_
    wp_steps
    wp_if hcc
    · exfalso; rw [← hrest] at hcc; exact Bool.false_ne_true (hult_false.symm.trans hcc)
    · wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
      refine Wire.SepWPp.mono_pre ?_
        (hcont key rest _ hd (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
           by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
           by simpa [arm64_norm] using hregs2.x19_eq,
           ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
            by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
            by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
          hcrl3 (by simpa [arm64_norm] using htr2.trans htr) (by simp [arm64_norm]))
      have hscr := pkScratch24_ok_entails_memRegion48 sp' key (BitVec.ofNat 64 (bs.length - rest.length))
      unfold pkAfterVarintMem sliceCursorAfter; simp only [← hrest, hsub_bv]
      refine Entails.trans ?_ (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr)))
      apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl
  | none =>
    dsimp only [varintSliceResultAt]
    rw [pointsTo64_one_split32 (sp' + 112#64), sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun e => Wire.SepWPp.pure_pre fun _he_ne => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (post_err_1d0_placed_wp d (err := e) (mErr := m) (hnone hd)
        ⟨by simpa [arm64_norm] using hregs2.sp,
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hcrl3, by simpa [arm64_norm] using htr2.trans htr,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
        (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22))
    have hpair := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) ptr (BitVec.ofNat 64 bs.length)
    have hscr := pkScratch24_err_entails_memRegion48 sp' e
    simp only [arm64_norm] at hpair
    refine Entails.trans ?_ (pkErrMem_of_loopOf A sp' x19 ptr e 0 bs.length m bs)
    refine Entails.trans ?_ (sepConj_mono hpair (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hscr))))
    apply entails_of_eq; simp only [hstack, hsp_eq, arm64_norm]; ac_rfl

theorem decodeVarintMulti_098_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {bs : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (152)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx1 : s.readReg64 .x1 = ptr) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 bs.length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hne : bs ≠ []) (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint bs = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : decodeVarint bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have h1 : s.readReg64 (Reg.gpr 1#5) = ptr := hx1
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 bs.length := hx2
  have hlen_pos : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hlen64 : bs.length < 2 ^ 64 := by omega
  by_cases hlen11 : 11 ≤ bs.length
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = true := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_true_eq]; omega
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (172)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    exact decodeVarintSlice_0ac_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simpa [arm64_norm] using hx23) (by simpa [arm64_norm] using hx21)
      (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
      hcrl1 (by simpa [arm64_norm] using htr) hlen (Or.inl hlen11) hcont hnone
  · have hhi : (10#64).ult (BitVec.ofNat 64 bs.length) = false := by
      simp only [BitVec.ult, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlen64, decide_eq_false_iff_not]; omega
    have hlast_addr : ptr + BitVec.ofNat 64 bs.length + bv% (2 ^ 64 - 1) = ptr + BitVec.ofNat 64 (bs.length - 1) := by
      have heq : bs.length = (bs.length - 1) + 1 := by omega
      have h1_eq : BitVec.ofNat 64 bs.length = BitVec.ofNat 64 (bs.length - 1) + 1#64 := by
        conv_lhs => rw [heq]; exact BitVec.ofNat_add (bs.length - 1) 1
      rw [h1_eq]; bv_omega
    by_cases hlast : (bs.getLast hne).toNat ≤ 0x7F
    · have hbit31 := (signExtend32_bit31_eq_false_iff (bs.getLast hne)).mpr hlast
      unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (172)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
      refine Wire.SepWPp.mono_pre ?_
        (decodeVarintSlice_0ac_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simpa [arm64_norm] using hx23) (by simpa [arm64_norm] using hx21)
          (by simpa [arm64_norm] using hx1) (by simpa [arm64_norm] using hx2)
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr) hlen (Or.inr ⟨hne, hlast⟩) hcont hnone)
      apply entails_of_eq; unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [arm64_norm, sepConj_assoc]
    · have hbit31 := (signExtend32_bit31_eq_true_iff (bs.getLast hne)).mpr (by omega)
      unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [sepConj_assoc]
      refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (348)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
      refine Wire.SepWPp.mono_pre ?_
        (decodeVarintSlow_15c_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr) hlen hcont hnone)
      apply entails_of_eq; unfold pkLoopMem sliceCursorAt
      rw [Wire.pointsToBytes_split_last ptr bs hne, ← hlast_addr]; simp only [arm64_norm, sepConj_assoc]

theorem decodeVarint_080_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (128)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (key : BitVec 64) (rest : List (BitVec 8)) (s1 : State),
      decodeVarint (b0 :: bs1) = some (key, rest) →
      s1.pc = (blkPl_65).base + bv% (224) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace → s1.readReg64 .x0 = key →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr (b0 :: bs1) rest (b0 :: bs1).length m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr (b0 :: bs1) out) (tryFromQp s0))
    (hnone : decodeVarint (b0 :: bs1) = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr (b0 :: bs1) out) (tryFromQp s0) := by
  have h23 : s.readReg64 (Reg.gpr 23#5) = sp' + 40#64 := hx23
  have h21 : s.readReg64 (Reg.gpr 21#5) = sp' + 48#64 := hx21
  have h2 : s.readReg64 (Reg.gpr 2#5) = BitVec.ofNat 64 (b0 :: bs1).length := hx2
  by_cases hb0 : b0.toNat ≤ 0x7F
  · have hbit63 := (signExtend64_bit63_eq_false_iff b0).mpr hb0
    have hd := decodeVarint_cons_of_le b0 bs1 hb0
    have hsub1 : BitVec.ofNat 64 (bs1.length + 1) - 1#64 = BitVec.ofNat 64 bs1.length := by
      have h1_eq : BitVec.ofNat 64 (bs1.length + 1) = BitVec.ofNat 64 bs1.length + 1#64 :=
        BitVec.ofNat_add bs1.length 1
      rw [h1_eq]; bv_omega
    unfold pkLoopMem sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]; simp only [sepConj_assoc]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (224)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    have hse := signExtend64_eq_zeroExtend64_of_le b0 hb0
    refine Wire.SepWPp.mono_pre ?_
      (hcont (b0.zeroExtend 64) bs1 _ hd (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr) (by simp [hse, arm64_norm]))
    apply entails_of_eq; unfold pkAfterVarintMem sliceCursorAfter
    rw [pointsToBytes_cons ptr b0 bs1]
    simp only [List.length_cons, Nat.add_sub_cancel_left, hsub1, arm64_norm, sepConj_assoc]
  · have hbit63 := (signExtend64_bit63_eq_true_iff b0).mpr (by omega)
    unfold pkLoopMem sliceCursorAt; rw [pointsToBytes_cons ptr b0 bs1]; simp only [sepConj_assoc]
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (152)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (decodeVarintMulti_098_placed_cps d (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simpa [arm64_norm] using hx23) (by simpa [arm64_norm] using hx21)
        (by simp [arm64_norm]) (by simpa [arm64_norm] using hx2)
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr) (List.cons_ne_nil b0 bs1) hlen hcont hnone)
    apply entails_of_eq; unfold pkLoopMem sliceCursorAt
    rw [pointsToBytes_cons ptr b0 bs1]; simp only [arm64_norm, sepConj_assoc]

end Placed
end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers
