/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesEncode
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.EncodedLenPhase
public import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState.InnerReloc
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChainStep
import LibsignalBinary.Proofs.SpqrV1.Top.DecodeState
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesInnerDispatch
import LibsignalBinary.Proofs.SpqrV1.Top.Send.Pure

/-!
# `spqr::send`: `Message::serialize` through `PqRatchetState` Encoding (`0x317fc -> 0x320a4`)

Composes `<Message>::serialize`, 928-byte `States` relocation, `<States>::into_pb`, 352-byte
`PqRatchetState` stack assembly, and inlined `PqRatchetState` encoding (`0x317fc -> 0x320a4`) in
`spqr::send::<HookRng>`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (ShaCompress)
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.SpqrV1.Top.ChainFrom
open CryptoVerification.SpqrV1.Top.ChainFrom.ChainFromNorm
open CryptoVerification.SpqrV1.Top.ChainFromVersionNegotiation
open CryptoVerification.SpqrV1.Top.MessageSerialize
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.States.IntoPb
open CryptoVerification.SpqrV1.Prost.EncodeToVec

/-! ## 1. Relocation and Decomposition Helpers for `0x317fc..0x31918` -/

/-- Framed `memcpy` call rule for an explicit byte slice `src ↦ₛ bs`. -/
private theorem call_memcpy_bytes_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {bs : List (BitVec 8)} {n : Nat} (hlen : bs.length = n)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ (src ↦ₛ bs)) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf (((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.call_subroutine_frame hcall (x := (dst, src, bs)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm
    dsimp only [sessionMemcpyRegionSpec, memcpyRegionSpec]
    rw [hlen, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [sessionMemcpyRegionSpec]; rw [sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) (htr.trans htrace)
      ⟨hcs_sf.2.2.2.2.2.2.2.2.2.2.2⟩
      hcs_sf.1 hcs_sf.2.1 hcs_sf.2.2.1 hcs_sf.2.2.2.1 hcs_sf.2.2.2.2.1
      hcs_sf.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.1
      hcs_sf.2.2.2.2.2.2.2.2.1 hcs_sf.2.2.2.2.2.2.2.2.2.1

/-- Framed `memcpy` call rule for any `States.Leaves.Relocatable n F` predicate family. -/
private theorem call_memcpy_relocate_bridge2 {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry sessionMemcpyRegionSpec)
    (dst src : BitVec 64) {n : Nat} {F : BitVec 64 → SepProp}
    (hrel : States.Leaves.Relocatable n F)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp} {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true) (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace) (hx0 : s.readReg64 Reg.x0 = dst) (hx1 : s.readReg64 Reg.x1 = src)
    (hx2 : (s.readReg64 Reg.x2).toNat = n)
    (hsplit : P = (memRegion dst n ∗ F src) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp_call → sf.trace = s0.trace →
      VRegsAt s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      SepWP prog target_pc sf ((F dst ∗ memRegion src n) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  rw [hsplit]
  refine SepWP.weaken_pre (sepConj_mono_left (sepConj_mono_right (hrel src))) ?_
  wp_pull_exists; rename_i bs
  wp_focus_pure; intro hlen
  refine call_memcpy_bytes_bridge2 hcall dst src hlen hpc hrun hsp hsp_align hlr htrace hx0 hx1 hx2
    (Frame := States.Leaves.relocatedHeap F bs ∗ Frame) (by ac_rfl) ?_
  intro sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28
  have hrecomp := States.Leaves.relocatedHeap_recompose F bs dst
  have hsrc : (src ↦ₛ bs) ⊢ memRegion src n := by
    rw [← hlen]; exact pointsToBytes_entails_memRegion src bs
  refine SepWP.weaken_pre ?_
    (hnext sf hpc_sf hrun_sf hsp_sf htr_sf hv_sf hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28)
  refine Entails.trans (Entails.of_eq (show
    ((dst ↦ₛ bs) ∗ (src ↦ₛ bs)) ∗ (States.Leaves.relocatedHeap F bs ∗ Frame) =
    (((dst ↦ₛ bs) ∗ States.Leaves.relocatedHeap F bs) ∗ (src ↦ₛ bs)) ∗ Frame by ac_rfl)) ?_
  exact sepConj_mono_left (sepConj_mono hrecomp hsrc)

/-! ## 2. `chunkedStatesAt` Relocation (`0x31810..0x3184c`) -/

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedKeysUnsampledAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    Relocatable 56 (fun a => chunkedKeysUnsampledAt A a st) := by
  refine Relocatable.congr rfl (fun a => ?_)
    (Relocatable.of_unchunkedCt2SentAt A { epoch := st.uc.epoch, auth := st.uc.auth })
  rfl

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedKeysSampledAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.KeysSampled spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedKeysSampledAt A a st) := by
  refine Relocatable.congr rfl (fun a => (chunkedKeysSampledAt_eq_ct1ReceivedAt A a st).symm)
    (Relocatable.of_chunkedCt1ReceivedAt A (chunkedKeysSampledToCt1Received st))

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedEkSentCt1ReceivedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendEk.EkSentCt1Received spqrPolyApi (spqrAuthApi F)) :
    Relocatable 504 (fun a => chunkedEkSentCt1ReceivedAt A a st) :=
  Relocatable.sepConj (off := 104#64) (m := 504) rfl rfl
    (Relocatable.of_unchunkedEkSentCt1ReceivedAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ct2)

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedNoHeaderReceivedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.NoHeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 456 (fun a => chunkedNoHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 56#64) (m := 456) rfl rfl
    (Relocatable.of_unchunkedCt2SentAt A { epoch := st.uc.epoch, auth := st.uc.auth })
    (Relocatable.of_polyDecoderAt A st.receiving_hdr)

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedHeaderReceivedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    Relocatable 480 (fun a => chunkedHeaderReceivedAt A a st) :=
  Relocatable.sepConj (off := 80#64) (m := 480) rfl rfl
    (Relocatable.of_unchunkedEkSentAt A { epoch := st.uc.epoch, auth := st.uc.auth, dk := st.uc.hdr })
    (Relocatable.of_polyDecoderAt A st.receiving_ek)

open CryptoVerification.SpqrV1.States.Leaves in
private theorem Relocatable.of_chunkedCt1AcknowledgedAt_b2 (A : RustAlloc) {F : ShaCompress}
    (st : Chunked.SendCt.Ct1Acknowledged spqrPolyApi (spqrAuthApi F)) :
    Relocatable 528 (fun a => chunkedCt1AcknowledgedAt A a st) :=
  Relocatable.sepConj (off := 128#64) (m := 528) rfl rfl
    (Relocatable.of_unchunkedCt1SentAt A st.uc)
    (Relocatable.of_polyDecoderAt A st.receiving_ek)

open CryptoVerification.SpqrV1.States.Leaves in
theorem Relocatable.of_chunkedStatesAt (A : RustAlloc) {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) :
    Relocatable 928 (fun a => chunkedStatesAt A a st) := by
  cases st with
  | keysUnsampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 56#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 2#64)
        (Relocatable.sepConj (off := 56#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedKeysUnsampledAt_b2 A s) (Relocatable.of_memRegion 864)))
  | keysSampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 504#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 3#64)
        (Relocatable.sepConj (off := 504#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedKeysSampledAt_b2 A s) (Relocatable.of_memRegion 416)))
  | headerSent s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 880#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 4#64)
        (Relocatable.sepConj (off := 880#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedHeaderSentAt A s) (Relocatable.of_memRegion 40)))
  | ct1Received s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 504#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 5#64)
        (Relocatable.sepConj (off := 504#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedCt1ReceivedAt A s) (Relocatable.of_memRegion 416)))
  | ekSentCt1Received s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 504#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 6#64)
        (Relocatable.sepConj (off := 504#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedEkSentCt1ReceivedAt_b2 A s) (Relocatable.of_memRegion 416)))
  | noHeaderReceived s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 456#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 7#64)
        (Relocatable.sepConj (off := 456#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedNoHeaderReceivedAt_b2 A s) (Relocatable.of_memRegion 464)))
  | headerReceived s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 480#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 8#64)
        (Relocatable.sepConj (off := 480#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedHeaderReceivedAt_b2 A s) (Relocatable.of_memRegion 440)))
  | ct1Sampled s => exact Relocatable.of_chunkedCt1SampledAt A s
  | ekReceivedCt1Sampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 528#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 10#64)
        (Relocatable.sepConj (off := 528#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedEkReceivedCt1SampledAt A s) (Relocatable.of_memRegion 392)))
  | ct1Acknowledged s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 528#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 11#64)
        (Relocatable.sepConj (off := 528#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedCt1AcknowledgedAt_b2 A s) (Relocatable.of_memRegion 392)))
  | ct2Sampled s =>
    refine Relocatable.congr rfl (fun a => by dsimp only [chunkedStatesAt]; rw [BitVec.add_assoc a 8#64 456#64]; rfl)
      (Relocatable.sepConj (off := 8#64) (m := 928) rfl rfl (Relocatable.pointsTo64 12#64)
        (Relocatable.sepConj (off := 456#64) (m := 920) rfl rfl
          (Relocatable.of_chunkedCt2SampledAt A s) (Relocatable.of_memRegion 464)))

/-! ## 3. `outWords28` Relocation Bridge for `optProtoInnerStateAt` / `v1StatePBPinnedAt` (`0x3185c`) -/

theorem states_into_pb_innerState_isSome {F : ShaCompress}
    (st : States spqrPolyApi (spqrAuthApi F)) :
    ∃ is : V1State.InnerState, st.into_pb.innerState = some is := by
  cases st <;> exact ⟨_, rfl⟩

theorem quads28At_eq_outWords28 (a : BitVec 64)
    (i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 : BitVec 64) :
    DecodeState.quads28At a
      (((i0, i8, i16, i24, i32, i40, i48), (i56, i64, i72, i80, i88, i96, i104)),
       ((i112, i120, i128, i136, i144, i152, i160), (i168, i176, i184, i192, i200, i208, i216))) =
    outWords28 a i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 := by
  dsimp only [DecodeState.quads28At, DecodeState.quads14At, DecodeState.quads7At, outWords28]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]; ac_rfl

/-- Address-independent heap resource for `V1State.InnerState` while its 28 stack words are
    unpacked as `outWords28 a i0 ... i216`. -/
def protoInnerWordsHeap (A : RustAlloc) (is : V1State.InnerState)
    (i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 : BitVec 64) : SepProp :=
  let q : DecodeState.Quads28 :=
    (((i0, i8, i16, i24, i32, i40, i48), (i56, i64, i72, i80, i88, i96, i104)),
     ((i112, i120, i128, i136, i144, i152, i160), (i168, i176, i184, i192, i200, i208, i216)))
  ⌜q.head ≠ DecodeState.none3Cap⌝ ∗ DecodeState.canonicalV1InnerHeap A q is

theorem optProtoInnerStateAt_some_entails_outWords28 (A : RustAlloc) (a : BitVec 64)
    (is : V1State.InnerState) :
    optProtoInnerStateAt A a (some is) ⊢
      ∃∗ i0 : BitVec 64, ∃∗ i8 : BitVec 64, ∃∗ i16 : BitVec 64, ∃∗ i24 : BitVec 64,
      ∃∗ i32 : BitVec 64, ∃∗ i40 : BitVec 64, ∃∗ i48 : BitVec 64, ∃∗ i56 : BitVec 64,
      ∃∗ i64 : BitVec 64, ∃∗ i72 : BitVec 64, ∃∗ i80 : BitVec 64, ∃∗ i88 : BitVec 64,
      ∃∗ i96 : BitVec 64, ∃∗ i104 : BitVec 64, ∃∗ i112 : BitVec 64, ∃∗ i120 : BitVec 64,
      ∃∗ i128 : BitVec 64, ∃∗ i136 : BitVec 64, ∃∗ i144 : BitVec 64, ∃∗ i152 : BitVec 64,
      ∃∗ i160 : BitVec 64, ∃∗ i168 : BitVec 64, ∃∗ i176 : BitVec 64, ∃∗ i184 : BitVec 64,
      ∃∗ i192 : BitVec 64, ∃∗ i200 : BitVec 64, ∃∗ i208 : BitVec 64, ∃∗ i216 : BitVec 64,
        outWords28 a i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
          i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗
        protoInnerWordsHeap A is i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
          i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 := by
  refine Entails.trans (DecodeState.of_drop_inner_canonical A a (some is)) ?_
  unfold DecodeState.optProtoInnerStateAt; apply Entails.sepExists_elim
  rintro ⟨⟨⟨i0, i8, i16, i24, i32, i40, i48⟩, ⟨i56, i64, i72, i80, i88, i96, i104⟩⟩,
          ⟨⟨i112, i120, i128, i136, i144, i152, i160⟩, ⟨i168, i176, i184, i192, i200, i208, i216⟩⟩⟩
  refine Entails.sepExists_right i0 (Entails.sepExists_right i8 (Entails.sepExists_right i16
    (Entails.sepExists_right i24 (Entails.sepExists_right i32 (Entails.sepExists_right i40
    (Entails.sepExists_right i48 (Entails.sepExists_right i56 (Entails.sepExists_right i64
    (Entails.sepExists_right i72 (Entails.sepExists_right i80 (Entails.sepExists_right i88
    (Entails.sepExists_right i96 (Entails.sepExists_right i104 (Entails.sepExists_right i112
    (Entails.sepExists_right i120 (Entails.sepExists_right i128 (Entails.sepExists_right i136
    (Entails.sepExists_right i144 (Entails.sepExists_right i152 (Entails.sepExists_right i160
    (Entails.sepExists_right i168 (Entails.sepExists_right i176 (Entails.sepExists_right i184
    (Entails.sepExists_right i192 (Entails.sepExists_right i200 (Entails.sepExists_right i208
    (Entails.sepExists_right i216 ?_)))))))))))))))))))))))))))
  rw [quads28At_eq_outWords28]; dsimp only [protoInnerWordsHeap]; exact Entails.of_eq (by ac_rfl)

theorem outWords28_entails_v1StatePBPinnedAt (A : RustAlloc) (a : BitVec 64)
    (v1 : V1State) (is : V1State.InnerState) (his : v1.innerState = some is)
    (i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
     i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 : BitVec 64) :
    outWords28 a i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗
    protoInnerWordsHeap A is i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ⊢
    ∃∗ g_v1 : CryptoVerification.SpqrV1.ProtoRepr.V1StatePBGhost,
      Prost.EncodeToVec.optPqRatchetInnerPBPinnedAt A g_v1 a (some (.v1 v1)) := by
  change _ ⊢ ∃∗ g_v1 : CryptoVerification.SpqrV1.ProtoRepr.V1StatePBGhost,
    CryptoVerification.SpqrV1.ProtoRepr.v1StatePBPinnedAt A g_v1 a v1
  rw [← CryptoVerification.SpqrV1.ProtoRepr.v1StatePBAt_eq_exists_pinned,
      v1StatePBAt_eq_optProtoInnerStateAt, his]
  refine Entails.trans ?_ (DecodeState.optProtoInnerStateAt_canonical_entails_drop A a (some is))
  unfold DecodeState.optProtoInnerStateAt; dsimp only [protoInnerWordsHeap]
  refine Entails.sepExists_right
    (((i0, i8, i16, i24, i32, i40, i48), (i56, i64, i72, i80, i88, i96, i104)),
     ((i112, i120, i128, i136, i144, i152, i160), (i168, i176, i184, i192, i200, i208, i216))) ?_
  rw [quads28At_eq_outWords28]; exact Entails.of_eq (by ac_rfl)

/-! ## 4. Relocating `VersionNegotiationPB`, `ChainPB`, and `V1State` into `PqRatchetState` -/

def optVersionNegWordsHeap (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.VersionNegotiationPBGhost)
    (opt : Option VersionNegotiationPB) (w1 w2 w3 w4 w5 : BitVec 64) : SepProp :=
  match opt with
  | none => emp
  | some vn =>
    ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
      vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
    ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey

theorem optVersionNegotiationPBPinnedAt_entails_vnWords6 (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.VersionNegotiationPBGhost) (a : BitVec 64)
    (opt : Option VersionNegotiationPB) :
    CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBPinnedAt A g a opt ⊢
      ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
      ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64,
        vnWords6At a (Prost.EncodeToVec.optVersionNegCap g opt) w1 w2 w3 w4 w5 ∗
        optVersionNegWordsHeap A g opt w1 w2 w3 w4 w5 := by
  rw [Prost.EncodeToVec.optVersionNegotiationPBPinnedAt_eq]
  refine Entails.trans (sepConj_mono_right (optVersionNegRest_entails_words5 A g a opt)) ?_
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w1
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w2
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w3
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w4
  rw [sepExists_sepConj_right]; apply Entails.sepExists_elim; intro w5
  refine Entails.sepExists_right w1 (Entails.sepExists_right w2
    (Entails.sepExists_right w3 (Entails.sepExists_right w4 (Entails.sepExists_right w5 ?_))))
  unfold vnWords6At optVersionNegWordsHeap; exact Entails.of_eq (by ac_rfl)

theorem vnWords6_entails_optVersionNegotiationPBPinnedAt (A : RustAlloc)
    (g : CryptoVerification.SpqrV1.ProtoRepr.VersionNegotiationPBGhost) (a : BitVec 64)
    (opt : Option VersionNegotiationPB) (w1 w2 w3 w4 w5 : BitVec 64) :
    vnWords6At a (Prost.EncodeToVec.optVersionNegCap g opt) w1 w2 w3 w4 w5 ∗
      optVersionNegWordsHeap A g opt w1 w2 w3 w4 w5 ⊢
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBPinnedAt A g a opt := by
  rw [Prost.EncodeToVec.optVersionNegotiationPBPinnedAt_eq]; unfold vnWords6At optVersionNegWordsHeap
  refine Entails.trans (Entails.of_eq (show
    ((a ↦₆₄ Prost.EncodeToVec.optVersionNegCap g opt) ∗
      ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
      ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5)) ∗
      (match opt with
       | none => emp
       | some vn =>
         ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
           vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
         ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey) =
    (a ↦₆₄ Prost.EncodeToVec.optVersionNegCap g opt) ∗
      (((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
       ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗
       (match opt with
        | none => emp
        | some vn =>
          ⌜w1 = g.authKey.ptr ∧ w2 = BitVec.ofNat 64 vn.authKey.length ∧
            vnParamsDirMinVerWords vn w3 w4 w5⌝ ∗
          ProtoRepr.EncodedLen.vecU8Buf A g.authKey.cap g.authKey.ptr vn.authKey)) by ac_rfl)) ?_
  exact sepConj_mono_right (words5_entails_optVersionNegRest A g a opt w1 w2 w3 w4 w5)

def optChainWordsHeap (A : RustAlloc) (g : ChainFrom.ChainPBGhost) (x25 : BitVec 64)
    (opt : Option ChainPB) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) : SepProp :=
  match opt with
  | none => ⌜x25 = noneCap⌝
  | some pb =>
    ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap ∧ c1 = g.linksPtr ∧
      c2 = BitVec.ofNat 64 (g.epochs.zip pb.links).length ∧ c3 = g.nextRoot.cap ∧
      c4 = g.nextRoot.ptr ∧ c5 = BitVec.ofNat 64 pb.nextRoot.length ∧
      c6 = pb.currentEpoch ∧ c7 = pb.sendEpoch ∧ chainPBParamsDirWords pb c8 c9⌝ ∗
    chainPBHeapAt A g pb

theorem optChainPBRegSlotAt_entails_chainWords9 (A : RustAlloc) (a_slot : BitVec 64)
    (x25 : BitVec 64) (opt : Option ChainPB) :
    optChainPBRegSlotAt A a_slot x25 opt ⊢
      ∃∗ g : ChainFrom.ChainPBGhost,
      ∃∗ c1 : BitVec 64, ∃∗ c2 : BitVec 64, ∃∗ c3 : BitVec 64,
      ∃∗ c4 : BitVec 64, ∃∗ c5 : BitVec 64, ∃∗ c6 : BitVec 64,
      ∃∗ c7 : BitVec 64, ∃∗ c8 : BitVec 64, ∃∗ c9 : BitVec 64,
        chainWords9At a_slot c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
        optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  cases opt with
  | none =>
    unfold optChainPBRegSlotAt optChainWordsHeap
    apply Entails.pure_left; intro hx25; rw [memRegion_72_words9 a_slot]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro c9; apply Entails.sepExists_elim; intro c8
    apply Entails.sepExists_elim; intro c7; apply Entails.sepExists_elim; intro c6
    apply Entails.sepExists_elim; intro c5; apply Entails.sepExists_elim; intro c4
    apply Entails.sepExists_elim; intro c3; apply Entails.sepExists_elim; intro c2
    apply Entails.sepExists_elim; intro c1
    refine Entails.sepExists_right
      ({ linksCap := 0#64, linksPtr := 0#64, epochs := [], nextRoot := ⟨0#64, 0#64⟩ } :
        ChainFrom.ChainPBGhost)
      (Entails.sepExists_right c1 (Entails.sepExists_right c2 (Entails.sepExists_right c3
      (Entails.sepExists_right c4 (Entails.sepExists_right c5 (Entails.sepExists_right c6
      (Entails.sepExists_right c7 (Entails.sepExists_right c8 (Entails.sepExists_right c9 ?_)))))))))
    unfold chainWords9At
    exact Entails.trans (Entails.pure_right hx25 (Entails.of_eq (by ac_rfl))) (Entails.of_eq (by ac_rfl))
  | some pb =>
    unfold optChainPBRegSlotAt optChainWordsHeap
    apply Entails.sepExists_elim; intro g; apply Entails.pure_left; rintro ⟨hx25, hne⟩
    refine Entails.trans (chainPBRestAt_entails_words9 A g (a_slot - 8#64) pb) ?_
    apply Entails.sepExists_elim; intro c8; apply Entails.sepExists_elim; intro c9
    apply Entails.pure_left; intro hparams
    refine Entails.sepExists_right g (Entails.sepExists_right g.linksPtr
      (Entails.sepExists_right (BitVec.ofNat 64 (g.epochs.zip pb.links).length)
      (Entails.sepExists_right g.nextRoot.cap (Entails.sepExists_right g.nextRoot.ptr
      (Entails.sepExists_right (BitVec.ofNat 64 pb.nextRoot.length)
      (Entails.sepExists_right pb.currentEpoch (Entails.sepExists_right pb.sendEpoch
      (Entails.sepExists_right c8 (Entails.sepExists_right c9 ?_)))))))))
    unfold chainWords9At
    have ha0 : a_slot - 8#64 + 8#64 = a_slot := by bv_omega
    have ha8 : a_slot - 8#64 + 16#64 = a_slot + 8#64 := by bv_omega
    have ha16 : a_slot - 8#64 + 24#64 = a_slot + 16#64 := by bv_omega
    have ha24 : a_slot - 8#64 + 32#64 = a_slot + 24#64 := by bv_omega
    have ha32 : a_slot - 8#64 + 40#64 = a_slot + 32#64 := by bv_omega
    have ha40 : a_slot - 8#64 + 48#64 = a_slot + 40#64 := by bv_omega
    have ha48 : a_slot - 8#64 + 56#64 = a_slot + 48#64 := by bv_omega
    have ha56 : a_slot - 8#64 + 64#64 = a_slot + 56#64 := by bv_omega
    have ha64 : a_slot - 8#64 + 72#64 = a_slot + 64#64 := by bv_omega
    rw [ha0, ha8, ha16, ha24, ha32, ha40, ha48, ha56, ha64]
    refine Entails.trans (Entails.of_eq (show
      (a_slot ↦₆₄ g.linksPtr) ∗ ((a_slot + 8#64) ↦₆₄ BitVec.ofNat 64 (g.epochs.zip pb.links).length) ∗
        ((a_slot + 16#64) ↦₆₄ g.nextRoot.cap) ∗ ((a_slot + 24#64) ↦₆₄ g.nextRoot.ptr) ∗
        ((a_slot + 32#64) ↦₆₄ BitVec.ofNat 64 pb.nextRoot.length) ∗
        ((a_slot + 40#64) ↦₆₄ pb.currentEpoch) ∗ ((a_slot + 48#64) ↦₆₄ pb.sendEpoch) ∗
        ((a_slot + 56#64) ↦₆₄ c8) ∗ ((a_slot + 64#64) ↦₆₄ c9) ∗ chainPBHeapAt A g pb =
      chainWords9At a_slot g.linksPtr (BitVec.ofNat 64 (g.epochs.zip pb.links).length)
        g.nextRoot.cap g.nextRoot.ptr (BitVec.ofNat 64 pb.nextRoot.length)
        pb.currentEpoch pb.sendEpoch c8 c9 ∗ chainPBHeapAt A g pb by unfold chainWords9At; ac_rfl)) ?_
    exact sepConj_mono_right
      (Entails.pure_right ⟨hx25, hne, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hparams⟩ (Entails.refl _))

theorem chainWords9_entails_optChainPBPinnedAt (A : RustAlloc)
    (g : ChainFrom.ChainPBGhost) (a x25 : BitVec 64)
    (opt : Option ChainPB) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) :
    (a ↦₆₄ x25) ∗
      chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
      optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 ⊢
      CryptoVerification.SpqrV1.ProtoRepr.optChainPBPinnedAt A g.toProtoRepr a opt := by
  refine Entails.trans ?_ (ChainFrom.optChainPBAt_entails_protoRepr_pinned A g a opt)
  cases opt with
  | none =>
    unfold optChainWordsHeap ChainFrom.optChainPBAt
    refine Entails.trans (Entails.of_eq (show
      (a ↦₆₄ x25) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗ ⌜x25 = noneCap⌝ =
      ⌜x25 = noneCap⌝ ∗ ((a ↦₆₄ x25) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9) by ac_rfl)) ?_
    apply Entails.pure_left; rintro rfl
    exact sepConj_mono_right (chainWords9_to_memRegion_72 (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9)
  | some pb =>
    unfold optChainWordsHeap ChainFrom.optChainPBAt
    refine Entails.trans (Entails.of_eq (show
      (a ↦₆₄ x25) ∗ chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
        (⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap ∧ c1 = g.linksPtr ∧
          c2 = BitVec.ofNat 64 (g.epochs.zip pb.links).length ∧ c3 = g.nextRoot.cap ∧
          c4 = g.nextRoot.ptr ∧ c5 = BitVec.ofNat 64 pb.nextRoot.length ∧
          c6 = pb.currentEpoch ∧ c7 = pb.sendEpoch ∧ chainPBParamsDirWords pb c8 c9⌝ ∗ chainPBHeapAt A g pb) =
      ⌜x25 = g.linksCap ∧ g.linksCap ≠ noneCap ∧ c1 = g.linksPtr ∧
        c2 = BitVec.ofNat 64 (g.epochs.zip pb.links).length ∧ c3 = g.nextRoot.cap ∧
        c4 = g.nextRoot.ptr ∧ c5 = BitVec.ofNat 64 pb.nextRoot.length ∧
        c6 = pb.currentEpoch ∧ c7 = pb.sendEpoch ∧ chainPBParamsDirWords pb c8 c9⌝ ∗
        ((a ↦₆₄ x25) ∗ (chainWords9At (a + 8#64) c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗ chainPBHeapAt A g pb)) by ac_rfl)) ?_
    apply Entails.pure_left; rintro ⟨rfl, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hparams⟩
    refine Entails.trans ?_ (ChainFrom.ChainFromNorm.chainPBAt_unexpose_cap A g a pb)
    refine sepConj_mono_right ?_; unfold chainWords9At
    have ha16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
    have ha24 : a + 8#64 + 16#64 = a + 24#64 := by bv_omega
    have ha32 : a + 8#64 + 24#64 = a + 32#64 := by bv_omega
    have ha40 : a + 8#64 + 32#64 = a + 40#64 := by bv_omega
    have ha48 : a + 8#64 + 40#64 = a + 48#64 := by bv_omega
    have ha56 : a + 8#64 + 48#64 = a + 56#64 := by bv_omega
    have ha64 : a + 8#64 + 56#64 = a + 64#64 := by bv_omega
    have ha72 : a + 8#64 + 64#64 = a + 72#64 := by bv_omega
    rw [ha16, ha24, ha32, ha40, ha48, ha56, ha64, ha72]
    refine Entails.trans (Entails.of_eq (by ac_rfl))
      (words9_entails_chainPBRestAt A g a pb c8 c9 hparams)

open ProofLib.ProgramReflection in
theorem rodata_0x7e53a_eq_v1StateJumpTable :
    (libsignalSessionImage.data.drop (num% (ls_xref% 0x39148 0x3914c) - num% (ls_xref% 0x2440 0x2444))).take 11 =
      ProtoRepr.v1StateJumpTableBytes := by
  rfl_kernel

theorem rodata_v1StateJumpTable_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x39148 0x3914c)) (n := 11) (bs := ProtoRepr.v1StateJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

open ProofLib.ProgramReflection in
theorem rodata_0x82444_eq_statesIntoPbJumpTable :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "0000c7005d0098000a00fc001d01b600") - num% (ls_xref% 0x2440 0x2444))).take 22 =
      States.IntoPb.statesIntoPbJumpTableBytes := by
  rfl_kernel

theorem rodata_statesIntoPbJumpTable_intro {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ States.IntoPb.statesIntoPbJumpTableAt img.base ∗ P := by
  change s.mem ⊨ ((img.base + bv% (ls_bytes% "0000c7005d0098000a00fc001d01b600")) ↦ᵣ States.IntoPb.statesIntoPbJumpTableBytes) ∗ P
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_bytes% "0000c7005d0098000a00fc001d01b600")) (n := 22) (bs := States.IntoPb.statesIntoPbJumpTableBytes)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem memRegion_928_split_352_576 (sp : BitVec 64) :
    memRegion (sp + 0x1260#64) 928 =
      memRegion (sp + 0x1260#64) 352 ∗ memRegion (sp + 5056#64) 576 :=
  ProofLib.memRegion_split' (b := sp + 0x1260#64) (n := 352) (k := 576)
    (b' := sp + 5056#64) rfl (by bv_omega) (by decide)

theorem memRegion_224_split_24_200 (sp : BitVec 64) :
    memRegion (sp + 0x590#64) 224 =
      memRegion (sp + 1424#64) 24 ∗ memRegion (sp + 1448#64) 200 := by
  have h1424 : sp + 0x590#64 = sp + 1424#64 := rfl
  rw [h1424]
  exact ProofLib.memRegion_split' (b := sp + 1424#64) (n := 24) (k := 200)
    (b' := sp + 1448#64) rfl (by bv_omega) (by decide)

theorem chunkAt_entails_memRegion_34 (a : BitVec 64) (c : Chunk) :
    Poly.chunkAt a c ⊢ memRegion a 34 := by
  unfold Poly.chunkAt
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 2) (b' := a + 32#64)
        rfl (by bv_omega) (by decide)]
  have hdata : (a ↦ₛ c.data.toList) ⊢ memRegion a 32 := by
    have h := ProofLib.pointsToBytes_entails_memRegion a c.data.1
    rwa [c.data.2] at h
  exact sepConj_mono hdata (ProofLib.pointsTo16_entails_memRegion (a + 32#64) c.index)

theorem messagePayloadAt_entails_memRegion_40 (a : BitVec 64) (p : MessagePayload spqrPolyApi) :
    messagePayloadAt spqrPolyApi a p ⊢ memRegion (a + 8#64) 40 := by
  have h1_39 : ∀ tag : BitVec 8,
      ((a + 0x08#64) ↦₈ tag) ∗ memRegion (a + 0x09#64) 39 ⊢ memRegion (a + 8#64) 40 := by
    intro tag
    rw [ProofLib.memRegion_split' (b := a + 8#64) (n := 1) (k := 39) (b' := a + 0x09#64)
          rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (a + 8#64) tag)
  have hchunk_case : ∀ (tag : BitVec 8) (c : Chunk),
      ((a + 0x08#64) ↦₈ tag) ∗ memRegion (a + 0x09#64) 1 ∗
        Poly.chunkAt (a + 0x0a#64) c ∗ memRegion (a + 0x2c#64) 4 ⊢ memRegion (a + 8#64) 40 := by
    intro tag c
    refine Entails.trans ?_ (h1_39 tag)
    refine sepConj_mono_right ?_
    rw [ProofLib.memRegion_split' (b := a + 0x09#64) (n := 1) (k := 38) (b' := a + 0x0a#64)
          rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 0x0a#64) (n := 34) (k := 4) (b' := a + 0x2c#64)
          rfl (by bv_omega) (by decide)]
    exact sepConj_mono_right (sepConj_mono_left (chunkAt_entails_memRegion_34 (a + 0x0a#64) c))
  cases p with
  | none =>
    dsimp only [messagePayloadAt]
    exact h1_39 0#8
  | hdr c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 1#8 _
  | ek c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 2#8 _
  | ekCt1Ack c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 3#8 _
  | ct1Ack b =>
    dsimp only [messagePayloadAt]
    refine Entails.trans ?_ (h1_39 4#8)
    refine sepConj_mono_right ?_
    rw [ProofLib.memRegion_split' (b := a + 0x09#64) (n := 1) (k := 38) (b' := a + 0x0a#64)
          rfl (by bv_omega) (by decide)]
    exact sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion (a + 0x09#64) _)
  | ct1 c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 5#8 _
  | ct2 c =>
    dsimp only [messagePayloadAt]
    exact hchunk_case 6#8 _

theorem messageAt_entails_memRegion_48 (a : BitVec 64) (m : Message spqrPolyApi) :
    messageAt spqrPolyApi a m ⊢ memRegion a 48 := by
  unfold messageAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64)
        rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion a m.epoch)
    (messagePayloadAt_entails_memRegion_40 a m.payload)

theorem vecU8At_entails_vecU8 (A : RustAlloc) (v cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    vecU8At A v cap ptr bs ⊢ vecU8 A v bs := by
  unfold vecU8
  exact Entails.sepExists_right cap (Entails.sepExists_right ptr (Entails.refl _))

theorem optVersionNegWordsHeap_some_cap_ne (A : RustAlloc)
    (g : ProtoRepr.VersionNegotiationPBGhost) (vn : VersionNegotiationPB)
    (w1 w2 w3 w4 w5 : BitVec 64) :
    optVersionNegWordsHeap A g (some vn) w1 w2 w3 w4 w5 ⊢
      ⌜(Prost.EncodeToVec.optVersionNegCap g (some vn) + 1#64 == 0#64) = false⌝ ∗
      optVersionNegWordsHeap A g (some vn) w1 w2 w3 w4 w5 := by
  unfold optVersionNegWordsHeap ProtoRepr.EncodedLen.vecU8Buf
  rw [← sepConj_assoc]
  apply Entails.pure_left; rintro ⟨hw1, hw2, hw345⟩
  apply Entails.pure_left; rintro ⟨h1, h2, h3⟩
  have hne : (Prost.EncodeToVec.optVersionNegCap g (some vn) + 1#64 == 0#64) = false :=
    ProtoRepr.EncodedLen.cap_add_one_beq_zero_false h2
  rw [sepConj_assoc, ← sepConj_assoc]
  exact Entails.pure_right hne
    (Entails.pure_right ⟨hw1, hw2, hw345⟩
      (Entails.pure_right ⟨h1, h2, h3⟩ (Entails.refl _)))

theorem optChainWordsHeap_x25_eq (A : RustAlloc) (g : ChainFrom.ChainPBGhost) (x25 : BitVec 64)
    (opt : Option ChainPB) (c1 c2 c3 c4 c5 c6 c7 c8 c9 : BitVec 64) :
    optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 ⊢
      ⌜x25 = Prost.EncodeToVec.optChainCap g.toProtoRepr opt ∧
        (x25 + 1#64 == 0#64) = !opt.isSome⌝ ∗
      optChainWordsHeap A g x25 opt c1 c2 c3 c4 c5 c6 c7 c8 c9 := by
  cases opt with
  | none =>
    unfold optChainWordsHeap
    exact Entails.trans (Entails.of_eq (sepConj_emp _).symm)
      (Entails.pure_left fun hx25 => Entails.pure_right ⟨hx25, by rw [hx25]; decide⟩
        (Entails.trans (Entails.pure_right hx25 (Entails.refl _)) (Entails.of_eq (sepConj_emp _))))
  | some pb =>
    unfold optChainWordsHeap
    apply Entails.pure_left
    rintro ⟨hx25, hne, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hparams⟩
    have h1 : x25 = Prost.EncodeToVec.optChainCap g.toProtoRepr (some pb) := hx25
    have h2 : (x25 + 1#64 == 0#64) = !(some pb).isSome := by
      rw [hx25]; exact ChainFrom.ChainFromNorm.add_one_beq_zero_of_ne_noneCap hne
    exact Entails.pure_right ⟨h1, h2⟩
      (Entails.pure_right ⟨hx25, hne, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hparams⟩ (Entails.refl _))

/-- Combines `0x3185c -> 0x3191c / 0x31968` (`step_copy_pq_state_some_3185c` /
    `step_copy_pq_state_none_3185c`) with unpacking and reassembling `pqRatchetStatePBPinnedAt A
    g (s.sp + 4704#64)`. -/
theorem step_copy_and_assemble_pq_state_3185c {A : RustAlloc} {F : ShaCompress} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (v_20 : BitVec 64)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F))
    (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4096#64)
    (hrun : s.status = .Running)
    (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    let pq' : PqRatchetState :=
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName +
        (if vn.isSome then 4288#64 else 4364#64)) s
      (((s.sp + 0x20#64) ↦₆₄ v_20) ∗
        ProtoRepr.optVersionNegotiationPBAt A (s.sp + 0x30#64) vn ∗
        optChainPBRegSlotAt A (s.sp + 0xd90#64) (s.readReg64 .x25) ch ∗
        Drop.optProtoInnerStateAt A (s.sp + 0x590#64) st1.into_pb.innerState ∗
        memRegion (s.sp + 0x1260#64) 352 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧
        sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧
        sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧
        sf.readReg64 .x24 = s.readReg64 .x24 ∧
        sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        ∃ g : Prost.EncodeToVec.PqRatchetStatePBGhost,
          sf.readReg64 .x25 = Prost.EncodeToVec.optChainCap g.chain pq'.chain ∧
          sf.readReg64 .x26 = Prost.EncodeToVec.optVersionNegCap g.vn pq'.versionNegotiation ∧
          (sf.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome ∧
          (Q ⊢ ((s.sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗
            Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (s.sp + 4704#64) pq' ∗
            memRegion (s.sp + 0x30#64) 48 ∗
            memRegion (s.sp + 0xd90#64) 72 ∗
            memRegion (s.sp + 0x590#64) 224 ∗ Frame)) := by
  intro pq'
  obtain ⟨is, his⟩ := states_into_pb_innerState_isSome st1
  rw [his, Prost.EncodeToVec.optVersionNegotiationPBAt_eq_exists_pinned A (s.sp + 0x30#64) vn]
  wp_pull_exists; rename_i g_vn
  refine SepWP.focus_weaken
    (optVersionNegotiationPBPinnedAt_entails_vnWords6 A g_vn (s.sp + 0x30#64) vn) (by sep_focus) ?_
  wp_pull_exists; rename_i w1 w2 w3 w4 w5
  refine SepWP.focus_weaken
    (optChainPBRegSlotAt_entails_chainWords9 A (s.sp + 0xd90#64) (s.readReg64 .x25) ch)
    (by sep_focus) ?_
  wp_pull_exists; rename_i g_ch c1 c2 c3 c4 c5 c6 c7 c8 c9
  refine SepWP.focus_weaken
    (optChainWordsHeap_x25_eq A g_ch (s.readReg64 .x25) ch c1 c2 c3 c4 c5 c6 c7 c8 c9)
    (by sep_focus) ?_
  wp_focus_pure; rintro ⟨hx25_cap, hx25_some⟩
  refine SepWP.focus_weaken
    (optProtoInnerStateAt_some_entails_outWords28 A (s.sp + 0x590#64) is) (by sep_focus) ?_
  wp_pull_exists
  rename_i i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
    i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
  have h4704 : s.sp + 0x1260#64 = s.sp + 4704#64 := rfl
  have h4752 : s.sp + 0x1290#64 = (s.sp + 4704#64) + 48#64 := by bv_omega
  have h4760 : s.sp + 0x1298#64 = ((s.sp + 4704#64) + 48#64) + 8#64 := by bv_omega
  have h4832 : s.sp + 0x12e0#64 = (s.sp + 4704#64) + 128#64 := by bv_omega
  cases vn with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    have hvn_none : vnWords6At (s.sp + 0x30#64) (Prost.EncodeToVec.optVersionNegCap g_vn none) w1 w2 w3 w4 w5 =
        vnWords6At (s.sp + 0x30#64) noneCap w1 w2 w3 w4 w5 := rfl
    have hvn_none' : vnWords6At (s.sp + 4704#64) noneCap w1 w2 w3 w4 w5 =
        vnWords6At (s.sp + 4704#64) (Prost.EncodeToVec.optVersionNegCap g_vn none) w1 w2 w3 w4 w5 := rfl
    rw [hvn_none]
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (step_copy_pq_state_none_3185c s v_20 w1 w2 w3 w4 w5
        c1 c2 c3 c4 c5 c6 c7 c8 c9
        i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
        i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
        (optVersionNegWordsHeap A g_vn none w1 w2 w3 w4 w5 ∗
          optChainWordsHeap A g_ch (s.readReg64 .x25) ch c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
          protoInnerWordsHeap A is
            i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
            i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗ Frame)
        hpc hrun hx26 hsp_align) ?_)
    intro sf Qf hpcf _
    rintro ⟨hvf, hrunf, htrf, hspf, hx26f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f, hQf⟩
    refine SepWP.weaken_pre hQf ?_
    rw [h4704, h4752, h4760, h4832, hvn_none']
    have hvn_pack := vnWords6_entails_optVersionNegotiationPBPinnedAt A g_vn (s.sp + 4704#64) none w1 w2 w3 w4 w5
    have hch_pack := chainWords9_entails_optChainPBPinnedAt A g_ch ((s.sp + 4704#64) + 48#64) (s.readReg64 .x25) ch
      c1 c2 c3 c4 c5 c6 c7 c8 c9
    have hin_pack := outWords28_entails_v1StatePBPinnedAt A ((s.sp + 4704#64) + 128#64) st1.into_pb is his
      i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
    refine SepWP.focus_weaken hvn_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hch_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hin_pack (by sep_focus) ?_
    wp_pull_exists; rename_i g_v1
    refine Prost.EncodeToVec.SepWP.done hpcf hrunf
      ⟨hrunf, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f,
        ⟨g_vn, g_ch.toProtoRepr, g_v1⟩, hx25f.trans hx25_cap, hx26f, by rw [hx25f]; exact hx25_some, ?_⟩
    unfold Prost.EncodeToVec.pqRatchetStatePBPinnedAt
    dsimp only [pq']
    exact Entails.of_eq (by ac_rfl)
  | some v =>
    simp only [Option.isSome_some, ↓reduceIte]
    refine SepWP.focus_weaken
      (optVersionNegWordsHeap_some_cap_ne A g_vn v w1 w2 w3 w4 w5) (by sep_focus) ?_
    wp_focus_pure; intro hw0_ne
    refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
      (SepWP.seq (step_copy_pq_state_some_3185c s v_20
        (Prost.EncodeToVec.optVersionNegCap g_vn (some v)) w1 w2 w3 w4 w5
        c1 c2 c3 c4 c5 c6 c7 c8 c9
        i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
        i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
        (optVersionNegWordsHeap A g_vn (some v) w1 w2 w3 w4 w5 ∗
          optChainWordsHeap A g_ch (s.readReg64 .x25) ch c1 c2 c3 c4 c5 c6 c7 c8 c9 ∗
          protoInnerWordsHeap A is
            i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
            i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216 ∗ Frame)
        hpc hrun hx26 hw0_ne hsp_align) ?_)
    intro sf Qf hpcf _
    rintro ⟨hvf, hrunf, htrf, hspf, hx26f, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f, hQf⟩
    refine SepWP.weaken_pre hQf ?_
    rw [h4704, h4752, h4760, h4832]
    have hvn_pack := vnWords6_entails_optVersionNegotiationPBPinnedAt A g_vn (s.sp + 4704#64) (some v) w1 w2 w3 w4 w5
    have hch_pack := chainWords9_entails_optChainPBPinnedAt A g_ch ((s.sp + 4704#64) + 48#64) (s.readReg64 .x25) ch
      c1 c2 c3 c4 c5 c6 c7 c8 c9
    have hin_pack := outWords28_entails_v1StatePBPinnedAt A ((s.sp + 4704#64) + 128#64) st1.into_pb is his
      i0 i8 i16 i24 i32 i40 i48 i56 i64 i72 i80 i88 i96 i104 i112 i120
      i128 i136 i144 i152 i160 i168 i176 i184 i192 i200 i208 i216
    refine SepWP.focus_weaken hvn_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hch_pack (by sep_focus) ?_
    refine SepWP.focus_weaken hin_pack (by sep_focus) ?_
    wp_pull_exists; rename_i g_v1
    refine Prost.EncodeToVec.SepWP.done hpcf hrunf
      ⟨hrunf, htrf, hspf, hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx27f, hx28f,
        ⟨g_vn, g_ch.toProtoRepr, g_v1⟩, hx25f.trans hx25_cap, hx26f, by rw [hx25f]; exact hx25_some, ?_⟩
    unfold Prost.EncodeToVec.pqRatchetStatePBPinnedAt
    dsimp only [pq']
    exact Entails.of_eq (by ac_rfl)

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

/-! ## 5. Bridge 2 Composition (`0x317fc -> 0x320a4`) -/

theorem memRegion_24_words3_1424 (sp : BitVec 64) :
    memRegion (sp + 1424#64) 24 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
        ((sp + 1424#64) ↦₆₄ w0) ∗ ((sp + 1432#64) ↦₆₄ w1) ∗ ((sp + 1440#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split' (b := sp + 1424#64) (n := 8) (k := 16) (b' := sp + 1432#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp + 1432#64) (n := 8) (k := 8) (b' := sp + 1440#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 1424#64), ProofLib.memRegion_eight (sp + 1432#64),
      ProofLib.memRegion_eight (sp + 1440#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w2
  apply Entails.sepExists_elim; intro w1
  apply Entails.sepExists_elim; intro w0
  exact Entails.sepExists_right w0 (Entails.sepExists_right w1 (Entails.sepExists_right w2 (Entails.refl _)))

theorem stackAt_spqrSendCallee_split_b2 (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ stackAt sp n := by
  have hle' : n ≤ 123008 := hle
  have hbd : n + (spqrSendCalleeStack - n) ≤ 2 ^ 64 := by change n + (123008 - n) ≤ 2 ^ 64; omega
  have h := ProofLib.stackAt_split_bottom sp n (spqrSendCalleeStack - n) hbd
  rwa [Nat.add_sub_of_le hle] at h

theorem stackAt_spqrSendCallee_eq_allocHook_b2 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  stackAt_spqrSendCallee_split_b2 sp allocHookStack (by decide)

theorem sepWPp_of_sepWP_inImage_b2 {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop} (img : Obj.Image) (hinv : ImgCallInv img s)
    (h : SepWP prog mid s P (fun sm Pm => VRegsAt s sm ∧ (ImgCallInv img sm → StepInv s sm → SepWPp prog ret sm Pm Q Qp))) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL; obtain ⟨sm, hsteps, ⟨-, -, Pm, hmm, hvregs, hnext⟩ | hoom⟩ := h.elim hm hL
  · obtain ⟨sf, hsteps', hout⟩ := hnext ⟨hsteps.frozenLoaded hinv.1, hsteps.symtab_eq.trans hinv.2⟩
      ⟨fun _ hF => hsteps.frozenLoaded hF, hsteps.symtab_eq, hvregs.eq⟩ R hmm (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_call_inImage_calleeStack_b2 {α : Type} {prog : Program} {img : Obj.Image}
    {entry ret_pc ret : BitVec 64} {spec : Spec α} {x : α} {s0 s : State}
    (sp : BitVec 64) (n : Nat) (hle : n ≤ spqrSendCalleeStack := by decide)
    {P T_pre : SepProp} {T_post : State → SepProp} {Q : State → SepProp → Prop} {Fr F : SepProp}
    {φ_pre : Prop} {φ_post : State → Prop}
    (hcall : subroutine_ok prog entry (spec.inImage img)) (hinv : ImgCallInv img s)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hsp_align : (sp &&& 15#64 == 0#64) = true) (htr : s.trace = s0.trace)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec_pre : spec.pre x s = (⌜φ_pre⌝ ∗ T_pre ∗ stackAt s.sp n)) (hφ : φ_pre)
    (hP : P = (stackAt sp spqrSendCalleeStack ∗ T_pre) ∗ F)
    (hexit_eq : ∀ code sf, spec.onExit x code s sf = ⌜False⌝)
    (hpan_eq : ∀ sf, spec.onPanic x s sf = (⌜allocFailedIn s sf ∧ s.trace <+: sf.trace⌝ ∗ anyHeap))
    (hspec_post : ∀ sf, spec.post x s sf = (⌜φ_post sf⌝ ∗ T_post sf ∗ stackAt s.sp n))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running → sf.sp = sp →
      φ_post sf → ImgCallInv img sf → StepInv s sf →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = s.readReg64 .x20 →
      sf.readReg64 .x21 = s.readReg64 .x21 → sf.readReg64 .x22 = s.readReg64 .x22 →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = s.readReg64 .x24 →
      sf.readReg64 .x25 = s.readReg64 .x25 → sf.readReg64 .x26 = s.readReg64 .x26 →
      sf.readReg64 .x27 = s.readReg64 .x27 → sf.readReg64 .x28 = s.readReg64 .x28 →
      sf.readReg64 .fp = s.readReg64 .fp →
      SepWPp prog ret sf ((stackAt sp spqrSendCalleeStack ∗ T_post sf) ∗ F) Q
        (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)))
    (hoom_eq : ∀ sf, spec.onOom x s sf = ⌜False⌝ := by intros; rfl) :
    SepWPp prog ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) := by
  let F_ext := memRegion (sp - BitVec.ofNat 64 spqrSendCalleeStack) (spqrSendCalleeStack - n) ∗ F
  have hsp_al : s.spAligned = true := by unfold State.spAligned; rw [hsp]; exact hsp_align
  have h_step : SepWPp prog ret_pc s P
      (fun sm Pm => Pm = ((spec.inImage img).post x s sm ∗ F_ext) ∧
        sm.sp = s.sp ∧ CalleeSavedPreserved s sm)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ Fr)) :=
    ProofLib.SepWPp.call_wpp (x := x) (F := F_ext) hcall hpc hrun hsp_al hlr
      (fun R' hm => by
        change s.mem ⊨ (⌜ImgCallInv img s⌝ ∗ spec.pre x s) ∗ (F_ext ∗ R')
        rw [sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hinv, ?_⟩
        rw [hspec_pre, hsp, sepConj_assoc, sepConj_assoc, satisfies_pure_sepConj]; refine ⟨hφ, ?_⟩
        rw [hP, stackAt_spqrSendCallee_split_b2 sp n hle] at hm
        exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hm)
      (fun sm code R' _ hpost => by
        change sm.mem ⊨ spec.onExit x code s sm ∗ R' at hpost; rw [hexit_eq code sm] at hpost
        exact ProofLib.allowPanic_not_exited hpost)
      (fun sm _ _ hmFr => by
        change sm.mem ⊨ (spec.onPanic x s sm ∗ F_ext) ∗ Fr at hmFr; rw [hpan_eq sm] at hmFr
        refine allowPanic_frame ?_ hmFr
        rintro ⟨haf, hpr⟩; unfold allocFailedIn at haf ⊢; rw [htr] at haf hpr; exact ⟨haf, hpr⟩)
      (fun sm hpcm hrunm hspm hcsm => ProofLib.SepWPp.done hpcm hrunm ⟨rfl, hspm, hcsm⟩)
      (fun sm R' _ hpost => by
        change sm.mem ⊨ spec.onOom x s sm ∗ (F_ext ∗ R') at hpost; rw [hoom_eq sm] at hpost
        exact (ProofLib.allowPanic_not_exited hpost).elim)
  intro R' hm hL
  rcases h_step R' hm hL with ⟨sm, hsteps, ⟨hpcm, hrunm, _, hpost, rfl, hspm, hcsm⟩ | hpan | hoom⟩
  · change sm.mem ⊨ (spec.post x s sm ∗ F_ext) ∗ R' at hpost
    rw [sepConj_assoc, hspec_post sm, hsp] at hpost
    have hpost' : sm.mem ⊨ ⌜φ_post sm⌝ ∗ (((stackAt sp spqrSendCalleeStack ∗ T_post sm) ∗ F) ∗ R') := by
      rw [stackAt_spqrSendCallee_split_b2 sp n hle]
      exact Satisfies.mono (Entails.of_eq (by dsimp only [F_ext]; ac_rfl)) hpost
    rw [satisfies_pure_sepConj] at hpost'; rcases hpost' with ⟨hφ_post, hpost_mem⟩
    rw [hsp] at hspm
    rcases hcsm with ⟨hx19, hx20, hx21, hx22, hx23, hx24, hx25, hx26, hx27, hx28, hfp, hvregs⟩
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hpcm hrunm hspm hφ_post ⟨hsteps.frozenLoaded hinv.1, hsteps.symtab_eq.trans hinv.2⟩
        ⟨fun _ hF => hsteps.frozenLoaded hF, hsteps.symtab_eq, hvregs⟩
        hx19 hx20 hx21 hx22 hx23 hx24 hx25 hx26 hx27 hx28 hfp R' hpost_mem (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inl hpan)⟩
  · exact ⟨sm, hsteps, Or.inr (Or.inr hoom)⟩

theorem sepWPp_intro_rodata_bridge2 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {prog : Program} {ret : BitVec 64} {s : State} (hF : img.FrozenLoaded s)
    {P : SepProp} {Q Qp : State → SepProp → Prop}
    (h : SepWPp prog ret s
      (((img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
       ((img.base + bv% (ls_xref% 0x30a94 0x30a98 + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
       statesIntoPbJumpTableAt img.base ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  have hm3 := rodata_v1StateJumpTable_intro himg hF
    (rodata_spqrSendEncodeJumpTable_intro himg hF (rodata_statesIntoPbJumpTable_intro himg hF hm))
  exact h R (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm3) hL

theorem pqRatchetStatePBEncodedLen_some_v1_pos
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB) (v1s : V1State) :
    0 < Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 v1s) } := by
  unfold Prost.EncodeToVec.pqRatchetStatePBEncodedLen
  dsimp only
  have hp := Prost.EncodeToVec.optPqRatchetInnerPBFieldEncodedLen_pos (.v1 v1s)
  omega

/-- `0x31810 -> 0x5ce20`: checks `msg.serialize idx = 1#8 :: tail`, relocates `chunkedStatesAt`
    via `memcpy`, and sets up `<States>::into_pb` (`0x5ce20`, return `0x3185c`). -/
theorem step_post_message_serialize_to_into_pb_31810 {A : RustAlloc} {F : ShaCompress}
    {b : BitVec 64} {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext) (s : State) (tail : List (BitVec 8))
    (st1 : States spqrPolyApi (spqrAuthApi F)) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4020#64)
    (hrun : s.status = .Running) (hx26 : s.readReg64 .x26 = s.sp + 0x1260#64)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 159976#64) s
      (vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗ memRegion (s.sp + 0x1260#64) 928 ∗
        chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ Frame)
      (fun sf Q => VRegsAt s sf ∧
        sf.status = .Running ∧ sf.trace = s.trace ∧ sf.sp = s.sp ∧
        sf.readReg64 .x0 = s.sp + 0x1260#64 ∧ sf.readReg64 .x8 = s.sp + 0x590#64 ∧
        sf.readReg64 .x30 = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4096#64 ∧
        sf.readReg64 .x24 = s.sp + 0x1260#64 ∧
        sf.readReg64 .x19 = s.readReg64 .x19 ∧ sf.readReg64 .x20 = s.readReg64 .x20 ∧
        sf.readReg64 .x21 = s.readReg64 .x21 ∧ sf.readReg64 .x22 = s.readReg64 .x22 ∧
        sf.readReg64 .x23 = s.readReg64 .x23 ∧ sf.readReg64 .x25 = s.readReg64 .x25 ∧
        sf.readReg64 .x26 = s.readReg64 .x26 ∧ sf.readReg64 .x27 = s.readReg64 .x27 ∧
        sf.readReg64 .x28 = s.readReg64 .x28 ∧
        (Q ⊢ chunkedStatesAt A (s.sp + 0x1260#64) st1 ∗ memRegion (s.sp + 0x190#64) 928 ∗
          vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗ Frame)) := by
  have hmcpy := spqrSend_etvMemcpy_ok hA rfl
  refine SepWP.weaken_pre (Entails.of_eq (by ac_rfl))
    (SepWP.seq (step_post_message_serialize_to_memcpy_31810 s tail
      (chunkedStatesAt A (s.sp + 0x190#64) st1 ∗ Frame) hpc hrun hx26 hsp_align) ?_)
  intro s1 Q1 hpc1 _ ⟨hv1, hrun1, htr1, hsp1, hx0_1, hx1_1, hx2_1, hlr1, hx24_1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx25_1, hx26_1, hx27_1, hx28_1, hQ1⟩
  refine SepWP.weaken_pre hQ1 ?_
  refine call_memcpy_relocate_bridge2 hmcpy (s.sp + 0x1260#64) (s.sp + 0x190#64)
    (Relocatable.of_chunkedStatesAt A st1) hpc1 hrun1 hsp1 hsp_align hlr1 htr1 hx0_1 hx1_1
    (by rw [hx2_1]; rfl) (Frame := vecU8 A (s.sp + 0xff0#64) (1#8 :: tail) ∗ Frame) (by ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hv2 hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rwa [hsp2]
  refine SepWP.mono (step_post_memcpy_to_into_pb_3184c s2 _ hpc2 hrun2 hsp2_align) ?_
  intro sf Qf _ _ ⟨hvf, hrunf, htrf, hspf, hx0f, hx8f, hlrf,
    hx19f, hx20f, hx21f, hx22f, hx23f, hx24f, hx25f, hx26f, hx27f, hx28f, hQf⟩
  rw [hsp2] at hspf hx0f hx8f; rw [hQf]
  exact ⟨⟨hvf.eq.trans (hv2.eq.trans hv1.eq)⟩, hrunf, htrf.trans htr2, hspf, hx0f, hx8f, hlrf,
    hx24f.trans (hx24_2.trans hx24_1), hx19f.trans (hx19_2.trans hx19_1),
    hx20f.trans (hx20_2.trans hx20_1), hx21f.trans (hx21_2.trans hx21_1),
    hx22f.trans (hx22_2.trans hx22_1), hx23f.trans (hx23_2.trans hx23_1),
    hx25f.trans (hx25_2.trans hx25_1), hx26f.trans (hx26_2.trans hx26_1),
    hx27f.trans (hx27_2.trans hx27_1), hx28f.trans (hx28_2.trans hx28_1), Entails.of_eq (by ac_rfl)⟩

/-- Full Phase 3d–3e bridge (`0x317fc -> 0x320a4`, `entry + 4000#64 -> entry + 6216#64`). -/
theorem step_send_bridge2_317fc
    {img : Obj.Image} {A : RustAlloc} {F : ShaCompress} {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext) (himg : Obj.Loads libsignalSessionImage img)
    (hmser : MessageSerializeOkX spqrPolyApi img A ext) (hinto : StatesIntoPbOkX img A F ext)
    {entry : BitVec 64} (hfn : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry)
    {s0 s : State} (hinv_img : img.FrozenLoaded s0 ∧ s0.symtab = img.symtab)
    (sp v_20_old v0 v_sp10 v_sp18 : BitVec 64) (idx : BitVec 32)
    (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (st1 : States spqrPolyApi (spqrAuthApi F)) (msg : Message spqrPolyApi)
    (hlen : Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } < 2 ^ 63)
    (halign : sp &&& 15#64 = 0#64) {Fr : SepProp} {ret : BitVec 64} {P Frame : SepProp} {Q : State → SepProp → Prop}
    (hpc : s.pc = entry + 4000#64) (hrun : s.status = .Running) (hsp : s.sp = sp) (htr : s.trace = s0.trace)
    (hx24 : s.readReg32 .x24 = idx) (hx26 : s.readReg64 .x26 = sp + 0x1260#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64) (hinv0 : StepInv s0 s)
    (hP : P = (messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗
      chunkedStatesAt A (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗ memRegion (sp + 0x590#64) 224 ∗
      ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
      A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sm : State) (g : PqRatchetStatePBGhost) (w0 : BitVec 64),
      let pq' : PqRatchetState := { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
      sm.pc = entry + 6216#64 → sm.status = .Running → sm.sp = sp → sm.trace = s0.trace →
      sm.readReg64 .x19 = s.readReg64 .x19 → sm.readReg64 .x21 = s.readReg64 .x21 →
      sm.readReg64 .x23 = s.readReg64 .x23 →
      sm.readReg64 .x25 = Prost.EncodeToVec.optChainCap g.chain pq'.chain →
      (sm.readReg64 .x25 + 1#64 == 0#64) = !pq'.chain.isSome →
      sm.readReg64 .x27 = s.readReg64 .x27 → sm.readReg64 .x28 = sp + 4192#64 →
      StepInv s0 sm → ImgCallInv img sm →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sm
        ((Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (sp + 4704#64) pq' ∗
          vecU8 A (sp + 1424#64) (PqRatchetState.encodeRaw pq') ∗
          vecU8 A (sp + 4080#64) (msg.serialize idx) ∗
          ((sp + 32#64) ↦₆₄ s.readReg64 .x20) ∗
          (sp ↦₆₄ w0) ∗ ((sp + 16#64) ↦₆₄ Prost.EncodeToVec.optChainCap g.chain pq'.chain) ∗
          ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
          memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
          memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
          ((img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
          ((img.base + bv% (ls_xref% 0x30a94 0x30a98 + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
          statesIntoPbJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
        Q (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P Q
      (fun sf P_f => (sf.mem ⊨ P_f ∗ Fr) → (sf.mem ⊨ encodeToVecOnPanic s0 sf ∗ Fr)) := by
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  let roV1 : SepProp := (img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ ProtoRepr.v1StateJumpTableBytes
  let roSend : SepProp :=
    (img.base + bv% (ls_xref% 0x30a94 0x30a98 + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes
  have hsp_align : (sp &&& 15#64 == 0#64) = true := beq_iff_eq.mpr halign
  have hinv : ImgCallInv img s := ⟨hinv0.1 img hinv_img.1, hinv0.2.1.trans hinv_img.2⟩
  have hmser' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 170572#64)
      ((messageSerializeSpecX spqrPolyApi A).inImage img) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 170572) (b := img.base) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_lemma% fnOff "<spqr::v1::chunked::states::Message>::serialize") (by decide)) hmser
  have hinto' : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 159976#64)
      ((statesIntoPbSpecX A F img.base).inImage img) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := 159976) (b := img.base) (X := Rust.withPanics ext)
      spqrSend_fnOff States.IntoPb.statesIntoPb_fnOff (by decide)) hinto
  subst hP
  refine sepWPp_intro_rodata_bridge2 himg hinv.1 ?_
  refine sepWPp_of_sepWP_inImage_b2 img hinv
    (SepWP.mono (step_pre_message_serialize_317fc s _
      (by rw [hfn]; exact hpc) hrun (by rw [hsp]; exact hsp_align)) ?_)
  intro s1 Q1 hpc1 _ ⟨hv1, hrun1, htr1, hsp1, hx0_1, hx1_1, hx8_1, hlr1,
    hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hQ1⟩
  refine ⟨hv1, fun hinv1 hstep1 => ?_⟩
  rw [hQ1]; rw [hsp] at hsp1 hx0_1 hx8_1; rw [hfn] at hlr1
  have htr1' : s1.trace = s0.trace := htr1.trans htr
  have hinv0_1 : StepInv s0 s1 := hinv0.trans hstep1
  refine sepWPp_call_inImage_calleeStack_b2 sp messageSerializeStackX (by decide) hmser' hinv1
    hpc1 hrun1 hsp1 hsp_align htr1' hlr1
    (x := ({ msgA := sp + 0x1d70#64, index := idx, ret := sp + 0xff0#64, msg := msg } : MessageSerializeGhost spqrPolyApi))
    (φ_pre := s1.readReg64 .x0 = sp + 0x1d70#64 ∧
      (s1.readReg64 .x1).setWidth 32 = idx ∧ s1.readReg64 .x8 = sp + 0xff0#64)
    (φ_post := fun sf => sf.trace = s1.trace)
    (T_pre := messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗ memRegion (sp + 0xff0#64) 24 ∗ A.pool)
    (T_post := fun _ => messageAt spqrPolyApi (sp + 0x1d70#64) msg ∗
      vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗ A.pool)
    (F := (roV1 ∗ roSend ∗ statesIntoPbJumpTableAt img.base ∗
      chunkedStatesAt A (sp + 0x190#64) st1 ∗ memRegion (sp + 0x1260#64) 928 ∗ memRegion (sp + 0x590#64) 224 ∗
      ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18)) ∗ Frame)
    (by dsimp only [messageSerializeSpecX]; ac_rfl)
    ⟨hx0_1, by change s1.readReg32 .x1 = idx; rw [hx1_1, hx24], hx8_1⟩
    (by dsimp only [roV1, roSend]; ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [messageSerializeSpecX]; ac_rfl) ?_
  intro s2 hpc2 hrun2 hsp2 htr2 hinv2 hstep2
    hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 _
  have htr2' : s2.trace = s0.trace := htr2.trans htr1'
  have hinv0_2 : StepInv s0 s2 := hinv0_1.trans hstep2
  obtain ⟨tail, hser⟩ := message_serialize_eq_cons msg idx
  refine SepWPp.weaken_pre
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (messageAt_entails_memRegion_48 (sp + 0x1d70#64) msg)))) ?_
  rw [hser]
  refine sepWPp_of_sepWP_inImage_b2 img hinv2
    (SepWP.weaken_pre (Entails.of_eq (by rw [← hsp2]; ac_rfl))
      (SepWP.mono (step_post_message_serialize_to_into_pb_31810 hA s2 tail st1
        (roV1 ∗ roSend ∗ statesIntoPbJumpTableAt img.base ∗
          memRegion (sp + 0x1d70#64) 48 ∗ memRegion (sp + 0x590#64) 224 ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
          CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
          optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
          (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
        (by rw [hfn]; exact hpc2) hrun2 (by rw [hx26_2, hx26_1, hx26, hsp2])
        (by rw [hsp2]; exact hsp_align)) ?_))
  intro s3 Q3 hpc3 _ ⟨hv3, hrun3, htr3, hsp3, hx0_3, hx8_3, hlr3, hx24_3,
    hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx25_3, hx26_3, hx27_3, hx28_3, hQ3⟩
  refine ⟨hv3, fun hinv3 hstep3 => ?_⟩
  refine SepWPp.weaken_pre hQ3 ?_
  rw [hsp2] at hsp3 hx0_3 hx8_3 hx24_3 ⊢; rw [hfn] at hlr3; rw [← hser]
  have htr3' : s3.trace = s0.trace := htr3.trans htr2'
  have hinv0_3 : StepInv s0 s3 := hinv0_2.trans hstep3
  refine sepWPp_call_inImage_calleeStack_b2 sp statesIntoPbStackX (by decide) hinto' hinv3
    hpc3 hrun3 hsp3 hsp_align htr3' hlr3
    (x := ({ out := sp + 0x590#64, stA := sp + 0x1260#64, st := st1 } : StatesIntoPbGhost F))
    (φ_pre := s3.readReg64 .x8 = sp + 0x590#64 ∧
      s3.readReg64 .x0 = sp + 0x1260#64 ∧ img.base &&& 0xfff#64 = 0#64)
    (φ_post := fun sf => sf.trace = s3.trace)
    (T_pre := memRegion (sp + 0x590#64) optProtoInnerStateSize ∗
      chunkedStatesAt A (sp + 0x1260#64) st1 ∗ statesIntoPbJumpTableAt img.base ∗ A.pool)
    (T_post := fun _ => Drop.optProtoInnerStateAt A (sp + 0x590#64) st1.into_pb.innerState ∗
      memRegion (sp + 0x1260#64) chunkedStatesSize ∗ statesIntoPbJumpTableAt img.base ∗ A.pool)
    (F := (roV1 ∗ roSend ∗
      memRegion (sp + 0x190#64) 928 ∗ vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗
      memRegion (sp + 0x1d70#64) 48 ∗ ((sp + 0x20#64) ↦₆₄ v_20_old) ∗
      CryptoVerification.SpqrV1.ProtoRepr.optVersionNegotiationPBAt A (sp + 0x30#64) vn ∗
      optChainPBRegSlotAt A (sp + 0xd90#64) (s.readReg64 .x25) ch ∗
      (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18)) ∗ Frame)
    (by dsimp only [statesIntoPbSpecX, optProtoInnerStateSize]; ac_rfl)
    ⟨hx8_3, hx0_3, hb⟩ (by dsimp only [optProtoInnerStateSize]; ac_rfl)
    (fun _ _ => rfl) (fun _ => rfl)
    (fun _ => by dsimp only [statesIntoPbSpecX, chunkedStatesSize]; ac_rfl) ?_
  intro s4 hpc4 hrun4 hsp4 htr4 hinv4 hstep4
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx26_4 hx27_4 hx28_4 _
  have htr4' : s4.trace = s0.trace := htr4.trans htr3'
  have hinv0_4 : StepInv s0 s4 := hinv0_3.trans hstep4
  have hx25_s4 : s4.readReg64 .x25 = s.readReg64 .x25 :=
    hx25_4.trans (hx25_3.trans (hx25_2.trans hx25_1))
  have hx26_s4 : s4.readReg64 .x26 = s4.sp + 0x1260#64 := by
    rw [hsp4, hx26_4, hx26_3, hx26_2, hx26_1, hx26]
  refine SepWPp.weaken_pre
    (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (by dsimp only [chunkedStatesSize]; exact Entails.of_eq (memRegion_928_split_352_576 sp)))))) ?_
  refine sepWPp_of_sepWP_inImage_b2 img hinv4
    (SepWP.weaken_pre (Entails.of_eq (by rw [← hsp4, ← hx25_s4]; ac_rfl))
      (SepWP.mono (step_copy_and_assemble_pq_state_3185c s4 v_20_old vn ch st1
        (roV1 ∗ roSend ∗ statesIntoPbJumpTableAt img.base ∗
          memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x190#64) 928 ∗
          vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗ memRegion (sp + 0x1d70#64) 48 ∗
          (sp ↦₆₄ v0) ∗ ((sp + 16#64) ↦₆₄ v_sp10) ∗ ((sp + 24#64) ↦₆₄ v_sp18) ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack ∗ Frame)
        (by rw [hfn]; exact hpc4) hrun4 hx26_s4 (by rw [hsp4]; exact hsp_align)) ?_))
  intro s5 Q5 hpc5 _ ⟨hv5, hrun5, htr5, hsp5,
    hx19_5, hx20_5, hx21_5, hx22_5, hx23_5, hx24_5, hx25_5, hx27_5, hx28_5,
    g, hx25_cap, hx26_cap, hx25_some, hQ5⟩
  refine ⟨hv5, fun hinv5 hstep5 => ?_⟩
  refine SepWPp.weaken_pre hQ5 ?_; rw [hsp4] at hsp5 ⊢; rw [hfn] at hpc5
  have htr5' : s5.trace = s0.trace := htr5.trans htr4'
  have hinv0_5 : StepInv s0 s5 := hinv0_4.trans hstep5
  have hx19_s5 : s5.readReg64 .x19 = s.readReg64 .x19 :=
    hx19_5.trans (hx19_4.trans (hx19_3.trans (hx19_2.trans hx19_1)))
  have hx20_s4 : s4.readReg64 .x20 = s.readReg64 .x20 :=
    hx20_4.trans (hx20_3.trans (hx20_2.trans hx20_1))
  have hx21_s5 : s5.readReg64 .x21 = s.readReg64 .x21 :=
    hx21_5.trans (hx21_4.trans (hx21_3.trans (hx21_2.trans hx21_1)))
  have hx22_s5 : s5.readReg64 .x22 = s.readReg64 .x22 :=
    hx22_5.trans (hx22_4.trans (hx22_3.trans (hx22_2.trans hx22_1)))
  have hx23_s5 : s5.readReg64 .x23 = s.readReg64 .x23 :=
    hx23_5.trans (hx23_4.trans (hx23_3.trans (hx23_2.trans hx23_1)))
  have hx24_s5 : s5.readReg64 .x24 = sp + 4704#64 := hx24_5.trans (hx24_4.trans hx24_3)
  have hx27_s5 : s5.readReg64 .x27 = s.readReg64 .x27 :=
    hx27_5.trans (hx27_4.trans (hx27_3.trans (hx27_2.trans hx27_1)))
  have hx28_s5 : s5.readReg64 .x28 = sp + 4192#64 :=
    hx28_5.trans (hx28_4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))))
  rw [hx20_s4]
  have h590_split : memRegion (sp + 0x590#64) 224 ⊢
      (∃∗ v_590 : BitVec 64, ∃∗ v_598 : BitVec 64, ∃∗ v_5a0 : BitVec 64,
        ((sp + 1424#64) ↦₆₄ v_590) ∗ ((sp + 1432#64) ↦₆₄ v_598) ∗ ((sp + 1440#64) ↦₆₄ v_5a0)) ∗
      memRegion (sp + 1448#64) 200 := by
    rw [memRegion_224_split_24_200 sp]
    exact sepConj_mono_left (memRegion_24_words3_1424 sp)
  refine SepWPp.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h590_split))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun v_590 => SepWPp.exists_elim fun v_598 => SepWPp.exists_elim fun v_5a0 => ?_
  refine step_send_encode_from_vn_len_x hA himg hfn hinv_img sp (s.readReg64 .x22)
    v0 v_sp10 v_sp18 v_590 v_598 v_5a0 g
    { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }
    (pqRatchetStatePBEncodedLen_some_v1_pos vn ch st1.into_pb) hlen halign
    hpc5 hrun5 hsp5 htr5' hx22_s5 hx24_s5 hx25_cap hx26_cap hx28_s5 hinv0_5
    (F := ((sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗ memRegion (sp + 0x30#64) 48 ∗
      memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 1448#64) 200 ∗
      statesIntoPbJumpTableAt img.base ∗ memRegion (sp + 5056#64) 576 ∗
      memRegion (sp + 0x190#64) 928 ∗ vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗
      memRegion (sp + 0x1d70#64) 48 ∗ Frame)
    (by dsimp only [roV1, roSend]; ac_rfl) ?_
  intro sm ptr w0 hpcm hrunm hspm htrm hx19m hx21m hx23m hx25m hx27m hx28m hfpm hinv0_m
  have hinv_m : ImgCallInv img sm := ⟨hinv0_m.1 img hinv_img.1, hinv0_m.2.1.trans hinv_img.2⟩
  have hx25_some_m : (sm.readReg64 .x25 + 1#64 == 0#64) =
      !({ versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } : PqRatchetState).chain.isSome := by
    rw [hx25m, ← hx25_cap]; exact hx25_some
  refine SepWPp.weaken_pre ?_
    (hnext sm g w0 hpcm hrunm hspm htrm
      (hx19m.trans hx19_s5) (hx21m.trans hx21_s5) (hx23m.trans hx23_s5)
      hx25m hx25_some_m (hx27m.trans hx27_s5) hx28m hinv0_m hinv_m)
  have hvec := vecU8At_entails_vecU8 A (sp + 1424#64)
    (BitVec.ofNat 64 (Prost.EncodeToVec.pqRatchetStatePBEncodedLen
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }))
    ptr (PqRatchetState.encodeRaw { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) })
  refine Entails.trans (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvec))))) ?_
  change _ ⊢ ((Prost.EncodeToVec.pqRatchetStatePBPinnedAt A g (sp + 4704#64)
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) } ∗
    vecU8 A (sp + 1424#64) (PqRatchetState.encodeRaw
      { versionNegotiation := vn, chain := ch, inner := some (.v1 st1.into_pb) }) ∗
    vecU8 A (sp + 0xff0#64) (msg.serialize idx) ∗
    ((sp + 0x20#64) ↦₆₄ s.readReg64 .x20) ∗ (sp ↦₆₄ w0) ∗
    ((sp + 16#64) ↦₆₄ Prost.EncodeToVec.optChainCap g.chain ch) ∗ ((sp + 24#64) ↦₆₄ s.readReg64 .x22) ∗
    memRegion (sp + 0x30#64) 48 ∗ memRegion (sp + 0x190#64) 928 ∗ memRegion (sp + 1448#64) 200 ∗
    memRegion (sp + 0xd90#64) 72 ∗ memRegion (sp + 5056#64) 576 ∗ memRegion (sp + 0x1d70#64) 48 ∗
    ((img.base + bv% (ls_xref% 0x39148 0x3914c)) ↦ᵣ ProtoRepr.v1StateJumpTableBytes) ∗
    ((img.base + bv% (ls_xref% 0x30a94 0x30a98 + 22)) ↦ᵣ spqrSendEncodeJumpTableBytes) ∗
    statesIntoPbJumpTableAt img.base ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
  exact Entails.of_eq (by dsimp only [roV1, roSend]; ac_rfl)

end CryptoVerification.SpqrV1.Top.Send
