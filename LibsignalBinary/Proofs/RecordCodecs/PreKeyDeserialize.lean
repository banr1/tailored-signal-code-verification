/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeLoop
import LibsignalBinary.Proofs.RecordCodecs.PreKeyDeserialize.MergeFields
import LibsignalBinary.Proofs.TripleRatchet.Wire.TryFromLoopBody

/-!
# Verification of `PreKeyRecord::deserialize`

Proves `<libsignal_protocol::state::prekey::PreKeyRecord>::deserialize`
(`protocol/src/state/prekey.rs:44–49`, frame `sub sp, sp, #0xe0`) against `preKeyDeserializeSpec`
(any 4 KiB-aligned image base) and `preKeyDeserializePlacedSpec` (`[LibsignalPlacement]`,
Block `65`): decodes `PreKeyRecordStructure` (`id`, `public_key`, `private_key`) and maps any
`DecodeError` to `InvalidProtobufEncoding` after freeing partial `Vec<u8>` buffers.
-/

@[expose] public section

namespace CryptoVerification.RecordCodecsBinary.PreKeyDeserialize

open Arm64 ProofLib CryptoGames.LibsignalSession CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Wire
open CryptoVerification.RecordCodecsBinary.PreKeyDeserialize.Helpers

/-- `PreKeyRecord::deserialize` meets `preKeyDeserializeSpec` at any 4 KiB-aligned image base,
given the 4 prost/dealloc hooks (`PreKeyDeserializeHooks`) and the proved callees (`DecodeDeps`). -/
theorem preKeyDeserialize_ok_of_hooks {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hC : PreKeyDeserializeHooks img A ext) (d : DecodeDeps img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img) := by
  let _ := hb
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [preKeyDeserializeSpec, Spec.inImage] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hF, hsym⟩, ⟨hx0, hx1_nat, hlt, hx8⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗
        stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 := prologue_000_to_224_wp hC d (x := x) hlt hpc hrun hsp hF hsym hx0 hx1 hx8
  have hfull : Wire.SepWPp (tripleRatchetProgAtExt img.base ext)
      (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗
        stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf =>
        sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyDeserializeSpec A img).post x s0 sf))
      (tryFromQp s0) := by
    refine Wire.SepWPp.bind h1 ?_
    intro sm Pm hpcm hrunm ⟨hstm, hentm⟩
    exact Wire.SepWPp.mono_pre hentm
      (epilogue_224_wp (A := A) (x := x) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

/-- `PreKeyRecord::deserialize` meets `preKeyDeserializeSpec` at any 4 KiB-aligned image base,
given the hooks (`Stage2ContractsX`) and the proved callees (`DecodeDeps`). -/
theorem preKeyDeserialize_ok_of_deps {img : Obj.Image} {C : Crypto} {A : RustAlloc}
    {encFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → List (BitVec 8)}
    {decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8))}
    {ext : String → Option (State → State)}
    (hC : Stage2ContractsX img C A encFn decFn ext) (d : DecodeDeps img A ext)
    (hb : (img.base &&& 0xfff#64) = 0#64) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr preKeyDeserializeName)
      (preKeyDeserializeSpec A img) :=
  preKeyDeserialize_ok_of_hooks (PreKeyDeserializeHooks.of_stage2 hC) d hb

/-! ## Relocatable `[LibsignalPlacement]` Merge, Loop, Prologue, and Root Proof (Block `65`) -/

namespace Helpers
section Placed
open ProofLib.ProgramReflection CryptoGames CryptoGames.Ratchet
open CryptoVerification.LibsignalSessionRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.RecordCodecs CryptoVerification.RecordCodecs.Placed

theorem decodeKey_tail_0e0_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr key : BitVec 64}
    {bs rest : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hdv : decodeVarint bs = some (key, rest))
    (hpc : s.pc = (blkPl_65).base + bv% (224)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = key)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (s1 : State),
      decodeKey bs = some ((tag, wt), rest) →
      s1.pc = (blkPl_65).base + bv% (252) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : decodeKey bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkAfterVarintMem A sp' x19 ptr bs rest bs.length m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  have h0 : s.readReg64 (Reg.gpr 0#5) = key := hx0
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h22 : s.readReg64 (Reg.gpr 22#5) = 0x8000000000000002#64 := hregs.x22
  by_cases hkey32 : 2 ^ 32 ≤ key.toNat
  · have hdk : decodeKey bs = none := by unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte]
    have hcbnz := key_lsr32_ne_zero_of_ge key hkey32
    unfold pkAfterVarintMem; rw [pkMemRegion48_split_112_120_128 sp']
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (452)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    refine Wire.SepWPp.mono_pre ?_
      (decodeErrorFrom_1c4_placed_wp d (w0 := w0) (mErr := m) (hnone hdk)
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
         by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
         by simpa [arm64_norm] using hregs.x19_eq,
         ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
          by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
          by simpa [arm64_norm] using hregs.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
        hcrl1 (by simpa [arm64_norm] using htr) (by simp [KindNoHeap, arm64_norm]))
    refine Entails.trans ?_ (pkDecodeKey_err_entails A sp' x19 ptr w0 key bs rest bs.length m)
    apply entails_of_eq; ac_rfl
  · have hkey_lt : key.toNat < 2 ^ 32 := by omega
    have hcbnz := key_lsr32_eq_zero_of_lt key hkey_lt
    cases hwt : WireType.ofNat? (key.toNat % 8) with
    | none =>
      have hdk : decodeKey bs = none := by
        unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt]
      have hge6 : 6 ≤ key.toNat % 8 := (WireType.ofNat?_eq_none_iff (key.toNat % 8) (by omega)).mp hwt
      have hbcs := key_and7_ule6_of_ge key hge6
      unfold pkAfterVarintMem; rw [pkMemRegion48_split_112_120_128 sp']
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
      refine Wire.SepWPp.exists_pre fun w1 => Wire.SepWPp.exists_pre fun w0 => ?_
      refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (456)) ?_
      wp_steps
      refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
      refine Wire.SepWPp.mono_pre ?_
        (decodeErrorFrom_1c8_placed_wp d (kind := 0x8000000000000003#64) (mErr := m) (hnone hdk)
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr) (by simp [KindNoHeap]))
      refine Entails.trans ?_
        (pkDecodeKey_err_entails A sp' x19 ptr 0x8000000000000003#64 (key &&& 7#64) bs rest bs.length m)
      apply entails_of_eq; simp only [arm64_norm]
    | some wt =>
      have hlt6 : key.toNat % 8 < 6 := WireType.lt_six_of_ofNat?_eq_some hwt
      have hbcs := key_and7_ule6_of_lt key hlt6
      by_cases htag0 : key.toNat / 8 < 1
      · have hdk : decodeKey bs = none := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_eq_zero_of_lt1 key hkey_lt htag0
        unfold pkAfterVarintMem; rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
        simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
        refine Wire.SepWPp.exists_pre fun w0 => ?_
        refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (452)) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
        refine Wire.SepWPp.mono_pre ?_
          (decodeErrorFrom_1c4_placed_wp d (w0 := w0) (mErr := m) (hnone hdk)
            (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
            ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
             by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
             by simpa [arm64_norm] using hregs.x19_eq,
             ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
              by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
              by simpa [arm64_norm] using hregs.saved.x28⟩⟩
            (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
            hcrl1 (by simpa [arm64_norm] using htr) (by simp [KindNoHeap, arm64_norm]))
        refine Entails.trans
          (sepConj_mono (sliceCursorAfter_entails_memRegion (sp' + 40#64) ptr bs rest)
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_left (preKeyStructLoopOf_entails_of A (sp' + 56#64) bs.length m)))))) ?_
        apply entails_of_eq; simp only [arm64_norm, sepConj_assoc]
      · have hdk : decodeKey bs = some ((key.toNat / 8, wt), rest) := by
          unfold decodeKey; rw [hdv]; simp only [hkey32, ↓reduceIte, hwt, htag0]
        have hcbz := key_tag32_ne_zero_of_ge1 key hkey_lt htag0
        refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (252)) ?_
        wp_steps
        refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
        exact hcont (key.toNat / 8) wt _ hdk
          (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
          ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
           by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
           by simpa [arm64_norm] using hregs.x19_eq,
           ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
            by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
            by simpa [arm64_norm] using hregs.saved.x28⟩⟩
          (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp)
          hcrl1 (by simpa [arm64_norm] using htr)
          (by simp [arm64_norm]; exact key_and7_eq_wt key hwt)
          (by simp [arm64_norm]; exact key_tag32_zeroExtend64_eq key hkey_lt)

theorem decodeKey_080_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (128)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx23 : s.readReg64 .x23 = sp' + 40#64) (hx21 : s.readReg64 .x21 = sp' + 48#64)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ (tag : ℕ) (wt : WireType) (rest : List (BitVec 8)) (s1 : State),
      decodeKey (b0 :: bs1) = some ((tag, wt), rest) →
      s1.pc = (blkPl_65).base + bv% (252) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      s1.readReg64 .x8 = BitVec.ofNat 64 wt.toNat →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr (b0 :: bs1) rest (b0 :: bs1).length m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr (b0 :: bs1) out) (tryFromQp s0))
    (hnone : decodeKey (b0 :: bs1) = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr (b0 :: bs1) out) (tryFromQp s0) :=
  decodeVarint_080_placed_cps d hpc hrun hregs hx23 hx21 hx2 hsp hcrl htr hlen
    (fun key rest s1 hdv hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx0_1 =>
      decodeKey_tail_0e0_placed_cps d hdv hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx0_1
        (fun tag wt s2 hdk => hcont tag wt rest s2 hdk) hnone)
    (fun hdv_none => hnone (by simp [decodeKey, hdv_none]))

theorem mergeId_114_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (276)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v : BitVec 32) (rest : List (BitVec 8)) (s1 : State),
      mergeUint32 wt bs = some (v, rest) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length { m with id := v })
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : mergeUint32 wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  unfold pkLoopMem preKeyStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_id A g sp' m]; simp only [sepConj_assoc]
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (pointsTo32_entails_memRegion (sp' + 104#64) m.id))))) ?_
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hregs.x20
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' int32MergeStackX (skipFieldStackX 100)
  simp only [hstack]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 8) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro ⟨wt, sp' + 104#64, sp' + 184#64, sp' + 40#64, ptr, bs⟩
    (pk_int32Merge_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (292)) (by simpa [arm64_norm] using htr)
    (T := memRegion (sp' + 104#64) 4 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool ∗ stackAt sp' int32MergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 + 48#64 = sp' + 104#64 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧ bs.length < 9223372036854775808)
    (by cases wt <;> simp [int32MergeSpecX, hsp_eq, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  dsimp only [int32MergeSpecX]
  cases hm : mergeUint32 wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := mergeUint32_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr))
    have hstruct : (((sp' + 104#64) ↦₃₂ v) ∗ memRegion (sp' + 108#64) 4) ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey) ⊢
        preKeyStructLoopOf A (sp' + 56#64) rest.length { m with id := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A g (sp' + 56#64) rest.length { m with id := v }
          (hg.mono hrest_le))
      rw [preKeyStructAt_split_id A g sp' { m with id := v }]; exact Entails.refl _
    unfold pkAfterVarintMem
    simp only [hstack, hsp_eq, arm64_norm]
    simp only [sepConj_assoc] at hstruct
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hm
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64),
      ProofLib.memRegion_four (sp' + 104#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => Wire.SepWPp.exists_pre fun vErr => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (716)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (decodeErrorPush_2cc_placed_wp d (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0)
        (mErr := { m with id := vErr }) hout
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr)
        (by simp [arm64_norm]) hx0_ne (by decide))
    have hstruct : (((sp' + 104#64) ↦₃₂ vErr) ∗ memRegion (sp' + 108#64) 4) ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey) ⊢
        preKeyStructOf A (sp' + 56#64) { m with id := vErr } := by
      refine Entails.trans ?_ (preKeyStructAt_entails_of A g (sp' + 56#64) { m with id := vErr })
      rw [preKeyStructAt_split_id A g sp' { m with id := vErr }]; exact Entails.refl _
    simp only [hstack, hsp_eq, arm64_norm]
    simp only [sepConj_assoc] at hstruct
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; ac_rfl

theorem mergePublicKey_05c_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (92)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length { m with publicKey := v })
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  unfold pkLoopMem preKeyStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_pub A g sp' m]
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 7) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro
    ⟨wt, sp' + 56#64, g.pub.cap, g.pub.ptr, m.publicKey, sp' + 184#64, sp' + 40#64, ptr, bs⟩
    (pk_bytesMerge_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (108)) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 = sp' + 56#64 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk g.pub.cap bs.length)
    (by cases wt <;> simp [bytesMergeRawSpecX, hsp_eq, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, rfl, by bv_omega, hlen, hg.pub⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => Wire.SepWPp.pure_pre fun hcap' => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr))
    have hstruct : vecU8At A (sp' + 56#64) cap' ptr' v ∗
        (vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructLoopOf A (sp' + 56#64) rest.length { m with publicKey := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A { g with pub := ⟨cap', ptr'⟩ } (sp' + 56#64) rest.length
          { m with publicKey := v } ⟨hcap', bytesMergeCapOk_mono hg.priv hrest_le⟩)
      rw [preKeyStructAt_split_pub A { g with pub := ⟨cap', ptr'⟩ } sp' { m with publicKey := v }]
      exact Entails.refl _
    unfold pkAfterVarintMem; simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hm
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (716)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (decodeErrorPush_2cc_placed_wp d (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := m) hout
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr)
        (by simp [arm64_norm]) hx0_ne (by decide))
    have hstruct : vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
        (vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructOf A (sp' + 56#64) m := by
      rw [← preKeyStructAt_split_pub A g sp' m]; exact preKeyStructAt_entails_of A g (sp' + 56#64) m
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; ac_rfl

theorem mergePrivateKey_12c_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (300)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (v rest : List (BitVec 8)) (s1 : State),
      mergeBytes wt bs = some (v, rest) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length { m with privateKey := v })
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : mergeBytes wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  unfold pkLoopMem preKeyStructLoopOf
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_pure_left_comm, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun g => Wire.SepWPp.pure_pre fun hg => ?_
  rw [preKeyStructAt_split_priv A g sp' m]
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h20 : s.readReg64 (Reg.gpr 20#5) = sp' + 56#64 := hregs.x20
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have hstack := stackAt_sub_split sp' bytesMergeStackX (skipFieldStackX 100)
  simp only [hstack, sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 7) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro
    ⟨wt, sp' + 80#64, g.priv.cap, g.priv.ptr, m.privateKey, sp' + 184#64, sp' + 40#64, ptr, bs⟩
    (pk_bytesMerge_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (316)) (by simpa [arm64_norm] using htr)
    (T := vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
      ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
      sliceCursorAt (sp' + 40#64) ptr bs ∗ A.pool ∗ stackAt sp' bytesMergeStackX)
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      sp' + 56#64 + 24#64 = sp' + 80#64 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧ bs.length < 9223372036854775808 ∧
      BytesMergeCapOk g.priv.cap bs.length)
    (by cases wt <;> simp [bytesMergeRawSpecX, hsp_eq, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, by bv_omega, by bv_omega, hlen, hg.priv⟩ (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  dsimp only [bytesMergeRawSpecX]
  cases hm : mergeBytes wt bs with
  | some p =>
    rcases p with ⟨v, rest⟩
    dsimp only
    obtain ⟨k, hkl, hrest, _⟩ := mergeBytes_suffix hm
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.exists_pre fun cap' => Wire.SepWPp.exists_pre fun ptr' => Wire.SepWPp.pure_pre fun hcap' => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (hcont v rest _ hm (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr))
    have hstruct : vecU8At A (sp' + 80#64) cap' ptr' v ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructLoopOf A (sp' + 56#64) rest.length { m with privateKey := v } := by
      refine Entails.trans ?_
        (preKeyStructAt_entails_loopOf A { g with priv := ⟨cap', ptr'⟩ } (sp' + 56#64) rest.length
          { m with privateKey := v } ⟨bytesMergeCapOk_mono hg.pub hrest_le, hcap'⟩)
      rw [preKeyStructAt_split_priv A { g with priv := ⟨cap', ptr'⟩ } sp' { m with privateKey := v }]
      exact Entails.refl _
    unfold pkAfterVarintMem; simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hm
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    have h29_2 : s2.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs2.x29
    rw [pkMemRegion48_split8 sp', ProofLib.memRegion_eight (sp' + 112#64)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
    refine Wire.SepWPp.exists_pre fun w0 => ?_
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (716)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (decodeErrorPush_2cc_placed_wp d (err := s2.readReg64 (Reg.gpr 0#5)) (n := 0) (mErr := m) hout
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr)
        (by simp [arm64_norm]) hx0_ne (by decide))
    have hstruct : vecU8At A (sp' + 80#64) g.priv.cap g.priv.ptr m.privateKey ∗
        (vecU8At A (sp' + 56#64) g.pub.cap g.pub.ptr m.publicKey ∗
          ((sp' + 104#64) ↦₃₂ m.id) ∗ memRegion (sp' + 108#64) 4) ⊢
        preKeyStructOf A (sp' + 56#64) m := by
      rw [← preKeyStructAt_split_priv A g sp' m]; exact preKeyStructAt_entails_of A g (sp' + 56#64) m
    simp only [hstack, hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstruct)))))))
    apply entails_of_eq; ac_rfl

theorem mergeSkipField_144_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (324)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s)
    (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (rest : List (BitVec 8)) (s1 : State),
      skipField (2 * bs.length + 2) 100 tag wt bs = some rest →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : skipField (2 * bs.length + 2) 100 tag wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  unfold pkLoopMem
  have hsp_eq : s.sp = sp' := hregs.sp
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  have h8 : s.readReg64 (Reg.gpr 8#5) = BitVec.ofNat 64 wt.toNat := hx8
  have h1 : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 tag := hx1
  refine sepWPp_of_sepWP_lscro hcrl (mid := lsmpl.base 1) ?_
  wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine sepWPp_call_lscro ⟨wt, tag, 100, sp' + 184#64, sp' + 40#64, ptr, bs⟩
    (pk_skipField_placed_ok d)
    (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
    (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1
    (by simp [arm64_norm] : _ = (blkPl_65).base + bv% (340)) (by simpa [arm64_norm] using htr)
    (T := ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ sliceCursorAt (sp' + 40#64) ptr bs ∗
      A.pool ∗ stackAt sp' (skipFieldStackX 100))
    (φ := (BitVec.ofNat 64 wt.toNat).setWidth 8 = BitVec.ofNat 8 wt.toNat ∧
      (BitVec.ofNat 64 tag).setWidth 32 = BitVec.ofNat 32 tag ∧ tag < 4294967296 ∧
      sp' + 160#64 + 24#64 = sp' + 184#64 ∧
      (100#64 : BitVec 64).setWidth 32 = 100#32 ∧ 100 < 4294967296 ∧ bs.length < 9223372036854775808)
    (by cases wt <;> simp [skipFieldSpecX, hsp_eq, h1, WireType.toNat, arm64_norm])
    ⟨setWidth8_ofNat64 wt.toNat, setWidth32_ofNat64 tag, htag_lt, by bv_omega, rfl, by decide, hlen⟩
    (by sep_focus) ?_
  intro s2 hpc2 hrun2 hsp2 hsp2_align hcrl2 hcs2
  have hregs2 : PkLoopRegs s0 sp' x19 s2 :=
    PkLoopRegs.of_calleeSaved
      ⟨by simpa [arm64_norm] using hsp_eq, by simpa [arm64_norm] using h29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq,
       ⟨by simpa [arm64_norm] using hregs.saved.x24, by simpa [arm64_norm] using hregs.saved.x25,
        by simpa [arm64_norm] using hregs.saved.x26, by simpa [arm64_norm] using hregs.saved.x27,
        by simpa [arm64_norm] using hregs.saved.x28⟩⟩ hsp2 hcs2
  have hsp2_eq : s2.sp = sp' := hregs2.sp
  dsimp only [skipFieldSpecX]
  cases hs : skipField (2 * bs.length + 2) 100 tag wt bs with
  | some rest =>
    dsimp only
    obtain ⟨k, hkl, hrest⟩ := skipField_suffix hs
    have hrest_le : rest.length ≤ bs.length := by rw [hrest, List.length_drop]; omega
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_0 => ?_
    have hx0_0' : s2.readReg64 (Reg.gpr 0#5) = 0#64 := hx0_0
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (112)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (hcont rest _ hs (by simp [arm64_norm]) (by simp [hrun2, arm64_norm])
        ⟨by simpa [arm64_norm] using hregs2.sp, by simpa [arm64_norm] using hregs2.x29,
         by simpa [speWord, arm64_norm] using hregs2.x22, by simpa [arm64_norm] using hregs2.x20,
         by simpa [arm64_norm] using hregs2.x19_eq,
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align)
        hcrl3 (by simpa [arm64_norm] using htr2.trans htr))
    unfold pkAfterVarintMem; simp only [hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_left (preKeyStructLoopOf_mono A (sp' + 56#64) m hrest_le)))))
    apply entails_of_eq; ac_rfl
  | none =>
    dsimp only
    have hout := hnone hs
    rw [sepConj_assoc]
    refine Wire.SepWPp.pure_pre fun htr2 => ?_
    simp only [sepConj_assoc, sepConj_pure_left_comm]
    refine Wire.SepWPp.pure_pre fun hx0_ne => ?_
    have hx0_bne : (s2.readReg64 (Reg.gpr 0#5) != 0#64) = true := bne_iff_ne.mpr hx0_ne
    have hx0_beq : (s2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_eq_false_iff_ne.mpr hx0_ne
    refine sepWPp_of_sepWP_lscro hcrl2 (mid := (blkPl_65).base + bv% (464)) ?_
    wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) ?_; intro hcrl3
    refine Wire.SepWPp.mono_pre ?_
      (post_err_1d0_placed_wp d (err := s2.readReg64 (Reg.gpr 0#5)) (mErr := m) hout
        ⟨by simp [hsp2_eq, arm64_norm],
         by simp only [State.spAligned, arm64_norm] at hsp2_align ⊢; exact hsp2_align,
         hcrl3, by simp [htr2, htr, arm64_norm],
         ⟨by simpa [arm64_norm] using hregs2.saved.x24, by simpa [arm64_norm] using hregs2.saved.x25,
          by simpa [arm64_norm] using hregs2.saved.x26, by simpa [arm64_norm] using hregs2.saved.x27,
          by simpa [arm64_norm] using hregs2.saved.x28⟩⟩
        (by simp [arm64_norm]) (by simp [hrun2, arm64_norm]) (by simp [arm64_norm])
        (by simpa [arm64_norm] using hregs2.x19_eq) (by simpa [speWord, arm64_norm] using hregs2.x22))
    simp only [hsp_eq, arm64_norm]
    refine Entails.trans ?_
      (pkErrMem_of_loopOf A sp' x19 ptr (s2.readReg64 (Reg.gpr 0#5)) 0 bs.length m bs)
    apply entails_of_eq; ac_rfl

theorem dispatch_tag_0fc_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 : BitVec 64} {tag : ℕ} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_65).base + bv% (252)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag)
    (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (h1 : tag = 1 → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (276) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp)
    (h2 : tag = 2 → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (92) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp)
    (h3 : tag = 3 → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (300) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp)
    (h4 : 4 ≤ tag → ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (324) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x8 = s.readReg64 .x8 →
      s1.readReg64 .x1 = BitVec.ofNat 64 tag → s1.spAligned = true →
      LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1 P Q Qp) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s P Q Qp := by
  rcases tag with _ | _ | _ | _ | n
  · omega
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 1#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (276)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    exact h1 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq, ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 2#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (92)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    exact h2 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq, ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = 3#64 := hx1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (300)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    exact h3 rfl _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq, ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr
  · have hx1' : s.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (n + 4) := hx1
    obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ := pk_tag_ge4_conds (n + 4) (by omega) htag_lt
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (324)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    exact h4 (by omega) _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq, ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simpa [arm64_norm] using hx1')
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 htr

theorem mergeField_0fc_placed_cps [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {tag : ℕ} {wt : WireType} {bs : List (BitVec 8)}
    {m : PreKeyRecordStructure} {out : Except SignalProtocolError PreKeyRecord}
    (hpc : s.pc = (blkPl_65).base + bv% (252)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx8 : s.readReg64 .x8 = BitVec.ofNat 64 wt.toNat)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 tag) (htag_ge : 1 ≤ tag) (htag_lt : tag < 2 ^ 32)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hlen : bs.length < 2 ^ 63)
    (hcont : ∀ (m' : PreKeyRecordStructure) (rest : List (BitVec 8)) (s1 : State),
      PreKeyRecordStructure.mergeField m tag wt bs = some (m', rest) →
      s1.pc = (blkPl_65).base + bv% (112) → s1.status = .Running → PkLoopRegs s0 sp' x19 s1 →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (pkAfterVarintMem A sp' x19 ptr bs rest rest.length m')
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0))
    (hnone : PreKeyRecordStructure.mergeField m tag wt bs = none → out = .error .invalidProtobufEncoding) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr bs m) (pkEpiloguePostPlaced A s0 sp' x19 ptr bs out) (tryFromQp s0) := by
  refine dispatch_tag_0fc_placed_cps hpc hrun hregs hx1 htag_ge htag_lt hsp hcrl htr
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hsp1 hcrl1 htr1 => ?_)
    (fun htag s1 hpc1 hrun1 hregs1 hx8_1 hx1_1 hsp1 hcrl1 htr1 => ?_)
  · subst htag
    exact mergeId_114_placed_cps d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hsp1 hcrl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with id := v } rest s2 (by simp [PreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [PreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact mergePublicKey_05c_placed_cps d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hsp1 hcrl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with publicKey := v } rest s2 (by simp [PreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [PreKeyRecordStructure.mergeField, hm]))
  · subst htag
    exact mergePrivateKey_12c_placed_cps d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hsp1 hcrl1 htr1 hlen
      (fun v rest s2 hm => hcont { m with privateKey := v } rest s2 (by simp [PreKeyRecordStructure.mergeField, hm]))
      (fun hm => hnone (by simp [PreKeyRecordStructure.mergeField, hm]))
  · rcases Nat.exists_eq_add_of_le' htag with ⟨n, rfl⟩
    exact mergeSkipField_144_placed_cps d hpc1 hrun1 hregs1 (hx8_1.trans hx8) hx1_1 htag_lt hsp1 hcrl1 htr1 hlen
      (fun rest s2 hs => hcont m rest s2 (by simp [PreKeyRecordStructure.mergeField, skipUnknown, recursionLimit, hs]))
      (fun hs => hnone (by simp [PreKeyRecordStructure.mergeField, skipUnknown, recursionLimit, hs]))

theorem loopHeader_070_empty_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64} {m : PreKeyRecordStructure}
    {out : Except SignalProtocolError PreKeyRecord} (hok : out = .ok ⟨m⟩)
    (hpc : s.pc = (blkPl_65).base + bv% (112)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (pkLoopMem A sp' x19 ptr [] m) (pkEpiloguePostPlaced A s0 sp' x19 ptr [] out) (tryFromQp s0) := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  unfold pkLoopMem sliceCursorAt; simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (572)) ?_; wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (post_ok_23c_placed_wp (sp' := sp') (x19 := x19) (ptr := ptr) (m := m) (bs := []) (out := out) hok
      ⟨by simpa [arm64_norm] using hregs.sp, by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp,
       hcrl1, by simp [htr, arm64_norm], ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      (by simpa [arm64_norm] using hregs.x19_eq) (by simpa [arm64_norm] using hregs.x20))
  have h16 := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) ptr (BitVec.ofNat 64 ([] : List (BitVec 8)).length)
  have hof := preKeyStructLoopOf_entails_of A (sp' + 56#64) ([] : List (BitVec 8)).length m
  rw [← sepConj_assoc ((sp' + 40#64) ↦₆₄ ptr) ((sp' + 40#64 + 8#64) ↦₆₄ BitVec.ofNat 64 ([] : List (BitVec 8)).length)]
  refine Entails.trans
    (sepConj_mono h16 (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hof))))) ?_
  apply entails_of_eq; ac_rfl

theorem loopHeader_070_cons_placed_cps [LibsignalPlacement] {H : LibsignalHooks}
    {s0 s : State} {sp' x19 ptr : BitVec 64} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {F : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_65).base + bv% (112)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hsp : s.spAligned = true)
    (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace) (hlen : (b0 :: bs1).length < 2 ^ 63)
    (hcont : ∀ s1 : State, s1.pc = (blkPl_65).base + bv% (128) → s1.status = .Running →
      PkLoopRegs s0 sp' x19 s1 → s1.readReg64 .x23 = sp' + 40#64 → s1.readReg64 .x21 = sp' + 48#64 →
      s1.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length →
      s1.spAligned = true → LibsignalCodeRoLoaded lsmpl s1.mem → s1.trace = s0.trace →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
        (sliceCursorAt (sp' + 40#64) ptr (b0 :: bs1) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ F) Q Qp) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s
      (sliceCursorAt (sp' + 40#64) ptr (b0 :: bs1) ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗ F) Q Qp := by
  have h29 : s.readReg64 (Reg.gpr 29#5) = sp' + 160#64 := hregs.x29
  obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen
  unfold sliceCursorAt; simp only [sepConj_assoc]
  refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (128)) ?_; wp_steps
  refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
  refine Wire.SepWPp.mono_pre ?_
    (hcont _ (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
      ⟨by simpa [arm64_norm] using hregs.sp, by simpa [arm64_norm] using hregs.x29,
       by simpa [speWord, arm64_norm] using hregs.x22, by simpa [arm64_norm] using hregs.x20,
       by simpa [arm64_norm] using hregs.x19_eq, ⟨by simpa [arm64_norm] using hregs.saved.x24,
        by simpa [arm64_norm] using hregs.saved.x25, by simpa [arm64_norm] using hregs.saved.x26,
        by simpa [arm64_norm] using hregs.saved.x27, by simpa [arm64_norm] using hregs.saved.x28⟩⟩
      (by simp [arm64_norm]) (by simp [arm64_norm]) (by simp [arm64_norm])
      (by simp only [State.spAligned, arm64_norm] at hsp ⊢; exact hsp) hcrl1 (by simpa [arm64_norm] using htr))
  unfold sliceCursorAt; apply entails_of_eq; ac_rfl

theorem decodeLoop_080_step_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 s : State} {sp' x19 ptr : BitVec 64}
    {fuel : ℕ} {b0 : BitVec 8} {bs1 : List (BitVec 8)} {m : PreKeyRecordStructure}
    (ih : ∀ {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : PreKeyRecordStructure},
      s.pc = (blkPl_65).base + bv% (112) → s.status = .Running → PkLoopRegs s0 sp' x19 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 63 →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s (pkLoopMem A sp' x19 ptr bs m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs
          (pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField fuel m bs))) (tryFromQp s0))
    (hpc : s.pc = (blkPl_65).base + bv% (128)) (hrun : s.status = .Running)
    (hregs : PkLoopRegs s0 sp' x19 s) (hx23 : s.readReg64 .x23 = sp' + 40#64)
    (hx21 : s.readReg64 .x21 = sp' + 48#64) (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 (b0 :: bs1).length)
    (hsp : s.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s.mem) (htr : s.trace = s0.trace)
    (hfuel : (b0 :: bs1).length ≤ fuel + 1) (hlen : (b0 :: bs1).length < 2 ^ 63) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s (pkLoopMem A sp' x19 ptr (b0 :: bs1) m)
      (pkEpiloguePostPlaced A s0 sp' x19 ptr (b0 :: bs1)
        (pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1)))) (tryFromQp s0) := by
  refine decodeKey_080_placed_cps d hpc hrun hregs hx23 hx21 hx2 hsp hcrl htr hlen
    (fun tag wt rest1 s1 hdk hpc1 hrun1 hregs1 hsp1 hcrl1 htr1 hx8_1 hx1_1 => ?_)
    (fun hdk_none => by simp [decodeFieldsLoop, pkLoopOut, hdk_none])
  obtain ⟨k1, hk1_pos, hk1_le, hrest1_eq, htag_lt, htag_ge⟩ := decodeKey_suffix hdk
  have hrest1_len : rest1.length = (b0 :: bs1).length - k1 := by simp [hrest1_eq]
  unfold pkAfterVarintMem; refine pkAdvanceCursor_placed ⟨k1, hk1_le, hrest1_eq⟩ ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
      (preKeyStructLoopOf_mono A (sp' + 56#64) (m := rest1.length) (n := (b0 :: bs1).length) m (by omega)))))) ?_
  change Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s1
    (pkLoopMem A sp' x19 (ptr + BitVec.ofNat 64 ((b0 :: bs1).length - rest1.length)) rest1 m) _ _
  refine mergeField_0fc_placed_cps d hpc1 hrun1 hregs1 hx8_1 hx1_1 htag_ge htag_lt hsp1 hcrl1 htr1 (by omega)
    (fun m' rest2 s2 hmf hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 => ?_)
    (fun hmf_none => by simp [decodeFieldsLoop, pkLoopOut, hdk, hmf_none])
  obtain ⟨k2, hk2_le, hrest2_eq⟩ := pkMergeField_suffix hmf
  have hrest2_len : rest2.length = rest1.length - k2 := by simp [hrest2_eq]
  unfold pkAfterVarintMem; refine pkAdvanceCursor_placed ⟨k2, hk2_le, hrest2_eq⟩ ?_
  have hloop_eq : decodeFieldsLoop PreKeyRecordStructure.mergeField (fuel + 1) m (b0 :: bs1) =
      decodeFieldsLoop PreKeyRecordStructure.mergeField fuel m' rest2 := by simp [decodeFieldsLoop, hdk, hmf]
  rw [hloop_eq]; exact ih hpc2 hrun2 hregs2 hsp2 hcrl2 htr2 (by omega) (by omega)

theorem decodeLoop_070_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {s0 : State} {sp' x19 : BitVec 64} :
    ∀ (fuel : ℕ) {s : State} {ptr : BitVec 64} {bs : List (BitVec 8)} {m : PreKeyRecordStructure},
      s.pc = (blkPl_65).base + bv% (112) → s.status = .Running → PkLoopRegs s0 sp' x19 s →
      s.spAligned = true → LibsignalCodeRoLoaded lsmpl s.mem → s.trace = s0.trace →
      bs.length ≤ fuel → bs.length < 2 ^ 63 →
      Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s (pkLoopMem A sp' x19 ptr bs m)
        (pkEpiloguePostPlaced A s0 sp' x19 ptr bs
          (pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField fuel m bs))) (tryFromQp s0)
  | 0, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcrl, htr, hfuel, _ => by
    cases bs with
    | nil => exact loopHeader_070_empty_placed_wp rfl hpc hrun hregs hsp hcrl htr
    | cons b0 bs1 => simp at hfuel
  | fuel + 1, s, ptr, bs, m, hpc, hrun, hregs, hsp, hcrl, htr, hfuel, hlen => by
    cases bs with
    | nil => exact loopHeader_070_empty_placed_wp rfl hpc hrun hregs hsp hcrl htr
    | cons b0 bs1 =>
      unfold pkLoopMem; refine loopHeader_070_cons_placed_cps hpc hrun hregs hsp hcrl htr hlen ?_
      intro s1 hpc1 hrun1 hregs1 hx23_1 hx21_1 hx2_1 hsp1 hcrl1 htr1
      exact decodeLoop_080_step_placed_wp d (decodeLoop_070_placed_wp d fuel)
        hpc1 hrun1 hregs1 hx23_1 hx21_1 hx2_1 hsp1 hcrl1 htr1 hfuel hlen

theorem prologue_000_to_224_placed_wp [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) {x : DecodeGhost} {s0 : State}
    (hlt : x.bytes.length < 2 ^ 32) (hpc : s0.pc = (blkPl_65).base) (hrun : s0.status = .Running)
    (hsp : s0.spAligned = true) (hcrl : LibsignalCodeRoLoaded lsmpl s0.mem)
    (hx0 : s0.readReg64 .x0 = x.bytesA) (hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length)
    (hx8 : s0.readReg64 .x8 = x.ret) :
    Wire.SepWPp (lsProg_65 H) ((blkPl_65).base + bv% (548)) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sm Pm => PkEpilogueStatePlaced s0 (s0.sp - 224#64) sm ∧
        (Pm ⊢ pkEpilogueMem A (s0.sp - 224#64) x.ret x.bytesA x.bytes (PreKeyRecord.deserialize x.bytes) ∗
          pkCalleeSavedAt (s0.sp - 224#64) s0 ∗
          memRegion (s0.sp - 224#64 - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)))
      (tryFromQp s0) := by
  set sp' := s0.sp - 224#64
  have hstk1 := pkStack_smallRoot_split s0.sp; have hstk2 := pkSubStack_split sp'
  have h160 : memRegion sp' 160 = memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
      memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 112#64) 48 := by
    rw [show (160 : Nat) = 40 + (16 + (56 + 48)) by decide,
      ProofLib.memRegion_split sp' 40 120 (by decide), ProofLib.memRegion_split (sp' + 40#64) 16 104 (by decide),
      ProofLib.memRegion_split (sp' + 40#64 + 16#64) 56 48 (by decide)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  have h16 : memRegion (sp' + 40#64) 16 =
      (∃∗ u0 : BitVec 64, (sp' + 40#64) ↦₆₄ u0) ∗ (∃∗ u1 : BitVec 64, (sp' + 48#64) ↦₆₄ u1) := by
    rw [ProofLib.memRegion_split (sp' + 40#64) 8 8 (by decide), ProofLib.memRegion_eight, ProofLib.memRegion_eight]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
  refine Wire.SepWPp.mono_pre
    (P' := memRegion (sp' + 160#64) 64 ∗ memRegion (sp' + 56#64) 56 ∗ memRegion (sp' + 40#64) 16 ∗
      (memRegion sp' 40 ∗ memRegion (sp' + 112#64) 48 ∗ memRegion x.ret 56 ∗ (x.bytesA ↦ₛ x.bytes) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100) ∗
        memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)))
    (by rw [hstk1]; dsimp only [sp'] at hstk2 h160 ⊢; rw [hstk2, h160]; apply entails_of_eq; ac_rfl) ?_
  refine Wire.SepWPp.mono_pre
    (sepConj_mono (pkMemRegion64_unpack (sp' + 160#64))
      (sepConj_mono (pkStruct56_unpack_init (sp' + 56#64)) (Entails.refl _))) ?_
  rw [h16]; simp only [BitVec.add_assoc, BitVec.reduceAdd, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine Wire.SepWPp.exists_pre fun u1 => Wire.SepWPp.exists_pre fun u0 =>
    Wire.SepWPp.exists_pre fun s6w => Wire.SepWPp.exists_pre fun s5w => Wire.SepWPp.exists_pre fun s4w =>
    Wire.SepWPp.exists_pre fun s3w => Wire.SepWPp.exists_pre fun s2w => Wire.SepWPp.exists_pre fun s1w =>
    Wire.SepWPp.exists_pre fun s0w => Wire.SepWPp.exists_pre fun c7 => Wire.SepWPp.exists_pre fun c6 =>
    Wire.SepWPp.exists_pre fun c5 => Wire.SepWPp.exists_pre fun c4 => Wire.SepWPp.exists_pre fun c3 =>
    Wire.SepWPp.exists_pre fun c2 => Wire.SepWPp.exists_pre fun c1 => Wire.SepWPp.exists_pre fun c0 => ?_
  dsimp only [sp']
  have h0 : s0.readReg64 (Reg.gpr 0#5) = x.bytesA := hx0
  have h1 : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 x.bytes.length := hx1
  have h8 : s0.readReg64 (Reg.gpr 8#5) = x.ret := hx8
  cases hbs : x.bytes with
  | nil =>
    have h1_nil : s0.readReg64 (Reg.gpr 1#5) = 0#64 := by simpa [hbs] using h1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (372)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    have hoff40 : s0.sp - 184#64 = s0.sp - 224#64 + 40#64 := by bv_omega
    set F_saved := pkCalleeSavedAt sp' s0 ∗
      memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)
    have h16_pack := pointsTo64_pair_entails_memRegion16 (sp' + 40#64) x.bytesA 0#64
    refine Wire.SepWPp.mono_pre
      (P' := (memRegion sp' 40 ∗ memRegion (sp' + 40#64) 16 ∗
        vecHeader (sp' + 56#64) 0#64 1#64 0#64 ∗ vecHeader (sp' + 80#64) 0#64 1#64 0#64 ∗
        ((sp' + 104#64) ↦₃₂ 0#32) ∗ memRegion (sp' + 108#64) 4 ∗
        memRegion (sp' + 112#64) 48 ∗ ((sp' + 184#64) ↦₆₄ (sp' + 40#64)) ∗
        memRegion x.ret 56 ∗ (x.bytesA ↦ₛ ([] : List (BitVec 8))) ∗
        A.pool ∗ stackAt sp' (skipFieldStackX 100)) ∗ F_saved)
      (by
        dsimp only [F_saved, pkCalleeSavedAt, vecHeader, sp'] at h16_pack ⊢
        simp only [arm64_norm, sepConj_assoc] at h16_pack ⊢
        rw [← sepConj_assoc ((s0.sp - 224#64 + 40#64) ↦₆₄ x.bytesA) ((s0.sp - 224#64 + 48#64) ↦₆₄ 0#64)]
        refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h16_pack))))))))))))))))) ?_
        apply entails_of_eq; rw [hoff40]; ac_rfl) ?_
    exact Wire.SepWPp.frame_tryFrom
      (fast_empty_174_placed_wp (sp' := sp') (x19 := x.ret) (ptr := x.bytesA)
        (out := PreKeyRecord.deserialize []) rfl
        ⟨by simp [sp', arm64_norm], by simpa [State.spAligned, arm64_norm] using hsp, hcrl1, by simp [arm64_norm],
         ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) (by simp [arm64_norm]) (by simp [sp', arm64_norm]; bv_omega))
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)
  | cons b0 bs1 =>
    have hlen63 : (b0 :: bs1).length < 2 ^ 63 := by simp [hbs, List.length_cons] at hlt ⊢; omega
    obtain ⟨hc_eq, hc_ne⟩ := cons_len_bv64_ne_zero b0 bs1 hlen63
    have h1_cons : s0.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 (b0 :: bs1).length := by simpa [hbs] using h1
    refine sepWPp_of_sepWP_lscro hcrl (mid := (blkPl_65).base + bv% (128)) ?_; wp_steps
    refine Wire.SepWP.done (by simp [arm64_norm]) (by simp [hrun, arm64_norm]) ?_; intro hcrl1
    have hoff40 : s0.sp - 184#64 = s0.sp - 224#64 + 40#64 := by bv_omega
    set F_saved := pkCalleeSavedAt sp' s0 ∗
      memRegion (sp' - BitVec.ofNat 64 pkSubStack) (pkSubStack - skipFieldStackX 100)
    have hloop0 := pkEmptyHeaders_entails_loopOf A sp' (b0 :: bs1).length
    refine Wire.SepWPp.mono_pre
      (P' := pkLoopMem A sp' x.ret x.bytesA (b0 :: bs1) PreKeyRecordStructure.empty ∗ F_saved)
      (by
        unfold pkLoopMem sliceCursorAt; dsimp only [F_saved, pkCalleeSavedAt, vecHeader, sp'] at hloop0 ⊢
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
        refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono hloop0L (Entails.refl _)))))))))) ?_
        apply entails_of_eq; rw [hoff40]; ac_rfl) ?_
    have hdes : PreKeyRecord.deserialize (b0 :: bs1) =
        pkLoopOut (decodeFieldsLoop PreKeyRecordStructure.mergeField (bs1.length + 1)
          PreKeyRecordStructure.empty (b0 :: bs1)) := by
      rw [pkDeserialize_eq_of_decodeLoop (b0 :: bs1)]; simp only [List.length_cons]
      cases decodeFieldsLoop PreKeyRecordStructure.mergeField (bs1.length + 1) PreKeyRecordStructure.empty (b0 :: bs1) <;> rfl
    rw [hdes]
    exact Wire.SepWPp.frame_tryFrom
      (decodeLoop_080_step_placed_wp d (decodeLoop_070_placed_wp d bs1.length)
        (by simp [arm64_norm]) (by simp [hrun, arm64_norm])
        ⟨by simp [sp', arm64_norm], by simp [sp', arm64_norm]; bv_omega, by simp [arm64_norm],
         by simp [sp', arm64_norm]; bv_omega, by simp [arm64_norm],
         ⟨by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm], by simp [arm64_norm]⟩⟩
        (by simp [sp', arm64_norm]; bv_omega) (by simp [sp', arm64_norm]; bv_omega) (by simp [arm64_norm])
        (by simpa [State.spAligned, arm64_norm] using hsp) hcrl1 (by simp [arm64_norm]) (by simp) hlen63)
      (fun sf Pf ⟨hstf, hentf⟩ => ⟨hstf, sepConj_mono_left hentf⟩)

end Placed
end Helpers

section Placed
open CryptoVerification.RecordCodecs.Placed

/-- Relocatable `PreKeyRecord::deserialize` (Block `65`) meets `preKeyDeserializePlacedSpec`
under `[LibsignalPlacement]`, given `PortDepsPlaced A H`. -/
theorem preKeyRecord_deserialize_placed_ok [LibsignalPlacement] {A : RustAlloc} {H : LibsignalHooks}
    (d : PortDepsPlaced A H) :
    subroutine_ok (lsProg_65 H) (blkPl_65).base (preKeyDeserializePlacedSpec A) := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  have ⟨hcrl0, hpre⟩ := extract_withLsCodeRoLoaded hpre
  dsimp only [preKeyDeserializeRawSpec] at hpre
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1_nat, hlt, hx8⟩, hmem⟩
  have hx1 : s0.readReg64 .x1 = BitVec.ofNat 64 x.bytes.length := by
    rw [← hx1_nat, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hmem' : s0.mem ⊨
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s0.sp smallRootStack ∗ A.pool) ∗ R := by
    ac_nf at hmem ⊢
  have h1 := prologue_000_to_224_placed_wp d (x := x) hlt hpc hrun hsp hcrl0 hx0 hx1 hx8
  have hfull : Wire.SepWPp (lsProg_65 H) (s0.readReg64 .x30) s0
      ((x.bytesA ↦ₛ x.bytes) ∗ memRegion x.ret 56 ∗ stackAt s0.sp smallRootStack ∗ A.pool)
      (fun sf Pf => sf.sp = s0.sp ∧ (calleeSavedVRegs sf = calleeSavedVRegs s0 → CalleeSavedPreserved s0 sf) ∧
        (Pf ⊢ (preKeyDeserializePlacedSpec A).post x s0 sf)) (tryFromQp s0) := by
    refine Wire.SepWPp.bind h1 fun sm Pm hpcm hrunm ⟨hstm, hentm⟩ =>
      Wire.SepWPp.mono_pre hentm (epilogue_224_placed_wp (A := A) (x := x) hstm hpcm hrunm)
  obtain ⟨sf, hsteps, hex⟩ := hfull R hmem' hL
  refine reaches_outcome_steps hsteps (reaches_outcome.of_outcome ?_)
  rcases hex with ⟨hpc_f, hrun_f, Pf, hmf, ⟨hsp_f, hcs_f, hent_f⟩, hv_f⟩ | ⟨hpan, Pf, hmf, htr_f⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨⟨hpc_f, hsp_f, hrun_f⟩, ⟨hsp_f, hcs_f hv_f⟩,
      Satisfies.mono (sepConj_mono_left hent_f) hmf⟩
  · exact Or.inr (Or.inl ⟨hpan, htr_f R hmf⟩)
  · exact (allowPanic_not_exited hoom).elim

end Placed
end CryptoVerification.RecordCodecsBinary.PreKeyDeserialize

