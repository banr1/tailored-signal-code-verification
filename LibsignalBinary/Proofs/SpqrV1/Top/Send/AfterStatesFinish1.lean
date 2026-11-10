/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.Defs
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Drop.ProtoTop2
import LibsignalBinary.Proofs.SpqrV1.Top.Send.AfterStatesChain
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# `spqr::send`: Return Assembly, Epoch Dealloc, and Initial `PqRatchetState` Drop

Return struct assembly (`0x320a4..0x32114`), consumed epoch-secret check (`0x32114..0x32134`),
and `versionNegotiation` / `chain` / `none` / `.keysUnsampled` drop steps (`0x32134..0x32490`)
in `spqr::send::<HookRng>`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Layout.L22
open CryptoVerification.CodeLayout in
abbrev spqrSendDropJumpTableOff : Nat :=
  num% (ls_xref% 0x32270 0x32274)
end CryptoVerification.SpqrV1.Layout.L22

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.CodeLayout
open CryptoVerification.SpqrV1.Layout.L22
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.SpqrV1.Poly
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Prost.EncodeToVec hiding SepWP.done

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

private theorem send_noneCap2_add_two_beq_zero :
    (0xfffffffffffffffe#64 + 2#64 == 0#64) = true := rfl

private theorem send_noneCap2_add_two_bne_zero :
    (0xfffffffffffffffe#64 + 2#64 != 0#64) = false := rfl

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff Program.fnAddr
  v1StatePBPinnedAt
attribute [local arm64_norm, local wp_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm] none2Cap_add_two_beq_zero Drop.noneCap_add_two_beq_zero
  EncodedLen.noneCap_add_one_beq_zero EncodedLen.noneCap_add_one_bne_zero
  send_noneCap2_add_two_beq_zero send_noneCap2_add_two_bne_zero
  noneCap3_add_three_beq_zero noneCap3_add_three_bne_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
  (ls_lemma% fnOff "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]")
  (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::PolynomialEncoder>> [local#1]")
  (ls_lemma% fnOff "core::ptr::drop_glue::<core::option::Option<spqr::proto::pq_ratchet::v1_state::unchunked::Ct1Sent>> [local#1]")
  (ls_stub% "__rustc::__rust_dealloc")

/-! ## 1. Representation Bridge & `0x32058..0x320a4` `st.inner` Header Steps -/

theorem pqRatchetStatePBPinnedAt_entails_proto (A : RustAlloc) (g : PqRatchetStatePBGhost)
    (a : BitVec 64) (st : PqRatchetState) :
    pqRatchetStatePBPinnedAt A g a st ⊢ Drop.protoPqRatchetStateAt A a st := by
  rw [← pqRatchetStatePBAt_eq_protoPqRatchetStateAt, pqRatchetStatePBAt_eq_exists_pinned]
  exact Entails.sepExists_right g (Entails.refl _)

private theorem encodeVarintLoop_len_le_fin (fuel : Nat) (a : BitVec 64) :
    (encodeVarintLoop fuel a).length ≤ fuel := by
  induction fuel generalizing a with
  | zero => simp [encodeVarintLoop]
  | succ fuel ih =>
    simp only [encodeVarintLoop]; split
    · simp
    · simp only [List.length_cons]; have := ih (a >>> 7); omega

private theorem encode_varint_len_le_fin (a : BitVec 64) (into : Bytes) :
    (CryptoVerification.LibsignalSpqrV1.encode_varint a into).length ≤ into.length + 10 := by
  change (into ++ encodeVarintLoop MAX_VARINT_BYTES_LEN a).length ≤ into.length + 10
  rw [List.length_append]
  have h := encodeVarintLoop_len_le_fin MAX_VARINT_BYTES_LEN a
  have hm : MAX_VARINT_BYTES_LEN = 10 := rfl; omega

private theorem encode_chunk_len_le_fin {P : PolyApi} (c : P.Chunk) (into : Bytes) :
    (encode_chunk c into).length ≤ into.length + 42 := by
  dsimp only [encode_chunk]
  rw [List.length_append, List.Vector.toList_length]
  have h := encode_varint_len_le_fin ((P.chunkIndex c).zeroExtend 64) into
  omega

/-- Every serialized SPQR message `msg.serialize index` has length `≤ 64 < 2 ^ 32`, discharging
    `hmsg_len : msgBytes.length < 2 ^ 32` in `spqrSendResultAt` / `step_send_finish_320a4`. -/
theorem message_serialize_length_lt_pow32 {P : PolyApi} (msg : Message P) (index : BitVec 32) :
    (msg.serialize index).length < 2 ^ 32 := by
  dsimp only [Message.serialize]
  have h1 := encode_varint_len_le_fin msg.epoch [1#8]
  have h2 := encode_varint_len_le_fin (index.zeroExtend 64) (encode_varint msg.epoch [1#8])
  set into2 := encode_varint (index.zeroExtend 64) (encode_varint msg.epoch [1#8]) ++
    [(MessageType.from_payload msg.payload).toU8]
  have h2' : into2.length ≤ 22 := by
    rw [List.length_append, List.length_singleton]
    simp only [List.length_singleton] at h1
    omega
  cases msg.payload with
  | none | ct1Ack _ => exact Nat.lt_of_le_of_lt h2' (by decide)
  | hdr c | ek c | ekCt1Ack c | ct1 c | ct2 c =>
    exact Nat.lt_of_le_of_lt (encode_chunk_len_le_fin c into2) (by omega)

/-! ## 2. Tail-Deallocation Helpers at `0x31a4c` (`+4592`) and `0x31a50` (`+4596`) -/

theorem send_stackAt_callee_eq_allocHook (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - allocHookStack) ∗
        stackAt sp allocHookStack :=
  ProofLib.stackAt_split_bottom sp allocHookStack
    (spqrSendCalleeStack - allocHookStack) (by decide)

theorem send_stackAt_callee_eq_dropStack32 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack32) ∗
        stackAt sp dropStack32 :=
  ProofLib.stackAt_split_bottom sp dropStack32
    (spqrSendCalleeStack - dropStack32) (by decide)

theorem stackAt_spqrSendCallee_eq_dropStack48 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack48) ∗
        stackAt sp dropStack48 :=
  ProofLib.stackAt_split_bottom sp dropStack48
    (spqrSendCalleeStack - dropStack48) (by decide)

theorem stackAt_spqrSendCallee_eq_dropStack64 (sp : BitVec 64) :
    stackAt sp spqrSendCalleeStack =
      memRegion (sp - 123008#64) (spqrSendCalleeStack - dropStack64) ∗
        stackAt sp dropStack64 :=
  ProofLib.stackAt_split_bottom sp dropStack64
    (spqrSendCalleeStack - dropStack64) (by decide)

/-- `0x31a50 -> 0x31a54` (`entry + 4596#64 -> entry + 4600#64`, 1 instruction): calls `bl
    __rust_dealloc` with `(x0 = ptr, x1 = sz, x2 = align)` and lands at `0x31a54` preserving
    `x23`. -/
theorem step_tail_dealloc_31a50 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (ptr : BitVec 64) (sz align : Nat) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4596#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : (s.readReg64 .x1).toNat = sz)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4600#64) s
      ((A.live ptr sz align ∗ memRegion ptr sz) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range b (Rust.withPanics ext) 4596 4
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rw [send_stackAt_callee_eq_allocHook s.sp]
  wp_steps
  wp_call hdealloc_raw (ptr, sz, align)
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      Entails.of_eq (by ac_rfl)⟩

/-- `0x31a4c -> 0x31a54` (`entry + 4592#64 -> entry + 4600#64`, 2 instructions): executes `mov
    w2, #1; bl __rust_dealloc` with `(x0 = ptr, x1 = cap)` and lands at `0x31a54` preserving
    `x23`. -/
theorem step_tail_dealloc_31a4c {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (ptr cap x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4592#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr)
    (hx1 : s.readReg64 .x1 = cap)
    (hx23 : s.readReg64 .x23 = x23)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4600#64) s
      ((A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range b (Rust.withPanics ext) 4592 8
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rw [send_stackAt_callee_eq_allocHook s.sp]
  wp_steps
  wp_call hdealloc_raw (ptr, cap.toNat, 1)
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      Entails.of_eq (by ac_rfl)⟩

/-! ## 3. Return Struct Assembly (`0x320a4..0x32114`) & Epoch Secret Dealloc (`0x32114..0x32134`) -/

attribute [local simp, local arm64_norm, local wp_norm]
  extractLsb_lo_append64 extractLsb_hi_append64

/-- Stack slots `[sp + 8]`, `[sp + 24]`, `[sp + 40]` holding the optional 32-byte message key
    (`key : CryptoGames.HKDF.Salt`) at `0x320a4`:
    - `none`: `[sp + 8] = mkPtr`, `[sp + 24] = 0#64`, `[sp + 40] = mkCap`, and `vecU8Heap A mkCap mkPtr []`
    - `some k`: `[sp + 8] = mkPtr`, `[sp + 24] = 32#64`, `[sp + 40] = mkCap`, and `vecU8Heap A mkCap mkPtr k.toList` -/
def optMsgKeySlotsAt (A : RustAlloc) (sp : BitVec 64) :
    CryptoGames.HKDF.Salt → SepProp
  | none =>
    ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
      ((sp + 8#64) ↦₆₄ mkPtr) ∗
      ((sp + 24#64) ↦₆₄ 0#64) ∗
      ((sp + 40#64) ↦₆₄ mkCap) ∗
      DecodeState.vecU8Heap A mkCap mkPtr []
  | some k =>
    ∃∗ mkCap : BitVec 64, ∃∗ mkPtr : BitVec 64,
      ((sp + 8#64) ↦₆₄ mkPtr) ∗
      ((sp + 24#64) ↦₆₄ 32#64) ∗
      ((sp + 40#64) ↦₆₄ mkCap) ∗
      DecodeState.vecU8Heap A mkCap mkPtr k.toList

theorem vecU8_expose_words (A : RustAlloc) (a : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A a bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
        ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        DecodeState.vecU8Heap A cap ptr bs := by
  unfold vecU8
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader DecodeState.vecU8Heap
  exact Entails.of_eq (by ac_rfl)

theorem words_to_vecU8 (A : RustAlloc) (a cap ptr : BitVec 64) (bs : List (BitVec 8)) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗
      ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      DecodeState.vecU8Heap A cap ptr bs ⊢
      vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader DecodeState.vecU8Heap
  exact Entails.of_eq (by ac_rfl)

theorem memRegion_16_words2 (a : BitVec 64) :
    memRegion a 16 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 8) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64)]

theorem words2_to_memRegion_16 (a w0 w1 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ⊢ memRegion a 16 := by
  rw [memRegion_16_words2 a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (Entails.sepExists_right w1 (Entails.refl _))

theorem memRegion_48_words6 (a : BitVec 64) :
    memRegion a 48 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) ∗
      (∃∗ w3 : BitVec 64, (a + 24#64) ↦₆₄ w3) ∗
      (∃∗ w4 : BitVec 64, (a + 32#64) ↦₆₄ w4) ∗
      (∃∗ w5 : BitVec 64, (a + 40#64) ↦₆₄ w5) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 40) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 32) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 24) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 16) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 8) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64),
      ProofLib.memRegion_eight (a + 32#64), ProofLib.memRegion_eight (a + 40#64)]

theorem words6_to_memRegion_48 (a w0 w1 w2 w3 w4 w5 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
    ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ⊢
      memRegion a 48 := by
  rw [memRegion_48_words6 a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w4 (Entails.refl _))
      (Entails.sepExists_right w5 (Entails.refl _))))))

theorem memRegion_24_words3' (a : BitVec 64) :
    memRegion a 24 =
      (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗
      (∃∗ w1 : BitVec 64, (a + 8#64) ↦₆₄ w1) ∗
      (∃∗ w2 : BitVec 64, (a + 16#64) ↦₆₄ w2) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 8) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64)]

theorem words3_to_memRegion_24' (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢ memRegion a 24 := by
  rw [memRegion_24_words3' a]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (Entails.sepExists_right w2 (Entails.refl _)))

theorem memRegion_72_split_48_24 (ret : BitVec 64) :
    memRegion ret 72 = memRegion ret 48 ∗ memRegion (ret + 48#64) 24 := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 48) (k := 24) (b' := ret + 48#64)
        rfl rfl (by decide)]

theorem memRegion_24_split_8_16 (a : BitVec 64) :
    memRegion a 24 = (∃∗ w0 : BitVec 64, a ↦₆₄ w0) ∗ memRegion (a + 8#64) 16 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 16) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_eight a]

theorem sendResultAt_some_of_parts (A : RustAlloc) (ret : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt)
    (hmsg_len : msgBytes.length < 2 ^ 32) :
    vecU8 A ret stBytes ∗ vecU8 A (ret + 24#64) msgBytes ∗
      spqrSendKeyAt A (ret + 48#64) key ⊢
      spqrSendResultAt A ret (some (stBytes, key, msgBytes)) := by
  dsimp only [spqrSendResultAt]
  refine Entails.trans
    (Entails.pure_right hmsg_len (Entails.refl _))
    (Entails.of_eq (by ac_rfl))

theorem optKeyAt_none_of_word (A : RustAlloc) (a : BitVec 64) :
    (a ↦₆₄ 18446744073709551615#64) ∗ memRegion (a + 8#64) 16 ⊢
      spqrSendKeyAt A a none := by
  unfold spqrSendKeyAt noneCap
  exact Entails.refl _

theorem optKeyAt_some_of_words (A : RustAlloc) (a cap ptr : BitVec 64)
    (k : List.Vector (BitVec 8) 32) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ 32#64) ∗
      DecodeState.vecU8Heap A cap ptr k.toList ⊢
      spqrSendKeyAt A a (some k) := by
  have hlen : BitVec.ofNat 64 k.toList.length = 32#64 := by
    simp [List.Vector.toList_length]
  unfold spqrSendKeyAt
  rw [← hlen]
  exact words_to_vecU8 A a cap ptr k.toList

/-- `0x320a4 -> 0x32114` (`entry + 6216#64 -> entry + 6328#64`): Assembles `spqrSendResultAt A
    ret (some (stBytes, key, msgBytes))` at `ret` (`x19`) from `vecU8 A (s.sp + 1424#64)
    stBytes`, `vecU8 A (s.sp + 4080#64) msgBytes`, and `optMsgKeySlotsAt A s.sp key`, reloads
    `x19 = v_20` from `[s.sp + 32#64]`, and lands at `0x32114`. -/
theorem step_send_build_result_320a4 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (ret v_20 x21 x23 x25 x27 : BitVec 64)
    (stBytes msgBytes : Bytes) (key : CryptoGames.HKDF.Salt) (Frame : SepProp)
    (hmsg_len : msgBytes.length < 2 ^ 32)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6216#64)
    (hrun : s.status = .Running)
    (hx19 : s.readReg64 .x19 = ret)
    (hx21 : s.readReg64 .x21 = x21)
    (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25)
    (hx27 : s.readReg64 .x27 = x27)
    (hx28 : s.readReg64 .x28 = s.sp + 4192#64)
    (hret_align : (ret &&& 7#64 == 0#64) = true)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6328#64) s
      (memRegion ret 72 ∗
        vecU8 A (s.sp + 1424#64) stBytes ∗
        vecU8 A (s.sp + 4080#64) msgBytes ∗
        optMsgKeySlotsAt A s.sp key ∗
        ((s.sp + 32#64) ↦₆₄ v_20) ∗
        memRegion (s.sp + 4192#64) 48 ∗
        memRegion (s.sp + 7136#64) 16 ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = v_20 ∧
        sf.readReg64 .x21 = x21 ∧
        sf.readReg64 .x23 = x23 ∧
        sf.readReg64 .x25 = x25 ∧
        sf.readReg64 .x27 = x27 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ spqrSendResultAt A ret (some (stBytes, key, msgBytes)) ∗
          memRegion (s.sp + 8#64) 8 ∗
          memRegion (s.sp + 24#64) 24 ∗
          memRegion (s.sp + 1424#64) 24 ∗
          memRegion (s.sp + 4080#64) 24 ∗
          memRegion (s.sp + 4192#64) 48 ∗
          memRegion (s.sp + 7136#64) 16 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  spqr_send_fetches_range b (Rust.withPanics ext) 6216 112
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hdealloc_raw hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  have hst_exp := vecU8_expose_words A (s.sp + 1424#64) stBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hst_exp
  have hmsg_exp := vecU8_expose_words A (s.sp + 4080#64) msgBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hmsg_exp
  refine SepWP.focus_weaken hst_exp (by sep_focus) ?_
  wp_pull_exists; rename_i stCap stPtr
  refine SepWP.focus_weaken hmsg_exp (by sep_focus) ?_
  wp_pull_exists; rename_i msgCap msgPtr
  wp_conv_pre =>
    rw [memRegion_72_split_48_24 ret,
        memRegion_48_words6 ret,
        memRegion_48_words6 (s.sp + 4192#64),
        memRegion_16_words2 (s.sp + 7136#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_pull_exists
  have hret_st := words_to_vecU8 A ret stCap stPtr stBytes
  have hret_msg := words_to_vecU8 A (ret + 24#64) msgCap msgPtr msgBytes
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_msg
  have h1424 := words3_to_memRegion_24' (s.sp + 1424#64) stCap stPtr (BitVec.ofNat 64 stBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h1424
  have h4080 := words3_to_memRegion_24' (s.sp + 4080#64) msgCap msgPtr (BitVec.ofNat 64 msgBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4080
  have h4192 := words6_to_memRegion_48 (s.sp + 4192#64)
    stCap stPtr (BitVec.ofNat 64 stBytes.length) msgCap msgPtr (BitVec.ofNat 64 msgBytes.length)
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h4192
  have h7136 := words2_to_memRegion_16 (s.sp + 7136#64) stCap stPtr
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at h7136
  cases key with
  | some k =>
    dsimp only [optMsgKeySlotsAt]
    wp_pull_exists; rename_i mkCap mkPtr
    wp_conv_pre => rw [memRegion_24_words3' (ret + 48#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_pull_exists
    wp_steps
    have hret_key := optKeyAt_some_of_words A (ret + 48#64) mkCap mkPtr k
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
    have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
    have h24 := words3_to_memRegion_24' (s.sp + 24#64) 32#64 v_20 mkCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    refine SepWP.focus_weaken hret_st (by sep_focus) ?_
    refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
    refine SepWP.focus_weaken hret_key (by sep_focus) ?_
    refine SepWP.focus_weaken
      (sendResultAt_some_of_parts A ret stBytes msgBytes (some k) hmsg_len) (by sep_focus) ?_
    refine SepWP.focus_weaken h8 (by sep_focus) ?_
    refine SepWP.focus_weaken h24 (by sep_focus) ?_
    refine SepWP.focus_weaken h1424 (by sep_focus) ?_
    refine SepWP.focus_weaken h4080 (by sep_focus) ?_
    refine SepWP.focus_weaken h4192 (by sep_focus) ?_
    refine SepWP.focus_weaken h7136 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | none =>
    dsimp only [optMsgKeySlotsAt]
    wp_pull_exists; rename_i mkCap mkPtr
    wp_conv_pre => rw [memRegion_24_split_8_16 (ret + 48#64)]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_pull_exists
    refine SepWP.focus_weaken (vecU8Heap_entails_dealloc A mkCap mkPtr []) (by sep_focus) ?_
    wp_focus_pure; intro hcap_lt
    dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
    have hret_key := optKeyAt_none_of_word A (ret + 48#64)
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hret_key
    have h8 := ProofLib.pointsTo64_entails_memRegion (s.sp + 8#64) mkPtr
    have h24 := words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 mkCap
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at h24
    by_cases hc0 : (mkCap == 0#64) = true <;>
      simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
    · have hc_eq : mkCap = 0#64 := by rwa [beq_iff_eq] at hc0
      subst hc_eq
      wp_steps
      refine SepWP.focus_weaken hret_st (by sep_focus) ?_
      refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
      refine SepWP.focus_weaken hret_key (by sep_focus) ?_
      refine SepWP.focus_weaken
        (sendResultAt_some_of_parts A ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
      refine SepWP.focus_weaken h8 (by sep_focus) ?_
      refine SepWP.focus_weaken (words3_to_memRegion_24' (s.sp + 24#64) 0#64 v_20 0#64) (by sep_focus) ?_
      refine SepWP.focus_weaken h1424 (by sep_focus) ?_
      refine SepWP.focus_weaken h4080 (by sep_focus) ?_
      refine SepWP.focus_weaken h4192 (by sep_focus) ?_
      refine SepWP.focus_weaken h7136 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    · rw [send_stackAt_callee_eq_allocHook s.sp]
      wp_steps
      wp_call hdealloc_raw (mkPtr, mkCap.toNat, 1)
      refine SepWP.focus_weaken hret_st (by sep_focus) ?_
      refine SepWP.focus_weaken hret_msg (by sep_focus) ?_
      refine SepWP.focus_weaken hret_key (by sep_focus) ?_
      refine SepWP.focus_weaken
        (sendResultAt_some_of_parts A ret stBytes msgBytes none hmsg_len) (by sep_focus) ?_
      refine SepWP.focus_weaken h8 (by sep_focus) ?_
      refine SepWP.focus_weaken h24 (by sep_focus) ?_
      refine SepWP.focus_weaken h1424 (by sep_focus) ?_
      refine SepWP.focus_weaken h4080 (by sep_focus) ?_
      refine SepWP.focus_weaken h4192 (by sep_focus) ?_
      refine SepWP.focus_weaken h7136 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

@[local simp, local arm64_norm, local wp_norm]
theorem ite_zero32_self (P : Prop) [Decidable P] :
    (if P then (0#32 : BitVec 32) else 0#32) = 0#32 := by
  split <;> rfl

@[local simp, local arm64_norm, local wp_norm]
theorem ite_zero64_self (P : Prop) [Decidable P] :
    (if P then (0#64 : BitVec 64) else 0#64) = 0#64 := by
  split <;> rfl

/-- `0x32114 -> 0x32134` (`entry + 6328#64 -> entry + 6360#64`): When `x21 = noneCap ∨
    s.readReg32 .x19 = 0#32` (which holds on all `Ok` paths since any `Some(epoch_secret)` was
    already consumed by `Chain::add_epoch` with drop-flag `w20 = 0`), `sub x8, x21, #1; adds
    xzr, x8, #2; csel w8, wzr, w19, cs; tbz w8, #0, 0x32134` branches directly to `0x32134`. -/
theorem step_send_epoch_dealloc_32114 {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (x23 x25 : BitVec 64) (P : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6328#64)
    (hrun : s.status = .Running)
    (hx23 : s.readReg64 .x23 = x23)
    (hx25 : s.readReg64 .x25 = x25)
    (hflag : s.readReg64 .x21 = noneCap ∨ s.readReg32 .x19 = 0#32) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6360#64) s P
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        sf.readReg64 .x25 = x25 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ P)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 6328 16
  dsimp only [tripleRatchetProgAtExt, spqrSendName, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  rcases hflag with hx21 | hx19
  · wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩
  · have hgpr19 : BitVec.truncate 32 (s.readReg64 (Reg.gpr 19#5)) = 0#32 := hx19
    wp_steps
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.refl _⟩

/-! ## 4. Inlined `drop_in_place::<PqRatchetState>` (`0x32134..0x326c0`) Part 1 -/

theorem pqRatchetStatePBPinnedAt_cap_bounds {A : RustAlloc} {g : PqRatchetStatePBGhost}
    {a : BitVec 64} {st : PqRatchetState} {R : SepProp} {m : Memory}
    (hm : m ⊨ pqRatchetStatePBPinnedAt A g a st ∗ R) :
    (optChainCap g.chain st.chain + 1#64 == 0#64) = !st.chain.isSome ∧
      (optChainCap g.chain st.chain + 1#64 != 0#64) = st.chain.isSome := by
  rw [pqRatchetStatePBPinnedAt, optChainPBPinnedAt_eq A g.chain (a + 48#64) st.chain] at hm
  exact optChainRest_cap_bounds (A := A) (g := g.chain) (p := a + 48#64)
    (R := optVersionNegotiationPBPinnedAt A g.vn a st.versionNegotiation ∗
      ((a + 48#64) ↦₆₄ optChainCap g.chain st.chain) ∗
      optPqRatchetInnerPBPinnedAt A g.inner (a + 128#64) st.inner ∗ R)
    (Satisfies.mono (Entails.of_eq (by ac_rfl)) hm)

/-- `0x32134 -> 0x32164` (`entry + 6360#64 -> entry + 6408#64`): Drops `vn : Option
    VersionNegotiationPB` at `s.sp + 4704#64` (`sp + 0x1260`) and `ch : Option ChainPB` at `s.sp
    + 4752#64` (`sp + 0x1290`, calling `0x35530 = dropProtoSpqrChainName` when `ch = some _`),
    setting `x19 = s.sp + 4704#64` and turning `[s.sp + 4704 .. s.sp + 4832)` into `memRegion
    (s.sp + 4704#64) 128`. -/
theorem step_send_drop_vn_chain_32134 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (vn : Option VersionNegotiationPB) (ch : Option ChainPB)
    (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6360#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23)
    (hx25 : (s.readReg64 .x25 + 1#64 == 0#64) = !ch.isSome) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6408#64) s
      (optVersionNegotiationPBAt A (s.sp + 4704#64) vn ∗
        optChainPBAt A (s.sp + 4752#64) ch ∗
        A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x19 = s.sp + 4704#64 ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4704#64) 128 ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  have hchain_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]"))
      (dropProtoSpqrChainSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::ptr::drop_glue::<spqr::proto::pq_ratchet::Chain> [local#1]")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff dropProtoSpqrChain_fnOff (by decide))
    (drop_proto_spqr_chain_ok_ext hdealloc)
  simp only [rustDeallocSpec] at hdealloc_raw
  simp only [dropProtoSpqrChainSpec] at hchain_raw
  spqr_send_fetches_range b (Rust.withPanics ext) 6360 48
  dsimp only [tripleRatchetProgAtExt, spqrSendName, chainPBSize,
    BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hchain_raw ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  refine seq_clean (mid := entry + 6392#64)
    (P_mid := memRegion (s.sp + 4704#64) 48 ∗
      optChainPBAt A (s.sp + 4752#64) ch ∗
      A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
    (Q := fun sm =>
      sm.sp = s.sp ∧ sm.trace = s.trace ∧
      sm.readReg64 .x19 = s.sp + 4704#64 ∧
      sm.readReg64 .x23 = x23 ∧
      sm.readReg64 .x25 = s.readReg64 .x25 ∧
      calleeSavedVRegs sm = calleeSavedVRegs s)
    ?_ ?_
  · cases vn with
    | none =>
      dsimp only [optVersionNegotiationPBAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      have hnone48 := optVersionNegotiationPBAt_none_entails_memRegion_48 (s.sp + 4704#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone48
      refine SepWP.focus_weaken hnone48 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨Entails.of_eq (by ac_rfl),
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
    | some vnVal =>
      dsimp only [optVersionNegotiationPBAt]
      refine SepWP.focus_weaken
        (versionNegotiationPBAt_entails_dealloc A (s.sp + 4704#64) vnVal) (by sep_focus) ?_
      wp_pull_exists; rename_i g; rcases g with ⟨cap, ptr⟩
      wp_focus_pure; intro hcap_lt
      dsimp only [vecCapPtrDealloc] at hcap_lt ⊢
      have hhdr48 := vnHeader_entails_memRegion_48 (s.sp + 4704#64) cap ptr
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr48
      by_cases hc0 : (cap == 0#64) = true <;>
        simp only [hc0, Bool.false_eq_true, ↓reduceIte, emp_sepConj, sepConj_emp]
      · have hc_eq : cap = 0#64 := by rwa [beq_iff_eq] at hc0
        subst hc_eq
        wp_steps
        refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.of_eq (by ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      · have hslt := cap_ne_zero_slt_one_false hcap_lt hc0
        have hlt_false := cap_ne_zero_lt_one_false hcap_lt hc0
        rw [send_stackAt_callee_eq_allocHook s.sp]
        wp_steps
        wp_call hdealloc_raw (ptr, cap.toNat, 1)
        refine SepWP.focus_weaken hhdr48 (by sep_focus) ?_
        exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
          ⟨Entails.of_eq (by ac_rfl),
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
            by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
  · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hx19_1, hx23_1, hx25_1, hvregs1⟩
    have hjoin128 : memRegion (s.sp + 4704#64) 48 ∗ memRegion (s.sp + 4752#64) 80 ⊢
        memRegion (s.sp + 4704#64) 128 := by
      have h4752 : (s.sp + 4704#64) + 48#64 = s.sp + 4752#64 := by bv_omega
      rw [← h4752, ProofLib.memRegion_split (s.sp + 4704#64) 48 80 (by decide)]
      exact Entails.refl _
    have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
    cases ch with
    | none =>
      simp only [Option.isSome_none, Bool.not_false] at hx25
      have hx25_1' : (s1.readReg64 .x25 + 1#64 == 0#64) = true := by rw [hx25_1, hx25]
      dsimp only [optChainPBAt]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      have hnone80 := optChainPBAt_none_entails_memRegion_80 (s.sp + 4752#64)
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone80
      refine SepWP.focus_weaken hnone80 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some chVal =>
      simp only [Option.isSome_some, Bool.not_true] at hx25
      have hx25_1' : ¬((s1.readReg64 .x25 + 1#64 == 0#64) = true) := by
        rw [hx25_1, hx25]; decide
      dsimp only [optChainPBAt]
      rw [stackAt_spqrSendCallee_eq_dropStack48 s.sp]
      wp_steps
      wp_call hchain_raw ⟨s.sp + 4752#64, chVal⟩
      rw [hsp1]
      refine SepWP.focus_weaken hjoin128 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

open CryptoVerification.SpqrV1.Layout.L22 in
theorem fnAddr_adrp_3218c {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 6448#64) &&&
      0xfffffffffffff000#64) = b + bv% (page% (ls_off% "spqr::send::<libsignal_session::HookRng>" + 6448)) := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

def spqrSendDropJumpTableExpanded (b : BitVec 64) : SepProp :=
  ((b + bv% (spqrSendDropJumpTableOff + 0)) ↦₈ᵣ 0xbb#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 1)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 2)) ↦₈ᵣ 0x00#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 3)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 4)) ↦₈ᵣ 0x7b#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 5)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 6)) ↦₈ᵣ 0x00#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 7)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 8)) ↦₈ᵣ 0x3c#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 9)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 10)) ↦₈ᵣ 0xc8#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 11)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 12)) ↦₈ᵣ 0xe7#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 13)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 14)) ↦₈ᵣ 0xa4#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 15)) ↦₈ᵣ 0x00#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 16)) ↦₈ᵣ 0x25#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 17)) ↦₈ᵣ 0x01#8) ∗
  ((b + bv% (spqrSendDropJumpTableOff + 18)) ↦₈ᵣ 0x66#8) ∗ ((b + bv% (spqrSendDropJumpTableOff + 19)) ↦₈ᵣ 0x00#8)

theorem spqrSendDropJumpTableAt_eq_expanded (b : BitVec 64) :
    spqrSendDropJumpTableAt b = spqrSendDropJumpTableExpanded b := by
  unfold spqrSendDropJumpTableAt spqrSendDropJumpTableBytes spqrSendDropJumpTableExpanded
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- `0x32164 -> 0x31a54` (`entry + 6408#64 -> entry + 4600#64`) when `st.inner = none`
    (`0xfffffffffffffffd#64` = `none3Cap'`): `add x9, x8, #3` gives `0`, `subs xzr, x9, #2` sets
    `CC` (`0 < 2`), and `b.cc #-1820` jumps directly to `0x31a54` (`entry + 4600#64`). -/
theorem step_send_drop_inner_none_32164 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4600#64) s
      (optProtoPqRatchetInnerAt A (s.sp + 4832#64) none ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ Frame)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 6408 16
  dsimp only [tripleRatchetProgAtExt, spqrSendName, optProtoPqRatchetInnerAt,
    none3Cap', BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hnone224 := optProtoPqRatchetInnerAt_none_entails_memRegion_224 (s.sp + 4832#64)
  dsimp only [none3Cap'] at hnone224
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
  refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `0x32164 -> 0x31a54` (`entry + 6408#64 -> entry + 4600#64`) when `st.inner = some (.v1
    ⟨none⟩)` (`0xfffffffffffffffe#64` = `none2Cap`): `add x9, x8, #3` gives `1`, `subs xzr, x9,
    #2` sets `CC` (`1 < 2`), and `b.cc #-1820` jumps directly to `0x31a54` (`entry + 4600#64`). -/
theorem step_send_drop_inner_v1_none_32164 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (s : State) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) none ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗ Frame)) := by
  spqr_send_fetches_range b (Rust.withPanics ext) 6408 16
  dsimp only [tripleRatchetProgAtExt, spqrSendName, optProtoInnerStateAt,
    none2Cap, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  have hnone224 := optProtoInnerState_none_entails_224 (s.sp + 4832#64)
  dsimp only [none2Cap] at hnone224
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone224
  refine SepWP.focus_weaken hnone224 (by sep_focus) ?_
  exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
      by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

/-- `0x32164 -> 0x31a54` (`entry + 6408#64 -> entry + 4600#64`) for `st.inner = some (.v1 ⟨some
    (.keysUnsampled st)⟩)` (`idx = 0`, target `0x32490 = entry + 7220#64`). -/
theorem step_send_drop_inner_keysUnsampled_32164 {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64)
    (hdealloc : DeallocOkExt b A ext)
    (s : State) (st : V1State.Chunked.KeysUnsampled) (x23 : BitVec 64) (Frame : SepProp)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 6408#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx23 : s.readReg64 .x23 = x23) :
    SepWP (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + 4600#64) s
      (optProtoInnerStateAt A (s.sp + 4832#64) (some (.keysUnsampled st)) ∗
        spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
      (fun sf Q =>
        sf.status = .Running ∧
        sf.trace = s.trace ∧
        sf.sp = s.sp ∧
        sf.readReg64 .x23 = x23 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        (Q ⊢ memRegion (s.sp + 4832#64) 224 ∗
          spqrSendDropJumpTableAt b ∗ A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)) := by
  have hdealloc_raw : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc"))
      (rustDeallocSpec A) := sub_ok_of_addr_eq
    (Program.fnAddr_rel (k := num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_dealloc")) (b := b) (X := Rust.withPanics ext)
      spqrSend_fnOff (ls_stub% "__rustc::__rust_dealloc") (by decide))
    hdealloc
  simp only [rustDeallocSpec] at hdealloc_raw
  have hadrp := fnAddr_adrp_3218c (H := Rust.withPanics ext) hb
  spqr_send_fetches_range b (Rust.withPanics ext) 4592 8
  spqr_send_fetches_range b (Rust.withPanics ext) 6408 64
  spqr_send_fetches_range b (Rust.withPanics ext) 7220 52
  rw [spqrSendDropJumpTableAt_eq_expanded b]
  dsimp only [tripleRatchetProgAtExt, spqrSendName, optProtoInnerStateAt,
    protoInnerStateAt, protoChunkedKeysUnsampledAt,
    BitVec.ofNat_eq_ofNat] at hpc hdealloc_raw hadrp ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    "spqr::send::<libsignal_session::HookRng>" = entry
  examples_hide_fetches
  let a := s.sp + 4832#64
  have hjoin224 : (a ↦₆₄ 0x8000000000000000#64) ∗
      memRegion (a + 8#64) 56 ∗ memRegion (a + 64#64) 160 ⊢ memRegion a 224 :=
    tag_and_two_regions_entails_224 a 0x8000000000000000#64 56 160 64#64
      (BitVec.add_assoc a 8#64 56#64).symm rfl
  simp only [a, BitVec.add_assoc, BitVec.reduceAdd] at hjoin224
  cases huc : st.uc with
  | none =>
    dsimp only [optProtoUnchunkedKeysUnsampledAt, spqrSendDropJumpTableExpanded]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    wp_steps
    have hnone56 := optProtoUnchunkedNoHeaderReceivedAt_none_entails_memRegion_56 A (s.sp + 4840#64)
    dsimp only [optProtoUnchunkedNoHeaderReceivedAt] at hnone56
    simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone56
    refine SepWP.focus_weaken hnone56 (by sep_focus) ?_
    refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
    exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
      ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
        by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
  | some u =>
    dsimp only [optProtoUnchunkedKeysUnsampledAt, protoUnchunkedKeysUnsampledAt]
    cases hauth : u.auth with
    | none =>
      have hnone8 := optProtoAuthenticatorAt_8_none_entails_memRegion_56 A (s.sp + 4832#64) u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hnone8
      rw [optProtoAuthenticatorAt_none]
      dsimp only [spqrSendDropJumpTableExpanded]
      simp only [BitVec.add_assoc, BitVec.reduceAdd]
      wp_steps
      refine SepWP.focus_weaken hnone8 (by sep_focus) ?_
      refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
      exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
        ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
          by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
    | some auth =>
      rw [optProtoAuthenticatorAt_some]
      refine SepWP.focus_weaken (protoAuthenticatorAt_entails_dealloc A (s.sp + 4832#64 + 8#64) auth)
        (by sep_focus) ?_
      wp_pull_exists; rename_i ga; rw [twoVecHeadersAt_8_eq]
      wp_focus_pure; intro hga_lt
      have hne_none2 := Drop.cap_add_two_beq_zero_false hga_lt
      have hne_none1 := Drop.cap_add_one_beq_zero_false hga_lt
      have hhdr56 := auth8HeadersAt_entails_memRegion_56 (s.sp + 4832#64) ga u.epoch
      simp only [BitVec.add_assoc, BitVec.reduceAdd] at hhdr56 ⊢
      refine seq_clean (mid := entry + 7256#64)
        (P_mid := ((s.sp + 4832#64) ↦₆₄ 0x8000000000000000#64) ∗
          ((auth8HeadersAt (s.sp + 4832#64) ga ∗ vecCapPtrDealloc A ga.v2.cap ga.v2.ptr) ∗
            ((s.sp + 4888#64) ↦₆₄ u.epoch)) ∗
          memRegion (s.sp + 4896#64) 160 ∗
          spqrSendDropJumpTableExpanded b ∗
          A.pool ∗ stackAt s.sp spqrSendCalleeStack ∗ Frame)
        (Q := fun sm => sm.sp = s.sp ∧ sm.trace = s.trace ∧ sm.readReg64 .x23 = x23 ∧ calleeSavedVRegs sm = calleeSavedVRegs s)
        ?_ ?_
      · dsimp only [auth8HeadersAt, vecCapPtrDealloc, spqrSendDropJumpTableExpanded]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca1 : (ga.v1.cap == 0#64) = true <;>
          simp only [hca1, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (ga.v1.ptr, ga.v1.cap.toNat, 1)
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨Entails.of_eq (by ac_rfl),
              by wp_norm_goal, by wp_norm_goal, by wp_norm_goal, by wp_norm_goal⟩
      · intro s1 hpc1 hrun1 ⟨hsp1, htr1, hx23_1, hvregs1⟩
        have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rwa [hsp1]
        dsimp only [auth8HeadersAt, vecCapPtrDealloc]
        simp only [BitVec.add_assoc, BitVec.reduceAdd]
        by_cases hca2 : (ga.v2.cap == 0#64) = true <;>
          simp only [hca2, Bool.false_eq_true, ↓reduceIte, sepConj_emp, emp_sepConj]
        · wp_steps
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩
        · rw [send_stackAt_callee_eq_allocHook s.sp]
          wp_steps
          wp_call hdealloc_raw (ga.v2.ptr, ga.v2.cap.toNat, 1)
          rw [hsp1]
          refine SepWP.focus_weaken hhdr56 (by sep_focus) ?_
          refine SepWP.focus_weaken hjoin224 (by sep_focus) ?_
          exact ProofLib.SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
            ⟨by wp_norm_goal, by wp_norm_goal, by wp_norm_goal,
              by wp_norm_goal, by wp_norm_goal, Entails.of_eq (by ac_rfl)⟩

end CryptoVerification.SpqrV1.Top.Send
