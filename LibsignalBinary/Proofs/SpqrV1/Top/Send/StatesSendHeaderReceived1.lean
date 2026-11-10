/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.SpqrV1.Top.Send.StatesSendKeysUnsampled2
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.NewFromSliceInvariants
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntryEq
import LibsignalBinary.Proofs.TripleRatchet.Hkdf.ExtractCommon
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `spqr::send::<HookRng>`: Inlined `States::send` `.headerReceived` Arm (Part 1: `+1312..+1680`)

**Checked by Lean.**

Verifies the first half (`0x30d7c`, `entry + 1312#64 .. + 1680#64`) of the inlined
`.headerReceived` arm of `<States>::send`: RNG draw, `encapsulate1`, `hkdf_to_vec`, and
`<Authenticator>::update`.
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth CryptoVerification.SpqrV1.Kdf
open CryptoVerification.SpqrV1.GF.UnacceleratedMul CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Poly.NextChunk
open CryptoVerification.SpqrV1.Drop CryptoVerification.SpqrV1.States
open CryptoVerification.SpqrV1.States.Leaves CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "spqr::send::<libsignal_session::HookRng>")
  (ls_lemma% fnOff "spqr::kdf::hkdf_to_vec")
  (ls_lemma% fnOff "<spqr::authenticator::Authenticator>::update")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::encode_bytes")
  (ls_lemma% fnOff "<spqr::encoding::polynomial::PolyEncoder as spqr::encoding::Encoder>::next_chunk")
  (ls_stub% "libsignal_session_rng_fill")
  (ls_hook% "libsignal_session_rng_fill")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::encapsulate1")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::encapsulate1")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_alloc_zeroed")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "core::panicking::panic")
  (ls_stub% "core::result::unwrap_failed")

theorem spqrSend_hkdfToVec_ok {img : Obj.Image} {A : RustAlloc} {hkdf : HkdfFn}
    {ext : String → Option (State → State)}
    (h : HkdfToVecOkX img A hkdf ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "spqr::kdf::hkdf_to_vec"))
      ((hkdfToVecSpec A hkdf).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "spqr::kdf::hkdf_to_vec")) (by simp only [arm64_norm, spqrSendName, hkdfToVecName])

theorem spqrSend_authUpdate_ok {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (h : AuthUpdateOkX img F A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::update"))
      ((authUpdateSpec F A).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::update")) (by simp only [arm64_norm, spqrSendName, authUpdateName])

theorem spqrSend_hkdfToVec_ok_ext {img : Obj.Image} {A : RustAlloc} {hkdf : HkdfFn}
    {ext : String → Option (State → State)} (h : HkdfToVecOkExt img A hkdf ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "spqr::kdf::hkdf_to_vec"))
      ((hkdfToVecSpecExt A hkdf).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "spqr::kdf::hkdf_to_vec")) (by simp only [arm64_norm, spqrSendName, hkdfToVecName])

theorem spqrSend_authUpdate_ok_ext {img : Obj.Image} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)} (h : AuthUpdateOkExt img F A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::update"))
      ((authUpdateSpecExt F A).inImage img) :=
  sub_ok_at_of_fnAddr h spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::update")) (by simp only [arm64_norm, spqrSendName, authUpdateName])

theorem chunkedStatesAt_headerReceived_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedStatesAt A a (.headerReceived st) =
      ((a ↦₆₄ 8#64) ∗
       chunkedHeaderReceivedAt A (a + 8#64) st ∗
       memRegion (a + 488#64) 440) := by
  simp only [chunkedStatesAt, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

@[simp] theorem encaps1_ct1_len (K : MlKem) (hdr : Header) (rand : List.Vector (BitVec 8) 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (_h : K.encaps1 hdr rand = some (ct1, es, ss)) :
    ct1.toList.length = 960 :=
  List.Vector.toList_length _

@[simp] theorem encaps1_es_len (K : MlKem) (hdr : Header) (rand : List.Vector (BitVec 8) 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (_h : K.encaps1 hdr rand = some (ct1, es, ss)) :
    es.toList.length = 2080 :=
  List.Vector.toList_length _

@[simp] theorem encaps1_ss_len (K : MlKem) (hdr : Header) (rand : List.Vector (BitVec 8) 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (_h : K.encaps1 hdr rand = some (ct1, es, ss)) :
    ss.toList.length = 32 :=
  List.Vector.toList_length _

/-- Big-endian 8-byte encoding of an `Epoch` (`u64::to_be_bytes`). -/
def epochBeBytes (v : BitVec 64) : Bytes :=
  [ v.extractLsb' 56 8, v.extractLsb' 48 8, v.extractLsb' 40 8, v.extractLsb' 32 8,
    v.extractLsb' 24 8, v.extractLsb' 16 8, v.extractLsb'  8 8, v.extractLsb'  0 8 ]

theorem hkdfToVec_32_eq {F : ShaCompress} (salt ikm info : Bytes) :
    hkdfToVec F salt ikm info 32 = .ok (hkdfToVecUnchecked F salt ikm info 32) :=
  hkdfToSlice_of_le F salt ikm info (by decide)

theorem unchunkedSendCt1_of_ok {F : ShaCompress} (K : MlKem)
    (self : Unchunked.SendCt.HeaderReceived (spqrAuthApi F)) {tape : Bytes} (h : 32 ≤ tape.length)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (hencaps : K.encaps1 self.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = some (ct1, es, ss)) :
    let info := sckaKeyInfoPrefix ++ epochBeBytes self.epoch
    let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
    let auth' := self.auth.update F self.epoch secret
    let uc' : Unchunked.SendCt.Ct1Sent (spqrAuthApi F) :=
      { epoch := self.epoch, auth := auth', hdr := self.hdr, es := es.toList, ct1 := ct1.toList }
    self.send_ct1 K tape =
      .ok (uc', ct1.toList, { epoch := self.epoch, secret := secret }, tape.drop 32) := by
  dsimp only
  unfold Unchunked.SendCt.HeaderReceived.send_ct1
  rw [encaps1_of_le_32 K self.hdr h, hencaps]
  change (do
    let secret ← liftSpqrPanic (hkdfToVec F (List.replicate 32 0#8) ss.toList
      (sckaKeyInfoPrefix ++ epochBeBytes self.epoch) 32)
    let auth ← liftSpqrPanic (.ok (self.auth.update F self.epoch secret))
    Except.ok (({ epoch := self.epoch, auth := auth, hdr := self.hdr, es := es.toList, ct1 := ct1.toList } :
        Unchunked.SendCt.Ct1Sent (spqrAuthApi F)),
      ct1.toList, ({ epoch := self.epoch, secret := secret } : EpochSecret), tape.drop 32)) = _
  rw [hkdfToVec_32_eq]
  rfl

theorem send_ct1_chunk_of_ok {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) {tape : Bytes} (h : 32 ≤ tape.length)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    {sending_ct1 sending_ct1' : PolyEncoder} {chunk : Chunk}
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = some (ct1, es, ss))
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" ct1.toList = .ok sending_ct1)
    (hnc : sending_ct1.nextChunk = .ok (sending_ct1', chunk)) :
    let info := sckaKeyInfoPrefix ++ epochBeBytes st.uc.epoch
    let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
    let auth' := st.uc.auth.update F st.uc.epoch secret
    let uc' : Unchunked.SendCt.Ct1Sent (spqrAuthApi F) :=
      { epoch := st.uc.epoch, auth := auth', hdr := st.uc.hdr, es := es.toList, ct1 := ct1.toList }
    st.send_ct1_chunk K tape =
      .ok ({ uc := uc', sending_ct1 := sending_ct1', receiving_ek := st.receiving_ek },
        chunk, { epoch := st.uc.epoch, secret := secret }, tape.drop 32) := by
  dsimp only
  have hnc' : spqrPolyApi.next_chunk sending_ct1 = .ok (sending_ct1', chunk) := by
    change sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (sending_ct1', chunk)
    rw [hnc]; rfl
  unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk
  rw [unchunkedSendCt1_of_ok K st.uc h hencaps]
  simp only [henc, hnc', Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

theorem send_ct1_chunk_of_nextChunk_err {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) {tape : Bytes} (h : 32 ≤ tape.length)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    {sending_ct1 : PolyEncoder} {p : PolyPanic}
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = some (ct1, es, ss))
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" ct1.toList = .ok sending_ct1)
    (hnc : sending_ct1.nextChunk = .error p) :
    st.send_ct1_chunk K tape = .error (.spqr p.toSpqrPanic) := by
  have hnc' : spqrPolyApi.next_chunk sending_ct1 = .error p.toSpqrPanic := by
    change sending_ct1.nextChunk.mapError PolyPanic.toSpqrPanic = .error p.toSpqrPanic
    rw [hnc]; rfl
  unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk
  rw [unchunkedSendCt1_of_ok K st.uc h hencaps]
  simp only [henc, hnc', Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]


theorem chunkedHeaderReceivedAt_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) :
    chunkedHeaderReceivedAt A a st =
      (authenticatorAt A a st.uc.auth ∗
       vecU8 A (a + 48#64) st.uc.hdr ∗
       ((a + 72#64) ↦₆₄ st.uc.epoch) ∗
       polyDecoderAt A (a + 80#64) st.receiving_ek) := by
  simp only [chunkedHeaderReceivedAt, unchunkedHeaderReceivedAt,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem spqrSend_allocZeroed_ok {b : BitVec 64} {A : RustAlloc} {ext : String → Option (State → State)}
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed"))
      (rustAllocZeroedSpec A) :=
  alloc_zeroed_ok_at_ext b A ext hZero spqrSendName (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed"))
    (by simp only [arm64_norm, spqrSendName, allocZeroedName])

theorem spqrSend_unwrap_failed {b : BitVec 64} {ext : String → Option (State → State)} :
    (tripleRatchetProgAtExt b ext).externAt?
      ((tripleRatchetProgAtExt b ext).fnAddr spqrSendName + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::result::unwrap_failed")) = some Rust.panicked :=
  panic_at_sym_ext b ext spqrSendName "core::result::unwrap_failed" (num% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "core::result::unwrap_failed"))
    (by simp only [arm64_norm, spqrSendName]) (hp := by decide +kernel)

theorem zeroed_entails_memRegion (ptr : BitVec 64) (n : Nat) :
    (ptr ↦ₛ List.replicate n 0#8) ⊢ memRegion ptr n := by
  have h := pointsToBytes_entails_memRegion ptr (List.replicate n 0#8)
  rwa [List.length_replicate] at h

theorem call_rustAllocZeroed_inImage {A : RustAlloc} {prog : Program} {img : Obj.Image}
    {entry_alloc ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry_alloc (rustAllocZeroedSpec A))
    (size : Nat) (hlay : LayoutOk size 1)
    {s0 s : State} {sp_call : BitVec 64} {P Frame R : SepProp}
    {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hpc : s.pc = entry_alloc)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (htrace : s.trace = s0.trace)
    (hx0 : (s.readReg64 Reg.x0).toNat = size)
    (hx1 : (s.readReg64 Reg.x1).toNat = 1)
    (hsplit : P = (A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame)
    (hoom : ∀ sf : State, ImgCallInv img sf →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) = 0 →
      sf.trace = s0.trace ++ [allocFailedEvent] →
      SepWPp prog target_pc sf
        ((A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)))
    (hok : ∀ sf : State, ImgCallInv img sf →
      sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → CalleeSavedPreserved s sf →
      sf.readReg64 (Reg.gpr 0#5) ≠ 0 →
      (sf.readReg64 (Reg.gpr 0#5) == 0#64) = false →
      sf.trace = s0.trace →
      SepWPp prog target_pc sf
        ((A.live (sf.readReg64 (Reg.gpr 0#5)) size 1 ∗
          memRegion (sf.readReg64 (Reg.gpr 0#5)) size ∗
          A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp prog target_pc s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  rw [hsplit]
  refine of_sepWP_inImage (mid := ret_pc) img hinv ?_
  refine SepWP.fold (stackAt_spqrSendCallee_to_allocHook sp_call) (by sep_focus) ?_
  refine SepWP.call_subroutine_frame hcall (x := (size, 1))
    (F := memRegion (sp_call - 123008#64) 118912 ∗ Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf1 hpc1 hrun1 hsp1 hcs1 => ?_)
  · intro R' hm
    dsimp only [rustAllocZeroedSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    rw [show ((memRegion (sp_call - 123008#64) 118912 ∗ stackAt sp_call allocHookStack) ∗ A.pool ∗ Frame) ∗ R' =
        (A.pool ∗ stackAt sp_call allocHookStack) ∗ (memRegion (sp_call - 123008#64) 118912 ∗ Frame) ∗ R' by ac_rfl] at hm
    exact ⟨⟨hx0, hx1, hlay⟩, hm⟩
  · dsimp only [rustAllocZeroedSpec]
    rw [hsp, htrace]
    refine SepWP.fold (stackAt_spqrSendCallee_from_allocHook sp_call) (by sep_focus) ?_
    apply SepWP.done hpc1 hrun1
    intro hinv1
    by_cases h0 : sf1.readReg64 (Reg.gpr 0#5) = 0
    · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
      have hassoc :
          stackAt sp_call spqrSendCalleeStack ∗
            A.pool ∗ ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗ Frame =
          ⌜sf1.trace = s0.trace ++ [allocFailedEvent]⌝ ∗
            ((A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
      rw [hassoc]
      refine ProofLib.SepWPp.pure_elim fun htr_oom => ?_
      exact hoom sf1 hinv1 hpc1 hrun1 (hsp1.trans hsp) hcs1 h0 htr_oom
    · conv => arg 4; simp only [Reg.x0, h0, ↓reduceIte, sepConj_assoc]
      have hassoc :
          stackAt sp_call spqrSendCalleeStack ∗
            A.pool ∗
            ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
            A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ List.replicate size 0#8) ∗
            Frame =
          ⌜(sf1.readReg64 (Reg.gpr 0#5)).toNat % 1 = 0 ∧ sf1.trace = s0.trace⌝ ∗
            ((A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
              (sf1.readReg64 (Reg.gpr 0#5) ↦ₛ List.replicate size 0#8) ∗
              A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame) := by ac_rfl
      rw [hassoc]
      refine ProofLib.SepWPp.pure_elim fun htr_ok => ?_
      have h0b : (sf1.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne h0
      refine of_sepWP_inImage (mid := ret_pc) img hinv1 ?_
      refine SepWP.fold (zeroed_entails_memRegion (sf1.readReg64 (Reg.gpr 0#5)) size) (by sep_focus) ?_
      apply SepWP.done hpc1 hrun1
      intro hinv2
      have hframe :
          memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
            A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            A.pool ∗ stackAt sp_call spqrSendCalleeStack ∗ Frame =
          (A.live (sf1.readReg64 (Reg.gpr 0#5)) size 1 ∗
            memRegion (sf1.readReg64 (Reg.gpr 0#5)) size ∗
            A.pool ∗ stackAt sp_call spqrSendCalleeStack) ∗ Frame := by ac_rfl
      rw [hframe]
      exact hok sf1 hinv2 hpc1 hrun1 (hsp1.trans hsp) hcs1 h0 h0b htr_ok.2

/-- Residual heap ownership of `vecU8At A a cap ptr bs` after borrowing `(ptr ↦ₛ bs)`. -/
def vecU8Rest (A : RustAlloc) (cap ptr : BitVec 64) (bs : Bytes) : SepProp :=
  ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
  if cap = 0 then emp
  else
    A.live ptr cap.toNat 1 ∗
    memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)

theorem vecU8At_expose_rest {A : RustAlloc} (a cap ptr : BitVec 64) (bs : Bytes) :
    vecU8At A a cap ptr bs ⊢
    ⌜bs.length < 2 ^ 63⌝ ∗
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
    (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs := by
  unfold vecU8At vecHeader vecU8Rest
  by_cases hc : cap = 0#64
  · subst hc
    simp only [show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte,
      show (0 : BitVec 64).toNat = 0 from rfl, sepConj_emp, sepConj_assoc]
    have hcomm :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    simp only [pointsToBytes_nil, sepConj_emp, emp_sepConj, List.length_nil]
    refine Entails.pure_right hlt ?_
    have hcomm2 :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0)) := by ac_rfl
    rw [hcomm2]
    exact Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _)
  · have hc0 : cap ≠ 0 := hc
    simp only [hc0, ↓reduceIte, sepConj_assoc]
    have hcomm :
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    refine Entails.pure_right (by omega) ?_
    have hcomm2 :
        (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        A.live ptr cap.toNat 1 ∗
        memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) =
        ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
         (ptr ↦ₛ bs) ∗ A.live ptr cap.toNat 1 ∗
         memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length)) := by ac_rfl
    rw [hcomm2]
    exact Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _)

theorem vecU8_fold_rest {A : RustAlloc} (a cap ptr : BitVec 64) (bs : Bytes) :
    (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      (ptr ↦ₛ bs) ∗ vecU8Rest A cap ptr bs ⊢
    vecU8 A a bs := by
  unfold vecU8
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader vecU8Rest
  by_cases hc : cap = 0#64
  · subst hc
    simp only [show (0#64 : BitVec 64) = 0 from rfl, ↓reduceIte,
      show (0 : BitVec 64).toNat = 0 from rfl, sepConj_emp, sepConj_assoc]
    have hcomm :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜bs.length ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) := by ac_rfl
    rw [hcomm]
    refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
    have hbs : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hbs
    simp only [pointsToBytes_nil, sepConj_emp, List.length_nil]
    have hcomm2 :
        (a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0) ∗
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ =
        ⌜0 ≤ 0 ∧ 0 < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
        ((a ↦₆₄ 0) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ ((a + 16#64) ↦₆₄ BitVec.ofNat 64 0)) := by ac_rfl
    rw [hcomm2]
    exact Entails.pure_right ⟨hle, hlt, hp⟩ (Entails.refl _)
  · have hc0 : cap ≠ 0 := hc
    simp only [hc0, ↓reduceIte]
    exact Entails.of_eq (by ac_rfl)

theorem exists_words4_of_len32 (bs : List (BitVec 8)) (h : bs.length = 32) :
    ∃ w0 w1 w2 w3 : BitVec 64, ∀ a : BitVec 64,
      (a ↦ₛ bs) = words4At a w0 w1 w2 w3 := by
  obtain ⟨w0, w1, w2, w3, hw⟩ :=
    CryptoVerification.SpqrV1.Top.MessageSerialize.list_eq_unpack64_4_of_len32 bs h
  refine ⟨w0, w1, w2, w3, fun a => ?_⟩
  rw [hw, CryptoVerification.SpqrV1.Top.MessageSerialize.pointsToBytes_unpack64_4_eq a]
  rfl

/-- Sub-step 1a (`entry + 1312#64 -> entry + 1504#64`) on `K.encaps1 = some (ct1, es, ss)`:
    copies `epoch` and inline `Authenticator` words, fills 32-byte `rand` via `rng_fill`,
    allocates 2080-byte `es` buffer and 32-byte `ss` buffer via `__rust_alloc_zeroed`,
    calls `encapsulate1`, and steps through the `Ok` tag check to `entry + 1504#64`. -/
theorem step_headerReceived_1312_to_1504
    {img : Obj.Image} {K : MlKem} {A : RustAlloc} {ctl : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hZero : HookSat ext allocZeroedName (rustAllocZeroedSpec A))
    (hrng : HookSat ext rngFillName (rngFillSpec ctl))
    (henc1 : HookSat ext mlkemEncaps1Name (mlkemEncaps1Spec K))
    (g : AuthenticatorGhost) (auth : Authenticator) (epoch : BitVec 64)
    (hdr_cap hdr_ptr : BitVec 64) (hdr : Bytes) (hhdr_lt : hdr.length < 2 ^ 63)
    (sp cur : BitVec 64) (tape : List (BitVec 8))
    (h32 : 32 ≤ tape.length)
    (rand : List.Vector (BitVec 8) 32)
    (hrand_val : rand.toList = tape.take 32)
    {ct1 : List.Vector (BitVec 8) 960} {es : List.Vector (BitVec 8) 2080} {ss : List.Vector (BitVec 8) 32}
    (hencaps : K.encaps1 hdr rand = some (ct1, es, ss))
    (d4056 : BitVec 64)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1312#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hx24 : s.readReg64 .x24 = sp + 2384#64)
    (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx28 : s.readReg64 .x28 = sp + 4192#64)
    (htrace : s.trace = s0.trace)
    (hP : P = (
      authInlineWordsAt g (sp + 2392#64) auth ∗
      authHeapBufs A g auth ∗
      ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
      ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
      ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
      (hdr_ptr ↦ₛ hdr) ∗
      ((sp + 2464#64) ↦₆₄ epoch) ∗
      ((sp + 4056#64) ↦₆₄ d4056) ∗
      memRegion (sp + 4192#64) 48 ∗
      memRegion (sp + 4704#64) 961 ∗
      memRegion (sp + 7136#64) 32 ∗
      memRegion (sp + 7536#64) 32 ∗
      tapeAt ctl cur tape ∗
      A.pool ∗
      stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (es_ptr ss_ptr : BitVec 64),
      ImgCallInv img sf →
      es_ptr ≠ 0 → (es_ptr == 0#64) = false →
      ss_ptr ≠ 0 → (ss_ptr == 0#64) = false →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1504#64 →
      sf.status = .Running →
      sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 →
      sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr →
      sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 →
      sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = hdr_cap →
      sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length →
      sf.readReg64 .x28 = sp + 4192#64 →
      sf.trace = s0.trace →
      calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((authInlineWordsAt g (sp + 4192#64) auth ∗
          authHeapBufs A g auth ∗
          authInlineWordsAt g (sp + 2392#64) auth ∗
          ((sp + 2440#64) ↦₆₄ hdr_cap) ∗
          ((sp + 2448#64) ↦₆₄ hdr_ptr) ∗
          ((sp + 2456#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗
          (hdr_ptr ↦ₛ hdr) ∗
          ((sp + 2464#64) ↦₆₄ epoch) ∗
          ((sp + 4056#64) ↦₆₄ epoch) ∗
          ((sp + 4704#64) ↦₈ 0#8) ∗
          ((sp + 4705#64) ↦ₛ ct1.toList) ∗
          RustHeap.vecU8Buf A 2080#64 es_ptr es.toList ∗
          A.live ss_ptr 32 1 ∗
          (ss_ptr ↦ₛ ss.toList) ∗
          memRegion (sp + 7136#64) 32 ∗
          memRegion (sp + 7536#64) 32 ∗
          tapeAfter ctl cur tape 32 ∗
          A.pool ∗
          stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := spqrSend_shim_ok hA
  have hallocz := spqrSend_allocZeroed_ok (b := img.base) hZero
  have hrng_call := spqrSend_rngFill_ok (b := img.base) hrng
  have henc1_call := spqrSend_encapsulate1_ok (b := img.base) henc1
  have haerr := spqrSend_handle_error (b := img.base) (ext := ext)
  have hhdr_toNat : (BitVec.ofNat 64 hdr.length).toNat = hdr.length := Nat.mod_eq_of_lt (by omega)
  have hes_len : es.toList.length = 2080 := List.Vector.toList_length _
  spqr_send_fetches_range img.base (Rust.withPanics ext) 1312 192
  spqr_send_fetches_range img.base (Rust.withPanics ext) 13588 48
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  examples_hide_fetches; subst hP
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed")) img hinv
  rw [memRegion_48_eq_words6 (sp + 4192#64),
      memRegion_32_eq_words4 (sp + 7136#64),
      memRegion_32_eq_words4 (sp + 7536#64)]
  dsimp only [authInlineWordsAt]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 14 (apply SepWP.exists_elim; intro _)
  wp_steps
  refine SepWP.fold (words4At_entails_memRegion (sp + 7136#64) _ _ _ _)
    (by dsimp only [words4At]; sep_focus) ?_
  wp_apply
  wp_conv_pre => rw [List.take_append_of_le_length h32, Nat.min_eq_left h32, ← hrand_val]
  wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  refine call_rustAllocZeroed_inImage hallocz 2080 ⟨by decide, ⟨0, rfl⟩, by decide⟩
    (s0 := s0) (ret_pc := entry + 1400#64) (sp_call := sp) hinv1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hinv_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
    (fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
  · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc_zeroed")) img hinv_ok1
    wp_steps; wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hinv2
    refine call_rustAllocZeroed_inImage hallocz 32 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      (s0 := s0) (ret_pc := entry + 1424#64) (sp_call := sp) hinv2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf2 hinv_oom2 hpc2 hrun2 hsp2 _ h0_2 htr_oom2 => ?_)
      (fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
    · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [arm64_norm, *])
    · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply of_sepWP_inImage (mid := entry + 1504#64) img hinv_ok2
      obtain ⟨rw0, rw1, rw2, rw3, hrand_words⟩ :=
        exists_words4_of_len32 rand.toList (List.Vector.toList_length rand)
      wp_conv_pre => rw [hrand_words (sp + 7136#64)]; dsimp only [words4At]
      wp_steps
      have hfold_rand_7536 :
          words4At (sp + 7536#64) rw0 rw1 rw2 rw3 ⊢ ((sp + 7536#64) ↦ₛ rand.toList) := by
        rw [hrand_words (sp + 7536#64)]
        exact Entails.refl _
      refine SepWP.fold hfold_rand_7536 (by dsimp only [words4At]; sep_focus) ?_
      refine SepWP.fold (stackAt_spqrSendCallee_to_extHook sp) (by sep_focus) ?_
      wp_apply
      wp_conv_pre => simp only [hencaps, sepConj_assoc]
      wp_steps
      refine SepWP.fold (stackAt_spqrSendCallee_from_extHook sp)
        (by simp only [hsp2]; sep_focus) ?_
      have hfold_end :
          words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗
          ((sp + 7536#64) ↦ₛ rand.toList) ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 2080 1 ∗
          ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ es.toList) ⊢
          memRegion (sp + 7136#64) 32 ∗
          memRegion (sp + 7536#64) 32 ∗
          RustHeap.vecU8Buf A 2080#64 (sf1.readReg64 (Reg.gpr 0#5)) es.toList := by
        have h7536 := pointsToBytes_entails_memRegion (sp + 7536#64) rand.toList
        rw [List.Vector.toList_length] at h7536
        have hes_buf := live_pointsTo_entails_vecU8Buf (A := A) (sf1.readReg64 (Reg.gpr 0#5)) es.toList
          2080 hes_len (by decide) (by decide) hne0_1
        rw [show words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗ ((sp + 7536#64) ↦ₛ rand.toList) ∗
              A.live (sf1.readReg64 (Reg.gpr 0#5)) 2080 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ es.toList) =
            words4At (sp + 7136#64) rw0 rw1 rw2 rw3 ∗ ((sp + 7536#64) ↦ₛ rand.toList) ∗
            (A.live (sf1.readReg64 (Reg.gpr 0#5)) 2080 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ es.toList)) by ac_rfl]
        exact sepConj_mono (words4At_entails_memRegion (sp + 7136#64) rw0 rw1 rw2 rw3)
          (sepConj_mono h7536 hes_buf)
      refine SepWP.fold hfold_end
        (by dsimp only [words4At]; sep_focus) ?_
      refine finish_sepWP_inImage (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (fun hinv3 => hnext _ (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5))
          hinv3 hne0_1 h0b_1 hne0_2 h0b_2
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, arm64_norm, *])
          (by simp only [Reg.x19, arm64_norm, *])
          (by simp only [Reg.x20, arm64_norm, *])
          (by simp only [Reg.x21, arm64_norm, *])
          (by simp only [Reg.x22, arm64_norm, *])
          (by simp only [Reg.x23, arm64_norm, *])
          (by simp only [Reg.x24, arm64_norm, *])
          (by simp only [Reg.x25, arm64_norm, *])
          (by simp only [Reg.x26, arm64_norm, *])
          (by simp only [Reg.x27, arm64_norm, *])
          (by simp only [Reg.x28, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]))
        (by dsimp only [authInlineWordsAt]; simp only [BitVec.add_assoc, arm64_norm]; exact Entails.of_eq (by ac_rfl))

theorem rodata_sckaKeyInfoPrefix {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x30f68 0x30f6c)) ↦ᵣ sckaKeyInfoPrefix) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x30f68 0x30f6c)) (n := 33) (bs := sckaKeyInfoPrefix)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_zeros32 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x30f98 0x30f9c)) ↦ᵣ List.replicate 32 0#8) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x30f98 0x30f9c)) (n := 32) (bs := List.replicate 32 0#8)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem sepWPp_intro_rodata {prog : Program} {ret : BitVec 64} {s : State}
    {roAddr : BitVec 64} {roBytes : List (BitVec 8)} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → (s.mem ⊨ (roAddr ↦ᵣ roBytes) ∗ R))
    (h : SepWPp prog ret s ((roAddr ↦ᵣ roBytes) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hPR hL
  apply h R ?_ hL
  rw [sepConj_assoc]
  exact hro hPR

theorem finish_sepWP_inImage_drop_ro {prog : Program} {img : Obj.Image} {mid ret : BitVec 64}
    {s : State} {P P' Ro : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = mid) (hrun : s.status = .Running)
    (hnext : ImgCallInv img s → SepWPp prog ret s P' Q Qp)
    (himp : P ⊢ Ro ∗ P') :
    SepWP prog mid s P (fun sf P_f => ImgCallInv img sf → SepWPp prog ret sf P_f Q Qp) := by
  refine SepWP.fold himp (sepConj_emp _).symm ?_
  rw [sepConj_emp]
  apply SepWP.done hpc hrun
  intro hinv R hsat hL
  apply hnext hinv R ?_ hL
  rw [sepConj_assoc] at hsat
  exact Satisfies.of_sep_right hsat

def sckaInfoW0 : BitVec 64 := 0x505f6c616e676953#64
def sckaInfoW1 : BitVec 64 := 0x5f31565f414b4351#64
def sckaInfoW2 : BitVec 64 := 0x3836374d454b4c4d#64
def sckaInfoW3 : BitVec 64 := 0x654b20414b43533a#64

theorem sckaKeyInfoPrefix_eq_unpack64 :
    sckaKeyInfoPrefix =
      unpack64 sckaInfoW0 ++
        (unpack64 sckaInfoW1 ++
          (unpack64 sckaInfoW2 ++
            (unpack64 sckaInfoW3 ++ [0x79#8]))) := by
  rfl_kernel

theorem unpack64_rev64_eq_epochBeBytes (v : BitVec 64) :
    unpack64 (Arm64.rev64 v) = epochBeBytes v :=
  unpack64_rev64_eq_toBEBytes v

theorem rodata_sckaInfoW0 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% (ls_xref% 0x30f68 0x30f6c)) ↦₆₄ᵣ sckaInfoW0) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% (ls_xref% 0x30f68 0x30f6c)) (n := 8) (bs := unpack64 sckaInfoW0)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_sckaInfoW1 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% ((ls_xref% 0x30f68 0x30f6c) + 8)) ↦₆₄ᵣ sckaInfoW1) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% ((ls_xref% 0x30f68 0x30f6c) + 8)) (n := 8) (bs := unpack64 sckaInfoW1)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_sckaInfoW2 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% ((ls_xref% 0x30f68 0x30f6c) + 16)) ↦₆₄ᵣ sckaInfoW2) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% ((ls_xref% 0x30f68 0x30f6c) + 16)) (n := 8) (bs := unpack64 sckaInfoW2)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem rodata_sckaInfoW3 {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} (hF : img.FrozenLoaded s) {P : SepProp} (hP : s.mem ⊨ P) :
    s.mem ⊨ ((img.base + bv% ((ls_xref% 0x30f68 0x30f6c) + 24)) ↦₆₄ᵣ sckaInfoW3) ∗ P := by
  have hhb := loads_rodata_holdsBytes himg hF
    (off := num% ((ls_xref% 0x30f68 0x30f6c) + 24)) (n := 8) (bs := unpack64 sckaInfoW3)
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel)
    (by rfl_kernel) (by decide) (by rfl_kernel)
  have ⟨h1, h2⟩ := holdsBytes_ro hhb
  rw [pointsTo64RO_eq_pointsToBytesRO]
  exact Satisfies.rodata_intro h1 h2 (by decide) hP

theorem sepWPp_intro_rodata64 {prog : Program} {ret : BitVec 64} {s : State}
    {roAddr : BitVec 64} {w : BitVec 64} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hro : ∀ {R : SepProp}, (s.mem ⊨ R) → (s.mem ⊨ (roAddr ↦₆₄ᵣ w) ∗ R))
    (h : SepWPp prog ret s ((roAddr ↦₆₄ᵣ w) ∗ P) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hPR hL
  apply h R ?_ hL
  rw [sepConj_assoc]
  exact hro hPR

theorem memRegion_41_eq_infoSlots (a : BitVec 64) :
    memRegion a 41 =
      (∃∗ d0 : BitVec 64, a ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (a + 8#64) ↦₆₄ d1) ∗
      (∃∗ d2 : BitVec 64, (a + 16#64) ↦₆₄ d2) ∗
      (∃∗ d3 : BitVec 64, (a + 24#64) ↦₆₄ d3) ∗
      (∃∗ b32 : BitVec 8, (a + 32#64) ↦₈ b32) ∗
      (∃∗ d33 : BitVec 64, (a + 33#64) ↦₆₄ d33) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 32) (k := 9) (b' := a + 32#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 1) (k := 8) (b' := a + 33#64) rfl (by bv_omega) (by decide),
      memRegion_32_eq_words4 a,
      ProofLib.memRegion_one (a + 32#64),
      ProofLib.memRegion_eight (a + 33#64)]
  ac_rfl

theorem infoSlots_entails_pointsToBytes (a epoch : BitVec 64) :
    (a ↦₆₄ sckaInfoW0) ∗
      ((a + 8#64) ↦₆₄ sckaInfoW1) ∗
      ((a + 16#64) ↦₆₄ sckaInfoW2) ∗
      ((a + 24#64) ↦₆₄ sckaInfoW3) ∗
      ((a + 32#64) ↦₈ 0x79#8) ∗
      ((a + 33#64) ↦₆₄ Arm64.rev64 epoch) ⊢
    (a ↦ₛ (sckaKeyInfoPrefix ++ epochBeBytes epoch)) := by
  rw [sckaKeyInfoPrefix_eq_unpack64]
  simp only [List.append_assoc, List.singleton_append]
  rw [pointsToBytes_append a (unpack64 sckaInfoW0), unpack64_length,
      pointsToBytes_append (a + 8#64) (unpack64 sckaInfoW1), unpack64_length,
      show (a + 8#64) + 8#64 = a + 16#64 by bv_omega,
      pointsToBytes_append (a + 16#64) (unpack64 sckaInfoW2), unpack64_length,
      show (a + 16#64) + 8#64 = a + 24#64 by bv_omega,
      pointsToBytes_append (a + 24#64) (unpack64 sckaInfoW3), unpack64_length,
      show (a + 24#64) + 8#64 = a + 32#64 by bv_omega,
      pointsToBytes_cons (a + 32#64) 0x79#8,
      show (a + 32#64) + 1#64 = a + 33#64 by bv_omega,
      ← unpack64_rev64_eq_epochBeBytes epoch,
      ← pointsTo64_eq_pointsToBytes a sckaInfoW0,
      ← pointsTo64_eq_pointsToBytes (a + 8#64) sckaInfoW1,
      ← pointsTo64_eq_pointsToBytes (a + 16#64) sckaInfoW2,
      ← pointsTo64_eq_pointsToBytes (a + 24#64) sckaInfoW3,
      ← pointsTo64_eq_pointsToBytes (a + 33#64) (Arm64.rev64 epoch)]
  exact Entails.of_eq (by ac_rfl)

theorem fnAddr_adrp_30e84 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 1576#64) &&&
      0xfffffffffffff000#64) = b + page% ((ls_off% "spqr::send::<libsignal_session::HookRng>") + 1576) := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

theorem fnAddr_adrp_30eb4 {b : BitVec 64} {H : String → Option (State → State)}
    (hb : b &&& 0xfff#64 = 0#64) :
    (((libsignalSessionCode.rebase b H).fnAddr spqrSendName + 1624#64) &&&
      0xfffffffffffff000#64) = b + page% ((ls_off% "spqr::send::<libsignal_session::HookRng>") + 1624) := by
  rw [Program.fnAddr_rebase, spqrSend_fnOff]
  revert hb; bv_bits

theorem memRegion_32_split_24_8 (a : BitVec 64) :
    memRegion a 32 = memRegion a 24 ∗ memRegion (a + 24#64) 8 :=
  ProofLib.memRegion_split' (b := a) (n := 24) (k := 8) (b' := a + 24#64) rfl rfl (by decide)

theorem memRegion_32_16_eq_words2 (sp : BitVec 64) :
    memRegion (sp + 32#64) 16 =
      (∃∗ d0 : BitVec 64, (sp + 32#64) ↦₆₄ d0) ∗
      (∃∗ d1 : BitVec 64, (sp + 40#64) ↦₆₄ d1) := by
  rw [ProofLib.memRegion_split' (b := sp + 32#64) (n := 8) (k := 8) (b' := sp + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp + 32#64), ProofLib.memRegion_eight (sp + 40#64)]

/-! ## Sub-Step 2 (`entry + 1504#64 -> entry + 1680#64`) -/

theorem pointsTo8_and_ct1_entails_memRegion_961 (sp : BitVec 64) (b0 : BitVec 8)
    (ct1 : List.Vector (BitVec 8) 960) :
    ((sp + 4704#64) ↦₈ b0) ∗ ((sp + 4705#64) ↦ₛ ct1.toList) ⊢ memRegion (sp + 4704#64) 961 := by
  have h1 : ((sp + 4704#64) ↦₈ b0) ⊢ memRegion (sp + 4704#64) 1 := by
    rw [ProofLib.memRegion_one (sp + 4704#64)]
    exact ProofLib.Entails.sepExists_intro b0
  have h2 := pointsToBytes_entails_memRegion (sp + 4705#64) ct1.toList
  rw [List.Vector.toList_length] at h2
  rw [ProofLib.memRegion_split' (b := sp + 4704#64) (n := 1) (k := 960) (b' := sp + 4705#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono h1 h2

theorem fold_authenticatorAt_of_inline_local (A : RustAlloc) (g : AuthenticatorGhost)
    (a : BitVec 64) (auth : Authenticator) :
    authInlineWordsAt g a auth ∗ authHeapBufs A g auth ⊢ authenticatorAt A a auth := by
  rw [← authenticatorPinAt_eq_inline_heap A g a auth]
  exact authenticatorPinAt_entails_authenticatorAt A g a auth

theorem sp_add_4704_orr_1_eq {sp : BitVec 64} (hsp : (sp &&& 15#64 == 0#64) = true) :
    ((sp + 4704#64) ||| 1#64) = sp + 4705#64 := by
  have hsp' : sp &&& 15#64 = 0#64 := eq_of_beq hsp
  revert hsp'; bv_bits

theorem epochBeBytes_length (v : BitVec 64) : (epochBeBytes v).length = 8 := rfl

theorem vecU8_len32_expose_7536 {A : RustAlloc} (sp : BitVec 64) (bs : Bytes) (hlen : bs.length = 32) :
    vecU8 A (sp + 7536#64) bs ⊢
    (∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0 ∧ (cap == 0#64) = false⌝ ∗
      (((sp + 7536#64) ↦₆₄ cap) ∗
       ((sp + 7544#64) ↦₆₄ ptr) ∗
       ((sp + 7552#64) ↦₆₄ 32#64) ∗
       A.live ptr cap.toNat 1 ∗
       (ptr ↦ₛ bs) ∗
       memRegion (ptr + 32#64) (cap.toNat - 32))) := by
  unfold vecU8
  apply ProofLib.Entails.sepExists_elim; intro cap
  apply ProofLib.Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  unfold vecU8At vecHeader
  rw [hlen, show (sp + 7536#64) + 8#64 = sp + 7544#64 by bv_omega,
      show (sp + 7536#64) + 16#64 = sp + 7552#64 by bv_omega,
      show BitVec.ofNat 64 32 = 32#64 from rfl]
  have hcomm :
      (((sp + 7536#64) ↦₆₄ cap) ∗ ((sp + 7544#64) ↦₆₄ ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64)) ∗
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ memRegion (ptr + 32#64) (cap.toNat - 32)) =
      ⌜32 ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0⌝ ∗
      (((sp + 7536#64) ↦₆₄ cap) ∗ ((sp + 7544#64) ↦₆₄ ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ (ptr ↦ₛ bs) ∗ memRegion (ptr + 32#64) (cap.toNat - 32))) := by
    ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hlt, hp⟩ => ?_
  have hc : cap ≠ 0 := by intro h0; subst h0; revert hle; decide
  simp only [hc, ↓reduceIte]
  exact Entails.pure_right ⟨hle, hlt, hp, beq_false_of_ne hc⟩ (Entails.of_eq (by ac_rfl))

theorem step_headerReceived_1504_to_1680_ext {F : ShaCompress}
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (halign : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext)
    (hhkdf : HkdfToVecOkExt img A (hkdfToVecUnchecked F) ext) (hupd : AuthUpdateOkExt img F A ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ss_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator) (hdr : Header)
    (ct1 : List.Vector (BitVec 8) 960) (ss : List.Vector (BitVec 8) 32)
    (hroot_len : auth.rootKey.length + 32 < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1504#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = hdr_cap) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length) (htrace : s.trace = s0.trace)
    (hP : P = (
      memRegion (sp + 32#64) 16 ∗ authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 4704#64) ↦₈ 0#8) ∗ ((sp + 4705#64) ↦ₛ ct1.toList) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7536#64) 32 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (ct1_ptr info_ptr secret_cap secret_ptr : BitVec 64),
      let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      let auth' := auth.update F epoch secret
      ImgCallInv img sf →
      ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false → info_ptr ≠ 0 → (info_ptr == 0#64) = false →
      secret_ptr ≠ 0 → (secret_cap == 0#64) = false → 32 ≤ secret_cap.toNat → secret_cap.toNat < 2 ^ 63 →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1680#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length → sf.readReg64 .x28 = info_ptr →
      sf.trace = s0.trace → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authenticatorAt A (sp + 4192#64) auth' ∗ memRegion (sp + 4704#64) 961 ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) := by
  have hshim := spqrSend_shim_ok hA
  have halloc := spqrSend_alloc_ok hA
  have hmemcpy := spqrSend_memcpy_region_ok hA
  have haerr := spqrSend_handle_error (b := img.base) (ext := ext)
  have hct1_len : ct1.toList.length = 960 := List.Vector.toList_length _
  have hss_len : ss.toList.length = 32 := List.Vector.toList_length _
  have hadrp_e84 := fnAddr_adrp_30e84 (H := Rust.withPanics ext) halign
  have hadrp_eb4 := fnAddr_adrp_30eb4 (H := Rust.withPanics ext) halign
  spqr_send_fetches_range img.base (Rust.withPanics ext) 1504 180
  spqr_send_fetches_range img.base (Rust.withPanics ext) 13564 88
  generalize_entry hentry : (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName = entry
  have hhkdf_call := spqrSend_hkdfToVec_ok_ext hhkdf
  have hupd_call := spqrSend_authUpdate_ok_ext hupd
  rw [hentry] at hhkdf_call hupd_call
  examples_hide_fetches; subst hP
  simp only [Reg.x20, Reg.x21, Reg.x22, Reg.x24, Reg.x25, Reg.x26, Reg.x27]
    at hx20 hx21 hx22 hx24 hx25 hx26 hx27
  apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc")) img hinv
  rw [memRegion_32_16_eq_words2 sp]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  iterate 2 (apply SepWP.exists_elim; intro _)
  wp_steps; wp_apply; wp_steps
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  intro hinv1
  refine call_rustAlloc_inImage halloc 960 ⟨by decide, ⟨0, rfl⟩, by decide⟩
    (s0 := s0) (ret_pc := entry + 1524#64) (sp_call := sp) hinv1
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hinv_oom1 hpc1 hrun1 hsp1 _ h0_1 htr_oom1 => ?_)
    (fun sf1 hinv_ok1 hpc1 hrun1 hsp1 hcs1 hne0_1 h0b_1 htr_ok1 => ?_)
  · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom1
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro _
    exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [arm64_norm, *])
  · rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
    simp only [wp_norm, arm64_norm, *] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1 hvregs_1
    apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "__rustc::__rust_alloc")) img hinv_ok1
    have hct1_mem : memRegion (sf1.readReg64 (Reg.gpr 0#5)) 960 =
        memRegion (sf1.readReg64 (Reg.gpr 0#5)) ct1.toList.length := by rw [hct1_len]
    wp_conv_pre => rw [hct1_mem, ← sp_add_4704_orr_1_eq hsp_align]
    wp_steps; wp_apply; wp_steps
    wp_conv_pre => rw [sp_add_4704_orr_1_eq hsp_align]
    refine SepWP.fold (pointsTo8_and_ct1_entails_memRegion_961 sp 0#8 ct1) (by sep_focus) ?_
    wp_apply; wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    intro hinv2
    refine call_rustAlloc_inImage halloc 41 ⟨by decide, ⟨0, rfl⟩, by decide⟩
      (s0 := s0) (ret_pc := entry + 1572#64) (sp_call := sp) hinv2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, arm64_norm, *]) hsp_align
      (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
      (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
      (by sep_focus)
      (fun sf2 hinv_oom2 hpc2 hrun2 hsp2 _ h0_2 htr_oom2 => ?_)
      (fun sf2 hinv_ok2 hpc2 hrun2 hsp2 hcs2 hne0_2 h0b_2 htr_ok2 => ?_)
    · apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "alloc::raw_vec::handle_error")) img hinv_oom2
      wp_steps
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      intro _
      exact finish_oom_panic (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [arm64_norm, *])
    · rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
      simp only [wp_norm, arm64_norm, *] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2 hvregs_2
      apply sepWPp_intro_rodata64 (rodata_sckaInfoW0 himg hinv_ok2.1)
      apply sepWPp_intro_rodata64 (rodata_sckaInfoW1 himg hinv_ok2.1)
      apply sepWPp_intro_rodata64 (rodata_sckaInfoW2 himg hinv_ok2.1)
      apply sepWPp_intro_rodata64 (rodata_sckaInfoW3 himg hinv_ok2.1)
      apply sepWPp_intro_rodata (rodata_zeros32 himg hinv_ok2.1)
      apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "spqr::kdf::hkdf_to_vec")) img hinv_ok2
      rw [memRegion_41_eq_infoSlots (sf2.readReg64 (Reg.gpr 0#5)),
          memRegion_32_split_24_8 (sp + 7536#64)]
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      iterate 6 (apply SepWP.exists_elim; intro _)
      wp_conv_pre => simp only [BitVec.add_assoc, arm64_norm]
      wp_steps
      refine SepWP.fold (infoSlots_entails_pointsToBytes (sf2.readReg64 (Reg.gpr 0#5)) epoch)
        (by sep_focus) ?_
      refine finish_sepWP_inImage_drop_ro (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (Ro := ((img.base + bv% (ls_xref% 0x30f68 0x30f6c)) ↦₆₄ᵣ sckaInfoW0) ∗ ((img.base + bv% ((ls_xref% 0x30f68 0x30f6c) + 8)) ↦₆₄ᵣ sckaInfoW1) ∗
               ((img.base + bv% ((ls_xref% 0x30f68 0x30f6c) + 16)) ↦₆₄ᵣ sckaInfoW2) ∗ ((img.base + bv% ((ls_xref% 0x30f68 0x30f6c) + 24)) ↦₆₄ᵣ sckaInfoW3))
        (P' := (((img.base + bv% (ls_xref% 0x30f98 0x30f9c)) ↦ᵣ List.replicate 32 0#8) ∗
          ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A g auth ∗
          memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗
          ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ (sckaKeyInfoPrefix ++ epochBeBytes epoch)) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          memRegion (sp + 7536#64) 24 ∗ memRegion (sp + 7560#64) 8 ∗
          A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
        (fun hinv3 => ?_) (Entails.of_eq (by ac_rfl))
      have hpre_len : sckaKeyInfoPrefix.length = 33 := rfl
      have hinfo_len : (sckaKeyInfoPrefix ++ epochBeBytes epoch).length = 41 := by
        rw [List.length_append, hpre_len, epochBeBytes_length]
      let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      refine call_inImage_calleeStack (entry := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "spqr::kdf::hkdf_to_vec"))
        (spec := hkdfToVecSpecExt A (hkdfToVecUnchecked F))
        (x := ({
          outVec := sp + 7536#64,
          saltRO := true, saltA := img.base + bv% (ls_xref% 0x30f98 0x30f9c), salt := List.replicate 32 0#8,
          ikmRO := false, ikmA := ss_ptr, ikm := ss.toList,
          infoRO := false, infoA := sf2.readReg64 (Reg.gpr 0#5), info := info,
          okmLen := 32 } : HkdfToVecGhost))
        (s0 := s0) sp hkdfToVecStackExt (by decide)
        (T_pre := memRegion (sp + 7536#64) 24 ∗ ((img.base + bv% (ls_xref% 0x30f98 0x30f9c)) ↦ᵣ List.replicate 32 0#8) ∗
          (ss_ptr ↦ₛ ss.toList) ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗ A.pool)
        (T_post := fun _ => vecU8 A (sp + 7536#64) secret ∗ ((img.base + bv% (ls_xref% 0x30f98 0x30f9c)) ↦ᵣ List.replicate 32 0#8) ∗
          (ss_ptr ↦ₛ ss.toList) ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗ A.pool)
        (F := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A g auth ∗ memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗ A.live ss_ptr 32 1 ∗
          memRegion (sp + 7560#64) 8 ∗ Frame)
        (φ_pre := _) (φ_post := _) hhkdf_call hinv3
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
        hsp_align (by simp only [arm64_norm, *]) (ret_pc := entry + 1656#64) (by simp only [Reg.lr, arm64_norm, *])
        (by simp only [hkdfToVecSpecExt, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte]; ac_rfl)
        (by
          dsimp only [info]; rw [hss_len, hinfo_len]
          simp only [Reg.x8, Reg.x0, Reg.x1, Reg.x2, Reg.x3, Reg.x4, Reg.x5, Reg.x6,
            List.length_replicate, wp_norm, arm64_norm, *])
        (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
        (by intro _; simp only [hkdfToVecSpecExt, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte, secret]; ac_rfl) ?_
      intro sm1 hpc_sm1 hrun_sm1 hsp_sm1 hφ_sm1 hinv_sm1
        hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
      have hsec_len : secret.length = 32 := by simp only [secret, hφ_sm1]
      have htr_sm1 : sm1.trace = s0.trace := by
        simp only [secret, wp_norm, arm64_norm, *] at hφ_sm1; exact hφ_sm1
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        wp_norm, arm64_norm, *] at hx19_sm1 hx20_sm1 hx21_sm1 hx22_sm1 hx23_sm1 hx24_sm1 hx25_sm1 hx26_sm1 hx27_sm1 hx28_sm1 hvregs_sm1
      apply of_sepWP_inImage (mid := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::update")) img hinv_sm1
      refine SepWP.fold (vecU8_len32_expose_7536 sp secret hsec_len) (by sep_focus) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      apply SepWP.exists_elim; intro secret_cap
      apply SepWP.exists_elim; intro secret_ptr
      rw [sepConj_assoc]
      refine SepWP.pure_elim fun ⟨hsec_cap_ge, hsec_cap_lt, hsec_ptr_ne, hsec_cap_b⟩ => ?_
      refine SepWP.fold (fold_authenticatorAt_of_inline_local A g (sp + 4192#64) auth)
        (by sep_focus) ?_
      wp_steps
      refine finish_sepWP_inImage_drop_ro (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (Ro := (img.base + bv% (ls_xref% 0x30f98 0x30f9c)) ↦ᵣ List.replicate 32 0#8)
        (P' := (((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authenticatorAt A (sp + 4192#64) auth ∗ memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
        (fun hinv4 => ?_) (Entails.of_eq (by ac_rfl))
      refine call_inImage_calleeStack (entry := entry + bv% (ls_rel% "spqr::send::<libsignal_session::HookRng>" "<spqr::authenticator::Authenticator>::update"))
        (spec := authUpdateSpecExt F A)
        (x := ({
          selfA := sp + 4192#64, auth := auth, ep := epoch,
          kRO := false, kA := secret_ptr, k := secret } : AuthUpdateGhost))
        (s0 := s0) sp authUpdateStackExt (by decide)
        (T_pre := authenticatorAt A (sp + 4192#64) auth ∗ (secret_ptr ↦ₛ secret) ∗ A.pool)
        (T_post := fun _ => authenticatorAt A (sp + 4192#64) (auth.update F epoch secret) ∗
          (secret_ptr ↦ₛ secret) ∗ A.pool)
        (F := ((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          memRegion (sp + 4704#64) 961 ∗
          A.live (sf1.readReg64 (Reg.gpr 0#5)) 960 1 ∗ ((sf1.readReg64 (Reg.gpr 0#5)) ↦ₛ ct1.toList) ∗
          A.live (sf2.readReg64 (Reg.gpr 0#5)) 41 1 ∗ ((sf2.readReg64 (Reg.gpr 0#5)) ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗ Frame)
        (φ_pre := _) (φ_post := _) hupd_call hinv4
        (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [State.sp, arm64_norm, *])
        hsp_align (by simp only [arm64_norm, *]) (ret_pc := entry + 1680#64) (by simp only [Reg.lr, arm64_norm, *])
        (by simp only [authUpdateSpecExt, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte]; ac_rfl)
        (by
          rw [hsec_len]
          simp only [Reg.x0, Reg.x1, Reg.x2, Reg.x3, wp_norm, arm64_norm, *]; omega)
        (by ac_rfl) (fun _ _ => rfl) (fun _ => rfl)
        (by intro _; simp only [authUpdateSpecExt, ChainProofs.bytesAt, Bool.false_eq_true, ↓reduceIte]; ac_rfl) ?_
      intro sm2 hpc_sm2 hrun_sm2 hsp_sm2 htr_sm2 hinv_sm2
        hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
      simp only [Reg.x19, Reg.x20, Reg.x21, Reg.x22, Reg.x23, Reg.x24, Reg.x25, Reg.x26, Reg.x27, Reg.x28,
        wp_norm, arm64_norm, *] at htr_sm2 hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 hvregs_sm2
      apply of_sepWP_inImage (mid := entry + 1680#64) img hinv_sm2
      refine finish_sepWP_inImage hpc_sm2 hrun_sm2
        (fun hinv5 => hnext sm2 (sf1.readReg64 (Reg.gpr 0#5)) (sf2.readReg64 (Reg.gpr 0#5)) secret_cap secret_ptr
          hinv5 hne0_1 h0b_1 hne0_2 h0b_2 hsec_ptr_ne hsec_cap_b hsec_cap_ge hsec_cap_lt
          hpc_sm2 hrun_sm2 hsp_sm2
          hx19_sm2 hx20_sm2 hx21_sm2 hx22_sm2 hx23_sm2 hx24_sm2 hx25_sm2 hx26_sm2 hx27_sm2 hx28_sm2 htr_sm2
          (by simp only [wp_norm, arm64_norm, *]))
        (Entails.of_eq (by ac_rfl))

theorem step_headerReceived_1504_to_1680 {F : ShaCompress}
    {img : Obj.Image} {A : RustAlloc} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) (halign : img.base &&& 0xfff#64 = 0#64)
    (hA : AllocContracts img.base A ext)
    (hhkdf : HkdfToVecOkX img A (hkdfToVecUnchecked F) ext) (hupd : AuthUpdateOkX img F A ext)
    (sp epoch hdr_cap hdr_ptr es_ptr ss_ptr : BitVec 64)
    (g : AuthenticatorGhost) (auth : Authenticator) (hdr : Header)
    (ct1 : List.Vector (BitVec 8) 960) (ss : List.Vector (BitVec 8) 32)
    (hroot_len : auth.rootKey.length + 32 < 2 ^ 63)
    {ret : BitVec 64} {s0 s : State} {P Frame R : SepProp} {post : State → SepProp → Prop}
    (hinv : ImgCallInv img s) (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (hpc : s.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1504#64)
    (hrun : s.status = .Running) (hsp : s.sp = sp)
    (hx20 : s.readReg64 .x20 = ss_ptr) (hx21 : s.readReg64 .x21 = hdr_ptr)
    (hx22 : s.readReg64 .x22 = epoch) (hx24 : s.readReg64 .x24 = es_ptr)
    (hx25 : s.readReg64 .x25 = hdr_cap) (hx26 : s.readReg64 .x26 = sp + 4704#64)
    (hx27 : s.readReg64 .x27 = BitVec.ofNat 64 hdr.length) (htrace : s.trace = s0.trace)
    (hP : P = (
      memRegion (sp + 32#64) 16 ∗ authInlineWordsAt g (sp + 4192#64) auth ∗ authHeapBufs A g auth ∗
      ((sp + 4704#64) ↦₈ 0#8) ∗ ((sp + 4705#64) ↦ₛ ct1.toList) ∗
      A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
      memRegion (sp + 7536#64) 32 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame)
    (hnext : ∀ (sf : State) (ct1_ptr info_ptr secret_cap secret_ptr : BitVec 64),
      let info := sckaKeyInfoPrefix ++ epochBeBytes epoch
      let secret := hkdfToVecUnchecked F (List.replicate 32 0#8) ss.toList info 32
      let auth' := auth.update F epoch secret
      ImgCallInv img sf →
      ct1_ptr ≠ 0 → (ct1_ptr == 0#64) = false → info_ptr ≠ 0 → (info_ptr == 0#64) = false →
      secret_ptr ≠ 0 → (secret_cap == 0#64) = false → 32 ≤ secret_cap.toNat → secret_cap.toNat < 2 ^ 63 →
      sf.pc = (tripleRatchetProgAtExt img.base ext).fnAddr spqrSendName + 1680#64 →
      sf.status = .Running → sf.sp = sp →
      sf.readReg64 .x19 = s.readReg64 .x19 → sf.readReg64 .x20 = ss_ptr →
      sf.readReg64 .x21 = hdr_ptr → sf.readReg64 .x22 = epoch →
      sf.readReg64 .x23 = s.readReg64 .x23 → sf.readReg64 .x24 = es_ptr →
      sf.readReg64 .x25 = ct1_ptr → sf.readReg64 .x26 = sp + 4704#64 →
      sf.readReg64 .x27 = BitVec.ofNat 64 hdr.length → sf.readReg64 .x28 = info_ptr →
      sf.trace = s0.trace → calleeSavedVRegs sf = calleeSavedVRegs s →
      SepWPp (tripleRatchetProgAtExt img.base ext) ret sf
        ((((sp + 32#64) ↦₆₄ BitVec.ofNat 64 hdr.length) ∗ ((sp + 40#64) ↦₆₄ hdr_cap) ∗
          authenticatorAt A (sp + 4192#64) auth' ∗ memRegion (sp + 4704#64) 961 ∗
          A.live ct1_ptr 960 1 ∗ (ct1_ptr ↦ₛ ct1.toList) ∗
          A.live info_ptr 41 1 ∗ (info_ptr ↦ₛ info) ∗
          A.live ss_ptr 32 1 ∗ (ss_ptr ↦ₛ ss.toList) ∗
          ((sp + 7536#64) ↦₆₄ secret_cap) ∗ ((sp + 7544#64) ↦₆₄ secret_ptr) ∗ ((sp + 7552#64) ↦₆₄ 32#64) ∗
          A.live secret_ptr secret_cap.toNat 1 ∗ (secret_ptr ↦ₛ secret) ∗
          memRegion (secret_ptr + 32#64) (secret_cap.toNat - 32) ∗
          memRegion (sp + 7560#64) 8 ∗ A.pool ∗ stackAt sp spqrSendCalleeStack) ∗ Frame) post
        (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
          (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R))) :
    SepWPp (tripleRatchetProgAtExt img.base ext) ret s P post
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) →
        (sf.mem ⊨ (⌜allocFailedIn s0 sf ∧ s0.trace <+: sf.trace⌝ ∗ anyHeap) ∗ R)) :=
  step_headerReceived_1504_to_1680_ext himg halign hA
    (hkdfToVecOkExt_of_okX hhkdf) (authUpdateOkExt_of_okX hupd)
    sp epoch hdr_cap hdr_ptr es_ptr ss_ptr g auth hdr ct1 ss hroot_len
    hinv hsp_align hpc hrun hsp hx20 hx21 hx22 hx24 hx25 hx26 hx27 htrace hP hnext

end CryptoVerification.SpqrV1.Top.Send
