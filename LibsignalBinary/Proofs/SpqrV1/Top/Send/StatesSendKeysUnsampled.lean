/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Alloc.DoReserve
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
public import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
public import LibsignalBinary.Proofs.SpqrV1.Drop.StatesRepr
public import LibsignalBinary.Proofs.SpqrV1.Poly.EncodeBytes.Defs

/-!
# `spqr::send::<HookRng>`: Scaffolding for Inlined `States::send` `.keysUnsampled` Arm

**Checked by Lean.**

Provides pure unfolding lemmas, stack-layout predicates (`authInlineWordsAt`, `authHeapBufs`),
and callee contract predicates (`AuthMacHdrPinnedOkX`, `DoReserve2OkX`) for the inlined
`.keysUnsampled` arm (`0x309d0..0x31458`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Top.Send

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession (Crypto ShaCompress)
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSpqrV1 CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Poly CryptoVerification.SpqrV1.Poly.EncodeBytes
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnOff



theorem chunkedStatesAt_keysUnsampled_unfold (A : RustAlloc) {F : ShaCompress}
    (a : BitVec 64) (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) :
    chunkedStatesAt A a (.keysUnsampled st) =
      ((a ↦₆₄ 2#64) ∗
       authenticatorAt A (a + 8#64) st.uc.auth ∗
       ((a + 56#64) ↦₆₄ st.uc.epoch) ∗
       memRegion (a + 64#64) 864) := by
  simp only [chunkedStatesAt, chunkedKeysUnsampledAt, unchunkedKeysUnsampledAt,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem encodeBytesResult_of_len_even_le {msg : Bytes}
    (heven : msg.length % 2 = 0) (hle : msg.length ≤ 1048576) :
    ∃ enc : PolyEncoder,
      encodeBytesResult msg = .ok enc ∧
      expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:63" msg = .ok enc ∧
      expectEncodeBytes spqrPolyApi "v1/chunked/send_ct.rs:131" msg = .ok enc := by
  have h1 : (msg.length % 2 != 0) = false := by simp [heven]
  have h2 : ¬ (65536 * NUM_POLYS < msg.length) := by
    change ¬ (65536 * 16 < msg.length)
    omega
  refine ⟨{ idx := 0#32, s := .points (distributeMsgChunksTotal 0 msg (List.replicate NUM_POLYS { value := [] })) }, ?_, ?_, ?_⟩
  · unfold encodeBytesResult; simp [h1, h2]
  · unfold expectEncodeBytes spqrPolyApi
    dsimp only
    rw [encodeBytes_eq_ok]
    unfold encodeBytesResult
    simp [h1, h2, Bind.bind, Except.bind, Except.mapError, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]
  · unfold expectEncodeBytes spqrPolyApi
    dsimp only
    rw [encodeBytes_eq_ok]
    unfold encodeBytesResult
    simp [h1, h2, Bind.bind, Except.bind, Except.mapError, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

@[simp] theorem fromSeed_hdr_len (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    (K.fromSeed seed).1.toList.length = 64 :=
  List.Vector.toList_length _

@[simp] theorem fromSeed_ek_len (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    (K.fromSeed seed).2.1.toList.length = 1152 :=
  List.Vector.toList_length _

@[simp] theorem fromSeed_dk_len (K : MlKem) (seed : List.Vector (BitVec 8) 64) :
    (K.fromSeed seed).2.2.toList.length = 2400 :=
  List.Vector.toList_length _

theorem rngFill_64_of_le {tape : Bytes} (h : 64 ≤ tape.length) :
    (tape ++ List.replicate 64 0#8).take 64 = tape.take 64 ∧
    min 64 tape.length = 64 ∧
    (tape.take 64).length = 64 := by
  refine ⟨?_, Nat.min_eq_left h, by simp [h]⟩
  rw [List.take_append_of_le_length h]

theorem rngFill_32_of_le {tape : Bytes} (h : 32 ≤ tape.length) :
    (tape ++ List.replicate 32 0#8).take 32 = tape.take 32 ∧
    min 32 tape.length = 32 ∧
    (tape.take 32).length = 32 := by
  refine ⟨?_, Nat.min_eq_left h, by simp [h]⟩
  rw [List.take_append_of_le_length h]

theorem generate_eq_match (K : MlKem) (tape : Bytes) :
    generate K tape =
      match (if h : (tape.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE
             then some ⟨tape.take KEY_GENERATION_SEED_SIZE, h⟩ else none) with
      | none => .error (.rngExhausted KEY_GENERATION_SEED_SIZE tape.length)
      | some seed =>
        let (hdr, ek, dk) := K.fromSeed seed
        .ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList }, tape.drop KEY_GENERATION_SEED_SIZE) :=
  rfl

theorem generate_of_lt_64 (K : MlKem) {tape : Bytes} (h : tape.length < 64) :
    generate K tape = .error (.rngExhausted 64 tape.length) := by
  rw [generate_eq_match]
  have hlen : (tape.take KEY_GENERATION_SEED_SIZE).length ≠ KEY_GENERATION_SEED_SIZE := by
    change (tape.take 64).length ≠ 64
    rw [List.length_take]; omega
  rw [dite_eq_right (by simpa using hlen)]
  rfl

theorem generate_of_le_64 (K : MlKem) {tape : Bytes} (h : 64 ≤ tape.length) :
    let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
    let (hdr, ek, dk) := K.fromSeed seed
    generate K tape = .ok ({ ek := ek.toList, dk := dk.toList, hdr := hdr.toList }, tape.drop 64) := by
  dsimp only
  rw [generate_eq_match]
  have hlen : (tape.take KEY_GENERATION_SEED_SIZE).length = KEY_GENERATION_SEED_SIZE := by
    change (tape.take 64).length = 64
    rw [List.length_take]; omega
  rw [dite_eq_left hlen]
  rfl

theorem send_hdr_chunk_of_lt_64 {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) {tape : Bytes} (h : tape.length < 64) :
    st.send_hdr_chunk K spqrPolyApi tape = .error (.rngExhausted 64 tape.length) := by
  unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk Unchunked.SendEk.KeysUnsampled.send_header
  rw [generate_of_lt_64 K h]
  rfl

theorem encaps1_eq_match (K : MlKem) (hdr : Header) (tape : Bytes) :
    encaps1 K hdr tape =
      match (if h1 : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE
             then some ⟨tape.take SHARED_SECRET_SIZE, h1⟩ else none) with
      | none => .error (.rngExhausted SHARED_SECRET_SIZE tape.length)
      | some rand =>
        match K.encaps1 hdr rand with
        | none => .error .encaps1Failed
        | some (ct1, es, ss) => .ok ((ct1.toList, es.toList, ss.toList), tape.drop SHARED_SECRET_SIZE) :=
  rfl

theorem encaps1_of_lt_32 (K : MlKem) (hdr : Header) {tape : Bytes} (h : tape.length < 32) :
    encaps1 K hdr tape = .error (.rngExhausted 32 tape.length) := by
  rw [encaps1_eq_match]
  have hlen : (tape.take SHARED_SECRET_SIZE).length ≠ SHARED_SECRET_SIZE := by
    change (tape.take 32).length ≠ 32
    rw [List.length_take]; omega
  rw [dite_eq_right (by simpa using hlen)]
  rfl

theorem encaps1_of_le_32 (K : MlKem) (hdr : Header) {tape : Bytes} (h : 32 ≤ tape.length) :
    let rand : List.Vector (BitVec 8) 32 := ⟨tape.take 32, by rw [List.length_take]; omega⟩
    encaps1 K hdr tape =
      match K.encaps1 hdr rand with
      | none => .error .encaps1Failed
      | some (ct1, es, ss) => .ok ((ct1.toList, es.toList, ss.toList), tape.drop 32) := by
  dsimp only
  rw [encaps1_eq_match]
  have hlen : (tape.take SHARED_SECRET_SIZE).length = SHARED_SECRET_SIZE := by
    change (tape.take 32).length = 32
    rw [List.length_take]; omega
  rw [dite_eq_left hlen]
  rfl

theorem send_hdr_chunk_of_ok {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) {tape : Bytes} (h : 64 ≤ tape.length)
    {mac : Bytes} {sending_hdr sending_hdr' : PolyEncoder} {chunk : Chunk}
    (hmac : st.uc.auth.macHdr F st.uc.epoch (K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList = .ok mac)
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:63"
      ((K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList ++ mac) = .ok sending_hdr)
    (hnc : sending_hdr.nextChunk = .ok (sending_hdr', chunk)) :
    let seed : List.Vector (BitVec 8) 64 := ⟨tape.take 64, by rw [List.length_take]; omega⟩
    let (_, ek, dk) := K.fromSeed seed
    let hs : Unchunked.SendEk.HeaderSent (spqrAuthApi F) :=
      { epoch := st.uc.epoch, auth := st.uc.auth, ek := ek.toList, dk := dk.toList }
    st.send_hdr_chunk K spqrPolyApi tape =
      .ok ({ uc := hs, sending_hdr := sending_hdr' }, chunk, tape.drop 64) := by
  dsimp only
  have hmac' : (spqrAuthApi F).mac_hdr st.uc.auth st.uc.epoch
      (K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList = .ok mac := hmac
  have hnc' : spqrPolyApi.next_chunk sending_hdr = .ok (sending_hdr', chunk) := by
    change sending_hdr.nextChunk.mapError PolyPanic.toSpqrPanic = .ok (sending_hdr', chunk)
    rw [hnc]; rfl
  unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk Unchunked.SendEk.KeysUnsampled.send_header
  rw [generate_of_le_64 K h]
  simp only [hmac', henc, hnc', Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

theorem send_hdr_chunk_of_macHdr_err {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) {tape : Bytes} (h : 64 ≤ tape.length)
    {p : SpqrPanic}
    (hmac : st.uc.auth.macHdr F st.uc.epoch (K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList = .error p) :
    st.send_hdr_chunk K spqrPolyApi tape = .error (.spqr p) := by
  have hmac' : (spqrAuthApi F).mac_hdr st.uc.auth st.uc.epoch
      (K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList = .error p := hmac
  unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk Unchunked.SendEk.KeysUnsampled.send_header
  rw [generate_of_le_64 K h]
  simp only [hmac', Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

theorem send_hdr_chunk_of_nextChunk_err {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendEk.KeysUnsampled (spqrAuthApi F)) {tape : Bytes} (h : 64 ≤ tape.length)
    {mac : Bytes} {sending_hdr : PolyEncoder} {p : PolyPanic}
    (hmac : st.uc.auth.macHdr F st.uc.epoch (K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList = .ok mac)
    (henc : expectEncodeBytes spqrPolyApi "v1/chunked/send_ek.rs:63"
      ((K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList ++ mac) = .ok sending_hdr)
    (hnc : sending_hdr.nextChunk = .error p) :
    st.send_hdr_chunk K spqrPolyApi tape = .error (.spqr p.toSpqrPanic) := by
  have hmac' : (spqrAuthApi F).mac_hdr st.uc.auth st.uc.epoch
      (K.fromSeed ⟨tape.take 64, by rw [List.length_take]; omega⟩).1.toList = .ok mac := hmac
  have hnc' : spqrPolyApi.next_chunk sending_hdr = .error p.toSpqrPanic := by
    change sending_hdr.nextChunk.mapError PolyPanic.toSpqrPanic = .error p.toSpqrPanic
    rw [hnc]; rfl
  unfold Chunked.SendEk.KeysUnsampled.send_hdr_chunk Unchunked.SendEk.KeysUnsampled.send_header
  rw [generate_of_le_64 K h]
  simp only [hmac', henc, hnc', Bind.bind, Except.bind, liftM, monadLift, MonadLift.monadLift, liftSpqrPanic]

theorem send_ct1_chunk_of_lt_32 {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) {tape : Bytes} (h : tape.length < 32) :
    st.send_ct1_chunk K tape = .error (.rngExhausted 32 tape.length) := by
  unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk Unchunked.SendCt.HeaderReceived.send_ct1
  rw [encaps1_of_lt_32 K st.uc.hdr h]
  rfl

theorem send_ct1_chunk_of_encaps1_none {F : ShaCompress} (K : MlKem)
    (st : Chunked.SendCt.HeaderReceived spqrPolyApi (spqrAuthApi F)) {tape : Bytes} (h : 32 ≤ tape.length)
    (hencaps : K.encaps1 st.uc.hdr ⟨tape.take 32, by rw [List.length_take]; omega⟩ = none) :
    st.send_ct1_chunk K tape = .error .encaps1Failed := by
  unfold Chunked.SendCt.HeaderReceived.send_ct1_chunk Unchunked.SendCt.HeaderReceived.send_ct1
  rw [encaps1_of_le_32 K st.uc.hdr h, hencaps]
  rfl

theorem subroutine_ok_inImage {α : Type} {prog : Program} {entry : BitVec 64}
    {spec : Spec α} (img : Obj.Image) (h : subroutine_ok prog entry spec) :
    subroutine_ok prog entry (spec.inImage img) := by
  refine subroutine_ok_outcome_intro fun x R s0 hpc hrun hpre hal => ?_
  dsimp only [Spec.inImage] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  exact h.mono_outcome x R s0 hpc hrun hpre.2 hal fun _ hout => hout

/-- `<spqr::authenticator::Authenticator>::mac_hdr` (`0x5e068`) meets `(authMacHdrPinnedSpec F A).inImage img`
on `tripleRatchetProgAtExt img.base ext`. -/
def AuthMacHdrPinnedOkX (img : Obj.Image) (F : ShaCompress) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr authMacHdrName)
    ((authMacHdrPinnedSpec F A).inImage img)


theorem authMacHdrPinned_ok_ext_x {img : Obj.Image}
    {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hconcat3 : SliceConcat3OkX img A ext)
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A))
    (hA : AllocContractsX img A ext) :
    AuthMacHdrPinnedOkX img F A ext :=
  authMacHdrPinned_ok_of_contracts_x himg hconcat3 (libcrux_hmac_ok_x hhmac) hA.dealloc

/-- `alloc::raw_vec::RawVecInner<A>::do_reserve_and_handle [local#2]` (`0x37f7c`) meets
`(doReserve1Raw32Spec A).inImage img` on `tripleRatchetProgAtExt img.base ext`. -/
def DoReserve2OkX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) : Prop :=
  subroutine_ok (tripleRatchetProgAtExt img.base ext)
    ((tripleRatchetProgAtExt img.base ext).fnAddr doReserve2Name)
    ((doReserve1Raw32Spec A).inImage img)

theorem doReserve2_ok_ext_x (img : Obj.Image) {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts img.base A ext) :
    DoReserve2OkX img A ext :=
  subroutine_ok_inImage img (do_reserve_2_raw32_ok_ext hA)



/-- Inline 48-byte header words of `authenticatorPinAt A g p auth`. -/
def authInlineWordsAt (g : AuthenticatorGhost) (p : BitVec 64) (auth : Authenticator) : SepProp :=
  (p ↦₆₄ g.rootKey.cap) ∗ ((p + 8#64) ↦₆₄ g.rootKey.ptr) ∗
    ((p + 16#64) ↦₆₄ BitVec.ofNat 64 auth.rootKey.length) ∗
    ((p + 24#64) ↦₆₄ g.macKey.cap) ∗ ((p + 32#64) ↦₆₄ g.macKey.ptr) ∗
    ((p + 40#64) ↦₆₄ BitVec.ofNat 64 auth.macKey.length)

/-- Heap buffers of `authenticatorPinAt A g p auth` (independent of `p`). -/
def authHeapBufs (A : RustAlloc) (g : AuthenticatorGhost) (auth : Authenticator) : SepProp :=
  RustHeap.vecU8Buf A g.rootKey.cap g.rootKey.ptr auth.rootKey ∗
    RustHeap.vecU8Buf A g.macKey.cap g.macKey.ptr auth.macKey

theorem authenticatorPinAt_eq_inline_heap (A : RustAlloc) (g : AuthenticatorGhost)
    (p : BitVec 64) (auth : Authenticator) :
    authenticatorPinAt A g p auth =
      authInlineWordsAt g p auth ∗ authHeapBufs A g auth := by
  unfold authenticatorPinAt authInlineWordsAt authHeapBufs vecU8At vecHeader RustHeap.vecU8Buf
  rw [show (p + 0x18#64 : BitVec 64) = p + 24#64 from rfl,
      show (p + 24#64) + 8#64 = p + 32#64 by bv_omega,
      show (p + 24#64) + 16#64 = p + 40#64 by bv_omega]
  ac_rfl

theorem authInlineWordsAt_entails_memRegion (g : AuthenticatorGhost) (p : BitVec 64) (auth : Authenticator) :
    authInlineWordsAt g p auth ⊢ memRegion p 48 := by
  unfold authInlineWordsAt
  rw [ProofLib.memRegion_split' (b := p) (n := 8) (k := 40) (b' := p + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := p + 8#64) (n := 8) (k := 32) (b' := p + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 16#64) (n := 8) (k := 24) (b' := p + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 24#64) (n := 8) (k := 16) (b' := p + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := p + 32#64) (n := 8) (k := 8) (b' := p + 40#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
    (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
      (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
        (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
          (sepConj_mono (ProofLib.pointsTo64_entails_memRegion _ _)
            (ProofLib.pointsTo64_entails_memRegion _ _)))))

end CryptoVerification.SpqrV1.Top.Send


