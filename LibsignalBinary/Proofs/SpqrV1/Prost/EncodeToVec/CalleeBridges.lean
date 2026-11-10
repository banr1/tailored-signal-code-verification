/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.V1StateCommon
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.PolyDecoderExact
public import LibsignalBinary.Proofs.SpqrV1.Prost.EncodeToVec.AllocReservePhase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.ChainParamsBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.EpochDirectionBase
public import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.UnchunkedBase
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.ChainEncodedLen
import LibsignalBinary.Proofs.SpqrV1.ProtoRepr.EncodedLen.V1State

/-!
# `PqRatchetState::encode_to_vec`: Callee Contract Bridges

Relative-branch resolution and `withStepInv` stack-framing bridges adapting field-encoder and
`encoded_len` subroutine contracts for `PqRatchetState::encode_to_vec` (`0x6d010`).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Prost.EncodeToVec

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.CodeLayout
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.ProtoRepr
open CryptoVerification.SpqrV1.ProtoRepr.EncodedLen
open CryptoVerification.SpqrV1.Varint
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Prost.MessageEncode

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

attribute [local irreducible] libsignalSessionCode Program.fetch Program.externAt? Program.fnAddr

/-- Generic relative-branch target resolution from `spqrEncodeToVecName`. -/
theorem encodeToVec_callee_fnAddr_eq (b : BitVec 64)
    (ext : String → Option (State → State))
    {entry delta : BitVec 64} {calleeName : String} {calleeOff : Nat}
    (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (hcallee : libsignalSessionCode.fnOff calleeName = calleeOff)
    (hdelta : BitVec.ofNat 64 (num% (ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) + delta = BitVec.ofNat 64 calleeOff) :
    entry + delta = (spqrProgAtExt b ext).fnAddr calleeName := by
  subst hfn
  have h1 : (spqrProgAtExt b ext).fnOff spqrEncodeToVecName = num% (ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec") := spqrEncodeToVec_fnOff
  have h2 : (spqrProgAtExt b ext).fnOff calleeName = calleeOff := hcallee
  unfold Program.fnAddr
  rw [h1, h2]
  exact (BitVec.add_assoc b _ delta).trans (congrArg (b + ·) hdelta)

theorem etv_chainEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (s0 : State) :
    subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr chainEncodedLenLocal2Name)
      (withStepInv s0 (chainEncodedLenPinnedSpec A)) :=
  subroutine_ok_withStepInv s0 (chainEncodedLen_local2_pinned_ok_ext b A ext)

theorem etv_v1StateEncodedLen_ok (b : BitVec 64) (A : RustAlloc)
    (ext : String → Option (State → State)) (hb : b &&& 0xfff#64 = 0#64) (s0 : State) :
    subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr v1StateEncodedLenLocal2Name)
      (withStepInv s0 (v1StateEncodedLenRoPinnedSpec A (b + bv% (ls_xref% 0x62a38 0x62a3c)))) :=
  subroutine_ok_withStepInv s0 (v1StateEncodedLen_local2_pinned_ok_ext b A ext hb)

theorem etv_handle_alloc_error (b : BitVec 64) (ext : String → Option (State → State))
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) :
    (spqrProgAtExt b ext).externAt?
      (entry + bv% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec")) = some Rust.panicked := by
  subst hfn
  exact panic_at_handle_error_norm_ext (b := b) (ext := ext)
    (name := spqrEncodeToVecName)
    (k := num% (ls_off% "alloc::raw_vec::handle_error" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
    (by rw [spqrEncodeToVec_fnOff, (ls_stub% "alloc::raw_vec::handle_error")])

theorem etv_shim_ok {resStack : Nat} {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (s0 : State) :
    subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (shimStackSpecOf resStack)) := by
  subst hfn
  have hshim := shim_ok_at2_ext hA (name := spqrEncodeToVecName)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
    (by rw [spqrEncodeToVec_fnOff, (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")])
  apply subroutine_ok_withStepInv s0
  refine subroutine_ok_outcome_intro fun u R s hpc hrun hpre hal => ?_
  dsimp only [shimStackSpecOf] at hpre
  have hpre' : s.mem ⊨ noAllocShimSpec.pre u s ∗ (stackAt s.sp (encodeToVecCalleeStackOf resStack) ∗ R) := by
    dsimp only [noAllocShimSpec]; rw [emp_sepConj]
    exact hpre
  refine hshim.mono_outcome u (stackAt s.sp (encodeToVecCalleeStackOf resStack) ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [noAllocShimSpec, shimStackSpecOf] at hpost ⊢
    rwa [sepConj_assoc]
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem stackAt_callee_eq_allocHook {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    (sp1 : BitVec 64) :
    stackAt sp1 (encodeToVecCalleeStackOf resStack) =
      memRegion (sp1 - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
        (encodeToVecCalleeStackOf resStack - allocHookStack) ∗
        stackAt sp1 allocHookStack := by
  have h := ProofLib.stackAt_split_bottom sp1 allocHookStack
    (encodeToVecCalleeStackOf resStack - allocHookStack) (by omega)
  have heq : allocHookStack + (encodeToVecCalleeStackOf resStack - allocHookStack) =
      encodeToVecCalleeStackOf resStack := by omega
  simpa only [heq] using h

theorem etv_rustAlloc_ok {resStack : Nat}
    (hlow : allocHookStack ≤ encodeToVecCalleeStackOf resStack)
    (hhigh : encodeToVecCalleeStackOf resStack < 2 ^ 64)
    {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry)
    (s0 : State) :
    subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      (withStepInv s0 (rustAllocStackSpecOf resStack A)) := by
  subst hfn
  have halloc := alloc_ok_at_norm_ext hA (name := spqrEncodeToVecName)
    (k := num% (ls_off% "__rustc::__rust_alloc" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
    (by rw [spqrEncodeToVec_fnOff, (ls_stub% "__rustc::__rust_alloc")])
  apply subroutine_ok_withStepInv s0
  refine subroutine_ok_outcome_intro fun sz R s hpc hrun hpre hal => ?_
  dsimp only [rustAllocStackSpecOf] at hpre
  rw [stackAt_callee_eq_allocHook hlow hhigh s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack))
    (encodeToVecCalleeStackOf resStack - allocHookStack)
  have hpre' : s.mem ⊨ (rustAllocSpec A).pre (sz, 1) s ∗ (F_rem ∗ R) := by
    dsimp only [rustAllocSpec]
    simp only [satisfies_pure_sepConj, sepConj_assoc] at hpre ⊢
    rcases hpre with ⟨⟨hx0, hx1, hpos, hlt⟩, hm⟩
    have hx1' : (s.readReg64 .x1).toNat = 1 := by rw [hx1]; rfl
    refine ⟨⟨hx0, hx1', hpos, ⟨0, rfl⟩, by omega⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hm
  refine halloc.mono_outcome (sz, 1) (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [rustAllocSpec, rustAllocStackSpecOf] at hpost ⊢
    simp only [Nat.mod_one, true_and] at hpost
    rw [stackAt_callee_eq_allocHook hlow hhigh s.sp]
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem]; ac_rfl)) hpost
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_memcpy_ok {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext)
    {entry : BitVec 64} (hfn : (spqrProgAtExt b ext).fnAddr spqrEncodeToVecName = entry) :
    subroutine_ok (spqrProgAtExt b ext)
      (entry + bv% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
      etvMemcpyRegionSpec := by
  subst hfn
  exact hA.session_memcpy_region_ok_at spqrEncodeToVecName
    (num% (ls_off% "memcpy" - ls_off% "<spqr::proto::pq_ratchet::PqRatchetState as prost::message::Message>::encode_to_vec"))
    (by rw [spqrEncodeToVec_fnOff, (ls_stub% "memcpy")])

theorem etv_epochEncodedLen_ok {resStack : Nat} (hres : resStack + 176 < 2 ^ 64)
    (b : BitVec 64) (A : RustAlloc) (ext : String → Option (State → State)) (s0 : State) :
    subroutine_ok (spqrProgAtExt b ext)
      ((spqrProgAtExt b ext).fnAddr epochEncodedLenLocal2Name)
      (withStepInv s0 (epochEncLenStackSpecOf resStack A)) := by
  have hep := epochEncodedLen_local2_pinned_ok_ext b A ext
  apply subroutine_ok_withStepInv s0
  refine subroutine_ok_outcome_intro fun ⟨a, g, ep⟩ R s hpc hrun hpre hal => ?_
  dsimp only [epochEncLenStackSpecOf] at hpre
  rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) (160 + resStack)
  simp only [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (epochEncodedLenPinnedSpec A).pre ⟨a, g, ep⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [epochEncodedLenPinnedSpec, EpochEncodedLenFits]
    simp only [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0, hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; ac_rfl)) hm
  refine hep.mono_outcome ⟨a, g, ep⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [epochEncodedLenPinnedSpec, epochEncLenStackSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_unchunkedEncodedLen hres s.sp]
    exact Satisfies.mono (Entails.of_eq (by dsimp [F_rem, epochEncodedLenStack, unchunkedEncodedLenStack]; ac_rfl)) hpost
  · exact (allowPanic_not_exited hpan).elim
  · exact (allowPanic_not_exited hex).elim
  · exact (allowPanic_not_exited hoom).elim

private theorem elim_exact_cap_ptr {A : RustAlloc} {v cap ptr : BitVec 64}
    {bs1 bs2 : List (BitVec 8)} (hfit : bs1.length + bs2.length ≤ cap.toNat) :
    (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
      ⌜cap.toNat ≤ cap'.toNat ∧ (bs1.length + bs2.length ≤ cap.toNat → cap' = cap ∧ ptr' = ptr)⌝ ∗
      vecU8At A v cap' ptr' (bs1 ++ bs2)) ⊢
    vecU8At A v cap ptr (bs1 ++ bs2) :=
  Entails.sepExists_elim fun cap' =>
    Entails.sepExists_elim fun ptr' =>
      Entails.pure_left fun ⟨_, hpres⟩ => by
        obtain ⟨rfl, rfl⟩ := hpres hfit
        exact Entails.refl _

theorem etv_encodeVarint_exact_of_fit {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64}
    {A : RustAlloc} {s0 : State}
    (hfit_ok : subroutine_ok prog call_pc (withStepInv s0 (encodeVarintFitSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (encodeVarintExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, encodeVarintExactSpecOf] at hpre
  rw [stackAt_callee_eq_encodeVarint hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 128
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hfit' : x.bs.length + (LibsignalProtoCodec.encodeVarint x.val).length ≤ x.cap.toNat := by
    rwa [← protoEncodeVarint_eq_codec]
  have hpre' : s.mem ⊨ (withStepInv s0 (encodeVarintFitSpecOf resStack A)).pre
      ⟨x.val, x.v, x.cap, x.ptr, x.bs⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, encodeVarintFitSpecOf]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit'⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem]; ac_rfl)) hm
  refine hfit_ok.mono_outcome ⟨x.val, x.v, x.cap, x.ptr, x.bs⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodeVarintFitSpecOf, encodeVarintSpecOf, encodeVarintExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_encodeVarint hres s.sp, protoEncodeVarint_eq_codec]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (elim_exact_cap_ptr hfit')))) ?_
    exact Entails.of_eq (by dsimp only [F_rem]; ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStepInv, encodeVarintFitSpecOf, encodeVarintSpec,
      encodeVarintExactSpecOf, encodeToVecOnPanic] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact allowPanic_frame id hq
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_encodeChainParams_exact_of_spec {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64}
    {A : RustAlloc} {s0 : State}
    (hcp_ok : subroutine_ok prog call_pc (withStepInv s0 (encodeChainParamsSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (encodeChainParamsExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, encodeChainParamsExactSpecOf] at hpre
  rw [stackAt_callee_eq_msgEnc48Varint hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 80
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hw0, hw1, hw2, hx3, htag1, htag2, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withStepInv s0 (encodeChainParamsSpecOf resStack A)).pre
      ⟨x.tag, x.p, x.v, x.cap, x.ptr, x.bs⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, encodeChainParamsSpecOf, encodeChainParamsMsg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hw1, hw2, hx3, htag1, htag2, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, msgEnc48VarintStackOf]; ac_rfl)) hm
  refine hcp_ok.mono_outcome ⟨x.tag, x.p, x.v, x.cap, x.ptr, x.bs⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodeChainParamsSpecOf, encodeChainParamsMsg,
      encodeChainParamsExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_msgEnc48Varint hres s.sp]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left (elim_exact_cap_ptr hfit)))) ?_
    exact Entails.of_eq (by dsimp only [F_rem, msgEnc48VarintStackOf]; ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStepInv, encodeChainParamsSpecOf, msgEncOnPanic,
      encodeChainParamsExactSpecOf, encodeToVecOnPanic] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact allowPanic_frame id hq
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_encodeEpochDirection_exact_of_spec {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64}
    {A : RustAlloc} {s0 : State}
    (hed_ok : subroutine_ok prog call_pc (withStepInv s0 (encodeEpochDirectionPinnedSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (encodeEpochDirectionExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, encodeEpochDirectionExactSpecOf] at hpre
  rw [stackAt_callee_eq_authEncode hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 64
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hw0, hx1, hx2, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withStepInv s0 (encodeEpochDirectionPinnedSpecOf resStack A)).pre
      ⟨x.tag, x.dirA, x.g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, encodeEpochDirectionPinnedSpecOf, encodeEpochDirectionMsg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hw0, hx1, hx2, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; ac_rfl)) hm
  refine hed_ok.mono_outcome ⟨x.tag, x.dirA, x.g, x.dir, x.v, x.cap, x.ptr, x.bs⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodeEpochDirectionPinnedSpecOf, encodeEpochDirectionMsg,
      encodeEpochDirectionExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_authEncode hres s.sp]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (elim_exact_cap_ptr hfit))))) ?_
    exact Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStepInv, encodeEpochDirectionPinnedSpecOf, msgEncOnPanic,
      encodeEpochDirectionExactSpecOf, encodeToVecOnPanic] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact allowPanic_frame id hq
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_authEncode_exact_of_spec {resStack : Nat}
    (hres : resStack + 176 < 2 ^ 64) {prog : Program} {call_pc : BitVec 64}
    {A : RustAlloc} {s0 : State}
    (hauth_ok : subroutine_ok prog call_pc (withStepInv s0 (authEncodePinnedSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (authEncodeExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, authEncodeExactSpecOf] at hpre
  rw [stackAt_callee_eq_authEncode hres s.sp] at hpre
  let F_rem := memRegion (s.sp - BitVec.ofNat 64 (encodeToVecCalleeStackOf resStack)) 64
  rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hinv0, ⟨hx0, hx1, hfit⟩, hm⟩
  have hpre' : s.mem ⊨ (withStepInv s0 (authEncodePinnedSpecOf resStack A)).pre
      ⟨x.authA, x.g, x.auth, x.v, x.cap, x.ptr, x.bs⟩ s ∗ (F_rem ∗ R) := by
    dsimp only [withStepInv, authEncodePinnedSpecOf, encodeAuthMsg]
    rw [sepConj_assoc, satisfies_pure_sepConj, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨hinv0, ⟨hx0, hx1, Or.inl hfit⟩, ?_⟩
    exact Satisfies.mono (Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; ac_rfl)) hm
  refine hauth_ok.mono_outcome ⟨x.authA, x.g, x.auth, x.v, x.cap, x.ptr, x.bs⟩ (F_rem ∗ R) s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, authEncodePinnedSpecOf, encodeAuthMsg,
      authEncodeExactSpecOf] at hpost ⊢
    rw [stackAt_callee_eq_authEncode hres s.sp]
    refine Satisfies.mono ?_ hpost
    refine Entails.trans
      (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left (elim_exact_cap_ptr hfit))))) ?_
    exact Entails.of_eq (by dsimp only [F_rem, authEncodeStackOf]; ac_rfl)
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [withStepInv, authEncodePinnedSpecOf, encodeToVecOnPanic] at hq ⊢
    rw [← sepConj_assoc] at hq
    exact allowPanic_frame id hq
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem unchunkedMsgEncodeStackOf_eq (resStack : Nat) :
    unchunkedMsgEncodeStackOf resStack = encodeToVecCalleeStackOf resStack := by
  dsimp [unchunkedMsgEncodeStackOf, authEncodeStackOf, encodeToVecCalleeStackOf]; omega

theorem etv_ekSentCt1ReceivedEncode_of_spec {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc} {s0 : State}
    (hek_ok : subroutine_ok prog call_pc (withStepInv s0 (ekSentCt1ReceivedEncodePinnedSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (etvEkSentCt1ReceivedEncodeSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨ (withStepInv s0 (ekSentCt1ReceivedEncodePinnedSpecOf resStack A)).pre
      ⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withStepInv, ekSentCt1ReceivedEncodePinnedSpecOf, etvEkSentCt1ReceivedEncodeSpecOf,
      encodeEkSentCt1ReceivedMsg] at hpre ⊢
    rwa [unchunkedMsgEncodeStackOf_eq]
  refine hek_ok.mono_outcome ⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩ R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ekSentCt1ReceivedEncodePinnedSpecOf, etvEkSentCt1ReceivedEncodeSpecOf,
      encodeEkSentCt1ReceivedMsg] at hpost ⊢
    rwa [← unchunkedMsgEncodeStackOf_eq]
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_ct1SentEncode_of_spec {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc} {s0 : State}
    (hct1_ok : subroutine_ok prog call_pc (withStepInv s0 (ct1SentEncodePinnedSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (etvCt1SentEncodeSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  have hpre' : s.mem ⊨ (withStepInv s0 (ct1SentEncodePinnedSpecOf resStack A)).pre
      ⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withStepInv, ct1SentEncodePinnedSpecOf, etvCt1SentEncodeSpecOf,
      encodeCt1SentMsg] at hpre ⊢
    rwa [unchunkedMsgEncodeStackOf_eq]
  refine hct1_ok.mono_outcome ⟨x.msgA, x.g, x.m, x.v, x.cap, x.ptr, x.bs⟩ R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, ct1SentEncodePinnedSpecOf, etvCt1SentEncodeSpecOf,
      encodeCt1SentMsg] at hpost ⊢
    rwa [← unchunkedMsgEncodeStackOf_eq]
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem msgEnc48RepeatedStackOf_eq (resStack : Nat) :
    msgEnc48RepeatedStackOf resStack = encodeToVecCalleeStackOf resStack := by
  dsimp [msgEnc48RepeatedStackOf, encodeRepeatedStackOf, encodeToVecCalleeStackOf]
  omega

theorem etv_polyEncoderEncode_exact_of_spec {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc} {s0 : State}
    (hpe_ok : subroutine_ok prog call_pc (withStepInv s0 (encodePolyEncoderExactSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (etvPolyEncoderExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialEncoder := ⟨x.enc.idx, x.enc.pts, x.enc.polys⟩
  have hpb : ProtoPolynomialEncoder.toPB pb = x.enc := rfl
  have hpre' : s.mem ⊨ (withStepInv s0 (encodePolyEncoderExactSpecOf resStack A)).pre
      ⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withStepInv, encodePolyEncoderExactSpecOf, etvPolyEncoderExactSpecOf,
      encodePolyEncoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpe_ok.mono_outcome ⟨x.encA, ⟨x.g.pts, x.g.polys⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodePolyEncoderExactSpecOf, etvPolyEncoderExactSpecOf,
      encodePolyEncoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_polyDecoderEncode_exact_of_spec {resStack : Nat}
    {prog : Program} {call_pc : BitVec 64} {A : RustAlloc} {s0 : State}
    (hpd_ok : subroutine_ok prog call_pc (withStepInv s0 (encodePolyDecoderExactSpecOf resStack A))) :
    subroutine_ok prog call_pc (withStepInv s0 (etvPolyDecoderExactSpecOf resStack A)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  let pb : ProtoPolynomialDecoder := ⟨x.dec.ptsNeeded, x.dec.polys, x.dec.pts, x.dec.isComplete⟩
  have hpb : ProtoPolynomialDecoder.toPB pb = x.dec := rfl
  have hpre' : s.mem ⊨ (withStepInv s0 (encodePolyDecoderExactSpecOf resStack A)).pre
      ⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ s ∗ R := by
    dsimp only [withStepInv, encodePolyDecoderExactSpecOf, etvPolyDecoderExactSpecOf,
      encodePolyDecoderMsg] at hpre ⊢
    rwa [msgEnc48RepeatedStackOf_eq, hpb]
  refine hpd_ok.mono_outcome ⟨x.tag, x.decA, ⟨x.g.pts⟩, pb, x.v, x.cap, x.ptr, x.bs⟩ R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hex, hq⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [withStepInv, encodePolyDecoderExactSpecOf, etvPolyDecoderExactSpecOf,
      encodePolyDecoderMsg] at hpost ⊢
    rwa [← msgEnc48RepeatedStackOf_eq, ← hpb]
  · exact Or.inr (Or.inl ⟨hpan, hq⟩)
  · exact (allowPanic_not_exited hq).elim
  · exact (allowPanic_not_exited hoom).elim

theorem etv_leafEncLen16_withStepInv {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen16Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen16Spec reprAt encLen)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, leafEncLen16Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre'⟩
  refine hok.mono_outcome x R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · simp only [leafEncLen16Spec, satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · simp only [leafEncLen16Spec, satisfies_pure_sepConj] at hex; exact hex.1.elim
  · simp only [leafEncLen16Spec, satisfies_pure_sepConj] at hoom; exact hoom.1.elim

theorem etv_leafEncLen48_withStepInv {G M : Type}
    {reprAt : G → BitVec 64 → M → SepProp} {encLen : M → Nat}
    {prog : Program} {call_pc : BitVec 64} {s0 : State}
    (hok : subroutine_ok prog call_pc (leafEncLen48Spec reprAt encLen)) :
    subroutine_ok prog call_pc (withStepInv s0 (leafEncLen48Spec reprAt encLen)) := by
  refine subroutine_ok_outcome_intro fun x R s hpc hrun hpre hal => ?_
  dsimp only [withStepInv, leafEncLen48Spec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨_, hpre'⟩
  refine hok.mono_outcome x R s hpc hrun hpre' hal fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hpan⟩ | ⟨_, _, hex⟩ | ⟨_, hoom⟩
  · exact Or.inl ⟨hret, hcc, hpost⟩
  · simp only [leafEncLen48Spec, satisfies_pure_sepConj] at hpan; exact hpan.1.elim
  · simp only [leafEncLen48Spec, satisfies_pure_sepConj] at hex; exact hex.1.elim
  · simp only [leafEncLen48Spec, satisfies_pure_sepConj] at hoom; exact hoom.1.elim

end CryptoVerification.SpqrV1.Prost.EncodeToVec
