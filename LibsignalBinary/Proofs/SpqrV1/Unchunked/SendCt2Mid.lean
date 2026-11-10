/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Steps
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.SpqrV1.Auth.MacHdr
import LibsignalBinary.Proofs.SpqrV1.States.Leaves.Defs
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Base
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Decodes
import LibsignalBinary.Proofs.SpqrV1.Unchunked.SendCt2Issue1275
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Keys.Agree
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

/-!
# `<Ct1SentEkReceived>::send_ct2`: Segments 3 and 5a

**Checked by Lean.**

Verifies fixed-base Segment 3 (`encapsulate2`, 128-byte `ct2` allocation/copy, conditional
workspace free) and Segment 5a (`ct1.extend(ct2)`, `slice_concat_3`, `libcrux_hmac::hmac`,
and temporary MAC buffer deallocation).
-/

@[expose] public section

namespace CryptoVerification.SpqrV1.Unchunked

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.HMAC (ShaState hmacWith toBEBytes)
open CryptoGames.LibsignalSession (ShaCompress Crypto)
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalSpqrV1
open CryptoVerification.SpqrV1.Alloc
open CryptoVerification.SpqrV1.Auth
open CryptoVerification.SpqrV1.Drop
open CryptoVerification.CodeLayout

set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] spqrAuthApi
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.sub_add_cancel BitVec.toNat_zero

open CryptoVerification.SpqrV1.States.Leaves
open CryptoVerification.SpqrV1.ChainProofs
open CryptoVerification.LibsignalTripleRatchet.Keys
open NextKeyInternalFacts
open AgreeStateSimp
open DoReserveNorm

attribute [local arm64_norm ↓, local wp_norm ↓]
  DoReserveNorm.sp_setPC_pre DoReserveNorm.sp_setMem_setPC_pre
  DoReserveNorm.readReg64_setPC_pre DoReserveNorm.readReg64_setMem_setPC_pre
  DoReserveNorm.readReg32_setPC_pre DoReserveNorm.readReg32_setMem_setPC_pre
  DoReserveNorm.readReg_setPC_pre DoReserveNorm.readReg_setMem_setPC_pre
attribute [local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  bytesAt_true bytesAt_false toBEBytes_8_length ctLabel_length

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  unchunkedCt1SentEkReceivedSendCt2_fnOff
  sliceConcat_fnOff' doReserve7_fnOff mlkemEncaps2_fnOff
  MacHdrFacts.libcruxHmac_fnOff dealloc_fnOff
  (ls_lemma% fnOff "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")
  (ls_lemma% fnOff "<alloc::raw_vec::RawVecInner<_>>::reserve::do_reserve_and_handle::<alloc::alloc::Global> [local#6]")
  (ls_lemma% fnOff "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_hook% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_hook% "__rustc::__rust_dealloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_hook% "alloc::raw_vec::handle_error")
  (ls_stub% "libcrux_ml_kem::mlkem768::incremental::encapsulate2")
  (ls_hook% "libcrux_ml_kem::mlkem768::incremental::encapsulate2")
  (ls_stub% "libcrux_hmac::hmac")
  (ls_hook% "libcrux_hmac::hmac")

theorem encaps2_ok_at_sendCt2 {b : BitVec 64} {K : MlKem}
    {ext : String → Option (State → State)}
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "libcrux_ml_kem::mlkem768::incremental::encapsulate2" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (mlkemEncaps2Spec K) :=
  mlkem_encaps2_ok_at_ext b K ext hencaps2
    unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "libcrux_ml_kem::mlkem768::incremental::encapsulate2" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))

theorem hmac_ok_at_sendCt2 {b : BitVec 64} {F : ShaCompress} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A)) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name +
        bv% (ls_off% "libcrux_hmac::hmac" -
          ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))
      (libcruxHmacSafeSpec F A) :=
  libcrux_hmac_safe_ok_at_ext b F A ext hhmac
    unchunkedCt1SentEkReceivedSendCt2Name
    (num% (ls_off% "libcrux_hmac::hmac" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2"))

theorem call_mlkemEncaps2 {K : MlKem} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (mlkemEncaps2Spec K))
    (ret esA ekA : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx8 : s.readReg64 Reg.x8 = ret)
    (hx0 : s.readReg64 Reg.x0 = esA) (hx1 : s.readReg64 Reg.x1 = ekA)
    (hsplit : P = ((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
      memRegion ret 128 ∗ stackAt sp_call extHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        (((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := ⟨ret, esA, esVec, ekA, ekVec⟩) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; rw [hsplit] at hm; dsimp only [mlkemEncaps2Spec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx8, hx0, hx1⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [mlkemEncaps2Spec]; rw [hsp, htrace]
    refine SepWP.pure_left_focus (sf.trace = s0.trace) (by sep_focus) fun htr_sf => ?_
    have hassoc :
        ((esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack) ∗ Frame =
        (esA ↦ₛ esVec.toList) ∗ (ekA ↦ₛ ekVec.toList) ∗
          (ret ↦ₛ (K.encaps2 esVec ekVec).toList) ∗ stackAt sp_call extHookStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) htr_sf hcs_sf

theorem call_rustDealloc {A : RustAlloc} {prog : Program} {entry ret_pc target_pc : BitVec 64}
    (hcall : subroutine_ok prog entry (rustDeallocSpec A))
    (ptr : BitVec 64) (size align : Nat)
    {s0 s : State} {sp_call : BitVec 64} {P Frame : SepProp}
    {post : State → SepProp → Prop}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.sp = sp_call)
    (hsp_align : (sp_call &&& 15#64 == 0#64) = true)
    (hlr : s.readReg64 Reg.lr = ret_pc) (htrace : s.trace = s0.trace)
    (hx0 : s.readReg64 Reg.x0 = ptr)
    (hx1 : (s.readReg64 Reg.x1).toNat = size) (hx2 : (s.readReg64 Reg.x2).toNat = align)
    (hsplit : P = (A.pool ∗ A.live ptr size align ∗ memRegion ptr size ∗
      stackAt sp_call allocHookStack) ∗ Frame)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_call → sf.trace = s0.trace → CalleeSavedPreserved s sf →
      SepWP prog target_pc sf
        ((A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame) post) :
    SepWP prog target_pc s P post := by
  refine SepWP.call_subroutine_frame hcall (x := (ptr, size, align)) (F := Frame)
    hpc hrun (by rw [State.spAligned, hsp]; exact hsp_align) hlr ?_
    (fun _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun _ _ _ _ h => ((satisfies_pure_sepConj _ _ _).mp h).1)
    (fun sf hpc_sf hrun_sf hsp_sf hcs_sf => ?_)
  · intro R hm; rw [hsplit] at hm; dsimp only [rustDeallocSpec]
    rw [hsp, sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨⟨hx0, hx1, hx2⟩, by simpa only [sepConj_assoc] using hm⟩
  · dsimp only [rustDeallocSpec]; rw [hsp, htrace]
    refine SepWP.pure_left_focus (sf.trace = s0.trace) (by sep_focus) fun htr_sf => ?_
    have hassoc :
        (A.pool ∗ stackAt sp_call allocHookStack) ∗ Frame =
        A.pool ∗ stackAt sp_call allocHookStack ∗ Frame := by ac_rfl
    rw [← hassoc]
    exact hnext sf hpc_sf hrun_sf (hsp_sf.trans hsp) htr_sf hcs_sf

/-! ## Segment 3 (`0x5e628 → 0x5e690`) -/

@[simp, arm64_norm, wp_norm]
theorem sendCt2_extractLsb'_0_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  bv_kernel

@[simp, arm64_norm, wp_norm]
theorem sendCt2_extractLsb'_64_64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  bv_kernel

theorem memRegion_128_cells (a : BitVec 64) :
    memRegion a 128 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
       ∃∗ v4 : BitVec 64, ∃∗ v5 : BitVec 64, ∃∗ v6 : BitVec 64, ∃∗ v7 : BitVec 64,
       ∃∗ v8 : BitVec 64, ∃∗ v9 : BitVec 64, ∃∗ v10 : BitVec 64, ∃∗ v11 : BitVec 64,
       ∃∗ v12 : BitVec 64, ∃∗ v13 : BitVec 64, ∃∗ v14 : BitVec 64, ∃∗ v15 : BitVec 64,
        (a ↦₆₄ v0) ∗ ((a + 8#64) ↦₆₄ v1) ∗ ((a + 16#64) ↦₆₄ v2) ∗ ((a + 24#64) ↦₆₄ v3) ∗
        ((a + 32#64) ↦₆₄ v4) ∗ ((a + 40#64) ↦₆₄ v5) ∗ ((a + 48#64) ↦₆₄ v6) ∗ ((a + 56#64) ↦₆₄ v7) ∗
        ((a + 64#64) ↦₆₄ v8) ∗ ((a + 72#64) ↦₆₄ v9) ∗ ((a + 80#64) ↦₆₄ v10) ∗ ((a + 88#64) ↦₆₄ v11) ∗
        ((a + 96#64) ↦₆₄ v12) ∗ ((a + 104#64) ↦₆₄ v13) ∗ ((a + 112#64) ↦₆₄ v14) ∗ ((a + 120#64) ↦₆₄ v15)) := by
  rw [ProofLib.memRegion_cells a 16 (by decide)]
  dsimp only [cells]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    emp_sepConj, sepConj_emp]

theorem exists_unpack64_of_length_128 {bs : List (BitVec 8)} (h : bs.length = 128) :
    ∃ (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 : BitVec 64),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) =
          (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗ ((a + 24#64) ↦₆₄ w3) ∗
          ((a + 32#64) ↦₆₄ w4) ∗ ((a + 40#64) ↦₆₄ w5) ∗ ((a + 48#64) ↦₆₄ w6) ∗ ((a + 56#64) ↦₆₄ w7) ∗
          ((a + 64#64) ↦₆₄ w8) ∗ ((a + 72#64) ↦₆₄ w9) ∗ ((a + 80#64) ↦₆₄ w10) ∗ ((a + 88#64) ↦₆₄ w11) ∗
          ((a + 96#64) ↦₆₄ w12) ∗ ((a + 104#64) ↦₆₄ w13) ∗ ((a + 112#64) ↦₆₄ w14) ∗ ((a + 120#64) ↦₆₄ w15) := by
  have h1 : (bs.take 64).length = 64 := by rw [List.length_take]; omega
  have h2 : (bs.drop 64).length = 64 := by rw [List.length_drop]; omega
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, ha1, _, _⟩ := exists_unpack64_of_length_64_split h1
  obtain ⟨w8, w9, w10, w11, w12, w13, w14, w15, ha2, _, _⟩ := exists_unpack64_of_length_64_split h2
  refine ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, fun a => ?_⟩
  conv_lhs => rw [← List.take_append_drop 64 bs, pointsToBytes_append, h1]
  rw [ha1 a, ha2 (a + BitVec.ofNat 64 64)]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-- Residual `es` ownership after borrowing `(esWorkPtr ↦ₛ esVec.toList)`. -/
def sendCt2EsAfterWorkAt (A : RustAlloc) (esPtr esWorkPtr : BitVec 64) (es : Bytes) : SepProp :=
  if issue1275NeedsFlip ((es.drop 1536).take 512) then
    ⌜esWorkPtr ≠ 0#64⌝ ∗ (esPtr ↦ₛ es) ∗ A.live esWorkPtr 2080 1
  else
    ⌜esWorkPtr = esPtr⌝

theorem sendCt2EsWorkAt_entails (A : RustAlloc) (esPtr esWorkPtr : BitVec 64) (es : Bytes)
    {esVec : List.Vector (BitVec 8) 2080}
    (hesVec : esVec.toList = if issue1275NeedsFlip ((es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes es else es) :
    sendCt2EsWorkAt A esPtr esWorkPtr es ⊢
      (esWorkPtr ↦ₛ esVec.toList) ∗ sendCt2EsAfterWorkAt A esPtr esWorkPtr es := by
  unfold sendCt2EsWorkAt sendCt2EsAfterWorkAt
  by_cases hflip : issue1275NeedsFlip ((es.drop 1536).take 512) = true
  · simp only [hflip, ↓reduceIte] at hesVec ⊢
    rw [hesVec]
    exact Entails.of_eq (by ac_rfl)
  · simp only [hflip, Bool.false_eq_true, ↓reduceIte] at hesVec ⊢
    rw [hesVec]
    apply Entails.pure_left; intro heq
    subst heq
    rw [sepConj_comm]
    exact Entails.pure_right rfl (Entails.refl _)

set_option maxHeartbeats 1200000 in
/-- Segment 3: `encapsulate2`, `ct2` heap allocation (`128`B) and copy, and conditional `esWorkPtr`
deallocation (`0x5e628 → 0x5e690` + OOM `0x5e84c..0x5e854`). -/
theorem send_ct2_628_to_690_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hencaps2 : HookSat ext mlkemEncaps2Name (mlkemEncaps2Spec K))
    (x : UnchunkedSendCt2Ghost F)
    (esPtr ekPtr esWorkPtr : BitVec 64)
    (esVec : List.Vector (BitVec 8) 2080) (ekVec : List.Vector (BitVec 8) 1152)
    (s0 st : State) (F_frame R : SepProp)
    (hesVec : esVec.toList = if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then
      flipEndiannessOfEncapsulationStateBytes x.st.es else x.st.es)
    (hekVec : ekVec.toList = x.st.ek)
    (hct2_eq : x.ct2 = (K.encaps2 esVec ekVec).toList)
    (hekPtr_ne : ekPtr ≠ 0#64)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 0x228#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx19 : st.readReg64 .x19 = esPtr)
    (hx20 : st.readReg64 .x20 = ekPtr)
    (hx21 : st.readReg64 .x21 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 1#64 else 0#64))
    (hx22 : st.readReg64 .x22 = esWorkPtr)
    (hx27 : st.readReg64 .x27 = 1152#64)
    (hx28 : st.readReg64 .x28 = (if issue1275NeedsFlip ((x.st.es.drop 1536).take 512) then 2080#64 else bv% (2 ^ 64 - 1)))
    (hcont : ∀ (st' : State) (ptr_ct2 : BitVec 64),
      ptr_ct2 ≠ 0#64 →
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 656#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = esPtr →
      st'.readReg64 .x20 = ekPtr →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = st.readReg64 .x25 →
      st'.readReg64 .x26 = st.readReg64 .x26 →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = st.readReg64 .x29 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        ((esPtr ↦ₛ x.st.es) ∗
          (ekPtr ↦ₛ x.st.ek) ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          A.live ptr_ct2 128 1 ∗
          memRegion (s0.sp - 272#64) 128 ∗
          A.pool ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PostQ A F K b x s0 R)
        (sendCt2PostQp A F K b x s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (sendCt2EsWorkAt A esPtr esWorkPtr x.st.es ∗
        (ekPtr ↦ₛ x.st.ek) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        A.pool ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PostQ A F K b x s0 R)
      (sendCt2PostQp A F K b x s0 R) := by
  have henc := encaps2_ok_at_sendCt2 (b := b) hencaps2
  have hshim := shim_ok_at_sendCt2 hA
  have halloc := alloc_ok_at_sendCt2 hA
  have hdealloc := dealloc_ok_at_sendCt2 hA
  have hpan := panic_at_handle_error_sendCt2 b ext
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hek_beq : (ekPtr == 0#64) = false := beq_false_of_ne hekPtr_ne
  have hct2_len : x.ct2.length = 128 := by rw [hct2_eq]; exact (K.encaps2 esVec ekVec).2
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx19 hx20 hx21 hx22 hx27 hx28
  unfold tripleRatchetProgAtExt at hpc henc hshim halloc hdealloc hpan hcont ⊢
  send_ct2_fetches_range b (Rust.withPanics ext) 552 104
  send_ct2_fetches_range b (Rust.withPanics ext) 1100 12
  clear hA hencaps2
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      unchunkedCt1SentEkReceivedSendCt2Name = entry
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  refine SepWPp.fold (sendCt2EsWorkAt_entails A esPtr esWorkPtr x.st.es hesVec) (by sep_focus) ?_
  refine SepWPp.rw_pre (by rw [← hekVec]) ?_
  refine SepWPp.of_sepWP_mid (mid := entry + 596#64) ?_
  wp_steps
  refine call_mlkemEncaps2 henc (s0.sp - 272#64) esWorkPtr ekPtr esVec ekVec
    (s0 := s0) (ret_pc := entry + 580#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x8, arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf1 hpc1 hrun1 hsp1 htr1 hcs1 => ?_)
  rcases hcs1 with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
  simp only [arm64_norm] at hx19_1 hx20_1 hx21_1 hx22_1 hx23_1 hx24_1 hx25_1 hx26_1 hx27_1 hx28_1 hfp_1
  wp_steps; wp_apply; wp_steps
  have hstack_alloc :
      stackAt (s0.sp - 336#64) extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine SepWP.fold hstack_alloc (by sep_focus) ?_
  have hlay_128 : LayoutOk 128 1 := ⟨by decide, ⟨0, rfl⟩, by decide⟩
  refine call_rustAlloc halloc 128 1 hlay_128
    (s0 := s0) (ret_pc := entry + 596#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *]) (by simp only [Reg.x1, arm64_norm, *])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 hcs2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  by_cases hoom : sf2.readReg64 (Reg.gpr 0#5) = 0
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun htr_oom => ?_
    refine SepWPp.of_sepWP_mid
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) ?_
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) (by wp_norm_lhs) fun hm => ?_
    dsimp only [sendCt2PostQp, unchunkedCt1SentEkReceivedSendCt2Spec]
    simpa only [sepConj_assoc] using
      allowPanic_panicked (allocFailedIn_of_eq (by simp only [Rust.panicked, wp_norm, arm64_norm, *])) hm
  · conv => arg 4; simp only [Reg.x0, hoom, ↓reduceIte, sepConj_assoc]
    refine SepWPp.pure_elim fun ⟨_, htr_ok⟩ => ?_
    have hoom_false : (sf2.readReg64 (Reg.gpr 0#5) == 0#64) = false := beq_false_of_ne hoom
    obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, hct2_cells⟩ :=
      exists_unpack64_of_length_128 hct2_len
    refine SepWPp.rw_pre (by
      rw [← hct2_eq, hekVec,
        hct2_cells (s0.sp - 272#64),
        memRegion_128_cells (sf2.readReg64 (Reg.gpr 0#5))]) ?_
    sep_elim_exists
    by_cases hflip : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = false
    · refine SepWPp.rw_pre (by
        unfold sendCt2EsAfterWorkAt
        simp only [hflip, Bool.false_eq_true, ↓reduceIte] at hesVec ⊢
        rw [hesVec]) ?_
      refine SepWPp.pure_left_focus (esWorkPtr = esPtr) (by sep_focus) fun hwork_eq => ?_
      subst hwork_eq
      refine SepWPp.of_sepWP_mid (mid := entry + 656#64) ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hct2_cells (sf2.readReg64 (Reg.gpr 0#5))).symm) (by sep_focus) ?_
      have hsp_cells_back :
          ((s0.sp - 272#64) ↦₆₄ w0) ∗ ((s0.sp - 272#64 + 8#64) ↦₆₄ w1) ∗
            ((s0.sp - 272#64 + 16#64) ↦₆₄ w2) ∗ ((s0.sp - 272#64 + 24#64) ↦₆₄ w3) ∗
            ((s0.sp - 272#64 + 32#64) ↦₆₄ w4) ∗ ((s0.sp - 272#64 + 40#64) ↦₆₄ w5) ∗
            ((s0.sp - 272#64 + 48#64) ↦₆₄ w6) ∗ ((s0.sp - 272#64 + 56#64) ↦₆₄ w7) ∗
            ((s0.sp - 272#64 + 64#64) ↦₆₄ w8) ∗ ((s0.sp - 272#64 + 72#64) ↦₆₄ w9) ∗
            ((s0.sp - 272#64 + 80#64) ↦₆₄ w10) ∗ ((s0.sp - 272#64 + 88#64) ↦₆₄ w11) ∗
            ((s0.sp - 272#64 + 96#64) ↦₆₄ w12) ∗ ((s0.sp - 272#64 + 104#64) ↦₆₄ w13) ∗
            ((s0.sp - 272#64 + 112#64) ↦₆₄ w14) ∗ ((s0.sp - 272#64 + 120#64) ↦₆₄ w15) ⊢
            memRegion (s0.sp - 272#64) 128 := by
        rw [← hct2_cells (s0.sp - 272#64)]
        exact hct2_len ▸ pointsToBytes_entails_memRegion (s0.sp - 272#64) x.ct2
      refine SepWP.fold hsp_cells_back (by sep_focus) ?_
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
      refine SepWP.fold hstack_back (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ (sf2.readReg64 (Reg.gpr 0#5)) hoom
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [Reg.x29, wp_norm, arm64_norm, *]))
    · have hflip_t : issue1275NeedsFlip ((x.st.es.drop 1536).take 512) = true :=
        Bool.eq_true_of_not_eq_false hflip
      refine SepWPp.rw_pre (by
        unfold sendCt2EsAfterWorkAt
        simp only [hflip_t, ↓reduceIte]; rfl) ?_
      refine SepWPp.pure_left_focus (esWorkPtr ≠ 0#64) (by sep_focus) fun hwork_ne => ?_
      refine SepWPp.of_sepWP_mid (mid := entry + 656#64) ?_
      wp_steps
      refine SepWP.fold (Entails.of_eq (hct2_cells (sf2.readReg64 (Reg.gpr 0#5))).symm) (by sep_focus) ?_
      have hsp_cells_back :
          ((s0.sp - 272#64) ↦₆₄ w0) ∗ ((s0.sp - 272#64 + 8#64) ↦₆₄ w1) ∗
            ((s0.sp - 272#64 + 16#64) ↦₆₄ w2) ∗ ((s0.sp - 272#64 + 24#64) ↦₆₄ w3) ∗
            ((s0.sp - 272#64 + 32#64) ↦₆₄ w4) ∗ ((s0.sp - 272#64 + 40#64) ↦₆₄ w5) ∗
            ((s0.sp - 272#64 + 48#64) ↦₆₄ w6) ∗ ((s0.sp - 272#64 + 56#64) ↦₆₄ w7) ∗
            ((s0.sp - 272#64 + 64#64) ↦₆₄ w8) ∗ ((s0.sp - 272#64 + 72#64) ↦₆₄ w9) ∗
            ((s0.sp - 272#64 + 80#64) ↦₆₄ w10) ∗ ((s0.sp - 272#64 + 88#64) ↦₆₄ w11) ∗
            ((s0.sp - 272#64 + 96#64) ↦₆₄ w12) ∗ ((s0.sp - 272#64 + 104#64) ↦₆₄ w13) ∗
            ((s0.sp - 272#64 + 112#64) ↦₆₄ w14) ∗ ((s0.sp - 272#64 + 120#64) ↦₆₄ w15) ⊢
            memRegion (s0.sp - 272#64) 128 := by
        rw [← hct2_cells (s0.sp - 272#64)]
        exact hct2_len ▸ pointsToBytes_entails_memRegion (s0.sp - 272#64) x.ct2
      refine SepWP.fold hsp_cells_back (by sep_focus) ?_
      have hwork_mr : (esWorkPtr ↦ₛ esVec.toList) ⊢ memRegion esWorkPtr 2080 := by
        simpa only [esVec.toList_length] using pointsToBytes_entails_memRegion esWorkPtr esVec.toList
      refine SepWP.fold hwork_mr (by sep_focus) ?_
      refine call_rustDealloc hdealloc esWorkPtr 2080 1
        (s0 := s0) (ret_pc := entry + 656#64) (sp_call := s0.sp - 336#64)
        (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [State.sp, arm64_norm, *]) hfsp_align
        (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
        (by simp only [Reg.x0, arm64_norm, *])
        (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
        (by sep_focus)
        (fun sf3 hpc3 hrun3 hsp3 htr3 hcs3 => ?_)
      rcases hcs3 with ⟨hx19_3, hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hfp_3, hvregs_3⟩
      simp only [arm64_norm] at hx19_3 hx20_3 hx21_3 hx22_3 hx23_3 hx24_3 hx25_3 hx26_3 hx27_3 hx28_3 hfp_3
      have hstack_back :
          memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
            stackAt (s0.sp - 336#64) extHookStack :=
        Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
      refine SepWP.fold hstack_back (by sep_focus) ?_
      apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      refine SepWPp.rw_pre (by ac_rfl)
        (hcont _ (sf2.readReg64 (Reg.gpr 0#5)) hoom
          (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [State.sp, wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [Reg.x19, wp_norm, arm64_norm, *])
          (by simp only [Reg.x20, wp_norm, arm64_norm, *])
          (by simp only [Reg.x23, wp_norm, arm64_norm, *])
          (by simp only [Reg.x24, wp_norm, arm64_norm, *])
          (by simp only [Reg.x25, wp_norm, arm64_norm, *])
          (by simp only [Reg.x26, wp_norm, arm64_norm, *])
          (by simp only [Reg.x27, wp_norm, arm64_norm, *])
          (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

/-! ## Segment 5a (`0x5e6a4 → 0x5e744`) -/

theorem page_align_mask {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    b &&& 18446744073709547520#64 = b := by
  have hb : (b &&& 18446744073709547520#64) + (b &&& 4095#64) = b := by bv_kernel
  rw [halign, BitVec.add_zero] at hb
  exact hb

theorem adrp_ctLabel_sendCt2 {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    ((b + bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) + 740#64 &&& 18446744073709547520#64) + bv% (ls_xref% 0x592ec 0x592f0 - 0x59000) =
      b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext") := by
  rw [← page_align_mask halign]; bv_kernel

theorem adrp_ctLabel_sendCt2' {b : BitVec 64} (halign : b &&& 4095#64 = 0#64) :
    ((b + bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) + 740#64 &&& 18446744073709547520#64) + bv% (ls_xref% 0x592ec - 0x59000) + bv% ((ls_xref% 0x592ec 0x592f0) % 4096) =
      b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext") := by
  rw [← page_align_mask halign]; bv_kernel

theorem vecU8_expose_nonempty_144 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8))
    (hpos : 0 < bs.length) :
    vecU8 A (sp - 144#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ⌜cap ≠ 0#64 ∧ LayoutOk cap.toNat 1 ∧ ptr ≠ 0#64 ∧ bs.length ≤ cap.toNat⌝ ∗
          ((sp - 144#64) ↦₆₄ cap) ∗
          ((sp - 136#64) ↦₆₄ ptr) ∗
          ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
          (ptr ↦ₛ bs) ∗
          memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1 := by
  dsimp only [vecU8]
  refine Entails.sepExists_elim fun cap => Entails.sepExists_elim fun ptr => ?_
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  rw [vecU8At_eq_cells_heap A (sp - 144#64) cap ptr bs]
  have h8 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have h16 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  rw [h8, h16]
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (vecU8HeapAt_expose_nonempty A cap ptr bs hpos)))) ?_
  have hcomm :
      ((sp - 144#64) ↦₆₄ cap) ∗ ((sp - 136#64) ↦₆₄ ptr) ∗
        ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
          (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
          A.live ptr cap.toNat 1) =
      ⌜bs.length ≤ cap.toNat ∧ cap.toNat < 2 ^ 63 ∧ ptr ≠ 0#64 ∧ cap ≠ 0#64⌝ ∗
        ((sp - 144#64) ↦₆₄ cap) ∗ ((sp - 136#64) ↦₆₄ ptr) ∗
        ((sp - 128#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ∗
        A.live ptr cap.toNat 1 := by ac_rfl
  rw [hcomm]
  refine Entails.pure_left fun ⟨hle, hmax, hptr, hcap⟩ => ?_
  have hpos_cap : 0 < cap.toNat := by
    have : cap.toNat ≠ 0 := fun h0 => hcap (BitVec.eq_of_toNat_eq h0)
    omega
  have hlay : LayoutOk cap.toNat 1 := ⟨hpos_cap, ⟨0, rfl⟩, by omega⟩
  exact Entails.pure_right ⟨hcap, hlay, hptr, hle⟩ (Entails.refl _)

theorem memRegion_ct1_split_128_len (ptr_ct1' : BitVec 64) {len cap : Nat}
    (hge : len + 128 ≤ cap) (hlt : cap < 2 ^ 63) :
    memRegion (ptr_ct1' + BitVec.ofNat 64 len) (cap - len) =
      memRegion (ptr_ct1' + BitVec.ofNat 64 len) 128 ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 (len + 128)) (cap - (len + 128)) := by
  have h1 : cap - len = 128 + (cap - (len + 128)) := by omega
  have h2 : ptr_ct1' + BitVec.ofNat 64 (len + 128) =
      (ptr_ct1' + BitVec.ofNat 64 len) + BitVec.ofNat 64 128 := by bv_omega
  rw [ProofLib.memRegion_split' (b := ptr_ct1' + BitVec.ofNat 64 len) (n := 128)
        (k := cap - (len + 128)) (b' := ptr_ct1' + BitVec.ofNat 64 (len + 128))
        h1 h2 (by omega)]

theorem pointsToBytes_append_ct1_ct2 (ptr : BitVec 64) (bs1 bs2 : List (BitVec 8)) :
    (ptr ↦ₛ bs1) ∗ ((ptr + BitVec.ofNat 64 bs1.length) ↦ₛ bs2) ⊢ (ptr ↦ₛ (bs1 ++ bs2)) := by
  rw [pointsToBytes_append ptr bs1 bs2]
  exact Entails.refl _

theorem memRegion_sp_272_split_48_80 (sp : BitVec 64) :
    memRegion (sp - 272#64) 128 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 272#64) ↦₆₄ s0) ∗ ((sp - 264#64) ↦₆₄ s1) ∗
        ((sp - 256#64) ↦₆₄ s2) ∗ ((sp - 248#64) ↦₆₄ s3) ∗
        ((sp - 240#64) ↦₆₄ s4) ∗ ((sp - 232#64) ↦₆₄ s5)) ∗
      memRegion (sp - 224#64) 80 := by
  rw [ProofLib.memRegion_split' (b := sp - 272#64) (n := 48) (k := 80)
        (b' := sp - 224#64) rfl (by bv_omega) (by decide)]
  change memRegion (sp - 272#64) (8 * 6) ∗ memRegion (sp - 224#64) 80 = _
  rw [ProofLib.memRegion_cells (sp - 272#64) 6 (by decide)]
  have hc6 : cells (sp - 272#64) 6 =
      (∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
       ∃∗ s3 : BitVec 64, ∃∗ s4 : BitVec 64, ∃∗ s5 : BitVec 64,
        ((sp - 272#64) ↦₆₄ s0) ∗ ((sp - 264#64) ↦₆₄ s1) ∗
        ((sp - 256#64) ↦₆₄ s2) ∗ ((sp - 248#64) ↦₆₄ s3) ∗
        ((sp - 240#64) ↦₆₄ s4) ∗ ((sp - 232#64) ↦₆₄ s5)) := by
    cells_unfold
  rw [hc6]

theorem memRegion_24_cells (a : BitVec 64) :
    memRegion a 24 =
      ∃∗ s0 : BitVec 64, ∃∗ s1 : BitVec 64, ∃∗ s2 : BitVec 64,
        (a ↦₆₄ s0) ∗ ((a + 8#64) ↦₆₄ s1) ∗ ((a + 16#64) ↦₆₄ s2) := by
  have h16 : a + 8#64 + 8#64 = a + 16#64 := by bv_omega
  change memRegion a (8 * 3) = _
  rw [ProofLib.memRegion_cells a 3 (by decide)]
  dsimp only [cells]
  simp only [BitVec.add_zero, h16, sepExists_sepConj_left, sepExists_sepConj_right, sepConj_emp]

theorem fold_sp_272_24_24 (sp v0 v1 v2 v3 v4 v5 : BitVec 64) :
    ((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ∗
      ((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5) ⊢
      memRegion (sp - 272#64) 24 ∗ memRegion (sp - 248#64) 24 := by
  have h1 : (sp - 272#64) + 8#64 = sp - 264#64 := by bv_omega
  have h2 : (sp - 272#64) + 16#64 = sp - 256#64 := by bv_omega
  have h3 : (sp - 248#64) + 8#64 = sp - 240#64 := by bv_omega
  have h4 : (sp - 248#64) + 16#64 = sp - 232#64 := by bv_omega
  have ha : ((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ⊢
      memRegion (sp - 272#64) 24 := by
    rw [memRegion_24_cells (sp - 272#64), h1, h2]
    exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.refl _)))
  have hb : ((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5) ⊢
      memRegion (sp - 248#64) 24 := by
    rw [memRegion_24_cells (sp - 248#64), h3, h4]
    exact Entails.sepExists_right v3 (Entails.sepExists_right v4 (Entails.sepExists_right v5 (Entails.refl _)))
  have hgroup :
      ((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2) ∗
        ((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5) =
      (((sp - 272#64) ↦₆₄ v0) ∗ ((sp - 264#64) ↦₆₄ v1) ∗ ((sp - 256#64) ↦₆₄ v2)) ∗
        (((sp - 248#64) ↦₆₄ v3) ∗ ((sp - 240#64) ↦₆₄ v4) ∗ ((sp - 232#64) ↦₆₄ v5)) := by ac_rfl
  rw [hgroup]
  exact sepConj_mono ha hb

theorem fold_sp_144_24 (sp v0 v1 v2 : BitVec 64) :
    ((sp - 144#64) ↦₆₄ v0) ∗ ((sp - 136#64) ↦₆₄ v1) ∗ ((sp - 128#64) ↦₆₄ v2) ⊢
      memRegion (sp - 144#64) 24 := by
  have ha1 : (sp - 144#64) + 8#64 = sp - 136#64 := by bv_omega
  have ha2 : (sp - 144#64) + 16#64 = sp - 128#64 := by bv_omega
  rw [memRegion_24_cells (sp - 144#64), ha1, ha2]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1 (Entails.sepExists_right v2 (Entails.refl _)))

theorem bytes_rem_entails_memRegion_cap (ptr cap : BitVec 64) (bs : List (BitVec 8))
    (hle : bs.length ≤ cap.toNat) (hmax : cap.toNat < 2 ^ 63) :
    (ptr ↦ₛ bs) ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) ⊢
      memRegion ptr cap.toNat := by
  have hsplit : memRegion ptr cap.toNat =
      memRegion ptr bs.length ∗ memRegion (ptr + BitVec.ofNat 64 bs.length) (cap.toNat - bs.length) := by
    conv_lhs => rw [show cap.toNat = bs.length + (cap.toNat - bs.length) by omega]
    exact ProofLib.memRegion_split ptr bs.length (cap.toNat - bs.length) (by omega)
  rw [hsplit]
  exact sepConj_mono_left (pointsToBytes_entails_memRegion ptr bs)

set_option maxHeartbeats 1600000 in
/-- Segment 5a: copy `ct2` to `ptr_ct1' + x.st.ct1.length`, call `slice_concat_3` (`0x63eb0`),
call `libcrux_hmac::hmac` (`0x78c1c`), and deallocate the temporary message buffer (`0x5e6a4 → 0x5e744`). -/
theorem send_ct2_append_hmac_wpp {b : BitVec 64} {K : MlKem} {F : ShaCompress}
    {A : RustAlloc} {ext : String → Option (State → State)}
    (hA : AllocContracts4K b A ext)
    (hconcat3 : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr sliceConcatName) (sliceConcat3Spec A))
    (hhmac : HookSat ext libcruxHmacName (libcruxHmacSpec F A))
    (x : UnchunkedSendCt2Ghost F)
    (mkPtr cap_ct1' ptr_ct1' ptr_ct2 e0 : BitVec 64)
    (s0 st : State) (F_frame R : SepProp)
    (hb : b &&& 0xfff#64 = 0#64)
    (hct2_len : x.ct2.length = 128)
    (hmk_lt32 : x.st.auth.macKey.length < 2 ^ 32)
    (hdata_lt32 : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length < 2 ^ 32)
    (hmac_eq : x.mac = x.st.auth.macCtUnchecked F x.st.epoch (x.st.ct1 ++ x.ct2))
    (hge128 : x.st.ct1.length + 128 ≤ cap_ct1'.toNat)
    (hmax_ct1' : cap_ct1'.toNat < 2 ^ 63)
    (hpc : st.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 676#64)
    (hrun : st.status = .Running)
    (hsp : st.sp = s0.sp - 336#64)
    (hsp_s0 : (s0.sp &&& 15#64 == 0#64) = true)
    (htr : st.trace = s0.trace)
    (hvregs : calleeSavedVRegs st = calleeSavedVRegs s0)
    (hx1 : st.readReg64 .x1 = BitVec.ofNat 64 x.st.ct1.length)
    (hx25 : st.readReg64 .x25 = mkPtr)
    (hx26 : st.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length)
    (hx27 : st.readReg64 .x27 = ptr_ct2)
    (hx29 : st.readReg64 .x29 = s0.sp - 96#64)
    (hcont : ∀ (st' : State),
      st'.pc = (tripleRatchetProgAtExt b ext).fnAddr unchunkedCt1SentEkReceivedSendCt2Name + 836#64 →
      st'.status = .Running →
      st'.sp = s0.sp - 336#64 →
      st'.trace = s0.trace →
      calleeSavedVRegs st' = calleeSavedVRegs s0 →
      st'.readReg64 .x19 = st.readReg64 .x19 →
      st'.readReg64 .x20 = st.readReg64 .x20 →
      st'.readReg64 .x22 = ptr_ct1' →
      st'.readReg64 .x23 = st.readReg64 .x23 →
      st'.readReg64 .x24 = st.readReg64 .x24 →
      st'.readReg64 .x25 = mkPtr →
      st'.readReg64 .x26 = BitVec.ofNat 64 x.st.auth.macKey.length →
      st'.readReg64 .x27 = ptr_ct2 →
      st'.readReg64 .x29 = s0.sp - 96#64 →
      SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st'
        (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
          ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
          ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
          ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
          memRegion ptr_ct1' cap_ct1'.toNat ∗
          A.live ptr_ct1' cap_ct1'.toNat 1 ∗
          (ptr_ct2 ↦ₛ x.ct2) ∗
          (mkPtr ↦ₛ x.st.auth.macKey) ∗
          vecU8 A (s0.sp - 272#64) x.mac ∗
          memRegion (s0.sp - 248#64) 24 ∗
          memRegion (s0.sp - 224#64) 80 ∗
          memRegion (s0.sp - 144#64) 24 ∗
          ((s0.sp - 120#64) ↦ₛ toBEBytes 8 x.st.epoch) ∗
          ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
          A.pool ∗
          stackAt (s0.sp - 336#64) extHookStack ∗
          F_frame)
        (sendCt2PostQ A F K b x s0 R)
        (sendCt2PostQp A F K b x s0 R)) :
    SepWPp (tripleRatchetProgAtExt b ext) (s0.readReg64 .x30) st
      (((s0.sp - 312#64) ↦₆₄ x.st.epoch) ∗
        ((s0.sp - 304#64) ↦₆₄ cap_ct1') ∗
        ((s0.sp - 296#64) ↦₆₄ ptr_ct1') ∗
        ((s0.sp - 288#64) ↦₆₄ BitVec.ofNat 64 x.st.ct1.length) ∗
        (ptr_ct1' ↦ₛ x.st.ct1) ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length) (cap_ct1'.toNat - x.st.ct1.length) ∗
        A.live ptr_ct1' cap_ct1'.toNat 1 ∗
        (ptr_ct2 ↦ₛ x.ct2) ∗
        (mkPtr ↦ₛ x.st.auth.macKey) ∗
        memRegion (s0.sp - 272#64) 128 ∗
        memRegion (s0.sp - 144#64) 24 ∗
        ((s0.sp - 120#64) ↦₆₄ e0) ∗
        ((b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) ↦ᵣ Authenticator.ctLabel) ∗
        A.pool ∗
        stackAt (s0.sp - 336#64) extHookStack ∗
        F_frame)
      (sendCt2PostQ A F K b x s0 R)
      (sendCt2PostQp A F K b x s0 R) := by
  have h_concat3 := sliceConcat3_ok_at_sendCt2 hconcat3
  have h_hmac := hmac_ok_at_sendCt2 (b := b) (A := A) hhmac
  have h_dealloc := dealloc_ok_at_sendCt2 hA
  have hadrp_ct := adrp_ctLabel_sendCt2 hb
  have hadrp_ct' := adrp_ctLabel_sendCt2' hb
  have hfsp_align : ((s0.sp - 336#64) &&& 15#64 == 0#64) = true := by revert hsp_s0; bv_kernel
  have hsp_norm : st.readReg64 .sp = s0.sp - 336#64 := hsp
  simp only [wp_norm, arm64_norm] at hsp_norm hx1 hx25 hx26 hx27 hx29
  unfold tripleRatchetProgAtExt at hpc h_concat3 h_hmac h_dealloc hcont ⊢
  send_ct2_fetches_range b (Rust.withPanics ext) 676 160
  have hfn_eq : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr unchunkedCt1SentEkReceivedSendCt2Name =
      b + bv% (ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2") := by
    rw [Program.fnAddr_rebase, unchunkedCt1SentEkReceivedSendCt2_fnOff]
  rw [← hfn_eq] at hadrp_ct hadrp_ct'
  clear hA hconcat3 hhmac hfn_eq
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      unchunkedCt1SentEkReceivedSendCt2Name = entry
  generalize_entry
    (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok, SepWPp]
  examples_hide_fetches
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, hct2_cells⟩ :=
    exists_unpack64_of_length_128 hct2_len
  refine SepWPp.rw_pre (by
    rw [memRegion_ct1_split_128_len ptr_ct1' hge128 hmax_ct1',
      memRegion_128_cells (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length),
      hct2_cells ptr_ct2,
      memRegion_sp_272_split_48_80 s0.sp]) ?_
  sep_elim_exists
  refine SepWPp.of_sepWP_mid
    (mid := entry + bv% (ls_off% "<[&[u8]] as alloc::slice::Concat<u8>>::concat [local#2]" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) ?_
  wp_steps
  refine SepWP.fold (Entails.of_eq (hct2_cells ptr_ct2).symm) (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (hct2_cells (ptr_ct1' + BitVec.ofNat 64 x.st.ct1.length)).symm)
    (by sep_focus) ?_
  refine SepWP.fold
    (pointsToBytes_append_ct1_ct2 ptr_ct1' x.st.ct1 x.ct2)
    (by sep_focus) ?_
  refine SepWP.fold
    (Entails.of_eq (pointsTo64_rev64_eq_toBEBytes (s0.sp - 120#64) x.st.epoch))
    (by sep_focus) ?_
  have hct1_full_len :
      BitVec.ofNat 64 x.st.ct1.length + 128#64 = BitVec.ofNat 64 (x.st.ct1 ++ x.ct2).length := by
    rw [List.length_append, hct2_len]; bv_omega
  have hconcat3_bound :
      35 + 8 + (x.st.ct1 ++ x.ct2).length < 9223372036854775808 := by
    have hd : (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length =
        35 + 8 + (x.st.ct1 ++ x.ct2).length := by
      rw [List.length_append, List.length_append, ctLabel_length, toBEBytes_8_length]
    omega
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  wpp_call_sendCt2 h_concat3
    (⟨s0.sp - 144#64, s0.sp - 272#64,
      true, b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext"), Authenticator.ctLabel,
      false, s0.sp - 120#64, toBEBytes 8 x.st.epoch,
      false, ptr_ct1', x.st.ct1 ++ x.ct2⟩ : SliceConcat3Ghost)
  simp only [hsp, hx25, hx26, hx27, hx29] at hsp_sf h_6 h_7 h_8 hcs_sf
  rw [← List.append_assoc Authenticator.ctLabel]
  have hdata_pos :
      0 < (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length := by
    simp only [List.length_append, ctLabel_length]
    omega
  refine SepWPp.fold
    (vecU8_expose_nonempty_144 A s0.sp
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2))
      hdata_pos)
    (by sep_focus) ?_
  sep_elim_exists
  rename_i cap_md ptr_md
  refine SepWPp.pure_left_focus _ (by sep_focus) ?_
  rintro ⟨hcap_md_ne, hlay_md, hptr_md_ne, hle_md⟩
  have ⟨_, _, hmax_md⟩ := hlay_md
  have hcap_md_beq : (cap_md == 0#64) = false := beq_false_of_ne hcap_md_ne
  refine SepWPp.fold
    (fold_sp_272_24_24 s0.sp
      (b + bv% (ls_str% "Signal_PQCKA_V1_MLKEM768:ciphertext")) 35#64
      (s0.sp - 120#64) 8#64 ptr_ct1'
      (BitVec.ofNat 64 (x.st.ct1 ++ x.ct2).length))
    (by sep_focus) ?_
  have hfold_ct1 :
      (ptr_ct1' ↦ₛ (x.st.ct1 ++ x.ct2)) ∗
        memRegion (ptr_ct1' + BitVec.ofNat 64 (x.st.ct1.length + 128)) (cap_ct1'.toNat - (x.st.ct1.length + 128)) ⊢
        memRegion ptr_ct1' cap_ct1'.toNat := by
    rw [← show (x.st.ct1 ++ x.ct2).length = x.st.ct1.length + 128 by rw [List.length_append, hct2_len]]
    exact bytes_rem_entails_memRegion_cap ptr_ct1' cap_ct1' (x.st.ct1 ++ x.ct2)
      (by rw [List.length_append, hct2_len]; omega) hmax_ct1'
  refine SepWPp.fold hfold_ct1 (by sep_focus) ?_
  refine SepWPp.of_sepWP_mid
    (mid := entry + bv% (ls_off% "libcrux_hmac::hmac" -
      ls_off% "<spqr::v1::unchunked::send_ct::Ct1SentEkReceived>::send_ct2")) ?_
  wp_steps
  refine SepWP.fold
    (Entails.of_eq (show stackAt st.sp extHookStack = stackAt sf.sp extHookStack by rw [hsp, hsp_sf]))
    (by sep_focus) ?_
  have hmk_toNat : (BitVec.ofNat 64 x.st.auth.macKey.length).toNat = x.st.auth.macKey.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hdata_toNat :
      (BitVec.ofNat 64 (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length).toNat =
        (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  wpp_call_sendCt2 h_hmac
    (⟨s0.sp - 272#64, mkPtr, x.st.auth.macKey,
      ptr_md, Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)⟩ : LibcruxHmacCall)
  rw [hsp_sf] at hsp_sf_1
  rw [hcs_sf] at hcs_sf_1
  rw [← List.append_assoc Authenticator.ctLabel, ← macCtUnchecked_eq_hmacWith F x.st.auth x.st.epoch (x.st.ct1 ++ x.ct2), ← hmac_eq]
  refine SepWPp.fold
    (bytes_rem_entails_memRegion_cap ptr_md cap_md
      (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2))
      hle_md hmax_md)
    (by sep_focus) ?_
  refine SepWPp.of_sepWP_mid (mid := entry + 836#64) ?_
  wp_steps
  refine SepWP.fold
    (fold_sp_144_24 s0.sp cap_md ptr_md
      (BitVec.ofNat 64 (Authenticator.ctLabel ++ toBEBytes 8 x.st.epoch ++ (x.st.ct1 ++ x.ct2)).length))
    (by sep_focus) ?_
  have hstack_alloc :
      stackAt sf.sp extHookStack ⊢
        memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack := by
    rw [hsp_sf]
    exact Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp)
  refine SepWP.fold hstack_alloc (by sep_focus) ?_
  have hcap_md_toNat : (cap_md).toNat = cap_md.toNat := rfl
  refine call_rustDealloc h_dealloc ptr_md cap_md.toNat 1
    (s0 := s0) (ret_pc := entry + 836#64) (sp_call := s0.sp - 336#64)
    (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [State.sp, arm64_norm, *]) hfsp_align
    (by simp only [Reg.lr, arm64_norm, *]) (by simp only [arm64_norm, *])
    (by simp only [Reg.x0, arm64_norm, *])
    (by simp only [Reg.x1, arm64_norm, *]) (by simp only [Reg.x2, arm64_norm, *])
    (by sep_focus)
    (fun sf2 hpc2 hrun2 hsp2 htr_sf2 hcs2 => ?_)
  rcases hcs2 with ⟨hx19_2, hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hfp_2, hvregs_2⟩
  simp only [arm64_norm] at hx19_2 hx20_2 hx21_2 hx22_2 hx23_2 hx24_2 hx25_2 hx26_2 hx27_2 hx28_2 hfp_2
  have hstack_back :
      memRegion (s0.sp - 16720#64) 12288 ∗ stackAt (s0.sp - 336#64) allocHookStack ⊢
        stackAt (s0.sp - 336#64) extHookStack :=
    Entails.of_eq (stackAt_extHook_eq_allocHook s0.sp).symm
  refine SepWP.fold hstack_back (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
  refine SepWPp.rw_pre (by ac_rfl)
    (hcont sf2
      (by wp_norm_goal) (by simp only [wp_norm, arm64_norm, *])
      (by simp only [State.sp, wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [Reg.x19, wp_norm, arm64_norm, *])
      (by simp only [Reg.x20, wp_norm, arm64_norm, *])
      (by simp only [Reg.x22, wp_norm, arm64_norm, *])
      (by simp only [Reg.x23, wp_norm, arm64_norm, *])
      (by simp only [Reg.x24, wp_norm, arm64_norm, *])
      (by simp only [Reg.x25, wp_norm, arm64_norm, *])
      (by simp only [Reg.x26, wp_norm, arm64_norm, *])
      (by simp only [Reg.x27, wp_norm, arm64_norm, *])
      (by simp only [Reg.x29, wp_norm, arm64_norm, *]))

end CryptoVerification.SpqrV1.Unchunked
