/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Defs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2Qpan
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.AssemblyP2b2
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSpe2Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.DropSs3Ext
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP2BlocksErrA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.WireEntries.RecvWireSameAccount
import LibsignalBinary.Proofs.Cli.E2E.V1.BobTailV1
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderCore.AcceptDecode
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSlice
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageMerge.PolyCommon
import LibsignalBinary.Proofs.TripleRatchet.Alloc.PublicKeySerialize
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Step244

/-!
# Stage P2 Pure and Internal Callee Instantiation

Constructs `StageP2PureCallees` and `StageP2PureCallees4K` over `tripleRatchetExterns C ctl abs`
from the verified internal callees and SPQR V1 `initialize_bob_session` proofs, with `TrapsOnly`
extern-table refinement lifts.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

open Arm64 ProofLib ProofLib.ProgramReflection ProofLib.Variant
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh
open CryptoVerification.E2E.Pqxdh.Initiator hiding
  bv_sub_add_lit' stackAt_split_top sepWPp_pure_mid
open CryptoVerification.E2E.Pqxdh.ResponderCore
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.SpqrV1.Top.InitialState (InitialStateOkX InitialStateOkXExt initialStateValue)

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.hsp_592_add_96_eq_sp

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem progAtExt_fnAddr_eq (b : BitVec 64)
    (ext1 ext2 : String → Option (State → State)) (sym : String) :
    (tripleRatchetProgAtExt b ext1).fnAddr sym = (tripleRatchetProgAtExt b ext2).fnAddr sym :=
  rfl

/-- Pure `ext`-generic `SessionRecord::archive_current_state_inner` (empty-session fast path, zero extern calls). -/
theorem archive_current_state_inner_empty_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr archiveCurrentStateInnerName)
      archiveCurrentStateInnerEmptySpec := by
  unfold archiveCurrentStateInnerEmptySpec
  cells_unfold
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner") 0 412
  wp_init recPtr s0
  dsimp only [tripleRatchetProgAtExt] at *
  examples_generalize_entry
  examples_hide_fetches
  subst h
  wp_steps
  wp_done

/-- Pure `ext`-generic `map_iter_next` (empty-slice fast path, zero extern calls). -/
theorem map_iter_next_empty_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr mapIterNextName)
      mapIterNextEmptySpec := by
  unfold mapIterNextEmptySpec
  cells_unfold
  have hfn := (ls_lemma% fnOff "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next")
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next") 0 568
  wp_init x s0
  dsimp only [tripleRatchetProgAtExt] at *
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨outPtr, iterPtr, slicePtr⟩ := x
  dsimp only at *
  subst h h_1
  wp_pull_exists
  wp_steps
  wp_done

section PromoteMatchingSessionExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

set_option maxHeartbeats 800000 in
/-- Pure `ext`-generic `SessionRecord::promote_matching_session` (empty fast path, zero extern calls). -/
theorem promote_matching_session_empty_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName)
      promoteMatchingSessionEmptySpec := by
  unfold promoteMatchingSessionEmptySpec ResponderStore.sessionRecordEmptyHeaderAt
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_right, bv_sub_add_lit,
    BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  have hfn := (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session")
  have hfn_iter := (ls_lemma% fnOff "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next")
  have hiter := map_iter_next_empty_ok_ext (b := b) (ext := ext)
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr mapIterNextName =
      (tripleRatchetProgAtExt b ext).fnAddr promoteMatchingSessionName + 55540#64 := by
    simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
      show mapIterNextName = "<core::iter::adapters::map::Map<core::slice::iter::Iter<alloc::vec::Vec<u8>>, <libsignal_protocol::state::session::SessionRecord>::previous_session_states::{closure#0}> as core::iter::traits::iterator::Iterator>::next" from rfl,
      hfn_iter, hfn, BitVec.add_assoc]
    rfl
  rw [hrel] at hiter
  clear hrel
  simp only [mapIterNextEmptySpec, cells, sepExists_sepConj_right,
    sepConj_emp] at hiter
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_matching_session") 0 804
  wp_init x s0
  dsimp only [tripleRatchetProgAtExt] at hiter ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, outPtr⟩ := x
  dsimp only at *
  subst h h_1
  wp_pull_exists
  wp_steps
  wp_call hiter (s0.sp - 448#64, s0.sp - 1128#64, 8#64)
  wp_steps
  wp_done

end PromoteMatchingSessionExt

section KeyPairExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero
attribute [local simp, local arm64_norm, local wp_norm]
  CryptoVerification.E2E.Pqxdh.Shared.zext64_bv16_setWidth_8
  CryptoVerification.E2E.Pqxdh.Shared.zext64_bv8_setWidth_8
  zext64_bv16_setWidth_16 zext64_bv16_setWidth_32
  zext32_bv16_setWidth_8 zext32_bv16_setWidth_16
  clamp_lo_byte_norm clamp_lo_byte_norm'
  clamp_hi_byte_norm clamp_hi_byte_norm' clamp_hi_byte_norm'' clamp_hi_bfm_norm
  bv64_mask_low32_orr_zext32 bv64_mask_high32_orr_lsl32 bv64_mask_low16_orr_zext16

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_0 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 0 8 =
      u.extractLsb' 0 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_8 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 8 8 =
      u.extractLsb' 8 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_16 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 16 8 =
      u.extractLsb' 16 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_mask_low32_orr_zext32_extract_24 (w : BitVec 64) (u : BitVec 32) :
    ((w &&& 18446744069414584320#64) ||| u.zeroExtend 64).extractLsb' 24 8 =
      u.extractLsb' 24 8 := by bv_slice

@[local simp, local arm64_norm, local wp_norm]
private theorem p2_clamp_lo_byte_norm_64 (b0 : BitVec 8) :
    ((b0.zeroExtend 64) &&& 1065151889656#64).setWidth 8 = b0 &&& 0xf8#8 := by
  bv_slice

private theorem subroutine_ok_rel2_ext {α : Type} {b : BitVec 64}
    {ext : String → Option (State → State)}
    {spec : Spec α} {callee name : String} {offc off k : Nat}
    (h : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr callee) spec)
    (hc : libsignalSessionCode.fnOff callee = offc) (hfn : libsignalSessionCode.fnOff name = off)
    (hk : (off + k) % 2 ^ 64 = offc) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k) spec := by
  have hrel : (tripleRatchetProgAtExt b ext).fnAddr callee =
      (tripleRatchetProgAtExt b ext).fnAddr name + BitVec.ofNat 64 k := by
    rw [Program.fnAddr_rebase, Program.fnAddr_rebase, hfn, hc, BitVec.add_assoc,
      ← BitVec.ofNat_add]
    congr 1
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, hk, ← hk, Nat.mod_mod]
  rwa [hrel] at h

set_option maxHeartbeats 2400000 in
/-- Pure `ext`-generic `<curve::KeyPair>::from_public_and_private` (zero extern calls). -/
theorem curveKeyPairFromPubPriv_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr curveKeyPairFromPubPrivName)
      curveKeyPairFromPubPrivOkSpec := by
  unfold curveKeyPairFromPubPrivOkSpec
  simp only [memRegion_65_cells, cells, sepConj_emp, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub]
  have hfn : libsignalSessionCode.fnOff curveKeyPairFromPubPrivName =
      num% (ls_off% "<libsignal_core::curve::KeyPair>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair>::from_public_and_private")
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_core::curve::KeyPair>::from_public_and_private") 0 424
  wp_init x s0
  dsimp only [tripleRatchetProgAtExt] at *
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only at *
  subst h_1 h_3 h_5
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_6
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    hsk, hsk_clamp⟩ := exists_bytes32_of_length_32 h
  wp_pull_exists
  rw [pointsToBytes_cons, hpk (s0.readReg64 (.gpr 0#5) + 1#64),
    hsk (s0.readReg64 (.gpr 2#5)),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  dsimp only [bytes32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
/-- Pure `ext`-generic `<curve::KeyPair as KeyPairSerde>::from_public_and_private` (zero extern calls). -/
theorem curveKeyPairSerde_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr curveKeyPairSerdeName)
      curveKeyPairSerdeOkSpec := by
  unfold curveKeyPairSerdeOkSpec
  have hfn : libsignalSessionCode.fnOff curveKeyPairSerdeName =
      num% (ls_off% "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
  have hinner := subroutine_ok_rel2_ext
    (curveKeyPairFromPubPriv_ok_ext (b := b) (ext := ext))
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair>::from_public_and_private") hfn (k := 81416) (by decide)
  simp only [curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_core::curve::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") 0 288
  wp_init x s0
  dsimp only [tripleRatchetProgAtExt] at hinner ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only at *
  subst h_1 h_3 h_5
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_6
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  wp_pull_exists
  wp_steps
  wp_call hinner (s0.readReg64 (.gpr 0#5), pk, s0.readReg64 (.gpr 2#5), sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

set_option maxHeartbeats 1200000 in
/-- Pure `ext`-generic `<PreKeyRecord>::key_pair` (zero extern calls). -/
theorem preKeyRecordKeyPair_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)} :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr preKeyRecordKeyPairName)
      preKeyRecordKeyPairOkSpec := by
  unfold preKeyRecordKeyPairOkSpec
  have hfn : libsignalSessionCode.fnOff preKeyRecordKeyPairName =
      num% (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair")
  have hinner := subroutine_ok_rel2_ext
    (curveKeyPairFromPubPriv_ok_ext (b := b) (ext := ext))
    (ls_lemma% fnOff "<libsignal_core::curve::KeyPair>::from_public_and_private") hfn (k := 130596) (by decide)
  simp only [curveKeyPairFromPubPrivOkSpec, cells, sepExists_sepConj_right,
    sepConj_emp, bv_sub_add_lit', BitVec.reduceSub] at hinner
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_protocol::state::prekey::PreKeyRecord>::key_pair") 0 300
  wp_init x s0
  dsimp only [tripleRatchetProgAtExt] at hinner ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, pubPtr, pk, privPtr, sk, outPtr⟩ := x
  dsimp only at *
  subst h_1 h_2
  obtain ⟨pk0, pk1, pk2, pk3, pk4, pk5, pk6, pk7, pk8, pk9, pk10, pk11, pk12, pk13, pk14, pk15,
    pk16, pk17, pk18, pk19, pk20, pk21, pk22, pk23, pk24, pk25, pk26, pk27, pk28, pk29, pk30, pk31,
    hpk, _⟩ := exists_bytes32_of_length_32 h_3
  obtain ⟨sk0, sk1, sk2, sk3, sk4, sk5, sk6, sk7, sk8, sk9, sk10, sk11, sk12, sk13, sk14, sk15,
    sk16, sk17, sk18, sk19, sk20, sk21, sk22, sk23, sk24, sk25, sk26, sk27, sk28, sk29, sk30, sk31,
    _, hsk_clamp⟩ := exists_bytes32_of_length_32 h
  rw (occs := .pos [1]) [cells_8_sub176 s0.sp]
  rw (occs := .pos [1]) [cells_14_curveKeyPairSerde s0.sp]
  rw [memRegion_8_bytes (s0.sp - 8#64)]
  simp only [bv_sub_add_lit', BitVec.reduceSub]
  wp_pull_exists
  wp_steps
  wp_call hinner (pubPtr, pk, privPtr, sk, s0.sp - 104#64)
  rw [memRegion_65_bytes8 (s0.readReg64 (.gpr 8#5))]
  simp only [ProofLib.memRegion_eight]
  wp_pull_exists
  rw [hpk (s0.sp - 103#64),
    hsk_clamp (s0.sp - 71#64),
    hpk (s0.readReg64 (.gpr 8#5) + 1#64),
    hsk_clamp (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 1#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 9#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 17#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 25#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 33#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 41#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 49#64),
    pointsTo64_eq_extract_bytes8 (s0.readReg64 (.gpr 8#5) + 57#64)]
  rw [cells_8_sub176_mr s0.sp, cells_14_curveKeyPairSerde_mr s0.sp]
  dsimp only [memRegion_8_bytes_mr_rhs, bytes32At]
  simp only [bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_steps
  wp_done

private theorem p2_cells_sub32_4_merge (sp v0 v1 v2 v3 : BitVec 64) :
    ((sp - 32#64) ↦₆₄ v0) ∗ ((sp - 24#64) ↦₆₄ v1) ∗
    ((sp - 16#64) ↦₆₄ v2) ∗ ((sp - 8#64) ↦₆₄ v3) ⊢
      cells (sp - 32#64) 4 := by
  have hc4 : cells (sp - 32#64) 4 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
        ((sp - 32#64) ↦₆₄ w0) ∗ ((sp - 24#64) ↦₆₄ w1) ∗
        ((sp - 16#64) ↦₆₄ w2) ∗ ((sp - 8#64) ↦₆₄ w3)) := by
    cells_unfold
  rw [hc4]
  exact Entails.sepExists_right v0 (Entails.sepExists_right v1
    (Entails.sepExists_right v2 (Entails.sepExists_right v3 (Entails.refl _))))

private theorem p2_stackAt_promote_state_split (sp : BitVec 64) :
    stackAt sp allocHookStack =
      memRegion (sp - 4096#64) 4000 ∗ cells (sp - 96#64) 8 ∗ cells (sp - 32#64) 4 := by
  dsimp only [stackAt, allocHookStack]
  rw [show (4096 : Nat) = 4000 + (64 + 32) by decide,
    memRegion_split (sp - 4096#64) 4000 (64 + 32) (by decide),
    show sp - 4096#64 + 4000#64 = sp - 96#64 by bv_omega,
    memRegion_split (sp - 96#64) 64 32 (by decide),
    show sp - 96#64 + 64#64 = sp - 32#64 by bv_omega,
    ProofLib.memRegion_cells (sp - 96#64) 8 (by decide),
    ProofLib.memRegion_cells (sp - 32#64) 4 (by decide)]

private theorem p2_stackAt_kemKeyPairFromPubPriv (sp : BitVec 64) :
    memRegion (sp - 4160#64) 64 ∗ stackAt sp allocHookStack =
      stackAt (sp - 64#64) allocHookStack ∗ cells (sp - 64#64) 8 := by
  have h1 := ResponderStore.stackAt_split_top sp 64 allocHookStack (by decide)
  have h2 := ProofLib.stackAt_split_cells sp allocHookStack 8 (by decide)
  have h3 : (64 + allocHookStack : Nat) = allocHookStack + 8 * 8 := by decide
  have h4 : BitVec.ofNat 64 (64 + allocHookStack) = 4160#64 := rfl
  have h5 : BitVec.ofNat 64 (8 * 8) = 64#64 := rfl
  rw [h4] at h1
  rw [h5] at h2
  rw [← h1, h3, h2]

ls_attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_state")
  (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")
  (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair>::from_public_and_private")
  (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_hook% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")
  (ls_stub% "alloc::alloc::handle_alloc_error")

/-- Contract-backed 4 KiB-stacked `SessionRecord::promote_state` (empty fast path) on
`tripleRatchetProgAtExt b ext` from `HookSat ext "memcpy" p2Memcpy4KSpec`. -/
theorem promote_state_empty_4k_ok_ext {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hMemcpy : HookSat ext "memcpy" p2Memcpy4KSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteStateName)
      promoteStateEmpty4KSpec := by
  unfold promoteStateEmpty4KSpec
  have hfn : libsignalSessionCode.fnOff promoteStateName =
      num% (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") :=
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::promote_state")
  have harch := subroutine_ok_rel2_ext
    (archive_current_state_inner_empty_ok_ext (b := b) (ext := ext))
    (ls_lemma% fnOff "<libsignal_protocol::state::session::SessionRecord>::archive_current_state_inner")
    hfn (k := 2804) (by decide)
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr promoteStateName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state")))
      p2Memcpy4KSpec :=
    hook_ok_at (hname := "memcpy") (stub := libsignalSessionCode.fnOff "memcpy") rfl
      (k := num% (ls_off% "memcpy" -
        ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state"))
      (by dsimp only [promoteStateName]; simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by simp [Rust.isPanicSymbol]) hMemcpy
  dsimp only [p2Memcpy4KSpec, libcMemcpySpec] at hmemcpy
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_protocol::state::session::SessionRecord>::promote_state") 0 68
  wp_init x s0
  dsimp only [tripleRatchetProgAtExt] at harch hmemcpy ⊢
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨recPtr, srcPtr, bs⟩ := x
  dsimp only at *
  subst h_1 h_2
  rw (occs := .pos [1]) [p2_stackAt_promote_state_split s0.sp]
  have hc4 : cells (s0.sp - 32#64) 4 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v3 : BitVec 64,
        ((s0.sp - 32#64) ↦₆₄ v0) ∗ ((s0.sp - 24#64) ↦₆₄ v1) ∗
        ((s0.sp - 16#64) ↦₆₄ v2) ∗ ((s0.sp - 8#64) ↦₆₄ v3)) := by
    cells_unfold
  rw [hc4]
  simp only [sepExists_sepConj_right, sepConj_assoc]
  wp_pull_exists
  wp_steps
  wp_call harch (s0.readReg64 (.gpr 0#5))
  wp_steps
  apply ProofLib.SepWP.replace_pre (by sep_focus)
    (pointsTo64_memRegion_336_entails_344 (s0.readReg64 (.gpr 0#5)) 0xffffffffffffffff#64)
  apply ProofLib.SepWP.replace_pre (by sep_focus)
    (p2_cells_sub32_4_merge s0.sp _ _ _ _)
  refine SepWP.fold (Entails.of_eq (p2_stackAt_promote_state_split s0.sp).symm) (by sep_focus) ?_
  rw [← h]
  wp_call hmemcpy (s0.readReg64 (.gpr 0#5) + 0x18#64, s0.readReg64 (.gpr 1#5), bs)
  simp only [h] at *
  wp_done

set_option maxHeartbeats 1200000 in
/-- Contract-backed `<kem::KeyPair>::from_public_and_private` on `tripleRatchetProgAtExt b ext`
from `AllocHooks`, `noAllocShimSpec`, and `p2Memcpy4KSpec` (`allocHookStack = 4096` B). -/
theorem kemKeyPairFromPubPriv_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" noAllocShimSpec)
    (hMemcpy : HookSat ext "memcpy" p2Memcpy4KSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr kemKeyPairFromPubPrivName)
      (kemKeyPairFromPubPrivOkSpec A) := by
  unfold kemKeyPairFromPubPrivOkSpec
  simp only [p2_stackAt_kemKeyPairFromPubPriv]
  simp only [cells, sepConj_emp, sepExists_sepConj_right,
    BitVec.add_assoc, BitVec.reduceAdd]
  have hshim : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr kemKeyPairFromPubPrivName +
        BitVec.ofNat 64 (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
          ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private")))
      noAllocShimSpec :=
    hook_ok_at (hname := "__rustc::__rust_no_alloc_shim_is_unstable_v2")
      (stub := libsignalSessionCode.fnOff "__rustc::__rust_no_alloc_shim_is_unstable_v2") rfl
      (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
        ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
      (by dsimp only [kemKeyPairFromPubPrivName]; simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by simp [Rust.isPanicSymbol]) hShim
  have halloc := alloc_ok_at_ext b A ext hAlloc kemKeyPairFromPubPrivName
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    (by dsimp only [kemKeyPairFromPubPrivName]; simp only [arm64_norm])
  have hmemcpy : subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr kemKeyPairFromPubPrivName +
        BitVec.ofNat 64 (num% (ls_off% "memcpy" -
          ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private")))
      p2Memcpy4KSpec :=
    hook_ok_at (hname := "memcpy") (stub := libsignalSessionCode.fnOff "memcpy") rfl
      (k := num% (ls_off% "memcpy" -
        ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
      (by dsimp only [kemKeyPairFromPubPrivName]; simp only [arm64_norm])
      (by simp only [arm64_norm]) (fun _ => by simp only [arm64_norm])
      (by simp [Rust.isPanicSymbol]) hMemcpy
  have hpanic := ResponderCore.pqxdh_panic_at_handle_alloc_error_ext (b := b) (ext := ext)
    (name := kemKeyPairFromPubPrivName)
    (k := num% (ls_off% "alloc::alloc::handle_alloc_error" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    (by dsimp only [kemKeyPairFromPubPrivName]; simp only [arm64_norm])
  dsimp only [p2Memcpy4KSpec, libcMemcpySpec] at hmemcpy
  clear hAlloc hShim hMemcpy
  wpp_init g s0
  simp only [sepConj_assoc]
  have hfn : libsignalSessionCode.fnOff kemKeyPairFromPubPrivName =
      num% (ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair>::from_public_and_private")
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private") 0 364
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr kemKeyPairFromPubPrivName := by
    try dsimp only [tripleRatchetProgAtExt] at hpc
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hmemcpy hpanic ⊢
  clear hfn
  generalize_entry (libsignalSessionCode.rebase b
    (Rust.withPanics ext)).fnAddr kemKeyPairFromPubPrivName = entry
  examples_hide_fetches
  obtain ⟨pubPtr, pk, privPtr, sk, outPtr⟩ := g
  dsimp only at *
  subst h_1 h_3 h_5
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay1 : LayoutOk 1568 1 := ⟨by decide, hpow2, by decide⟩
  have hlay2 : LayoutOk 3168 1 := ⟨by decide, hpow2, by decide⟩
  rw [pointsToBytes_cons (s0.readReg64 (.gpr 0#5)),
    pointsToBytes_cons (s0.readReg64 (.gpr 2#5))]
  apply SepWPp.of_sepWP (mid := entry + 76#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (1568, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom1 : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom1
    simp only [hoom1, ite_true]
    refine sepWPp_pure_mid fun htrace1 => ?_
    apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" -
      ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
    wp_steps
    apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
    apply CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply.SepWPp_panic_oom
      (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      hpanic (by simp only [arm64_norm, *])
  · have hoom1_64 : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom1
    simp only [hoom1, ite_false, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨hmod1, htrace1⟩ => ?_
    apply SepWPp.of_sepWP (mid := entry + 140#64)
    wp_steps
    rw [← h_6]
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 0#5) + 1#64, pk)
    simp only [h_6] at *
    wp_steps
    wp_call hshim ()
    wp_steps
    wp_call halloc (3168, 1)
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    by_cases hoom2 : sf_4.readReg64 (Reg.gpr 0#5) = 0
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) = 0#64 := hoom2
      simp only [hoom2, ite_true]
      refine sepWPp_pure_mid fun htrace2 => ?_
      apply SepWPp.of_sepWP (mid := entry + bv% (ls_off% "alloc::alloc::handle_alloc_error" -
        ls_off% "<libsignal_protocol::kem::KeyPair>::from_public_and_private"))
      wp_steps
      apply SepWP.done (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
      apply CryptoVerification.LibsignalTripleRatchet.ReceiveRatchetApply.SepWPp_panic_oom
        (by simp only [arm64_norm, *]) (by simp only [arm64_norm, *])
        hpanic (by simp only [arm64_norm, *])
    · have hoom2_64 : sf_4.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom2
      simp only [hoom2, ite_false, sepConj_assoc]
      refine sepWPp_pure_mid fun ⟨hmod2, htrace2⟩ => ?_
      apply SepWPp.of_sepWP_ret
      wp_steps
      rw [← h]
      wp_call hmemcpy (sf_4.readReg64 (Reg.gpr 0#5), s0.readReg64 (Reg.gpr 2#5) + 1#64, sk)
      simp only [h] at *
      wp_steps
      wp_done

set_option maxHeartbeats 1200000 in
/-- Contract-backed `<kem::KeyPair as KeyPairSerde>::from_public_and_private` on
`tripleRatchetProgAtExt b ext` (`allocHookStack = 4096` B). -/
theorem kemKeyPairSerde_ok_ext {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" noAllocShimSpec)
    (hMemcpy : HookSat ext "memcpy" p2Memcpy4KSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr kemKeyPairSerdeName)
      (kemKeyPairFromPubPrivOkSpec A) := by
  have hfn : libsignalSessionCode.fnOff kemKeyPairSerdeName =
      num% (ls_off% "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") :=
    (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private")
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private") 0 4
  have hinner := kemKeyPairFromPubPriv_ok_ext (b := b) (A := A) (ext := ext) hAlloc hShim hMemcpy
  exact subroutine_ok_of_b ‹_›
    (by simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase,
      (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair as libsignal_protocol::state::signed_prekey::KeyPairSerde>::from_public_and_private"),
      (ls_lemma% fnOff "<libsignal_protocol::kem::KeyPair>::from_public_and_private"), arm64_norm])
    rfl (by intros; rfl) hinner (by intros; rfl) (by intros; rfl) (by intros; rfl)

end KeyPairExt

section InitBobErr4KExt

attribute [local irreducible] Program.fetch Program.externAt? Program.fnAddr Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit bv_sub_add_lit' BitVec.toNat_zero bv_sub_sub_lit bv_add_neg64
attribute [local arm64_norm ↓, local wp_norm ↓]
  sp_setPC_pre sp_setMem_setPC_pre
  readReg64_setPC_pre readReg64_setMem_setPC_pre
  readReg32_setPC_pre readReg32_setMem_setPC_pre
  readReg_setPC_pre readReg_setMem_setPC_pre
attribute [local simp, local arm64_norm, local wp_norm, local arm64_norm ↓, local wp_norm ↓]
  CryptoVerification.libsignalSessionCode_fnOff_0x21c80

private theorem p2_initBob_stack_ext_split (sp : BitVec 64) :
    stackAt sp (768 + Initiator.pqxdhEntryStackExt) =
      memRegion (sp - 33536#64) (32768 - pqxdhEntryStack) ∗ stackAt sp (768 + pqxdhEntryStack) := by
  have h := p2_stackAt_split_of_le sp (768 + Initiator.pqxdhEntryStackExt) (768 + pqxdhEntryStack)
    (by decide) (by decide)
  have h1 : BitVec.ofNat 64 (768 + Initiator.pqxdhEntryStackExt) = 33536#64 := rfl
  have h2 : (768 + Initiator.pqxdhEntryStackExt) - (768 + pqxdhEntryStack) =
      32768 - pqxdhEntryStack := by
    dsimp only [Initiator.pqxdhEntryStackExt]; omega
  rw [h1, h2] at h
  exact h

private theorem p2_initBob_sub768_ext_split (sp : BitVec 64) :
    stackAt (sp - 768#64) Initiator.pqxdhEntryStackExt =
      memRegion (sp - 33536#64) (32768 - pqxdhEntryStack) ∗
        stackAt (sp - 768#64) pqxdhEntryStack := by
  have h := p2_stackAt_split_of_le (sp - 768#64) Initiator.pqxdhEntryStackExt pqxdhEntryStack
    (by decide) (by decide)
  have h1 : (sp - 768#64) - BitVec.ofNat 64 Initiator.pqxdhEntryStackExt = sp - 33536#64 := by
    dsimp only [Initiator.pqxdhEntryStackExt]; bv_omega
  have h2 : Initiator.pqxdhEntryStackExt - pqxdhEntryStack = 32768 - pqxdhEntryStack := rfl
  rw [h1, h2] at h
  exact h

private theorem p2_initBobErrOwnedAt_merge (A : RustAlloc)
    (outPtr errTag w2 w3 w4 w5 w6 : BitVec 64)
    (hw1 : errTag ≠ pollReadyOkWord ∧ errTag ≠ 0xfffffffffffffffd#64) :
    ResponderCore.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    Kits.initBobErrOwnedAt A outPtr := by
  change Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
    (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
    ((outPtr + 8#64) ↦₆₄ errTag) ∗
    ((outPtr + 16#64) ↦₆₄ w2) ∗
    ((outPtr + 24#64) ↦₆₄ w3) ∗
    ((outPtr + 32#64) ↦₆₄ w4) ∗
    ((outPtr + 40#64) ↦₆₄ w5) ∗
    ((outPtr + 48#64) ↦₆₄ w6) ∗
    memRegion (outPtr + 56#64) 288 ⊢
    Kits.initBobErrOwnedAt A outPtr
  have hrearr :
      Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗ (((outPtr + 8#64) ↦₆₄ errTag) ∗
        (((outPtr + 16#64) ↦₆₄ w2) ∗ (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
          (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
            memRegion (outPtr + 56#64) 288))))))) =
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
      (((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
        memRegion (outPtr + 56#64) 288) := by ac_rfl
  rw [hrearr]
  unfold Kits.initBobErrOwnedAt
  refine sepConj_mono_right ?_
  refine Entails.sepExists_right errTag (Entails.sepExists_right w2 (Entails.sepExists_right w3
    (Entails.sepExists_right w4 (Entails.sepExists_right w5 (Entails.sepExists_right w6 ?_)))))
  rw [pure_sepConj_of_true hw1]
  simp only [speWordsAt, BitVec.add_assoc, BitVec.reduceAdd]
  exact Entails.of_eq (by ac_rfl)

set_option maxHeartbeats 1200000 in
/-- Contract-backed `initialize_bob_session` owned-error proof on `tripleRatchetProgAtExt img.base ext`
at `768 + Initiator.pqxdhEntryStackExt` (`33536` B, zero `trTrapProgAt`). -/
theorem initializeBobSession_err_owned_4k_ok_ext
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContractsExt P A img ext)
    (hag : ResponderCore.PqxdhCalculateAgreementOkExt P A img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
      (Kits.initializeBobSessionErrOwned4KSpec P A img) := by
  unfold Kits.initializeBobSessionErrOwned4KSpec Spec.inImage
    Kits.initializeBobSessionErrOwned4KInnerSpec Kits.initializeBobSessionErrOwnedAtInnerSpec
    bobParamsFieldsAt rustPanicOnOom
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  have haccept := subroutine_ok_rel_pqxdh_ext
    (pqxdhAccept_err_owned_base_ok_ext himg hWF hH hag)
    CryptoVerification.libsignalSessionCode_fnOff_0x23920 hfn (k := 7328) (by decide)
  dsimp only [pqxdhAcceptErrOwnedExtSpec, pqxdhAcceptErrOwnedExtInnerSpec,
    ResponderCore.pqxdhAcceptErrOwnedAt] at haccept
  clear hfn
  wpp_init x s0
  have hfn : libsignalSessionCode.fnOff initializeBobSessionSym = 0x21c80 :=
    CryptoVerification.libsignalSessionCode_fnOff_0x21c80
  code_fetches CryptoVerification.libsignalSessionCode
    CryptoVerification.E2E.Pqxdh.initializeBobSession img.base
    (Rust.withPanics ext) hfn 0x21c80 608
  replace hpc : s0.pc =
      (libsignalSessionCode.rebase img.base
        (Rust.withPanics ext)).fnAddr initializeBobSessionSym := by
    try dsimp only [tripleRatchetProgAtExt] at hpc
    rw [hpc, Program.fnAddr_rebase, hfn]
  dsimp only [tripleRatchetProgAtExt] at haccept
  clear hfn
  generalize_entry (libsignalSessionCode.rebase img.base
    (Rust.withPanics ext)).fnAddr initializeBobSessionSym = entry
  examples_hide_fetches
  obtain ⟨inp, ikBPk, spkBPk, sameAccountByte, argPtr, pqskPtr, ctSlicePtr, ctBufPtr,
    ratchetKeyPairPtr, outPtr⟩ := x
  dsimp only at *
  subst h_3 h_4 h_5
  rw (occs := .pos [1]) [p2_initBob_stack_ext_split s0.sp]
  rw (occs := .pos [1]) [stackAt_initBob_entry s0.sp]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.reduceSub, sepConj_assoc]
  repeat (refine SepWPp.exists_elim fun _ => ?_)
  apply SepWPp.of_sepWP_frozen_inImage h_2 h_1 (mid := entry + 7328#64)
  wp_steps
  refine SepWP.fold (Entails.of_eq (p2_initBob_sub768_ext_split s0.sp).symm) (by sep_focus) ?_
  apply SepWP.done (by wp_norm_goal) (by wp_norm_goal)
  intro hF1 hsym1
  refine SepWPp.call_inImage_frame' hF1 hsym1 haccept
    (ret_pc := entry + 56#64)
    (x := ⟨inp, s0.readReg64 (.gpr 0#5), pqskPtr, ctSlicePtr, ctBufPtr, s0.sp - 488#64⟩)
    (by wp_norm_lhs) (by wp_norm_lhs) (by simp only [*, State.spAligned, arm64_norm])
    (by wp_norm_lhs)
    (by simp only [arm64_norm]; rfl)
    (by simp only [arm64_norm, *])
    (by sep_focus)
    (fun _ _ _ _ hm => allowPanic_not_exited hm)
    (fun sm _ hm => by
      simpa only [sepConj_assoc] using
        allowPanic_frame (fun h => ResponderCore.allocFailedIn_of_trace_eq (s0 := s0)
          (by simp only [arm64_norm]) h) hm)
    (fun sf_1 hpc_1 hrun_1 hsp_1 hsp_al_1 hcs_1 hF2 hsym2 => ?_)
  dsimp only at *
  simp only [*, arm64_norm] at hsp_1
  dsimp only [CalleeSavedPreserved, Reg.fp] at hcs_1
  rcases hcs_1 with ⟨hcs1_19, hcs1_20, hcs1_21, hcs1_22, hcs1_23, hcs1_24, hcs1_25, hcs1_26,
    hcs1_27, hcs1_28, hcs1_29, hcs1_vregs⟩
  simp only [*, arm64_norm]
    at hcs1_19 hcs1_20 hcs1_21 hcs1_22 hcs1_23 hcs1_24 hcs1_25 hcs1_26 hcs1_27 hcs1_28
       hcs1_29 hcs1_vregs
  conv =>
    arg 4
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub,
      arm64_norm, sepConj_assoc]
  refine SepWPp.exists_elim fun errTag => ?_
  refine SepWPp.exists_elim fun w2 => ?_
  refine SepWPp.exists_elim fun w3 => ?_
  refine SepWPp.exists_elim fun w4 => ?_
  refine SepWPp.exists_elim fun w5 => ?_
  refine SepWPp.exists_elim fun w6 => ?_
  refine SepWPp.pure_left fun ⟨htr1, herrTag⟩ => ?_
  apply SepWPp.of_sepWP_ret
  rw [p2_initBob_sub768_ext_split s0.sp,
      memRegion_280_none_split s0.sp,
      memRegion_344_none_split (s0.readReg64 (.gpr 8#5))]
  simp (config := { maxSteps := 1000000 }) only [
    cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    bv_sub_add_lit', BitVec.add_assoc, BitVec.reduceAdd, BitVec.reduceSub, sepConj_assoc]
  wp_pull_exists
  wp_steps
  refine SepWP.fold
    (p2_initBobErrOwnedAt_merge A (s0.readReg64 (.gpr 8#5)) errTag w2 w3 w4 w5 w6 herrTag)
    (by sep_focus) ?_
  refine SepWP.fold (cells6_sub764_merge s0.sp _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (memRegion_280_none_split s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (sub488_none_104_merge s0.sp errTag w2 w3 w4 w5 w6) (by sep_focus) ?_
  refine SepWP.fold (cells12_sub96_merge s0.sp _ _ _ _ _ _ _ _ _ _ _ _) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (stackAt_initBob_entry s0.sp).symm) (by sep_focus) ?_
  refine SepWP.fold (Entails.of_eq (p2_initBob_stack_ext_split s0.sp).symm) (by sep_focus) ?_
  wp_done

private theorem p2_initBobErrOwnedAt_to_initBobErrAt (A : RustAlloc) (outPtr : BitVec 64) :
    Kits.initBobErrOwnedAt A outPtr ∗ anyHeap ⊢ initBobErrAt outPtr ∗ anyHeap := by
  unfold Kits.initBobErrOwnedAt
  conv =>
    lhs
    simp only [speWordsAt, sepExists_sepConj_left, sepExists_sepConj_right,
      BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine Entails.sepExists_elim fun errTag => Entails.sepExists_elim fun w2 =>
    Entails.sepExists_elim fun w3 => Entails.sepExists_elim fun w4 =>
    Entails.sepExists_elim fun w5 => Entails.sepExists_elim fun w6 => ?_
  rw [sepConj_left_comm]
  refine Entails.pure_left fun herr => ?_
  have h1 :
      (outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        (((outPtr + 8#64) ↦₆₄ errTag) ∗ (((outPtr + 16#64) ↦₆₄ w2) ∗
          (((outPtr + 24#64) ↦₆₄ w3) ∗ (((outPtr + 32#64) ↦₆₄ w4) ∗
            (((outPtr + 40#64) ↦₆₄ w5) ∗ (((outPtr + 48#64) ↦₆₄ w6) ∗
              (Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4 ∗
                (memRegion (outPtr + 56#64) 288 ∗ anyHeap)))))))) =
      ((outPtr ↦₆₄ 0xffffffffffffffff#64) ∗
        ((outPtr + 8#64) ↦₆₄ errTag) ∗ ((outPtr + 16#64) ↦₆₄ w2) ∗
        ((outPtr + 24#64) ↦₆₄ w3) ∗ ((outPtr + 32#64) ↦₆₄ w4) ∗
        ((outPtr + 40#64) ↦₆₄ w5) ∗ ((outPtr + 48#64) ↦₆₄ w6) ∗
        memRegion (outPtr + 56#64) 288) ∗
      (anyHeap ∗ Kits.pqxdhAcceptErrPayloadAt A errTag w2 w3 w4) := by ac_rfl
  rw [h1]
  exact sepConj_mono (initBobErrAt_merge outPtr errTag w2 w3 w4 w5 w6 herr) (entails_anyHeap _)

/-- Contract-backed `initialize_bob_session` unowned-error proof (`initializeBobSessionErr4KSpec`)
on `tripleRatchetProgAtExt img.base ext` at `768 + Initiator.pqxdhEntryStackExt` (`33536` B). -/
theorem initializeBobSession_err_4k_ok_ext
    {P : Primitives} {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContractsExt P A img ext)
    (hag : ResponderCore.PqxdhCalculateAgreementOkExt P A img ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr initializeBobSessionSym)
      (initializeBobSessionErr4KSpec P A img) := by
  refine subroutine_ok_map_panic
    (initializeBobSession_err_owned_4k_ok_ext himg hWF hH hag) ?_
    (fun _ _ _ _ _ _ he => by
      dsimp only [Kits.initializeBobSessionErrOwned4KSpec,
        Kits.initializeBobSessionErrOwned4KInnerSpec,
        Kits.initializeBobSessionErrOwnedAtInnerSpec, Spec.inImage] at he
      exact not_satisfies_false_sepConj he)
    (fun _ _ _ _ _ _ _ ho => by
      dsimp only [Kits.initializeBobSessionErrOwned4KSpec,
        Kits.initializeBobSessionErrOwned4KInnerSpec,
        Kits.initializeBobSessionErrOwnedAtInnerSpec, Spec.inImage] at ho
      exact (not_satisfies_false_sepConj ho).elim)
  intro g R s0 hpre
  refine ⟨g, R, hpre, fun sf hpost => ?_, fun sf hpan => hpan⟩
  dsimp only [Kits.initializeBobSessionErrOwned4KSpec,
    Kits.initializeBobSessionErrOwned4KInnerSpec,
    Kits.initializeBobSessionErrOwnedAtInnerSpec,
    initializeBobSessionErr4KSpec, initializeBobSessionErr4KInnerSpec,
    Spec.inImage] at hpost ⊢
  refine Arm64.Satisfies.mono ?_ hpost
  refine sepConj_mono_left (sepConj_mono_right (sepConj_mono_right ?_))
  exact sepConj_mono_left (p2_initBobErrOwnedAt_to_initBobErrAt A g.outPtr)

end InitBobErr4KExt

theorem InitializeBobV1OkExt.of_trapsOnly
    {P : Primitives} {A : RustAlloc} {F : ShaCompress} {img : Obj.Image}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (tripleRatchetProgAtExt img.base ext1) (tripleRatchetProgAtExt img.base ext2))
    (h : InitializeBobV1OkExt P A F img ext1) :
    InitializeBobV1OkExt P A F img ext2 := by
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hF hsym hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  rw [← progAtExt_fnAddr_eq img.base ext1 ext2 initializeBobSessionSym] at hpc
  exact SepWPp.of_trapsOnly hT
    (h s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hF hsym hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)

/-- Lift `StageP2PureCallees` across `TrapsOnly` extern-table refinement. -/
theorem StageP2PureCallees.of_trapsOnly
    {P : Primitives} {A : RustAlloc} {F : ShaCompress} {img : Obj.Image}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (tripleRatchetProgAtExt img.base ext1) (tripleRatchetProgAtExt img.base ext2))
    (h : StageP2PureCallees P A F img ext1) :
    StageP2PureCallees P A F img ext2 where
  publicKeySerialize :=
    subroutine_ok.of_trapsOnly_eq hT h.publicKeySerialize
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  promoteMatchingSessionEmpty :=
    subroutine_ok.of_trapsOnly_eq hT h.promoteMatchingSessionEmpty
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  curveKeyPairSerde :=
    subroutine_ok.of_trapsOnly_eq hT h.curveKeyPairSerde
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  kemKeyPairSerde :=
    subroutine_ok.of_trapsOnly_eq hT h.kemKeyPairSerde
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  preKeyRecordKeyPair :=
    subroutine_ok.of_trapsOnly_eq hT h.preKeyRecordKeyPair
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  dropSpe2 :=
    subroutine_ok.of_trapsOnly_eq hT h.dropSpe2
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  isSameAccount :=
    subroutine_ok.of_trapsOnly_eq hT h.isSameAccount
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  initializeBobErr :=
    subroutine_ok.of_trapsOnly_eq hT h.initializeBobErr
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  initializeBobV1 :=
    InitializeBobV1OkExt.of_trapsOnly hT h.initializeBobV1
  promoteStateEmpty :=
    subroutine_ok.of_trapsOnly_eq hT h.promoteStateEmpty
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  dropProcessPrekeyImplState1 :=
    subroutine_ok.of_trapsOnly_eq hT h.dropProcessPrekeyImplState1
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  dropSessionStructure3 :=
    subroutine_ok.of_trapsOnly_eq hT h.dropSessionStructure3
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl

/-- Construct `StageP2PureCallees` at `tripleRatchetExterns C ctl abs` from the verified pure and
SPQR V1 internal callee theorems. -/
theorem stageP2PureCallees_of_tripleRatchetExterns
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hA : AllocHooks A abs)
    (hAC : AllocContracts img.base A (tripleRatchetExterns C ctl abs))
    (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContracts P A img abs)
    (hP : PrimitivesMatchCrypto P C)
    (hinit : InitialStateOkX img A F (tripleRatchetExterns C ctl abs)) :
    StageP2PureCallees P A F img (tripleRatchetExterns C ctl abs) where
  publicKeySerialize := public_key_serialize_ok_ext hAC
  promoteMatchingSessionEmpty := promote_matching_session_empty_ok
  curveKeyPairSerde := curveKeyPairSerde_ok
  kemKeyPairSerde := kemKeyPairSerde_ok hA
  preKeyRecordKeyPair := preKeyRecordKeyPair_ok
  dropSpe2 := GenP3.drop_spe2_ok_ext himg hAC
  isSameAccount :=
    CryptoVerification.Cli.E2E.Pqxdh.WireEntries.isSameAccountEqDistinct_ok img.base C A ctl abs
  initializeBobErr := initializeBobSession_err_ok himg hWF hH hP
  initializeBobV1 := CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1 himg hWF hH hP hinit
  promoteStateEmpty := promote_state_empty_ok
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_ok
  dropSessionStructure3 := GenP3.drop_session_structure3_ok_ext hAC

theorem InitializeBobV1OkExt4K.of_trapsOnly
    {P : Primitives} {A : RustAlloc} {F : ShaCompress} {img : Obj.Image}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (tripleRatchetProgAtExt img.base ext1) (tripleRatchetProgAtExt img.base ext2))
    (h : InitializeBobV1OkExt4K P A F img ext1) :
    InitializeBobV1OkExt4K P A F img ext2 := by
  intro s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
    hF hsym hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc
  rw [← progAtExt_fnAddr_eq img.base ext1 ext2 initializeBobSessionSym] at hpc
  exact SepWPp.of_trapsOnly hT
    (h s0 inp ikBPk spkBPk argPtr pqskPtr ctSlicePtr ctBufPtr ratchetKeyPairPtr outPtr drKey Frame
      hF hsym hrun hpc hsp hpqr hx0 hx1 hx8 htr hrep hopk hwell hik hspk hacc)

theorem StageP2PureCallees4K.of_trapsOnly
    {P : Primitives} {A : RustAlloc} {F : ShaCompress} {img : Obj.Image}
    {ext1 ext2 : String → Option (State → State)}
    (hT : TrapsOnly (tripleRatchetProgAtExt img.base ext1) (tripleRatchetProgAtExt img.base ext2))
    (h : StageP2PureCallees4K P A F img ext1) :
    StageP2PureCallees4K P A F img ext2 where
  publicKeySerialize :=
    subroutine_ok.of_trapsOnly_eq hT h.publicKeySerialize
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  promoteMatchingSessionEmpty :=
    subroutine_ok.of_trapsOnly_eq hT h.promoteMatchingSessionEmpty
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  curveKeyPairSerde :=
    subroutine_ok.of_trapsOnly_eq hT h.curveKeyPairSerde
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  kemKeyPairSerde :=
    subroutine_ok.of_trapsOnly_eq hT h.kemKeyPairSerde
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  preKeyRecordKeyPair :=
    subroutine_ok.of_trapsOnly_eq hT h.preKeyRecordKeyPair
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  dropSpe2 :=
    subroutine_ok.of_trapsOnly_eq hT h.dropSpe2
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  isSameAccount :=
    subroutine_ok.of_trapsOnly_eq hT h.isSameAccount
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  initializeBobErr :=
    subroutine_ok.of_trapsOnly_eq hT h.initializeBobErr
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  initializeBobV1 :=
    InitializeBobV1OkExt4K.of_trapsOnly hT h.initializeBobV1
  promoteStateEmpty :=
    subroutine_ok.of_trapsOnly_eq hT h.promoteStateEmpty
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  dropProcessPrekeyImplState1 :=
    subroutine_ok.of_trapsOnly_eq hT h.dropProcessPrekeyImplState1
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl
  dropSessionStructure3 :=
    subroutine_ok.of_trapsOnly_eq hT h.dropSessionStructure3
      (progAtExt_fnAddr_eq img.base ext1 ext2 _) rfl

/-- Construct `StageP2PureCallees4K` directly on `tripleRatchetProgAtExt img.base ext` from
contract-backed hook hypotheses (zero `trTrapProgAt`, zero 0-stack `AllocContracts`). -/
theorem StageP2PureCallees4K.of_hooks
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" noAllocShimSpec)
    (hMemcpy : HookSat ext "memcpy" p2Memcpy4KSpec)
    (hSame : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32
      img.base A ext)
    (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContractsExt P A img ext)
    (hext : Initiator.PqxdhHkdfExtractOk_ext P img ext)
    (hexp : Initiator.PqxdhHkdfExpandMultiInfoOk_ext P img ext)
    (hag : ResponderCore.PqxdhCalculateAgreementOkExt P A img ext)
    (hinit : InitialStateOkXExt img A F ext) :
    StageP2PureCallees4K P A F img ext where
  publicKeySerialize := p2_publicKeySerialize_of_hooks hAlloc hShim
  promoteMatchingSessionEmpty := promote_matching_session_empty_ok_ext
  curveKeyPairSerde := curveKeyPairSerde_ok_ext
  kemKeyPairSerde := kemKeyPairSerde_ok_ext hAlloc hShim hMemcpy
  preKeyRecordKeyPair := preKeyRecordKeyPair_ok_ext
  dropSpe2 := GenP3.drop_spe2_of_allocHooks_ext himg hAlloc
  isSameAccount := hSame
  initializeBobErr := initializeBobSession_err_4k_ok_ext himg hWF hH hag
  initializeBobV1 :=
    CryptoVerification.Cli.E2E.V1.initializeBobSession_ok_v1_ext himg hWF hH hext hexp hag hinit
  promoteStateEmpty := promote_state_empty_4k_ok_ext hMemcpy
  dropProcessPrekeyImplState1 := drop_process_prekey_impl_state1_ext_ok
  dropSessionStructure3 := GenP3.drop_session_structure3_of_allocHooks_ext hAlloc

abbrev stageP2PureCallees4K_of_hooks := @StageP2PureCallees4K.of_hooks

/-- 18176-byte `InitialStateOkX` (`18176` B) wrapper for `StageP2PureCallees4K.of_hooks`. -/
theorem StageP2PureCallees4K.of_hooks_x
    {P : Primitives} {A : RustAlloc} {F : ShaCompress}
    {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img)
    (hAlloc : AllocHooks A ext)
    (hShim : HookSat ext "__rustc::__rust_no_alloc_shim_is_unstable_v2" noAllocShimSpec)
    (hMemcpy : HookSat ext "memcpy" p2Memcpy4KSpec)
    (hSame : CryptoVerification.Cli.LibsignalTripleRatchet.DecryptPq.IsSameAccountDistinctOkExt32
      img.base A ext)
    (hWF : StructuralPrims P)
    (hH : ResponderCore.PqxdhHookContractsExt P A img ext)
    (hext : Initiator.PqxdhHkdfExtractOk_ext P img ext)
    (hexp : Initiator.PqxdhHkdfExpandMultiInfoOk_ext P img ext)
    (hag : ResponderCore.PqxdhCalculateAgreementOkExt P A img ext)
    (hinit : InitialStateOkX img A F ext) :
    StageP2PureCallees4K P A F img ext :=
  StageP2PureCallees4K.of_hooks himg hAlloc hShim hMemcpy hSame hWF hH hext hexp hag
    (CryptoVerification.Cli.E2E.V1.initialStateOkX_to_ext hinit)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits

