/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.L1GX.Leaf.MF14Aux.Helpers
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ProtoCodecRoundTrip
import LibsignalBinary.Proofs.TripleRatchet.Prost.Int32Merge

/-!
# Pure and layout helpers for `merge_field` tag 9 (`MergeFieldX9P`)

Instruction decodes, varint/payload byte decompositions, `.rodata` jump-table lookup, and
`prostSSGXAt` layout splits around `ss + 0xf8..0x128` for the PQXDH `pending_pre_key` arms of
`SessionStructure::merge_field`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.L1GX.Leaf.MF9PAux

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record.DeserializeSeed CryptoVerification.E2E.Record.DeserializeGeneral
open CryptoVerification.E2E.Record.L1GX
open CryptoVerification.E2E.Record.L1GX.Leaf.MF14Aux
open CryptoVerification.E2E.Record.Serialization (OkAt allocPanic)

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

gen_decodes libsignalSessionCode_tree x9p
  [0x581c → 0x5858, 0x5b30 → 0x5b84, 0x5f24 → 0x5f34, 0x5f74 → 0x5fbc,
   0x6010 → 0x606c, 0x60b8 → 0x610c, 0x6148 → 0x6150]

/-! ## Payload and varint lemmas -/

theorem encodeVarint_37_57_x9p {n : Nat} (h1 : 37 ≤ n) (h2 : n ≤ 57) :
    encodeVarint (BitVec.ofNat 64 n) = [BitVec.ofNat 8 n] ∧
      BitVec.signExtend 64 (BitVec.ofNat 8 n) = BitVec.ofNat 64 n ∧
      (BitVec.ofNat 64 n).getLsbD 63 = false := by
  have hd : n - 37 ≤ 20 := by omega
  have hn : n = 37 + (n - 37) := by omega
  rw [hn]
  generalize n - 37 = d at hd
  rcases d with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
      d
  all_goals try decide
  omega

theorem pendingB0_signExtend_1_x9p (v : BitVec 64) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (36 + (encodeVarint v).length)) =
      BitVec.ofNat 64 (36 + (encodeVarint v).length) := by
  have hm := encodeVarint_length_bounds_mf14 v
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.1

theorem pendingB0_getLsbD_63_1_x9p (v : BitVec 64) :
    (BitVec.ofNat 64 (36 + (encodeVarint v).length)).getLsbD 63 = false := by
  have hm := encodeVarint_length_bounds_mf14 v
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.2

theorem pendingB0_signExtend_2_x9p (v1 v2 : BitVec 64) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (37 + (encodeVarint v1).length + (encodeVarint v2).length))
    =
      BitVec.ofNat 64 (37 + (encodeVarint v1).length + (encodeVarint v2).length) := by
  have hm1 := encodeVarint_length_bounds_mf14 v1
  have hm2 := encodeVarint_length_bounds_mf14 v2
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.1

theorem pendingB0_getLsbD_63_2_x9p (v1 v2 : BitVec 64) :
    (BitVec.ofNat 64 (37 + (encodeVarint v1).length + (encodeVarint v2).length)).getLsbD 63 =
      false := by
  have hm1 := encodeVarint_length_bounds_mf14 v1
  have hm2 := encodeVarint_length_bounds_mf14 v2
  exact (encodeVarint_37_57_x9p (by omega) (by omega)).2.2

theorem pendingId_payload_eq_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenFieldX.pendingId i k).payload =
      BitVec.ofNat 8 (36 + (encodeVarint (i.setWidth 64)).length) ::
        8#8 :: (encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k)) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hb : pendingIdBody i k =
      8#8 :: (encodeVarint (i.setWidth 64) ++ (18#8 :: 33#8 :: k)) := by
    unfold pendingIdBody; rw [hl]; rfl
  have hblen : (pendingIdBody i k).length = 36 + (encodeVarint (i.setWidth 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hvar := (encodeVarint_37_57_x9p (n := 36 + (encodeVarint (i.setWidth 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingId_payload_length_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33) :
    (GenFieldX.pendingId i k).payload.length = 37 + (encodeVarint (i.setWidth 64)).length := by
  rw [pendingId_payload_eq_x9p i hk]
  simp only [List.length_cons, List.length_append, hk]; omega

theorem pendingSpk_none_payload_eq_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk none k spk).payload =
      BitVec.ofNat 8 (36 + (encodeVarint (spk.signExtend 64)).length) ::
        18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hs : int32Field 3 spk = 24#8 :: encodeVarint (spk.signExtend 64) := by
    unfold int32Field; simp [hspk]; rfl
  have hb : pendingSpkBody none k spk =
      18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))) := by
    unfold pendingSpkBody optUint32Field; rw [hl, hs]; simp
  have hblen : (pendingSpkBody none k spk).length =
      36 + (encodeVarint (spk.signExtend 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have hvar := (encodeVarint_37_57_x9p (n := 36 + (encodeVarint (spk.signExtend 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingSpk_none_payload_length_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk none k spk).payload.length =
      37 + (encodeVarint (spk.signExtend 64)).length := by
  rw [pendingSpk_none_payload_eq_x9p hk hspk]
  simp only [List.length_cons, List.length_append, hk]; omega

theorem pendingSpk_some_payload_eq_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length = 33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk (some i) k spk).payload =
      BitVec.ofNat 8 (37 + (encodeVarint (i.setWidth 64)).length +
          (encodeVarint (spk.signExtend 64)).length) ::
        8#8 :: (encodeVarint (i.setWidth 64) ++
          (18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))))) := by
  have hl : lenField 2 k = 18#8 :: 33#8 :: k := by unfold lenField; rw [hk]; rfl
  have hs : int32Field 3 spk = 24#8 :: encodeVarint (spk.signExtend 64) := by
    unfold int32Field; simp [hspk]; rfl
  have hb : pendingSpkBody (some i) k spk =
      8#8 :: (encodeVarint (i.setWidth 64) ++
        (18#8 :: (33#8 :: k ++ (24#8 :: encodeVarint (spk.signExtend 64))))) := by
    unfold pendingSpkBody optUint32Field
    rw [hl, hs]
    simp [encodeKey, encodeVarint, encodeVarintAux, WireType.toNat]
  have hblen : (pendingSpkBody (some i) k spk).length =
      37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
    rw [hb]; simp only [List.length_cons, List.length_append, hk]; omega
  have hm1 := encodeVarint_length_bounds_mf14 (i.setWidth 64)
  have hm2 := encodeVarint_length_bounds_mf14 (spk.signExtend 64)
  have hvar := (encodeVarint_37_57_x9p
    (n := 37 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length)
    (by omega) (by omega)).1
  dsimp only [GenFieldX.payload]
  rw [hblen, hvar, hb, List.singleton_append]

theorem pendingSpk_some_payload_length_x9p (i : BitVec 32) {k : List (BitVec 8)} (hk : k.length =
    33)
    {spk : BitVec 32} (hspk : spk ≠ 0#32) :
    (GenFieldX.pendingSpk (some i) k spk).payload.length =
      38 + (encodeVarint (i.setWidth 64)).length + (encodeVarint (spk.signExtend 64)).length := by
  rw [pendingSpk_some_payload_eq_x9p i hk hspk]
  simp only [List.length_cons, List.length_append, hk]; omega

theorem mergeUint32_encode_64_x9p (v64 : BitVec 64) (rest : List (BitVec 8)) :
    mergeUint32 .varint (encodeVarint v64 ++ rest) = some (v64.setWidth 32, rest) := by
  simp [mergeUint32, decodeVarint_encodeVarint]

theorem setWidth32_setWidth64_x9p (x : BitVec 32) :
    (x.setWidth 64).setWidth 32 = x := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_setWidth, BitVec.toNat_setWidth]
  have := x.isLt
  omega

theorem setWidth32_signExtend64_x9p (x : BitVec 32) :
    (x.signExtend 64).setWidth 32 = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend]
  simp [hj, show j < 64 by omega]

theorem mergeBytes_k_x9p {k : List (BitVec 8)} (hk : k.length = 33)
    (rest : List (BitVec 8)) :
    mergeBytes .lengthDelimited (33#8 :: k ++ rest) = some (k, rest) := by
  have h := mergeBytes_encode k rest (by omega)
  rw [hk] at h
  exact h

/-! ## Jump-table byte at `.rodata + 0x79024` -/

theorem rodata_jump_tag9_x9p {s : State} (hF : sessionImg0.FrozenLoaded s) :
    s.mem.read8 (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) = 0xb5#8 ∧
      s.mem.canRead (sessionImg0.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) 1 = true := by
  have hhb := loads_rodata_holdsBytes E2E.Record.loads_sessionImg0 hF
    (off := num% (ls_bytes% "0082775f19328d6db5d6cb6d" + 8)) (n := 1) (bs := [0xb5#8])
    (by decide) (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) (by rfl_kernel) rfl (by
      rfl_kernel)
  exact ⟨(holdsBytes_cons_iff.mp hhb).1.1, (memSlice_of_holdsBytes_ro hhb).1⟩

/-! ## `SessionStructure` layout splits at `+0xf8..0x128` -/

/-- Portion of `prostSSGXAt` outside the 48-byte `pending_pre_key` region at `ss + 0xf8..0x128`. -/
def prostSSRest_x9p (A : RustAlloc) (ss : BitVec 64) (v : SSG) : SepProp :=
  vecU8 A ss v.lik ∗ vecU8 A (ss + 0x18#64) v.rik ∗ vecU8 A (ss + 0x30#64) v.root ∗
    vecOf A 104 8 (fun c a => prostChainGAt A a c) (ss + 0x48#64) v.recv ∗
    vecU8 A (ss + 0x60#64) [] ∗ vecU8 A (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainGAt A (ss + 0x90#64) c) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ v.prevCounter) ∗
    ((ss + 0x150#64) ↦₃₂ 0#32) ∗ ((ss + 0x154#64) ↦₃₂ 0#32)

theorem memRegion_40_split_x9p (ss : BitVec 64) :
    memRegion (ss + 0x100#64) 40 =
      (∃∗ w100 : BitVec 64, (ss + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (ss + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 64, (ss + 0x110#64) ↦₆₄ w110) ∗
      (∃∗ w118 : BitVec 64, (ss + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (ss + 0x120#64) ↦₃₂ w120) ∗
      memRegion (ss + 0x124#64) 4 := by
  rw [memRegion_split' (b := ss + 0x100#64) (b' := ss + 0x108#64) (n := 8) (k :=
      32) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x108#64) (b' := ss + 0x110#64) (n := 8) (k :=
        24) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x110#64) (b' := ss + 0x118#64) (n := 8) (k :=
        16) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x118#64) (b' := ss + 0x120#64) (n := 8) (k :=
        8) rfl (by bv_lin) (by decide),
      memRegion_split' (b := ss + 0x120#64) (b' := ss + 0x124#64) (n := 4) (k :=
        4) rfl (by bv_lin) (by decide),
      ProofLib.memRegion_eight (ss + 0x100#64), ProofLib.memRegion_eight (ss + 0x108#64),
      ProofLib.memRegion_eight (ss + 0x110#64), ProofLib.memRegion_eight (ss + 0x118#64),
      ProofLib.memRegion_four (ss + 0x120#64)]

theorem prostSSGXAt_fresh_unfold_x9p (A : RustAlloc) (ss : BitVec 64) (v : SSG)
    (hp : v.pending = none) :
    prostSSGXAt A ss ⟨v, ExtraG.empty⟩ =
      ((ss + 0xf8#64) ↦₆₄ 0xffffffffffffffff#64) ∗
      (∃∗ w100 : BitVec 64, (ss + 0x100#64) ↦₆₄ w100) ∗
      (∃∗ w108 : BitVec 64, (ss + 0x108#64) ↦₆₄ w108) ∗
      (∃∗ w110 : BitVec 64, (ss + 0x110#64) ↦₆₄ w110) ∗
      (∃∗ w118 : BitVec 64, (ss + 0x118#64) ↦₆₄ w118) ∗
      (∃∗ w120 : BitVec 32, (ss + 0x120#64) ↦₃₂ w120) ∗
      memRegion (ss + 0x124#64) 4 ∗
      prostSSRest_x9p A ss v := by
  unfold prostSSGXAt prostSSRest_x9p ExtraG.empty kyberAt
  rw [hp, memRegion_40_split_x9p ss]
  dsimp only [noneCap]
  ac_rfl

theorem pointsTo64_split32_x9p (a : BitVec 64) (v : BitVec 64) :
    (a ↦₆₄ v) = (a ↦₃₂ v.truncate 32) ∗ ((a + 4#64) ↦₃₂ v.extractLsb' 32 32) :=
  ProofLib.pointsTo64_split32 a v

theorem split_272_x9p (ss : BitVec 64) :
    ((ss + 272#64) ↦₆₄ 1#64) = ((ss + 272#64) ↦₃₂ 1#32) ∗ ((ss + 276#64) ↦₃₂ 0#32) := by
  have h := pointsTo64_split32_x9p (ss + 272#64) 1#64
  have h1 : (1#64).truncate 32 = 1#32 := rfl
  have h2 : (1#64).extractLsb' 32 32 = 0#32 := rfl
  have h3 : ss + 272#64 + 4#64 = ss + 276#64 := by bv_lin
  rw [h1, h2, h3] at h
  exact h

theorem mask_hi32_truncate32_x9p (w : BitVec 64) :
    (w &&& 18446744069414584320#64 ||| 0#64).truncate 32 = 0#32 := by
  simp

theorem pid_disc_lsb_x9p (w : BitVec 64) :
    ((BitVec.zeroExtend 64 (BitVec.truncate 32 (w &&& 18446744069414584320#64 ||| 0#64))).getLsbD 0
      == true) = false := by
  rw [mask_hi32_truncate32_x9p]; rfl

theorem pid_none_entails_x9p (ss : BitVec 64) (w110 : BitVec 64) :
    ((ss + 272#64) ↦₆₄ (w110 &&& 18446744069414584320#64 ||| 0#64)) ⊢
      ((ss + 0x110#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x114#64) 4 := by
  rw [pointsTo64_split32_x9p, mask_hi32_truncate32_x9p]
  have h110 : ss + 272#64 = ss + 0x110#64 := rfl
  have h114 : ss + 272#64 + 4#64 = ss + 0x114#64 := by bv_lin
  rw [h110, h114]
  exact sepConj_mono_right (Prost.pointsTo32_entails_memRegion4 _ _)

theorem vecU8_intro_x9p (A : RustAlloc) (a cap ptr : BitVec 64) (k : List (BitVec 8)) :
    vecU8At A a cap ptr k ⊢ vecU8 A a k := by
  unfold vecU8
  exact Entails.trans
    (Entails.sepExists_intro (P := fun ptr' => vecU8At A a cap ptr' k) ptr)
    (Entails.sepExists_intro (P := fun cap' => ∃∗ ptr', vecU8At A a cap' ptr' k) cap)

theorem prostSSGXAt_post_fold_id_x9p (A : RustAlloc) (ss cap' ptr' : BitVec 64)
    (v : SSG) (i : BitVec 32) (k : List (BitVec 8)) :
    vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ 0#32) ∗
      memRegion (ss + 0x124#64) 4 ∗ prostSSRest_x9p A ss v ⊢
      prostSSGXAt A ss (SSGX.apply ⟨v, ExtraG.empty⟩ (.pendingId i k)) := by
  refine Entails.trans (sepConj_mono_left (vecU8_intro_x9p A _ cap' ptr' k)) ?_
  unfold prostSSGXAt prostSSRest_x9p SSGX.apply pidAt kyberAt ExtraG.empty
  dsimp only
  apply Entails.of_eq
  ac_rfl

theorem prostSSGXAt_post_fold_spk_some_x9p (A : RustAlloc) (ss cap' ptr' : BitVec 64)
    (v : SSG) (i : BitVec 32) (k : List (BitVec 8)) (spk : BitVec 32) :
    vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 0x110#64) ↦₃₂ 1#32) ∗ ((ss + 0x114#64) ↦₃₂ i) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4 ∗ prostSSRest_x9p A ss v ⊢
      prostSSGXAt A ss (SSGX.apply ⟨v, ExtraG.empty⟩ (.pendingSpk (some i) k spk)) := by
  refine Entails.trans (sepConj_mono_left (vecU8_intro_x9p A _ cap' ptr' k)) ?_
  unfold prostSSGXAt prostSSRest_x9p SSGX.apply pidAt kyberAt ExtraG.empty
  dsimp only
  apply Entails.of_eq
  ac_rfl

theorem prostSSGXAt_post_fold_spk_none_x9p (A : RustAlloc) (ss cap' ptr' w110 : BitVec 64)
    (v : SSG) (k : List (BitVec 8)) (spk : BitVec 32) :
    vecU8At A (ss + 0xf8#64) cap' ptr' k ∗
      ((ss + 272#64) ↦₆₄ (w110 &&& 18446744069414584320#64 ||| 0#64)) ∗
      ((ss + 0x118#64) ↦₆₄ 0#64) ∗ ((ss + 0x120#64) ↦₃₂ spk) ∗
      memRegion (ss + 0x124#64) 4 ∗ prostSSRest_x9p A ss v ⊢
      prostSSGXAt A ss (SSGX.apply ⟨v, ExtraG.empty⟩ (.pendingSpk none k spk)) := by
  refine Entails.trans
    (sepConj_mono (vecU8_intro_x9p A _ cap' ptr' k)
      (sepConj_mono_left (pid_none_entails_x9p ss w110))) ?_
  unfold prostSSGXAt prostSSRest_x9p SSGX.apply pidAt kyberAt ExtraG.empty
  dsimp only
  apply Entails.of_eq
  ac_rfl

theorem emptyVec_pending_eq_vecU8At_x9p (A : RustAlloc) (ss : BitVec 64) :
    ((ss + 0xf8#64) ↦₆₄ 0#64) ∗ ((ss + 0x100#64) ↦₆₄ 1#64) ∗ ((ss + 0x108#64) ↦₆₄ 0#64) =
      vecU8At A (ss + 0xf8#64) 0#64 1#64 [] := by
  have h100 : ss + 0xf8#64 + 8#64 = ss + 0x100#64 := by bv_lin
  have h108 : ss + 0xf8#64 + 16#64 = ss + 0x108#64 := by bv_lin
  have hp : ([] : List (BitVec 8)).length ≤ (0#64 : BitVec 64).toNat ∧
      (0#64 : BitVec 64).toNat < 2 ^ 63 ∧ (1#64 : BitVec 64) ≠ 0 :=
    ⟨by decide, by decide, by decide⟩
  dsimp only [vecU8At, vecHeader]
  have hite : (if (0#64 : BitVec 64) = 0 then emp else
      A.live (1#64) (0#64).toNat 1 ∗ 1#64 ↦ₛ [] ∗
        memRegion (1#64 + BitVec.ofNat 64 ([] : List (BitVec 8)).length)
          ((0#64 : BitVec 64).toNat - ([] : List (BitVec 8)).length)) = emp := rfl
  rw [h100, h108, eq_true hp, hite, pure_true, emp_sepConj, sepConj_emp, List.length_nil]

/-! ## Stack-frame splits -/

theorem stackAt_mergeField_unfold_x9p (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStack =
      ∃∗ v80 : BitVec 64, ∃∗ v72 : BitVec 64, ∃∗ v64 : BitVec 64,
      ∃∗ v56 : BitVec 64, ∃∗ v48 : BitVec 64, ∃∗ v40 : BitVec 64,
      ∃∗ v32 : BitVec 64, ∃∗ v24 : BitVec 64, ∃∗ v16 : BitVec 64,
      ∃∗ v8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ v80) ∗ ((sp0 - 72#64) ↦₆₄ v72) ∗
        ((sp0 - 64#64) ↦₆₄ v64) ∗ ((sp0 - 56#64) ↦₆₄ v56) ∗
        ((sp0 - 48#64) ↦₆₄ v48) ∗ ((sp0 - 40#64) ↦₆₄ v40) ∗
        ((sp0 - 32#64) ↦₆₄ v32) ∗ ((sp0 - 24#64) ↦₆₄ v24) ∗
        ((sp0 - 16#64) ↦₆₄ v16) ∗ ((sp0 - 8#64) ↦₆₄ v8) ∗
        memRegion (sp0 - 240#64) 160 ∗
        stackAt (sp0 - 240#64) mergeFieldSubStack_mf14 := by
  have h1 : stackAt sp0 mergeFieldStack =
      cells (sp0 - 80#64) 10 ∗
      (memRegion (sp0 - 240#64) 160 ∗ stackAt (sp0 - 240#64) mergeFieldSubStack_mf14) := by
    rw [stackAt_mergeField_split_mf14 sp0]; ac_rfl
  rw [h1]
  simp only [cells, sepConj_emp, sepExists_sepConj_left, sepExists_sepConj_right,
    show sp0 - 80#64 + 8#64 = sp0 - 72#64 by bv_lin,
    show sp0 - 72#64 + 8#64 = sp0 - 64#64 by bv_lin,
    show sp0 - 64#64 + 8#64 = sp0 - 56#64 by bv_lin,
    show sp0 - 56#64 + 8#64 = sp0 - 48#64 by bv_lin,
    show sp0 - 48#64 + 8#64 = sp0 - 40#64 by bv_lin,
    show sp0 - 40#64 + 8#64 = sp0 - 32#64 by bv_lin,
    show sp0 - 32#64 + 8#64 = sp0 - 24#64 by bv_lin,
    show sp0 - 24#64 + 8#64 = sp0 - 16#64 by bv_lin,
    show sp0 - 16#64 + 8#64 = sp0 - 8#64 by bv_lin,
    sepConj_assoc]


end CryptoVerification.E2E.Record.L1GX.Leaf.MF9PAux
