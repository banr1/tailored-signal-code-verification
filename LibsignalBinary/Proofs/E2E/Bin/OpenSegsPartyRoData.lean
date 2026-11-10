/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

import all Init.Data.String.Defs
public import LibsignalBinary.Proofs.E2E.Bin.SpecsCommon
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.E2E.Bin.CalleeProofs
import LibsignalBinary.Proofs.E2E.Bin.OpenSegs
import LibsignalBinary.Proofs.E2E.StoreNew.RoData
import LibsignalBinary.Proofs.TripleRatchet.Bytes.From
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.InImageCallees.Calls
import LibsignalBinary.Proofs.TripleRatchet.Prost.BytesMerge.Phase23
import ProofLib.SepLogic.WP.Apply
import ProofLib.SepLogic.WPp

@[expose] public section

namespace CryptoVerification.E2E.Bin

set_option warningAsError false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000

open Arm64 ProofLib ProofLib.ObjectLoad CryptoGames
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalProtoCodec

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local arm64_norm ↓, local wp_norm ↓]
  tpidrEl0_setPC_pre_open tpidrEl0_setMem_setPC_pre_open
  trace_setPC_pre_open trace_setMem_setPC_pre_open
  fastStateSP fastReadReg64 fastReadReg32 fastReadReg
attribute [-arm64_norm, -wp_norm]
  ProofLib.reduceStateSP
  ProofLib.reduceStateReadReg64
  ProofLib.reduceStateReadReg32
  ProofLib.reduceStateReadReg

/-! ## `.rodata` and `.data.rel.ro` Facts for `ALICE` and `BOB` -/

section PartyRoDataFacts
open ProofLib.ObjectLoad.RoDataFactsAux ProofLib.ProgramReflection
set_option maxRecDepth 2000000

end PartyRoDataFacts

theorem loads_reloc_word_holdsBytes_inRo {li : Obj.LinkedImage} {img : Obj.Image} {s : State}
    (himg : Obj.Loads li img) (hF : img.FrozenLoaded s) {secOff target : Nat}
    (hro : inLiRoData li secOff 8 = true)
    (hoff : li.dataOff ≤ secOff)
    (hlen : secOff - li.dataOff ≤ li.data.length)
    (hany : li.relocs.any (fun r =>
      decide (r.off = secOff - li.dataOff ∧ r.width = 8 ∧ r.target = target)) = true)
    (hall : li.relocs.all (fun r =>
      decide ((r.off = secOff - li.dataOff ∧ r.width = 8 ∧ r.target = target) ∨
        r.off + r.width ≤ secOff - li.dataOff ∨ secOff - li.dataOff + 8 ≤ r.off)) = true) :
    Obj.HoldsBytes s.mem (img.base + BitVec.ofNat 64 secOff)
      (Obj.bytesLE 8 (img.base + BitVec.ofNat 64 target)) (fun _ => .ro) := by
  obtain ⟨data, hfold, -, hwf, -, himg_eq⟩ := load_eq_ok himg
  have hda : img.dataAddr = img.base + BitVec.ofNat 64 li.dataOff := congrArg Obj.Image.dataAddr himg_eq
  have hdata_eq : img.data = data := congrArg Obj.Image.data himg_eq
  have hro_map : img.roData = li.roData.map (fun (o, m) => (img.base + BitVec.ofNat 64 o, m)) :=
    congrArg Obj.Image.roData himg_eq
  simp only [inLiRoData, List.any_eq_true, decide_eq_true_eq] at hro
  obtain ⟨⟨rOff, rLen⟩, hr_mem, hr_le1, hr_le2, hr_lt⟩ := hro
  intro j hj
  have hj8 : j < 8 := hj
  have hlen_app : secOff - li.dataOff ≤ (li.data ++ List.replicate li.bss 0).length := by
    rw [List.length_append]; omega
  have hout := StoreNew.foldlM_dataReloc_getElem?_reloc li.relocs _ data hfold hlen_app hany hall hj8
  rw [← hdata_eq, List.getElem?_eq_getElem hj] at hout
  have hi : secOff - li.dataOff + j < img.data.length := (List.getElem?_eq_some_iff.mp hout).1
  have hget : img.data[secOff - li.dataOff + j] =
      (Obj.bytesLE 8 (img.base + BitVec.ofNat 64 target))[j] :=
    Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hout)
  have ha_eq : img.dataAddr + BitVec.ofNat 64 (secOff - li.dataOff + j) =
      img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 j := by
    rw [hda, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; omega
  have ha_eq' : img.dataAddr + BitVec.ofNat 64 (secOff - li.dataOff + j) =
      img.base + BitVec.ofNat 64 (secOff + j) := by
    rw [ha_eq, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hisRo : img.isRoData (img.dataAddr + BitVec.ofNat 64 (secOff - li.dataOff + j)) = true := by
    simp only [Obj.Image.isRoData, hro_map, List.any_map, List.any_eq_true]
    refine ⟨(rOff, rLen), hr_mem, ?_⟩
    simp only [Function.comp_apply, decide_eq_true_eq, ha_eq']
    rw [bv_add_sub_add_of_le img.base (by omega) (by omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hread, hperm'⟩ := hF.roData (secOff - li.dataOff + j) hi hisRo
  rw [← ha_eq, hread, hget]
  exact ⟨rfl, hperm'⟩

theorem pointsToBytesRO_partyTail_eq (p : BitVec 64) (r : Role) :
    ((p + 8#64) ↦ᵣ (leBytes 8 36 ++ r.idPrivBytes ++ r.idPubWire)) =
      ((p + 8#64) ↦₆₄ᵣ 36#64) ∗
      ((p + 16#64) ↦ᵣ r.idPrivBytes) ∗
      ((p + 48#64) ↦ᵣ r.idPubWire) := by
  have h1 : leBytes 8 36 = Obj.bytesLE 8 36#64 := rfl
  have hlen1 : BitVec.ofNat 64 (Obj.bytesLE 8 36#64).length = 8#64 := rfl
  have hlen2 : BitVec.ofNat 64 r.idPrivBytes.length = 32#64 := by cases r <;> rfl
  rw [List.append_assoc, h1, pointsToBytesRO_append, hlen1, StoreNew.pointsToBytesRO_bytesLE8_eq,
      pointsToBytesRO_append, hlen2]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

open ProofLib.ProgramReflection in
theorem aliceNameBytes_length : aliceNameBytes.length = 36 := by rfl_kernel
open ProofLib.ProgramReflection in
theorem bobNameBytes_length : bobNameBytes.length = 36 := by rfl_kernel

/-! ## Read-Only `memcpy`, `PublicKey::try_from`, and `IdentityKey::decode` -/

def openMemcpyRoSpec : Spec (BitVec 64 × BitVec 64 × List (BitVec 8)) where
  pre := fun (dst, src, bs) s0 =>
    ⌜s0.readReg64 .x0 = dst ∧
     s0.readReg64 .x1 = src ∧
     (s0.readReg64 .x2).toNat = bs.length ∧
     bs.length ≤ 2 ^ 64⌝ ∗
    memRegion dst bs.length ∗
    (src ↦ᵣ bs)
  post := fun (dst, src, bs) s0 sf =>
    ⌜sf.readReg64 .x0 = dst ∧ sf.trace = s0.trace ∧ sf.tpidrEl0 = s0.tpidrEl0⌝ ∗
    (dst ↦ₛ bs) ∗
    (src ↦ᵣ bs)

theorem openMemcpy_ro_hookOk : HookOk hookMemcpy openMemcpyRoSpec := by
  refine retHook_ok fun ⟨dst, src, bs⟩ R s0 _ hpre _ => ?_
  simp only [openMemcpyRoSpec, sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hlen⟩, hmem⟩
  have hsrc_front : s0.mem ⊨ (src ↦ᵣ bs) ∗ (memRegion dst bs.length ∗ R) := by
    rwa [← sepConj_assoc, sepConj_comm (memRegion dst bs.length), sepConj_assoc] at hmem
  have hread : s0.mem.readBytes src bs.length = bs :=
    (IsBlockRO.pointsToBytesRO src bs hlen).read hsrc_front
  refine ⟨?_, rfl, ‹_›, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  · dsimp only
    rw [hx0, hx1, hx2, hread]
    exact keepsFrozen_writeBytes_of_memRegion bs hlen hmem
  · simp only [openMemcpyRoSpec, retHook, State.readReg64_setPC, State.readReg64_setMem,
      hx0, hx1, hx2, hread, sepConj_assoc, satisfies_pure_sepConj, true_and]
    exact ⟨⟨rfl, rfl⟩, satisfies_writeBytes bs hlen hmem⟩

theorem pointsToBytesRO_of_unpack64_32 {bs : List (BitVec 8)} {w0 w1 w2 w3 : BitVec 64}
    (hbs : bs = unpack64 w0 ++ unpack64 w1 ++ unpack64 w2 ++ unpack64 w3) (a : BitVec 64) :
    (a ↦ᵣ bs) =
      (a ↦₆₄ᵣ w0) ∗ ((a + 8#64) ↦₆₄ᵣ w1) ∗ ((a + 16#64) ↦₆₄ᵣ w2) ∗ ((a + 24#64) ↦₆₄ᵣ w3) := by
  have hlen : BitVec.ofNat 64 (unpack64 w0).length = 8#64 := rfl
  have hlen1 : BitVec.ofNat 64 (unpack64 w1).length = 8#64 := rfl
  have hlen2 : BitVec.ofNat 64 (unpack64 w2).length = 8#64 := rfl
  rw [hbs, List.append_assoc, List.append_assoc,
      pointsToBytesRO_append, hlen,
      pointsToBytesRO_append, hlen1,
      pointsToBytesRO_append, hlen2,
      ← pointsTo64RO_eq_pointsToBytesRO,
      ← pointsTo64RO_eq_pointsToBytesRO,
      ← pointsTo64RO_eq_pointsToBytesRO,
      ← pointsTo64RO_eq_pointsToBytesRO]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

def pkTryFromLen33RoSpec : Spec (BitVec 64 × BitVec 64 × Role) where
  pre := fun (out, keyPtr, r) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ᵣ r.idPubWire) ∗ memRegion out 40
  post := fun (out, keyPtr, r) s0 sf =>
    ⌜sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.trace = s0.trace⌝ ∗
      (keyPtr ↦ᵣ r.idPubWire) ∗
      (out ↦₈ 0#8) ∗ ((out + 1#64) ↦ₛ r.idKey.publicKey.bytes.toList) ∗
      memRegion (out + 33#64) 7

theorem pkTryFrom_len33_ro_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr pkTryFromName) pkTryFromLen33RoSpec := by
  simp only [pkTryFromLen33RoSpec]
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom.pkTryFrom b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") (num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")) 0 48
  code_fetches_range libsignalSessionCode CryptoVerification.LibsignalTripleRatchet.PublicKeyTryFrom.pkTryFrom b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from") (num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")) 196 76
  wp_init g s0
  examples_generalize_entry
  examples_hide_fetches
  obtain ⟨out, keyPtr, r⟩ := g
  dsimp only at *
  subst out keyPtr
  obtain ⟨w0, w1, w2, w3, hbs, hpk_cells⟩ :=
    exists_unpack64_of_length_32 (bs := r.idKey.publicKey.bytes.toList)
      (role_idKey_bytes_length r)
  rw [role_idPubWire_eq r, pointsToBytesRO_cons,
      pointsToBytesRO_of_unpack64_32 hbs (s0.readReg64 (Reg.gpr 0#5) + 1#64),
      PublicKeyTryFrom.memRegion_40_split_ok (s0.readReg64 (Reg.gpr 8#5))]
  wp_pull_exists
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  wp_steps
  rw [hpk_cells (s0.readReg64 (Reg.gpr 8#5) + 1#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_done

theorem pk_try_from_len33_ro_ok_at (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (name : String) (k : Nat)
    (hk : libsignalSessionCode.fnOff name + k = libsignalSessionCode.fnOff pkTryFromName) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr name + BitVec.ofNat 64 k) pkTryFromLen33RoSpec :=
  inImage_ok_at hk (pkTryFrom_len33_ro_ok b C ctl abs)

private def remoteKeyChunks (a : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) : SepProp :=
  (a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
  ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6) ∗
  ((a + 7#64) ↦₁₆ v7) ∗ ((a + 9#64) ↦₃₂ v9) ∗ ((a + 13#64) ↦₁₆ v13) ∗
  ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ v31)

theorem sevenLo_eq_sevenHi (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ b4) ∗ ((a + 5#64) ↦₈ b5) ∗ ((a + 6#64) ↦₈ b6)) =
      ((a ↦₈ b0) ∗ ((a + 1#64) ↦₈ b1) ∗ ((a + 2#64) ↦₈ b2) ∗ ((a + 3#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3))) := by
  rw [← pointsToBytes4_eq_pointsTo32, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem sevenLo_eq_sevenHi' (a a1 a2 a3 a4 a5 a6 : BitVec 64)
    (h1 : a + 1#64 = a1) (h2 : a + 2#64 = a2) (h3 : a + 3#64 = a3)
    (h4 : a + 4#64 = a4) (h5 : a + 5#64 = a5) (h6 : a + 6#64 = a6)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    ((a ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗ (a4 ↦₈ b4) ∗ (a5 ↦₈ b5) ∗ (a6 ↦₈ b6) ∗ rest) =
      ((a ↦₈ b0) ∗ (a1 ↦₈ b1) ∗ (a2 ↦₈ b2) ∗ (a3 ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) := by
  subst h1 h2 h3 h4 h5 h6
  simpa only [sepConj_assoc] using
    congrArg (· ∗ rest) (sevenLo_eq_sevenHi a b0 b1 b2 b3 b4 b5 b6)

theorem sevenLo_eq_sevenHi_ro (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) :
    ((a ↦₃₂ᵣ (b3 ++ b2 ++ b1 ++ b0)) ∗ ((a + 4#64) ↦₈ᵣ b4) ∗ ((a + 5#64) ↦₈ᵣ b5) ∗ ((a + 6#64) ↦₈ᵣ b6)) =
      ((a ↦₈ᵣ b0) ∗ ((a + 1#64) ↦₈ᵣ b1) ∗ ((a + 2#64) ↦₈ᵣ b2) ∗ ((a + 3#64) ↦₃₂ᵣ (b6 ++ b5 ++ b4 ++ b3))) := by
  rw [← pointsToBytesRO4_eq_pointsTo32RO, ← pointsToBytesRO4_eq_pointsTo32RO]
  simp only [pointsToBytesRO_cons, pointsToBytesRO_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

theorem truncate16_zeroExtend32 (v : BitVec 16) :
    BitVec.truncate 16 (BitVec.zeroExtend 32 v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi32 : i < 32 := by omega
  simp [hi]

theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ₛ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by
    simp [List.length_take, List.length_drop]
    omega
  rw [pointsToBytes_append, hlen, List.drop_drop]

private theorem exists_remoteKeyChunks_of_length_32 {bs : List (BitVec 8)} (h : bs.length = 32) :
    ∃ (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
      (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
      (v15 v23 : BitVec 64) (v31 : BitVec 8),
      ∀ a : BitVec 64,
        (a ↦ₛ bs) = remoteKeyChunks a b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 := by
  refine ⟨bs.getD 0 0#8, bs.getD 1 0#8, bs.getD 2 0#8, bs.getD 3 0#8,
    bs.getD 4 0#8, bs.getD 5 0#8, bs.getD 6 0#8,
    pack16 (bs.getD 7 0#8) (bs.getD 8 0#8),
    pack32 (bs.getD 9 0#8) (bs.getD 10 0#8) (bs.getD 11 0#8) (bs.getD 12 0#8),
    pack16 (bs.getD 13 0#8) (bs.getD 14 0#8),
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    bs.getD 31 0#8, fun a => ?_⟩
  have hle : ∀ k, k ≤ 32 → k ≤ bs.length := fun k hk => h ▸ hk
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 4 (hle 4 (by decide)),
      pointsToBytes_drop_split _ bs 4 1 (hle 5 (by decide)),
      pointsToBytes_drop_split _ bs 5 1 (hle 6 (by decide)),
      pointsToBytes_drop_split _ bs 6 1 (hle 7 (by decide)),
      pointsToBytes_drop_split _ bs 7 2 (hle 9 (by decide)),
      pointsToBytes_drop_split _ bs 9 4 (hle 13 (by decide)),
      pointsToBytes_drop_split _ bs 13 2 (hle 15 (by decide)),
      pointsToBytes_drop_split _ bs 15 8 (hle 23 (by decide)),
      pointsToBytes_drop_split _ bs 23 8 (hle 31 (by decide)),
      pointsToBytes_drop_split _ bs 31 1 (hle 32 (by decide))]
  have hdrop32 : bs.drop 32 = [] := by simp [h]
  rw [hdrop32, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take4_eq_pointsTo32 _ bs 0 (hle 4 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 4 (hle 5 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 5 (hle 6 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 6 (hle 7 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 7 (hle 9 (by decide)),
      pointsToBytes_take4_eq_pointsTo32 _ bs 9 (hle 13 (by decide)),
      pointsToBytes_take2_eq_pointsTo16 _ bs 13 (hle 15 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 15 (hle 23 (by decide)),
      pointsToBytes_take8_eq_pointsTo64 _ bs 23 (hle 31 (by decide)),
      pointsToBytes_take1_eq_pointsTo8 _ bs 31 (hle 32 (by decide))]
  have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
  have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
  have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
  have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
  rw [h8, h1, h4, h2]
  simp only [remoteKeyChunks, pack32, BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunks_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (ret + 8#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗
      ((ret + 15#64) ↦₁₆ v7) ∗ ((ret + 17#64) ↦₃₂ v9) ∗ ((ret + 21#64) ↦₁₆ v13) ∗
      ((ret + 23#64) ↦₆₄ v15) ∗ ((ret + 31#64) ↦₆₄ v23) ∗ ((ret + 39#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

private theorem remoteKeyChunks_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8)
    (v7 : BitVec 16) (v9 : BitVec 32) (v13 : BitVec 16)
    (v15 v23 : BitVec 64) (v31 : BitVec 8) :
    remoteKeyChunks (sp - 87#64) b0 b1 b2 b3 b4 b5 b6 v7 v9 v13 v15 v23 v31 =
      ((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
      ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗
      ((sp - 80#64) ↦₁₆ v7) ∗ ((sp - 78#64) ↦₃₂ v9) ∗ ((sp - 74#64) ↦₁₆ v13) ∗
      ((sp - 72#64) ↦₆₄ v15) ∗ ((sp - 64#64) ↦₆₄ v23) ∗ ((sp - 56#64) ↦₈ v31) := by
  dsimp only [remoteKeyChunks]
  have h83 : sp - 87#64 + 4#64 = sp - 83#64 := by bv_omega
  have h82 : sp - 87#64 + 5#64 = sp - 82#64 := by bv_omega
  have h81 : sp - 87#64 + 6#64 = sp - 81#64 := by bv_omega
  have h80 : sp - 87#64 + 7#64 = sp - 80#64 := by bv_omega
  have h78 : sp - 87#64 + 9#64 = sp - 78#64 := by bv_omega
  have h74 : sp - 87#64 + 13#64 = sp - 74#64 := by bv_omega
  have h72 : sp - 87#64 + 15#64 = sp - 72#64 := by bv_omega
  have h64 : sp - 87#64 + 23#64 = sp - 64#64 := by bv_omega
  have h56 : sp - 87#64 + 31#64 = sp - 56#64 := by bv_omega
  rw [h83, h82, h81, h80, h78, h74, h72, h64, h56]

private theorem sevenLo_sp_87 (sp : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 87#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((sp - 83#64) ↦₈ b4) ∗ ((sp - 82#64) ↦₈ b5) ∗ ((sp - 81#64) ↦₈ b6) ∗ rest) =
      (((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗
       ((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (sp - 87#64) (sp - 86#64) (sp - 85#64) (sp - 84#64)
    (sp - 83#64) (sp - 82#64) (sp - 81#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sevenLo_ret_8 (ret : BitVec 64)
    (b0 b1 b2 b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((ret + 8#64) ↦₃₂ (b3 ++ b2 ++ b1 ++ b0)) ∗
     ((ret + 12#64) ↦₈ b4) ∗ ((ret + 13#64) ↦₈ b5) ∗ ((ret + 14#64) ↦₈ b6) ∗ rest) =
      (((ret + 8#64) ↦₈ b0) ∗ ((ret + 9#64) ↦₈ b1) ∗ ((ret + 10#64) ↦₈ b2) ∗
       ((ret + 11#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) :=
  sevenLo_eq_sevenHi' (ret + 8#64) (ret + 9#64) (ret + 10#64) (ret + 11#64)
    (ret + 12#64) (ret + 13#64) (ret + 14#64)
    (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega) (by bv_omega)
    b0 b1 b2 b3 b4 b5 b6 rest

private theorem sp_88_four_bytes (sp : BitVec 64) (b0 b1 b2 : BitVec 8) (rest : SepProp) :
    (((sp - 88#64) ↦₈ 0#8) ∗ ((sp - 87#64) ↦₈ b0) ∗ ((sp - 86#64) ↦₈ b1) ∗ ((sp - 85#64) ↦₈ b2) ∗ rest) =
      (((sp - 88#64) ↦₃₂ (b2 ++ b1 ++ b0 ++ 0#8)) ∗ rest) := by
  have h87 : sp - 87#64 = sp - 88#64 + 1#64 := by bv_omega
  have h86 : sp - 86#64 = sp - 88#64 + 2#64 := by bv_omega
  have h85 : sp - 85#64 = sp - 88#64 + 3#64 := by bv_omega
  rw [h87, h86, h85, ← pointsToBytes4_eq_pointsTo32]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem sp_84_split_16 (sp : BitVec 64) (b3 b4 b5 b6 : BitVec 8) (rest : SepProp) :
    (((sp - 84#64) ↦₃₂ (b6 ++ b5 ++ b4 ++ b3)) ∗ rest) =
      (((sp - 84#64) ↦₁₆ (b4 ++ b3)) ∗ ((sp - 82#64) ↦₁₆ (b6 ++ b5)) ∗ rest) := by
  have h82 : sp - 82#64 = sp - 84#64 + 2#64 := by bv_omega
  rw [h82, ← pointsToBytes4_eq_pointsTo32, ← pointsToBytes2_eq_pointsTo16, ← pointsToBytes2_eq_pointsTo16]
  simp only [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp,
    BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

private theorem memRegion_40_identityKeyDecode_split (ret : BitVec 64) :
    memRegion ret 40 =
      (∃∗ r0 : BitVec 64, ret ↦₆₄ r0) ∗
      (∃∗ r8 : BitVec 32, (ret + 8#64) ↦₃₂ r8) ∗
      (∃∗ r12 : BitVec 8, (ret + 12#64) ↦₈ r12) ∗
      (∃∗ r13 : BitVec 8, (ret + 13#64) ↦₈ r13) ∗
      (∃∗ r14 : BitVec 8, (ret + 14#64) ↦₈ r14) ∗
      (∃∗ r15 : BitVec 16, (ret + 15#64) ↦₁₆ r15) ∗
      (∃∗ r17 : BitVec 32, (ret + 17#64) ↦₃₂ r17) ∗
      (∃∗ r21 : BitVec 16, (ret + 21#64) ↦₁₆ r21) ∗
      (∃∗ r23 : BitVec 64, (ret + 23#64) ↦₆₄ r23) ∗
      (∃∗ r31 : BitVec 64, (ret + 31#64) ↦₆₄ r31) ∗
      (∃∗ r39 : BitVec 8, (ret + 39#64) ↦₈ r39) := by
  rw [ProofLib.memRegion_split' (b := ret) (n := 8) (k := 32)
        (b' := ret + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 8#64) (n := 4) (k := 28)
        (b' := ret + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 12#64) (n := 1) (k := 27)
        (b' := ret + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 13#64) (n := 1) (k := 26)
        (b' := ret + 14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 14#64) (n := 1) (k := 25)
        (b' := ret + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 15#64) (n := 2) (k := 23)
        (b' := ret + 17#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 17#64) (n := 4) (k := 19)
        (b' := ret + 21#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 21#64) (n := 2) (k := 17)
        (b' := ret + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 23#64) (n := 8) (k := 9)
        (b' := ret + 31#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := ret + 31#64) (n := 8) (k := 1)
        (b' := ret + 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight ret, memRegion_four (ret + 8#64),
      memRegion_one (ret + 12#64), memRegion_one (ret + 13#64), memRegion_one (ret + 14#64),
      memRegion_two (ret + 15#64), memRegion_four (ret + 17#64), memRegion_two (ret + 21#64),
      ProofLib.memRegion_eight (ret + 23#64), ProofLib.memRegion_eight (ret + 31#64), memRegion_one (ret + 39#64)]

private theorem stackAt_identityKeyDecode_split (sp : BitVec 64) :
    stackAt sp 0x60 =
      memRegion (sp - 96#64) 8 ∗
      memRegion (sp - 88#64) 40 ∗
      (∃∗ s48 : BitVec 64, (sp - 48#64) ↦₆₄ s48) ∗
      (∃∗ s56 : BitVec 8, (sp - 40#64) ↦₈ s56) ∗
      memRegion (sp - 39#64) 7 ∗
      cells (sp - 32#64) 3 ∗
      (∃∗ s88 : BitVec 32, (sp - 8#64) ↦₃₂ s88) ∗
      (∃∗ s92 : BitVec 16, (sp - 4#64) ↦₁₆ s92) ∗
      memRegion (sp - 2#64) 2 := by
  simp only [stackAt]
  rw [show BitVec.ofNat 64 0x60 = 96#64 from rfl,
      ProofLib.memRegion_split' (b := sp - 96#64) (n := 8) (k := 88)
        (b' := sp - 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 88#64) (n := 40) (k := 48)
        (b' := sp - 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 48#64) (n := 8) (k := 40)
        (b' := sp - 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 40#64) (n := 1) (k := 39)
        (b' := sp - 39#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 39#64) (n := 7) (k := 32)
        (b' := sp - 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 32#64) (n := 24) (k := 8)
        (b' := sp - 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 8#64) (n := 4) (k := 4)
        (b' := sp - 4#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 4#64) (n := 2) (k := 2)
        (b' := sp - 2#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight (sp - 48#64), memRegion_one (sp - 40#64),
      (ProofLib.memRegion_cells (sp - 32#64) 3 (by decide) :
        memRegion (sp - 32#64) 24 = cells (sp - 32#64) 3),
      memRegion_four (sp - 8#64), memRegion_two (sp - 4#64)]

private theorem memRegion_sp_88_40_split (sp : BitVec 64) :
    memRegion (sp - 88#64) 40 =
      (∃∗ k0 : BitVec 32, (sp - 88#64) ↦₃₂ k0) ∗
      (∃∗ k4 : BitVec 16, (sp - 84#64) ↦₁₆ k4) ∗
      (∃∗ k6 : BitVec 16, (sp - 82#64) ↦₁₆ k6) ∗
      (∃∗ k8 : BitVec 16, (sp - 80#64) ↦₁₆ k8) ∗
      (∃∗ k10 : BitVec 32, (sp - 78#64) ↦₃₂ k10) ∗
      (∃∗ k14 : BitVec 16, (sp - 74#64) ↦₁₆ k14) ∗
      (∃∗ k16 : BitVec 64, (sp - 72#64) ↦₆₄ k16) ∗
      (∃∗ k24 : BitVec 64, (sp - 64#64) ↦₆₄ k24) ∗
      (∃∗ k32 : BitVec 8, (sp - 56#64) ↦₈ k32) ∗
      memRegion (sp - 55#64) 7 := by
  rw [ProofLib.memRegion_split' (b := sp - 88#64) (n := 4) (k := 36)
        (b' := sp - 84#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 84#64) (n := 2) (k := 34)
        (b' := sp - 82#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 82#64) (n := 2) (k := 32)
        (b' := sp - 80#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 80#64) (n := 2) (k := 30)
        (b' := sp - 78#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 78#64) (n := 4) (k := 26)
        (b' := sp - 74#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 74#64) (n := 2) (k := 24)
        (b' := sp - 72#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 72#64) (n := 8) (k := 16)
        (b' := sp - 64#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 64#64) (n := 8) (k := 8)
        (b' := sp - 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := sp - 56#64) (n := 1) (k := 7)
        (b' := sp - 55#64) rfl (by bv_omega) (by decide),
      memRegion_four (sp - 88#64), memRegion_two (sp - 84#64), memRegion_two (sp - 82#64),
      memRegion_two (sp - 80#64), memRegion_four (sp - 78#64), memRegion_two (sp - 74#64),
      ProofLib.memRegion_eight (sp - 72#64), ProofLib.memRegion_eight (sp - 64#64), memRegion_one (sp - 56#64)]

def identityKeyDecodeRoSpec : Spec (BitVec 64 × BitVec 64 × Role) where
  pre := fun (out, keyPtr, r) s =>
    ⌜s.readReg64 .x8 = out ∧ s.readReg64 .x0 = keyPtr ∧ s.readReg64 .x1 = 33#64⌝ ∗
      (keyPtr ↦ᵣ r.idPubWire) ∗ memRegion out 40 ∗
      stackAt s.sp 0x60
  post := fun (out, keyPtr, r) s0 sf =>
    ⌜sf.tpidrEl0 = s0.tpidrEl0 ∧ sf.trace = s0.trace⌝ ∗
      (keyPtr ↦ᵣ r.idPubWire) ∗
      (out ↦₆₄ 0xfffffffffffffffe#64) ∗
      ((out + 8#64) ↦ₛ r.idKey.publicKey.bytes.toList) ∗
      stackAt s0.sp 0x60

set_option maxHeartbeats 800000 in
theorem identityKey_decode_ro_tripleRatchetProgAt_ok (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr identityKeyDecodeName)
      identityKeyDecodeRoSpec := by
  simp only [identityKeyDecodeRoSpec]
  have htry := pk_try_from_len33_ro_ok_at b C ctl abs
    identityKeyDecodeName (k := num% (ls_off% "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from" - ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode"))
    (by rw [identityKeyDecode_fnOff, (ls_lemma% fnOff "<libsignal_core::curve::PublicKey as core::convert::TryFrom<&[u8]>>::try_from")])
  simp only [pkTryFromLen33RoSpec] at htry
  code_fetches_range libsignalSessionCode CryptoVerification.E2E.Bin.identityKeyDecode b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode") (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode")) 0 40
  code_fetches_range libsignalSessionCode CryptoVerification.E2E.Bin.identityKeyDecode b
    (Rust.withPanics (tripleRatchetExterns C ctl abs))
    (ls_lemma% fnOff "<libsignal_protocol::identity_key::IdentityKey>::decode") (num% (ls_off% "<libsignal_protocol::identity_key::IdentityKey>::decode")) 64 108
  dsimp only [tripleRatchetProgAt, identityKeyDecodeName, BitVec.ofNat_eq_ofNat] at htry ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics (tripleRatchetExterns C ctl abs))).fnAddr "<libsignal_protocol::identity_key::IdentityKey>::decode" = entry
  wp_init x s0
  examples_hide_fetches
  obtain ⟨ret, keyPtr, r⟩ := x
  dsimp only at *
  subst ret keyPtr
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, v7, v9, v13, v15, v23, v31, hchunks⟩ :=
    exists_remoteKeyChunks_of_length_32 (role_idKey_bytes_length r)
  rw [memRegion_40_identityKeyDecode_split (s0.readReg64 (Reg.gpr 8#5)),
      hchunks (s0.readReg64 (Reg.gpr 8#5) + 8#64),
      remoteKeyChunks_ret_8 (s0.readReg64 (Reg.gpr 8#5)),
      stackAt_identityKeyDecode_split s0.sp]
  cells_unfold
  wp_pull_exists
  wp_steps
  wp_apply
  rw [hchunks (s0.sp - 87#64), remoteKeyChunks_sp_87 s0.sp]
  wp_steps
  rw [sevenLo_sp_87 s0.sp]
  wp_steps
  simp only [sepConj_assoc]
  rw [sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5)),
      sp_88_four_bytes s0.sp,
      sp_84_split_16 s0.sp]
  wp_steps
  try rw [truncate16_zeroExtend32]
  try rw [truncate16_zeroExtend32]
  try rw [← sevenLo_ret_8 (s0.readReg64 (Reg.gpr 8#5))]
  try rw [memRegion_sp_88_40_split s0.sp]
  wp_done

theorem identityKey_decode_ro_ok (C : Crypto) (img : Obj.Image) (ctl : BitVec 64)
    (abs : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    subroutine_ok (tripleRatchetProg img C ctl abs)
      (img.base + identityKeyDecodeOff)
      (identityKeyDecodeRoSpec.inImage img) := by
  have hfn : (tripleRatchetProgAt img.base C ctl abs).fnAddr identityKeyDecodeName =
      img.base + identityKeyDecodeOff := by
    rw [tripleRatchetProgAt, Program.fnAddr_rebase, identityKeyDecode_fnOff]
  rw [tripleRatchetProg_eq_tripleRatchetProgAt himg, ← hfn]
  exact LibsignalTripleRatchet.subroutine_ok_inImage img
    (identityKey_decode_ro_tripleRatchetProgAt_ok img.base C ctl abs)

/-! ## Private Key Chunk Decomposition (`r.idPrivBytes`, 32 B) -/

def Role.privB0 : Role → BitVec 8
  | .alice => 0x70#8
  | .bob   => 0xd8#8

def Role.privB31 : Role → BitVec 8
  | .alice => 0x47#8
  | .bob   => 0x74#8

theorem role_idPrivBytes_length (r : Role) : r.idPrivBytes.length = 32 := by
  cases r <;> rfl

theorem role_privB0_eq (r : Role) : r.idPrivBytes.getD 0 0#8 = r.privB0 := by
  cases r <;> rfl

theorem role_privB31_eq (r : Role) : r.idPrivBytes.getD 31 0#8 = r.privB31 := by
  cases r <;> rfl

theorem role_keyPairBytes_eq (r : Role) :
    r.keyPairBytes = r.idKey.publicKey.bytes.toList ++ r.idPrivBytes := by
  cases r <;> rfl

theorem pointsToBytesRO_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off k : Nat)
    (h : off + k ≤ bs.length) :
    (a ↦ᵣ bs.drop off) =
      (a ↦ᵣ (bs.drop off).take k) ∗ ((a + BitVec.ofNat 64 k) ↦ᵣ bs.drop (off + k)) := by
  conv => lhs; rw [← List.take_append_drop k (bs.drop off)]
  have hlen : ((bs.drop off).take k).length = k := by
    simp [List.length_take, List.length_drop]
    omega
  rw [pointsToBytesRO_append, hlen, List.drop_drop]

def privKeyChunksRO (a : BitVec 64)
    (b0 : BitVec 8) (v1 : BitVec 32) (v5 : BitVec 16) (b7 : BitVec 8)
    (b8 b9 b10 b11 b12 b13 b14 : BitVec 8)
    (v15 v23 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₈ᵣ b0) ∗ ((a + 1#64) ↦₃₂ᵣ v1) ∗ ((a + 5#64) ↦₁₆ᵣ v5) ∗ ((a + 7#64) ↦₈ᵣ b7) ∗
  ((a + 8#64) ↦₃₂ᵣ (b11 ++ b10 ++ b9 ++ b8)) ∗
  ((a + 12#64) ↦₈ᵣ b12) ∗ ((a + 13#64) ↦₈ᵣ b13) ∗ ((a + 14#64) ↦₈ᵣ b14) ∗
  ((a + 15#64) ↦₆₄ᵣ v15) ∗ ((a + 23#64) ↦₆₄ᵣ v23) ∗ ((a + 31#64) ↦₈ᵣ b31)

def privKeyChunksRW (a : BitVec 64)
    (b0 : BitVec 8) (v1 : BitVec 32) (v5 : BitVec 16) (b7 : BitVec 8)
    (b8 b9 b10 b11 b12 b13 b14 : BitVec 8)
    (v15 v23 : BitVec 64) (b31 : BitVec 8) : SepProp :=
  (a ↦₈ b0) ∗ ((a + 1#64) ↦₃₂ v1) ∗ ((a + 5#64) ↦₁₆ v5) ∗ ((a + 7#64) ↦₈ b7) ∗
  ((a + 8#64) ↦₃₂ (b11 ++ b10 ++ b9 ++ b8)) ∗
  ((a + 12#64) ↦₈ b12) ∗ ((a + 13#64) ↦₈ b13) ∗ ((a + 14#64) ↦₈ b14) ∗
  ((a + 15#64) ↦₆₄ v15) ∗ ((a + 23#64) ↦₆₄ v23) ∗ ((a + 31#64) ↦₈ b31)

theorem exists_privKeyChunks (r : Role) :
    ∃ (v1 : BitVec 32) (v5 : BitVec 16) (b7 : BitVec 8)
      (b8 b9 b10 b11 b12 b13 b14 : BitVec 8)
      (v15 v23 : BitVec 64),
      (∀ a : BitVec 64,
        (a ↦ᵣ r.idPrivBytes) =
          privKeyChunksRO a r.privB0 v1 v5 b7 b8 b9 b10 b11 b12 b13 b14 v15 v23 r.privB31) ∧
      (∀ a : BitVec 64,
        (a ↦ₛ r.idPrivBytes) =
          privKeyChunksRW a r.privB0 v1 v5 b7 b8 b9 b10 b11 b12 b13 b14 v15 v23 r.privB31) := by
  let bs := r.idPrivBytes
  have h : bs.length = 32 := role_idPrivBytes_length r
  have hle : ∀ k, k ≤ 32 → k ≤ bs.length := fun k hk => h ▸ hk
  refine ⟨pack32 (bs.getD 1 0#8) (bs.getD 2 0#8) (bs.getD 3 0#8) (bs.getD 4 0#8),
    pack16 (bs.getD 5 0#8) (bs.getD 6 0#8),
    bs.getD 7 0#8,
    bs.getD 8 0#8, bs.getD 9 0#8, bs.getD 10 0#8, bs.getD 11 0#8,
    bs.getD 12 0#8, bs.getD 13 0#8, bs.getD 14 0#8,
    pack64 (bs.getD 15 0#8) (bs.getD 16 0#8) (bs.getD 17 0#8) (bs.getD 18 0#8)
      (bs.getD 19 0#8) (bs.getD 20 0#8) (bs.getD 21 0#8) (bs.getD 22 0#8),
    pack64 (bs.getD 23 0#8) (bs.getD 24 0#8) (bs.getD 25 0#8) (bs.getD 26 0#8)
      (bs.getD 27 0#8) (bs.getD 28 0#8) (bs.getD 29 0#8) (bs.getD 30 0#8),
    ⟨fun a => ?_, fun a => ?_⟩⟩
  · change (a ↦ᵣ bs.drop 0) = _
    rw [pointsToBytesRO_drop_split a bs 0 1 (hle 1 (by decide)),
        pointsToBytesRO_drop_split _ bs 1 4 (hle 5 (by decide)),
        pointsToBytesRO_drop_split _ bs 5 2 (hle 7 (by decide)),
        pointsToBytesRO_drop_split _ bs 7 1 (hle 8 (by decide)),
        pointsToBytesRO_drop_split _ bs 8 4 (hle 12 (by decide)),
        pointsToBytesRO_drop_split _ bs 12 1 (hle 13 (by decide)),
        pointsToBytesRO_drop_split _ bs 13 1 (hle 14 (by decide)),
        pointsToBytesRO_drop_split _ bs 14 1 (hle 15 (by decide)),
        pointsToBytesRO_drop_split _ bs 15 8 (hle 23 (by decide)),
        pointsToBytesRO_drop_split _ bs 23 8 (hle 31 (by decide)),
        pointsToBytesRO_drop_split _ bs 31 1 (hle 32 (by decide))]
    have hdrop32 : bs.drop 32 = [] := by simp [h]
    rw [hdrop32, pointsToBytesRO_nil, sepConj_emp,
        pointsToBytesRO_take1_eq_pointsTo8RO _ bs 0 (hle 1 (by decide)),
        pointsToBytesRO_take4_eq_pointsTo32RO _ bs 1 (hle 5 (by decide)),
        pointsToBytesRO_take2_eq_pointsTo16RO _ bs 5 (hle 7 (by decide)),
        pointsToBytesRO_take1_eq_pointsTo8RO _ bs 7 (hle 8 (by decide)),
        pointsToBytesRO_take4_eq_pointsTo32RO _ bs 8 (hle 12 (by decide)),
        pointsToBytesRO_take1_eq_pointsTo8RO _ bs 12 (hle 13 (by decide)),
        pointsToBytesRO_take1_eq_pointsTo8RO _ bs 13 (hle 14 (by decide)),
        pointsToBytesRO_take1_eq_pointsTo8RO _ bs 14 (hle 15 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 15 (hle 23 (by decide)),
        pointsToBytesRO_take8_eq_pointsTo64RO _ bs 23 (hle 31 (by decide)),
        pointsToBytesRO_take1_eq_pointsTo8RO _ bs 31 (hle 32 (by decide))]
    have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
    have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
    have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
    have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
    rw [h8, h1, h4, h2, ← role_privB0_eq r, ← role_privB31_eq r]
    simp only [privKeyChunksRO, pack32, BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl
  · change (a ↦ₛ bs.drop 0) = _
    rw [pointsToBytes_drop_split a bs 0 1 (hle 1 (by decide)),
        pointsToBytes_drop_split _ bs 1 4 (hle 5 (by decide)),
        pointsToBytes_drop_split _ bs 5 2 (hle 7 (by decide)),
        pointsToBytes_drop_split _ bs 7 1 (hle 8 (by decide)),
        pointsToBytes_drop_split _ bs 8 4 (hle 12 (by decide)),
        pointsToBytes_drop_split _ bs 12 1 (hle 13 (by decide)),
        pointsToBytes_drop_split _ bs 13 1 (hle 14 (by decide)),
        pointsToBytes_drop_split _ bs 14 1 (hle 15 (by decide)),
        pointsToBytes_drop_split _ bs 15 8 (hle 23 (by decide)),
        pointsToBytes_drop_split _ bs 23 8 (hle 31 (by decide)),
        pointsToBytes_drop_split _ bs 31 1 (hle 32 (by decide))]
    have hdrop32 : bs.drop 32 = [] := by simp [h]
    rw [hdrop32, pointsToBytes_nil, sepConj_emp,
        pointsToBytes_take1_eq_pointsTo8 _ bs 0 (hle 1 (by decide)),
        pointsToBytes_take4_eq_pointsTo32 _ bs 1 (hle 5 (by decide)),
        pointsToBytes_take2_eq_pointsTo16 _ bs 5 (hle 7 (by decide)),
        pointsToBytes_take1_eq_pointsTo8 _ bs 7 (hle 8 (by decide)),
        pointsToBytes_take4_eq_pointsTo32 _ bs 8 (hle 12 (by decide)),
        pointsToBytes_take1_eq_pointsTo8 _ bs 12 (hle 13 (by decide)),
        pointsToBytes_take1_eq_pointsTo8 _ bs 13 (hle 14 (by decide)),
        pointsToBytes_take1_eq_pointsTo8 _ bs 14 (hle 15 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 15 (hle 23 (by decide)),
        pointsToBytes_take8_eq_pointsTo64 _ bs 23 (hle 31 (by decide)),
        pointsToBytes_take1_eq_pointsTo8 _ bs 31 (hle 32 (by decide))]
    have h8 : BitVec.ofNat 64 8 = 8#64 := rfl
    have h1 : BitVec.ofNat 64 1 = 1#64 := rfl
    have h4 : BitVec.ofNat 64 4 = 4#64 := rfl
    have h2 : BitVec.ofNat 64 2 = 2#64 := rfl
    rw [h8, h1, h4, h2, ← role_privB0_eq r, ← role_privB31_eq r]
    simp only [privKeyChunksRW, pack32, BitVec.add_assoc, BitVec.reduceAdd]
    ac_rfl

theorem memRegion_32_privKey_split (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ r0 : BitVec 8, a ↦₈ r0) ∗
      (∃∗ r1 : BitVec 32, (a + 1#64) ↦₃₂ r1) ∗
      (∃∗ r5 : BitVec 16, (a + 5#64) ↦₁₆ r5) ∗
      (∃∗ r7 : BitVec 8, (a + 7#64) ↦₈ r7) ∗
      (∃∗ r8 : BitVec 32, (a + 8#64) ↦₃₂ r8) ∗
      (∃∗ r12 : BitVec 8, (a + 12#64) ↦₈ r12) ∗
      (∃∗ r13 : BitVec 8, (a + 13#64) ↦₈ r13) ∗
      (∃∗ r14 : BitVec 8, (a + 14#64) ↦₈ r14) ∗
      (∃∗ r15 : BitVec 64, (a + 15#64) ↦₆₄ r15) ∗
      (∃∗ r23 : BitVec 64, (a + 23#64) ↦₆₄ r23) ∗
      (∃∗ r31 : BitVec 8, (a + 31#64) ↦₈ r31) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 1) (k := 31)
        (b' := a + 1#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 1#64) (n := 4) (k := 27)
        (b' := a + 5#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 5#64) (n := 2) (k := 25)
        (b' := a + 7#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 7#64) (n := 1) (k := 24)
        (b' := a + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 4) (k := 20)
        (b' := a + 12#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 12#64) (n := 1) (k := 19)
        (b' := a + 13#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 13#64) (n := 1) (k := 18)
        (b' := a + 14#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 14#64) (n := 1) (k := 17)
        (b' := a + 15#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 15#64) (n := 8) (k := 9)
        (b' := a + 23#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 23#64) (n := 8) (k := 1)
        (b' := a + 31#64) rfl (by bv_omega) (by decide),
      memRegion_one a, memRegion_four (a + 1#64), memRegion_two (a + 5#64),
      memRegion_one (a + 7#64), memRegion_four (a + 8#64),
      memRegion_one (a + 12#64), memRegion_one (a + 13#64), memRegion_one (a + 14#64),
      ProofLib.memRegion_eight (a + 15#64), ProofLib.memRegion_eight (a + 23#64),
      memRegion_one (a + 31#64)]

theorem role_privB0_clamp (r : Role) :
    BitVec.truncate 8 (BitVec.zeroExtend 32 r.privB0 &&& 0xfffffff8#32) = r.privB0 := by
  cases r <;> rfl

theorem role_privB31_clamp (r : Role) :
    BitVec.truncate 8
      (Arm64.evalBitfield .W32 .BFM 0x40#64 (BitVec.zeroExtend 64 r.privB31) 0 5) = r.privB31 := by
  cases r <;> rfl

theorem extractLsb'_lo64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 0 64 = lo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  simp [hi_lt]

theorem extractLsb'_hi64_append (hi lo : BitVec 64) :
    (hi ++ lo).extractLsb' 64 64 = hi := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi_lt
  simp [hi_lt]

theorem role_keyPairBytes_pointsTo (r : Role) (a : BitVec 64) :
    (a ↦ₛ r.keyPairBytes) =
      (a ↦ₛ r.idKey.publicKey.bytes.toList) ∗ ((a + 32#64) ↦ₛ r.idPrivBytes) := by
  rw [role_keyPairBytes_eq r, pointsToBytes_append, role_idKey_bytes_length r]

theorem memRegion_32_four_64 (a : BitVec 64) :
    memRegion a 32 =
      (∃∗ r0 : BitVec 64, a ↦₆₄ r0) ∗
      (∃∗ r1 : BitVec 64, (a + 8#64) ↦₆₄ r1) ∗
      (∃∗ r2 : BitVec 64, (a + 16#64) ↦₆₄ r2) ∗
      (∃∗ r3 : BitVec 64, (a + 24#64) ↦₆₄ r3) := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 24)
        (b' := a + 8#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 16)
        (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 8)
        (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_eight a, ProofLib.memRegion_eight (a + 8#64),
      ProofLib.memRegion_eight (a + 16#64), ProofLib.memRegion_eight (a + 24#64)]

theorem pointsTo64_5_entails_memRegion_40 (a : BitVec 64) (w0 w1 w2 w3 w4 : BitVec 64) :
    ((a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ∗
     ((a + 24#64) ↦₆₄ w3) ∗ ((a + 32#64) ↦₆₄ w4)) ⊢ memRegion a 40 := by
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 32)
        (b' := a + 8#64) rfl (by bv_omega) (by decide),
      memRegion_32_four_64 (a + 8#64),
      ProofLib.memRegion_eight a]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]
  exact sepConj_mono (Entails.sepExists_right w0 (Entails.refl _))
    (sepConj_mono (Entails.sepExists_right w1 (Entails.refl _))
      (sepConj_mono (Entails.sepExists_right w2 (Entails.refl _))
        (sepConj_mono (Entails.sepExists_right w3 (Entails.refl _))
          (Entails.sepExists_right w4 (Entails.refl _)))))

end CryptoVerification.E2E.Bin

