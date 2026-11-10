/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.StoreNew.Defs
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
public import LibsignalBinary.Proofs.TripleRatchet.Prog
import GeneratedLean.LibsignalSessionCode -- shake: keep
import ProofLib.SepLogic.WP.Access

/-!
# GOT, `.data.rel.ro`, hook, and memory-splitting lemmas for `StoreNew`

Proves `storeNewRoDataAt_intro` from `Obj.Loads libsignalSessionImage img` and `img.FrozenLoaded`,
together with `ADRP`/`ADD` address resolution, `hashmap_random_keys` hook wrappers, and memory
decompositions for the 24-byte TLS cell, 48-byte `HashMap`, and 120-byte `InMemIdentityKeyStore`.
-/

@[expose] public section

namespace CryptoVerification.E2E.StoreNew

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ObjectLoad.RoDataFactsAux
open CryptoGames.LibsignalSession
open CryptoVerification.RustHeap
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

/-! ## Relocated `.data.rel.ro` word loading (`0x4a658 -> img.base + 0x4a5f0`) -/

theorem dataReloc_apply_length_ge {base : BitVec 64} {d out : List (BitVec 8)}
    {r : Obj.DataReloc} (h : Obj.DataReloc.apply base d r = .ok out) :
    d.length ≤ out.length := by
  unfold Obj.DataReloc.apply at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  simp only [Except.ok.injEq] at h
  subst h
  simp only [List.length_append, List.length_take, List.length_drop, bytesLE_length]
  omega

theorem dataReloc_apply_getElem?_self {base : BitVec 64} {d out : List (BitVec 8)}
    {r : Obj.DataReloc} (h : Obj.DataReloc.apply base d r = .ok out)
    (hlen : r.off ≤ d.length) {j : Nat} (hj : j < r.width) :
    out[r.off + j]? = (Obj.bytesLE r.width (base + BitVec.ofNat 64 r.target))[j]? := by
  unfold Obj.DataReloc.apply at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  simp only [Except.ok.injEq] at h
  subst h
  have htk : (d.take r.off).length = r.off := by
    simp only [List.length_take]; omega
  have hbw : (Obj.bytesLE r.width (base + BitVec.ofNat 64 r.target)).length = r.width :=
    bytesLE_length _ _
  rw [List.append_assoc, List.getElem?_append_right (by omega), htk,
    Nat.add_sub_cancel_left, List.getElem?_append_left (by omega)]

theorem foldlM_dataReloc_preserve_reloc {base : BitVec 64} {off target : Nat} :
    ∀ (rs : List Obj.DataReloc) (d out : List (BitVec 8)),
      rs.foldlM (Obj.DataReloc.apply base) d = .ok out →
      off ≤ d.length →
      rs.all (fun r => decide ((r.off = off ∧ r.width = 8 ∧ r.target = target) ∨
        r.off + r.width ≤ off ∨ off + 8 ≤ r.off)) = true →
      ∀ {j : Nat}, j < 8 →
        d[off + j]? = (Obj.bytesLE 8 (base + BitVec.ofNat 64 target))[j]? →
        out[off + j]? = (Obj.bytesLE 8 (base + BitVec.ofNat 64 target))[j]?
  | [], d, out, h, _, _, _, _, hd => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hd
  | r :: rs, d, out, h, hlen, hrs, j, hj, hd => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hrs
    cases hr : Obj.DataReloc.apply base d r with
    | error _ => rw [hr] at h; cases h
    | ok d' =>
      rw [hr] at h
      have hlen' : off ≤ d'.length := Nat.le_trans hlen (dataReloc_apply_length_ge hr)
      have hd' : d'[off + j]? = (Obj.bytesLE 8 (base + BitVec.ofNat 64 target))[j]? := by
        rcases hrs.1 with ⟨rfl, hw, rfl⟩ | hdisj
        · have hs := dataReloc_apply_getElem?_self hr hlen (by omega : j < r.width)
          rwa [hw] at hs
        · obtain ⟨x, hx⟩ : ∃ x, (Obj.bytesLE 8 (base + BitVec.ofNat 64 target))[j]? = some x :=
            ⟨_, List.getElem?_eq_getElem (by rw [bytesLE_length]; exact hj)⟩
          rw [hx] at hd ⊢
          exact dataReloc_apply_getElem?_of_disjoint hr (by omega) hd
      exact foldlM_dataReloc_preserve_reloc rs d' out h hlen' hrs.2 hj hd'

theorem foldlM_dataReloc_getElem?_reloc {base : BitVec 64} {off target : Nat} :
    ∀ (rs : List Obj.DataReloc) (d out : List (BitVec 8)),
      rs.foldlM (Obj.DataReloc.apply base) d = .ok out →
      off ≤ d.length →
      rs.any (fun r => decide (r.off = off ∧ r.width = 8 ∧ r.target = target)) = true →
      rs.all (fun r => decide ((r.off = off ∧ r.width = 8 ∧ r.target = target) ∨
        r.off + r.width ≤ off ∨ off + 8 ≤ r.off)) = true →
      ∀ {j : Nat}, j < 8 →
        out[off + j]? = (Obj.bytesLE 8 (base + BitVec.ofNat 64 target))[j]?
  | [], _, _, _, _, hany, _, _, _ => by simp at hany
  | r :: rs, d, out, h, hlen, hany, hrs, j, hj => by
    simp only [List.foldlM_cons, bind, Except.bind] at h
    simp only [List.any_cons, Bool.or_eq_true, decide_eq_true_eq] at hany
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hrs
    cases hr : Obj.DataReloc.apply base d r with
    | error _ => rw [hr] at h; cases h
    | ok d' =>
      rw [hr] at h
      have hlen' : off ≤ d'.length := Nat.le_trans hlen (dataReloc_apply_length_ge hr)
      by_cases hm : r.off = off ∧ r.width = 8 ∧ r.target = target
      · rcases hm with ⟨rfl, hw, rfl⟩
        have hd' := dataReloc_apply_getElem?_self hr hlen (by omega : j < r.width)
        rw [hw] at hd'
        exact foldlM_dataReloc_preserve_reloc rs d' out h hlen' hrs.2 hj hd'
      · have hany' : rs.any (fun r => decide (r.off = off ∧ r.width = 8 ∧ r.target = target)) = true :=
          hany.resolve_left hm
        exact foldlM_dataReloc_getElem?_reloc rs d' out h hlen' hany' hrs.2 hj

theorem loads_reloc_word_holdsBytes {li : Obj.LinkedImage} {img : Obj.Image} {s : State}
    (himg : Obj.Loads li img) (hF : img.FrozenLoaded s) {secOff target : Nat}
    (hsec : (secOff, 32) ∈ li.roData)
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
  intro j hj
  have hj8 : j < 8 := by rw [bytesLE_length] at hj; exact hj
  have hlen_app : secOff - li.dataOff ≤ (li.data ++ List.replicate li.bss 0).length := by
    rw [List.length_append]; omega
  have hout := foldlM_dataReloc_getElem?_reloc li.relocs _ data hfold hlen_app hany hall hj8
  rw [← hdata_eq, List.getElem?_eq_getElem hj] at hout
  have hi : secOff - li.dataOff + j < img.data.length := (List.getElem?_eq_some_iff.mp hout).1
  have hget : img.data[secOff - li.dataOff + j] =
      (Obj.bytesLE 8 (img.base + BitVec.ofNat 64 target))[j] :=
    Option.some.inj ((List.getElem?_eq_getElem hi).symm.trans hout)
  have ha_eq : img.dataAddr + BitVec.ofNat 64 (secOff - li.dataOff + j) =
      img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 j := by
    rw [hda, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add]
    congr 2; omega
  have hisRo : img.isRoData (img.dataAddr + BitVec.ofNat 64 (secOff - li.dataOff + j)) = true := by
    simp only [Obj.Image.isRoData, hro_map, List.any_map, List.any_eq_true]
    refine ⟨(secOff, 32), hsec, ?_⟩
    simp only [Function.comp_apply, decide_eq_true_eq, ha_eq]
    have e : img.base + BitVec.ofNat 64 secOff + BitVec.ofNat 64 j -
        (img.base + BitVec.ofNat 64 secOff) = BitVec.ofNat 64 j := by bv_lin
    rw [e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  obtain ⟨hread, hperm'⟩ := hF.roData (secOff - li.dataOff + j) hi hisRo
  rw [← ha_eq, hread, hget]
  exact ⟨rfl, hperm'⟩

/-! ## `libsignalSessionImage` GOT and `.data.rel.ro` facts -/

section ConcreteImageFacts
open ProofLib.ProgramReflection
set_option maxRecDepth 2000000

theorem sessionImage_gotOff_eq : libsignalSessionImage.gotOff = num% (ls_field% gotOff) := by rfl_kernel

theorem sessionImage_got_eq : libsignalSessionImage.got = [Obj.GotEntry.tpoff 16] := by rfl_kernel

theorem sessionImage_roData_0x4a658 : (num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")), 32) ∈ libsignalSessionImage.roData :=
  List.mem_of_elem_eq_true (by rfl_kernel)

theorem sessionImage_reloc_0x4a658_any :
    libsignalSessionImage.relocs.any (fun r =>
      decide (r.off = num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) - libsignalSessionImage.dataOff ∧ r.width = 8 ∧ r.target = num% (ls_bytes% "ffffffffffffffff67726f75705f6964"))) = true := by
  rfl_kernel

theorem sessionImage_reloc_0x4a658_all :
    libsignalSessionImage.relocs.all (fun r =>
      decide ((r.off = num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) - libsignalSessionImage.dataOff ∧ r.width = 8 ∧ r.target = num% (ls_bytes% "ffffffffffffffff67726f75705f6964")) ∨
        r.off + r.width ≤ num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) - libsignalSessionImage.dataOff ∨
        num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) - libsignalSessionImage.dataOff + 8 ≤ r.off)) = true := by
  rfl_kernel

theorem sessionImage_0x4a660_hk :
    (num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964") + 8) - libsignalSessionImage.dataOff) + 24 ≤ libsignalSessionImage.data.length :=
  Nat.le_of_ble_eq_true (by rfl_kernel)

theorem sessionImage_0x4a660_noReloc :
    noRelocInRange libsignalSessionImage.relocs
      (libsignalSessionImage.data.length + libsignalSessionImage.bss)
      (num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964") + 8) - libsignalSessionImage.dataOff) 24 = true := by
  rfl_kernel

theorem sessionImage_0x4a660_inRo :
    inLiRoData libsignalSessionImage (num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964") + 8)) 24 = true := by
  rfl_kernel

theorem sessionImage_0x4a660_bytes :
    (libsignalSessionImage.data.drop (num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964") + 8) - libsignalSessionImage.dataOff)).take 24 =
      List.replicate 24 0#8 := by
  rfl_kernel

end ConcreteImageFacts

theorem bytesLE_8_eq_unpack64 (v : BitVec 64) : Obj.bytesLE 8 v = unpack64 v := rfl

theorem pointsToBytesRO_bytesLE8_eq (a v : BitVec 64) :
    (a ↦ᵣ Obj.bytesLE 8 v) = (a ↦₆₄ᵣ v) := by
  rw [bytesLE_8_eq_unpack64, ← pointsTo64RO_eq_pointsToBytesRO]

theorem pointsToBytesRO_zeros24_eq (b : BitVec 64) :
    ((b + (emptyRawTableOff + 8#64)) ↦ᵣ List.replicate 24 0#8) =
      ((b + (emptyRawTableOff + 8#64)) ↦₆₄ᵣ 0#64) ∗
      ((b + (emptyRawTableOff + 16#64)) ↦₆₄ᵣ 0#64) ∗
      ((b + (emptyRawTableOff + 24#64)) ↦₆₄ᵣ 0#64) := by
  have hrep : List.replicate 24 (0#8 : BitVec 8) =
      Obj.bytesLE 8 0#64 ++ (Obj.bytesLE 8 0#64 ++ Obj.bytesLE 8 0#64) := rfl
  rw [hrep, pointsToBytesRO_append, pointsToBytesRO_append]
  have hlen : BitVec.ofNat 64 (Obj.bytesLE 8 0#64).length = 8#64 := rfl
  rw [hlen, pointsToBytesRO_bytesLE8_eq, pointsToBytesRO_bytesLE8_eq, pointsToBytesRO_bytesLE8_eq]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem got_tpoff_holdsBytes {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    Obj.HoldsBytes s.mem (img.base + tlsKeysGotOff) (Obj.bytesLE 8 tlsKeysTpoff) (fun _ => .ro) := by
  have hgot := hF.got
  obtain ⟨_, _, _, _, _, himg_eq⟩ := load_eq_ok himg
  have hga : img.gotAddr = img.base + tlsKeysGotOff := by
    rw [congrArg Obj.Image.gotAddr himg_eq, sessionImage_gotOff_eq]
  have hgb : img.gotBytes = Obj.bytesLE 8 tlsKeysTpoff := by
    unfold Obj.Image.gotBytes
    rw [congrArg Obj.Image.got himg_eq, sessionImage_got_eq]; rfl
  rwa [hga, hgb] at hgot

theorem emptyRawTable_zeros_holdsBytes {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    Obj.HoldsBytes s.mem (img.base + (emptyRawTableOff + 8#64)) (List.replicate 24 0#8) (fun _ => .ro) :=
  loads_rodata_holdsBytes himg hF
    (off := num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964") + 8)) (n := 24) (bs := List.replicate 24 0#8)
    (by decide) sessionImage_0x4a660_hk sessionImage_0x4a660_noReloc
    sessionImage_0x4a660_inRo rfl sessionImage_0x4a660_bytes

theorem emptyRawTable_ctrl_holdsBytes {img : Obj.Image} {s : State}
    (himg : Obj.Loads libsignalSessionImage img) (hF : img.FrozenLoaded s) :
    Obj.HoldsBytes s.mem (img.base + emptyRawTableOff)
      (Obj.bytesLE 8 (img.base + emptyCtrlOff)) (fun _ => .ro) :=
  loads_reloc_word_holdsBytes himg hF
    (secOff := num% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964"))) (target := num% (ls_bytes% "ffffffffffffffff67726f75705f6964"))
    sessionImage_roData_0x4a658 (by decide)
    (by have := sessionImage_0x4a660_hk; omega)
    sessionImage_reloc_0x4a658_any sessionImage_reloc_0x4a658_all

theorem bytesLE8_length_le (w : BitVec 64) : (Obj.bytesLE 8 w).length ≤ 2 ^ 64 := by
  change 8 ≤ 2 ^ 64
  decide

/-- Introduce `storeNewRoDataAt img.base tlsKeysTpoff (img.base + emptyCtrlOff)` into any spatial state
from `Obj.Loads libsignalSessionImage img` and `img.FrozenLoaded s`. -/
theorem storeNewRoDataAt_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {s : State} {P : SepProp} (hF : img.FrozenLoaded s) (hP : s.mem ⊨ P) :
    s.mem ⊨ storeNewRoDataAt img.base tlsKeysTpoff (img.base + emptyCtrlOff) ∗ P := by
  have h1 := Satisfies.of_holdsBytes_ro (emptyRawTable_zeros_holdsBytes himg hF) (by decide) hP
  rw [pointsToBytesRO_zeros24_eq] at h1
  have h2 := Satisfies.of_holdsBytes_ro (emptyRawTable_ctrl_holdsBytes himg hF)
    (bytesLE8_length_le _) h1
  rw [pointsToBytesRO_bytesLE8_eq] at h2
  have h3 := Satisfies.of_holdsBytes_ro (got_tpoff_holdsBytes himg hF) (by decide) h2
  rw [pointsToBytesRO_bytesLE8_eq] at h3
  simpa only [storeNewRoDataAt, sepConj_assoc] using h3

/-! ## `ADRP` / `ADD` address lemmas and `randomKeys` hook wrappers -/

theorem adrp_got_session_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") = entry) :
    ((entry + bv% (12) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_field% gotOff) - page% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_receiver_chain" + 872))) + bv% ((ls_field% gotOff) % 4096) =
      b + tlsKeysGotOff := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem adrp_ro_session_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new") = entry) :
    ((entry + bv% (44) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) - page% (ls_off% "<libsignal_protocol::state::session::SessionState>::with_receiver_chain" + 872))) + bv% ((ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) % 4096) =
      b + emptyRawTableOff := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem adrp_got_identity_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") = entry) :
    ((entry + bv% (16) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_field% gotOff) - page% (ls_off% "<libsignal_protocol::sealed_sender::sealed_sender_v1::EphemeralKeys>::calculate" + 532))) + bv% ((ls_field% gotOff) % 4096) =
      b + tlsKeysGotOff := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc, BitVec.add_assoc]
  rfl

theorem adrp_ro_identity_eq (b entry : BitVec 64)
    (halign : b &&& 0xfff#64 = 0#64) (hentry : b + bv% (ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new") = entry) :
    ((entry + bv% (60) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) - page% (ls_off% "<libsignal_protocol::sealed_sender::sealed_sender_v1::EphemeralKeys>::calculate" + 532))) + bv% ((ls_reloc% (ls_bytes% "ffffffffffffffff67726f75705f6964")) % 4096) =
      b + emptyRawTableOff := by
  subst hentry
  rw [BitVec.add_assoc b, adrp_page_of_aligned halign, BitVec.add_assoc, BitVec.add_assoc]
  rfl

open ProofLib.ProgramReflection in
theorem tripleRatchetExterns_randomKeys (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    Rust.withPanics (tripleRatchetExterns C ctl abs) randomKeysName = abs randomKeysName := by
  rfl_kernel

theorem randomKeys_ok_at_session {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (b : BitVec 64) (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr inMemSignedPreKeyStoreNewName + bv% (ls_off% "std::sys::random::linux::hashmap_random_keys" - ls_off% "<libsignal_protocol::storage::inmem::InMemSignedPreKeyStore>::new"))
      randomKeysSpec := by
  refine hook_ok_at_raw (hname := randomKeysName)
    (stub := num% (ls_off% "std::sys::random::linux::hashmap_random_keys")) inMemSignedPreKeyStoreNew_fnOff (by decide) (by decide)
    (ls_hook% "std::sys::random::linux::hashmap_random_keys") ?_
  simpa [HookSat, tripleRatchetExterns_randomKeys] using hRk

theorem randomKeys_ok_at_identity {C : Crypto}
    {ctl : BitVec 64} {abs : String → Option (State → State)}
    (b : BitVec 64) (hRk : HookSat abs randomKeysName randomKeysSpec) :
    subroutine_ok (tripleRatchetProgAt b C ctl abs)
      ((tripleRatchetProgAt b C ctl abs).fnAddr inMemIdentityKeyStoreNewName + bv% (ls_off% "std::sys::random::linux::hashmap_random_keys" - ls_off% "<libsignal_protocol::storage::inmem::InMemIdentityKeyStore>::new"))
      randomKeysSpec := by
  refine hook_ok_at_raw (hname := randomKeysName)
    (stub := num% (ls_off% "std::sys::random::linux::hashmap_random_keys")) inMemIdentityKeyStoreNew_fnOff (by decide) (by decide)
    (ls_hook% "std::sys::random::linux::hashmap_random_keys") ?_
  simpa [HookSat, tripleRatchetExterns_randomKeys] using hRk

/-! ## Memory-region and byte-slice splitting lemmas -/

theorem memRegion_eight (a : BitVec 64) : memRegion a 8 = ∃∗ v : BitVec 64, a ↦₆₄ v :=
  IsBlock.eq (IsBlock.memRegion a 8)
    (IsBlock.sepExists fun v => IsBlock.pointsTo64 a v)
    fun _ => ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩

theorem memRegion_48_eq_cells (out : BitVec 64) : memRegion out 48 = cells out 6 :=
  memRegion_cells out 6 (by decide)

theorem memRegion_120_split (out : BitVec 64) :
    memRegion out 120 =
      cells out 14 ∗ (∃∗ v : BitVec 32, (out + 112#64) ↦₃₂ v) ∗ memRegion (out + 116#64) 4 := by
  rw [show (120 : Nat) = 112 + (4 + 4) from rfl,
    memRegion_split out 112 8 (by decide),
    memRegion_cells out 14 (by decide),
    memRegion_split (out + 112#64) 4 4 (by decide),
    memRegion_four (out + 112#64)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem stackAt_32_eq_cells (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewFrame = cells (sp - 32#64) 4 := by
  simp only [stackAt, inMemSessionStoreNewFrame]
  exact memRegion_cells (sp - 32#64) 4 (by decide)

theorem stackAt_48_eq_cells (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewFrame = cells (sp - 48#64) 6 := by
  simp only [stackAt, inMemIdentityStoreNewFrame]
  exact memRegion_cells (sp - 48#64) 6 (by decide)

theorem stackAt_sessionStoreNew_split (sp : BitVec 64) :
    stackAt sp inMemSessionStoreNewStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show inMemSessionStoreNewStack = extHookStack + 8 * 4 by decide]
  exact stackAt_split_cells sp extHookStack 4 (by decide)

theorem stackAt_identityStoreNew_split (sp : BitVec 64) :
    stackAt sp inMemIdentityStoreNewStack =
      stackAt (sp - 48#64) extHookStack ∗ cells (sp - 48#64) 6 := by
  rw [show inMemIdentityStoreNewStack = extHookStack + 8 * 6 by decide]
  exact stackAt_split_cells sp extHookStack 6 (by decide)

/-- The `i`-th 64-bit little-endian word of a byte list `bs`. -/
def word64At (bs : List (BitVec 8)) (i : Nat) : BitVec 64 :=
  pack64 (bs.getD (8 * i + 0) 0#8) (bs.getD (8 * i + 1) 0#8)
    (bs.getD (8 * i + 2) 0#8) (bs.getD (8 * i + 3) 0#8)
    (bs.getD (8 * i + 4) 0#8) (bs.getD (8 * i + 5) 0#8)
    (bs.getD (8 * i + 6) 0#8) (bs.getD (8 * i + 7) 0#8)

theorem pointsToBytes_drop_split (a : BitVec 64) (bs : List (BitVec 8)) (off n : Nat)
    (h : off + n ≤ bs.length) :
    (a ↦ₛ bs.drop off) =
      (a ↦ₛ (bs.drop off).take n) ∗
        ((a + BitVec.ofNat 64 n) ↦ₛ bs.drop (off + n)) := by
  have hlen : ((bs.drop off).take n).length = n := by
    simp only [List.length_take, List.length_drop]; omega
  conv => lhs; rw [← List.take_append_drop n (bs.drop off), List.drop_drop]
  rw [pointsToBytes_append, hlen]

/-- Any 64-byte slice `a ↦ₛ bs` (`bs.length = 64`) decomposes into 8 consecutive 64-bit words. -/
theorem pointsToBytes_64_eq_words (a : BitVec 64) {bs : List (BitVec 8)} (h : bs.length = 64) :
    (a ↦ₛ bs) =
      (a ↦₆₄ word64At bs 0) ∗
      ((a + 8#64) ↦₆₄ word64At bs 1) ∗
      ((a + 16#64) ↦₆₄ word64At bs 2) ∗
      ((a + 24#64) ↦₆₄ word64At bs 3) ∗
      ((a + 32#64) ↦₆₄ word64At bs 4) ∗
      ((a + 40#64) ↦₆₄ word64At bs 5) ∗
      ((a + 48#64) ↦₆₄ word64At bs 6) ∗
      ((a + 56#64) ↦₆₄ word64At bs 7) := by
  change (a ↦ₛ bs.drop 0) = _
  rw [pointsToBytes_drop_split a bs 0 8 (by omega),
      pointsToBytes_drop_split _ bs 8 8 (by omega),
      pointsToBytes_drop_split _ bs 16 8 (by omega),
      pointsToBytes_drop_split _ bs 24 8 (by omega),
      pointsToBytes_drop_split _ bs 32 8 (by omega),
      pointsToBytes_drop_split _ bs 40 8 (by omega),
      pointsToBytes_drop_split _ bs 48 8 (by omega),
      pointsToBytes_drop_split _ bs 56 8 (by omega)]
  have hdrop64 : bs.drop 64 = [] := by simp [h]
  rw [hdrop64, pointsToBytes_nil, sepConj_emp,
      pointsToBytes_take8_eq_pointsTo64 _ bs 0 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 8 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 16 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 24 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 32 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 40 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 48 (by omega),
      pointsToBytes_take8_eq_pointsTo64 _ bs 56 (by omega)]
  change _ = _
  simp only [word64At, Nat.mul_zero, Nat.zero_add, Nat.reduceMul, Nat.reduceAdd,
    BitVec.add_assoc, BitVec.reduceAdd]

/-- A zeroed 24-byte TLS block `(t ↦₆₄ 0#64) ∗ ((t + 8#64) ↦₆₄ 0#64) ∗ ((t + 16#64) ↦₆₄ 0#64)`
entails `tlsKeysRawAt t 0#64 0#64 0#8` (and hence `tlsKeysUninitAt t`). -/
theorem zeroWords_entails_tlsKeysRawAt (t : BitVec 64) :
    ((t ↦₆₄ 0#64) ∗ ((t + 8#64) ↦₆₄ 0#64) ∗ ((t + 16#64) ↦₆₄ 0#64)) ⊢
      tlsKeysRawAt t 0#64 0#64 0#8 := by
  unfold tlsKeysRawAt
  refine sepConj_mono_right (sepConj_mono_right ?_)
  rw [pointsTo64_eq_pointsToBytes (t + 16#64) 0#64]
  have hu : unpack64 0#64 = 0#8 :: List.replicate 7 0#8 := rfl
  rw [hu, pointsToBytes_cons]
  have ha : t + 16#64 + 1#64 = t + 17#64 := by bv_arith
  rw [ha]
  exact sepConj_mono_right (pointsToBytes_entails_memRegion (t + 17#64) (List.replicate 7 0#8))

end CryptoVerification.E2E.StoreNew
