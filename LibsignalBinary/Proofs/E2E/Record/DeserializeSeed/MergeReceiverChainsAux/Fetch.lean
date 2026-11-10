/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.Instances
public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
import LibsignalBinary.Proofs.Placed.BridgeReloc

/-!
# Instruction Fetch, Jump Table, and Callee Transfers for Seed `merge_field` Tag `7`

Provides instruction-fetch automation, `.rodata` jump-table lemmas, and cross-block callee transfers
(`message::merge<Chain>` and `RawVec<Chain>::grow_one`) for `SessionStructure::merge_field`
(`0x581c`, block `15`) on tag `7`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

section Fetch

open Lean Meta Elab Command Tactic Arm64 ProofLib ProofLib.ProgramReflection

gen_decodes libsignalSessionCode_tree receiverChainsBin [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 60), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 628) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 700),
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1096) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1196), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1880) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1904), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2472) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 2484)]

elab "mf7_fetches_range " b:term:max H:term:max kStart:num kEnd:num : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let kStart := kStart.getNat
  let kEnd := kEnd.getNat
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let mut k := kStart
  while k <= kEnd do
    let dec := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeSeed
      s!"receiverChainsBin_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    if k == 0 then
      evalTactic (← `(tactic|
        have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
    else
      evalTactic (← `(tactic|
        have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))
    k := k + 4

end Fetch

open Arm64 ProofLib CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchet.Prost
open CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer
open CryptoVerification.E2E.Record

theorem chainMerge_fnAddr_eq_receiverChains (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + bv% (2 ^ 64 + (ls_off% "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (tripleRatchetProgAt b C ctl abs).fnAddr chainMergeName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  have h2 := (ls_lemma% fnOff "prost::encoding::message::merge::<libsignal_protocol::proto::storage::session_structure::Chain, &mut &[u8]> [local#1]")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, mergeFieldName, chainMergeName, h1, h2]
  rw [BitVec.add_assoc]
  rfl

theorem growOneChain_fnAddr_eq_receiverChains (b : BitVec 64) (C : Crypto) (ctl : BitVec 64)
    (abs : String → Option (State → State)) :
    (tripleRatchetProgAt b C ctl abs).fnAddr mergeFieldName + bv% (ls_off% "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one" - ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") =
      (tripleRatchetProgAt b C ctl abs).fnAddr growOneChainName := by
  have h1 := (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  have h2 := (ls_lemma% fnOff "<alloc::raw_vec::RawVec<libsignal_protocol::proto::storage::session_structure::Chain>>::grow_one")
  simp only [tripleRatchetProgAt, Program.fnAddr_rebase, mergeFieldName, growOneChainName, h1, h2]
  rw [BitVec.add_assoc]
  rfl

open ProofLib.ProgramReflection in
/-- The 15-byte jump table of `SessionStructure::merge_field` at rodata `0x4901c` (tags 1..15). -/
def mfJumpTable_receiverChains : List (BitVec 8) :=
  [0x00#8, 0x82#8, 0x77#8, 0x5f#8, 0x19#8, 0x32#8, 0x8d#8, 0x6d#8,
   0xb5#8, 0xd6#8, 0xcb#8, 0x6d#8, 0x0b#8, 0x4c#8, 0x24#8]

open ProofLib.ProgramReflection in
theorem rodata_0x4601c_eq_receiverChains :
    (libsignalSessionImage.data.drop (num% (ls_bytes% "0082775f19328d6db5d6cb6d") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 15 = mfJumpTable_receiverChains := by
  rfl_kernel

open ProofLib.ProgramReflection in
theorem rodata_mfJumpTable_intro_receiverChains {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) ↦ᵣ mfJumpTable_receiverChains) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_bytes% "0082775f19328d6db5d6cb6d")) (secLen := 15) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x4601c_eq_receiverChains] at h

theorem rodata_mfJumpTable_tag7_intro_receiverChains {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 6)) ↦₈ᵣ 0x8d#8) ∗ P := by
  have hm := rodata_mfJumpTable_intro_receiverChains himg hro hP
  have heq : mfJumpTable_receiverChains =
      mfJumpTable_receiverChains.take 6 ++ (0x8d#8 :: mfJumpTable_receiverChains.drop 7) := rfl
  have hlen : (mfJumpTable_receiverChains.take 6).length = 6 := rfl
  have hoff : (img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) + 6#64 = img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 6) := by
    rw [BitVec.add_assoc]; rfl
  have h : ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) ↦ᵣ mfJumpTable_receiverChains) =
      ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) ↦ᵣ mfJumpTable_receiverChains.take 6) ∗
        ((((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) + 6#64) ↦₈ᵣ 0x8d#8) ∗
         (((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d")) + 6#64 + 1#64) ↦ᵣ mfJumpTable_receiverChains.drop 7)) := by
    conv_lhs => rw [heq]
    rw [pointsToBytesRO_append, pointsToBytesRO_cons, hlen]
  rw [h, hoff, sepConj_assoc] at hm
  have hm1 := Satisfies.of_sep_right hm
  let B := ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 6)) ↦₈ᵣ 0x8d#8)
  let S := ((img.base + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 6) + 1#64) ↦ᵣ mfJumpTable_receiverChains.drop 7)
  have hm1' : m ⊨ (B ∗ S) ∗ P := hm1
  have hswap : (B ∗ S) ∗ P = S ∗ (B ∗ P) := by
    rw [sepConj_comm B S, sepConj_assoc]
  rw [hswap] at hm1'
  exact Satisfies.of_sep_right hm1'

/-! ## Relocatable `[LibsignalPlacement]` Callee and `.rodata` Helpers -/

section Placed

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

theorem chainMerge_placed_ok_sub_receiverChains [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h : ChainMergeSeedPlacedOk H) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 11) chainMergeSeedPlacedSpec :=
  ls_call_ro_of_block (callerProg := lsProg_15 H) h

theorem growOneChain_placed_ok_sub_receiverChains [LibsignalPlacement]
    {H : String → Option (State → State)}
    (h : subroutine_ok ((blkPC_43).rebase (blkPl_43).base H) (blkPl_43).base
      (withLsCodeLoaded lsmpl (CryptoVerification.LibsignalSession.growOneSpec A0))) :
    subroutine_ok (lsProg_15 H) (lsmpl.base 43)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl
        (CryptoVerification.LibsignalSession.growOneSpec A0)) :=
  ls_call_ro_of_cl (callerProg := lsProg_15 H) h

theorem rodata_mfJumpTable_placed_intro_receiverChains [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsmpl.ρ mergeFieldRodataSym ↦ᵣ mfJumpTable_receiverChains) ∗ P :=
  lsro_slice_intro hro (by lsro_addr) (by decide +kernel) hP

theorem rodata_mfJumpTable_tag7_placed_intro_receiverChains [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 6#64) ↦₈ᵣ 0x8d#8) ∗ P :=
  lsro8_intro hro (by lsro_addr) (by decide +kernel) hP

end Placed

end CryptoVerification.E2E.Record.DeserializeSeed
