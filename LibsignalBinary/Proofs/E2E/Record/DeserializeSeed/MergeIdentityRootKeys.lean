/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.E2E.Record.DeserializeSeed.Defs
public import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.VarintBridge
import ProofLib.RegChain
import ProofLib.SepLogic.WPp

/-!
# Seed `SessionStructure::merge_field` on Identity and Root Keys (Tags `2`, `3`, `4`)

Proves `mergeFieldSeed234_ok` and `mergeFieldSeed234_placed_ok` for
`<SessionStructure as prost::Message>::merge_field::<&mut &[u8]>` (`0x581c`, block `15`) restricted
to tags `2` (`local_identity_public` at `+0x00`), `3` (`remote_identity_public` at `+0x18`), and
`4` (`root_key` at `+0x30`), dispatching via the `.rodata` byte jump table to `bytes::merge`.
-/

@[expose] public section

namespace CryptoVerification.E2E.Record.DeserializeSeed

open Arm64 ProofLib ProofLib.ProgramReflection CryptoGames CryptoGames.LibsignalSession
open CryptoGames.LibsignalSessionApi CryptoVerification.E2E.Record CryptoVerification.RustHeap
open CryptoVerification.E2E.Record
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.E2E.Record CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E.Record

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt? sessionImg0
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

namespace IdentityRootKeysStateSimp

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) :
    calleeSavedVRegs (s.setPC pc) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem calleeSavedVRegs_setMem_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (m : Memory) :
    calleeSavedVRegs ((s.setPC pc).setMem m) = calleeSavedVRegs s := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) :
    (s.setPC pc).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem sp_setMem_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (m : Memory) :
    ((s.setPC pc).setMem m).sp = s.sp := by cases s; rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg64 r = s.readReg64 r :=
  State.readReg64_setPC s pc r

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg64_setMem_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg64 r = s.readReg64 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (r : Reg) :
    (s.setPC pc).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg32_setMem_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (m : Memory) (r : Reg) :
    ((s.setPC pc).setMem m).readReg32 r = s.readReg32 r := by
  cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (w : RegWidth) (r : Reg) :
    (s.setPC pc).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem readReg_setMem_setPC_pre_identityRootKeys (s : State) (pc : BitVec 64) (m : Memory) (w : RegWidth) (r : Reg) :
    ((s.setPC pc).setMem m).readReg w r = s.readReg w r := by
  cases w <;> cases r <;> rfl

section Fetch

open Lean Meta Elab Command Tactic

gen_decodes libsignalSessionCode_tree mf234 [(ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>") → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 60), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 444) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 460), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 540) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 556),
    (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 584) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 600), (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1880) → (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" + 1904)]

elab "mf234_fetches " b:term:max H:term:max : tactic => do
  let off := num% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  let ranges := [(0, 64), (444, 20), (540, 20), (584, 20), (1880, 28)]
  let fetchEntry := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr_entry
  let fetchAdd := mkIdent `CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let hfn ← `(ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")
  for (start, len) in ranges do
    for i in [0 : len / 4] do
      let k := start + 4 * i
      let dec := mkIdent (.str `CryptoVerification.E2E.Record.DeserializeSeed.IdentityRootKeysStateSimp
        s!"mf234_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
      let kq := Syntax.mkNumLit (toString k)
      if k == 0 then
        evalTactic (← `(tactic|
          have := $fetchEntry (b := $b) (H := $H) $hfn (by decide) $dec))
      else
        evalTactic (← `(tactic|
          have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

end Fetch

/-! ## Entry Address and `adrp` Normalization -/

@[irreducible] def mfEntry_identityRootKeys : BitVec 64 := bv% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")

theorem fnAddr_mergeField_eq_mfEntry_identityRootKeys (H : String → Option (State → State)) :
    (libsignalSessionCode.rebase sessionImg0.base H).fnAddr
      "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>" =
      mfEntry_identityRootKeys := by
  unfold mfEntry_identityRootKeys
  rw [Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")]
  rfl

@[local arm64_norm ↓, local wp_norm ↓]
theorem mfEntry_adrp_identityRootKeys :
    ((mfEntry_identityRootKeys + 40#64) &&& bv% (2 ^ 64 - 4096)) = 20480#64 := by
  unfold mfEntry_identityRootKeys; rfl

theorem bytesMerge_fnAddr_eq_identityRootKeys (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)} :
    mfEntry_identityRootKeys + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")) =
      (tripleRatchetProgAt sessionImg0.base C ctl abs).fnAddr Prost.bytesMergeName := by
  unfold mfEntry_identityRootKeys
  rw [tripleRatchetProgAt, Program.fnAddr_rebase, EntryAux.sessionImg0_base, (ls_lemma% fnOff "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]")]
  rfl

/-! ## Pure Codec and Seed Field Helpers -/

theorem seedSlice_length_le_identityRootKeys (f : List (BitVec 8)) (off n : Nat) :
    (seedSlice f off n).length ≤ n := by
  unfold seedSlice
  exact List.length_take_le n (f.drop off)

theorem pbPubkey_length_le_identityRootKeys (f : List (BitVec 8)) (off : Nat) :
    (pbPubkey (seedSlice f off 32)).length < 128 := by
  unfold pbPubkey
  have h := seedSlice_length_le_identityRootKeys f off 32
  simp only [List.length_cons]
  omega

theorem fld_234_length_lt_128_identityRootKeys {f : List (BitVec 8)} {b : List (BitVec 8)}
    (hmem : SeedField.lik b ∈ seedFields f ∨
      SeedField.rik b ∈ seedFields f ∨
      SeedField.root b ∈ seedFields f) :
    b.length < 128 := by
  unfold seedFields at hmem
  rcases hmem with h | h | h
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (((h | h | h | h) | h) | h) | h
    · cases h
    · injection h with h; subst h; exact pbPubkey_length_le_identityRootKeys f 0
    · cases h
    · cases h
    · split at h <;> simp at h
    · split at h <;> simp at h
    · split at h <;> simp at h
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (((h | h | h | h) | h) | h) | h
    · cases h
    · cases h
    · injection h with h; subst h; exact pbPubkey_length_le_identityRootKeys f 32
    · cases h
    · split at h <;> simp at h
    · split at h <;> simp at h
    · split at h <;> simp at h
  · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with (((h | h | h | h) | h) | h) | h
    · cases h
    · cases h
    · cases h
    · injection h with h; subst h
      have hs := seedSlice_length_le_identityRootKeys f 64 32
      omega
    · split at h <;> simp at h
    · split at h <;> simp at h
    · split at h <;> simp at h

theorem decodeVarint_cons_of_lt_128_identityRootKeys (b0 : BitVec 8) (bs : List (BitVec 8)) (hb0 : b0.toNat < 128) :
    decodeVarint (b0 :: bs) = some ((b0.setWidth 64 &&& 127#64) ||| 0#64, bs) := by
  unfold decodeVarint decodeVarintAux
  have hnot : ¬ 127 < b0.toNat := by omega
  simp [hnot]

theorem mergeBytes_lengthDelimited_of_lt_128_identityRootKeys {b tail : List (BitVec 8)}
    (hb : b.length < 128) :
    mergeBytes .lengthDelimited ([BitVec.ofNat 8 b.length] ++ b ++ tail) = some (b, tail) := by
  have hb0 : (BitVec.ofNat 8 b.length).toNat < 128 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    exact hb
  have hdv : decodeVarint (BitVec.ofNat 8 b.length :: (b ++ tail)) =
       some (BitVec.ofNat 64 b.length, b ++ tail) := by
    rw [decodeVarint_cons_of_lt_128_identityRootKeys _ _ hb0]
    have h64 : ((BitVec.ofNat 8 b.length).setWidth 64 &&& 127#64) ||| 0#64 =
        BitVec.ofNat 64 b.length := by
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
      change (b.length % 256 % 2 ^ 64 &&& 127) ||| 0 = b.length % 2 ^ 64
      rw [Nat.or_zero, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
        Nat.and_two_pow_sub_one_eq_mod b.length 7, Nat.mod_eq_of_lt hb,
        Nat.mod_eq_of_lt (by omega)]
    rw [h64]
  have hlen : (BitVec.ofNat 64 b.length).toNat = b.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  unfold mergeBytes
  simp [hdv, hlen]

/-! ## `.rodata` Jump Table (`0x4901c`, Tags `1..15`) -/

noncomputable abbrev mfJumpTable_identityRootKeys : List (BitVec 8) :=
  (libsignalSessionImage.data.drop (num% (ls_bytes% "0082775f19328d6db5d6cb6d") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 15

theorem rodata_mfJumpTable_intro_identityRootKeys {m : Memory} {P : SepProp}
    (hro : sessionImg0.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((bv% (ls_bytes% "0082775f19328d6db5d6cb6d") : BitVec 64) ↦ᵣ mfJumpTable_identityRootKeys) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads loads_sessionImg0
    (secOff := num% (ls_bytes% "0082775f19328d6db5d6cb6d")) (secLen := 15) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  have hbase : sessionImg0.base + BitVec.ofNat 64 (num% (ls_bytes% "0082775f19328d6db5d6cb6d")) = bv% (ls_bytes% "0082775f19328d6db5d6cb6d") := by
    rw [EntryAux.sessionImg0_base]; rfl
  rwa [hbase] at h

theorem mfJumpTable_split4_identityRootKeys :
    mfJumpTable_identityRootKeys = 0x00#8 :: 0x82#8 :: 0x77#8 :: 0x5f#8 :: mfJumpTable_identityRootKeys.drop 4 := by
  rfl_kernel

def mfRoBytes_identityRootKeys : SepProp :=
  (((mfEntry_identityRootKeys + 40#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 1 - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712))) ↦₈ᵣ 0x82#8) ∗
  (((mfEntry_identityRootKeys + 40#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 2 - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712))) ↦₈ᵣ 0x77#8) ∗
  (((mfEntry_identityRootKeys + 40#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 3 - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712))) ↦₈ᵣ 0x5f#8)

theorem rodata_intro_identityRootKeys {m : Memory} {P : SepProp}
    (hro : sessionImg0.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ mfRoBytes_identityRootKeys ∗ P := by
  have h := rodata_mfJumpTable_intro_identityRootKeys hro hP
  rw [mfJumpTable_split4_identityRootKeys, pointsToBytesRO_cons, pointsToBytesRO_cons,
    pointsToBytesRO_cons, pointsToBytesRO_cons] at h
  have h1 : (mfEntry_identityRootKeys + 40#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 1 - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712)) = bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 1) := by
    unfold mfEntry_identityRootKeys; rfl
  have h2 : (mfEntry_identityRootKeys + 40#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 2 - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712)) = bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 2) := by
    unfold mfEntry_identityRootKeys; rfl
  have h3 : (mfEntry_identityRootKeys + 40#64 &&& bv% (2 ^ 64 - 4096)) + bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 3 - page% (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::encode_raw::<alloc::vec::Vec<u8>>" + 712)) = bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 3) := by
    unfold mfEntry_identityRootKeys; rfl
  have h' : m ⊨ ((bv% (ls_bytes% "0082775f19328d6db5d6cb6d") ↦₈ᵣ 0x00#8) ∗ ((bv% (ls_bytes% "0082775f19328d6db5d6cb6d" + 4) ↦ᵣ mfJumpTable_identityRootKeys.drop 4))) ∗ (mfRoBytes_identityRootKeys ∗ P) := by
    dsimp only [mfRoBytes_identityRootKeys]
    rw [h1, h2, h3]
    convert h using 1; ac_rfl
  exact Satisfies.of_sep_right h'

/-! ## Stack Frame and `prostSSAt` Decomposition -/

def mfSavedRegs_identityRootKeys (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64) : SepProp :=
  ((sp0 - 80#64) ↦₆₄ s0.readReg64 .x29) ∗
  ((sp0 - 72#64) ↦₆₄ s0.readReg64 .x30) ∗
  ((sp0 - 64#64) ↦₆₄ s0.readReg64 .x25) ∗
  ((sp0 - 56#64) ↦₆₄ w56) ∗
  ((sp0 - 48#64) ↦₆₄ s0.readReg64 .x24) ∗
  ((sp0 - 40#64) ↦₆₄ s0.readReg64 .x23) ∗
  ((sp0 - 32#64) ↦₆₄ s0.readReg64 .x22) ∗
  ((sp0 - 24#64) ↦₆₄ s0.readReg64 .x21) ∗
  ((sp0 - 16#64) ↦₆₄ s0.readReg64 .x20) ∗
  ((sp0 - 8#64) ↦₆₄ s0.readReg64 .x19)

def mfUnusedStack_identityRootKeys (sp0 : BitVec 64) : SepProp :=
  memRegion (sp0 - 16384#64) 7648 ∗ memRegion (sp0 - 240#64) 160

theorem stackAt_mergeField_split_identityRootKeys (sp0 : BitVec 64) :
    stackAt sp0 mergeFieldStack =
      mfUnusedStack_identityRootKeys sp0 ∗ stackAt (sp0 - 240#64) Prost.bytesMergeStack ∗
        (∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
         ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
         ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
          ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
          ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
          ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
          ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
          ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
  have h1 := LibsignalTripleRatchet.stackAt_split_cells sp0 16304 10 (by decide)
  change stackAt sp0 mergeFieldStack = stackAt (sp0 - 80#64) 16304 ∗ cells (sp0 - 80#64) 10 at h1
  have h2 : stackAt (sp0 - 80#64) 16304 =
      mfUnusedStack_identityRootKeys sp0 ∗ stackAt (sp0 - 240#64) Prost.bytesMergeStack := by
    unfold stackAt mfUnusedStack_identityRootKeys
    change memRegion (sp0 - 80#64 - 16304#64) 16304 =
      (memRegion (sp0 - 16384#64) 7648 ∗ memRegion (sp0 - 240#64) 160) ∗
        memRegion (sp0 - 240#64 - 8496#64) 8496
    have hsplit1 := memRegion_split (sp0 - 80#64 - 16304#64) 7648 8656 (by decide)
    have hsplit2 := memRegion_split (sp0 - 80#64 - 16304#64 + 7648#64) 8496 160 (by decide)
    have ha1 : sp0 - 80#64 - 16304#64 = sp0 - 16384#64 := by bv_omega
    have ha2 : sp0 - 80#64 - 16304#64 + 7648#64 = sp0 - 240#64 - 8496#64 := by bv_omega
    have ha3 : sp0 - 240#64 - 8496#64 + 8496#64 = sp0 - 240#64 := by bv_omega
    rw [show (16304 : Nat) = 7648 + 8656 by rfl, hsplit1,
      show (8656 : Nat) = 8496 + 160 by rfl, hsplit2, ha2, ha1, ha3]
    ac_rfl
  have hc10 : cells (sp0 - 80#64) 10 =
      (∃∗ w80 : BitVec 64, ∃∗ w72 : BitVec 64, ∃∗ w64 : BitVec 64, ∃∗ w56 : BitVec 64,
       ∃∗ w48 : BitVec 64, ∃∗ w40 : BitVec 64, ∃∗ w32 : BitVec 64, ∃∗ w24 : BitVec 64,
       ∃∗ w16 : BitVec 64, ∃∗ w8 : BitVec 64,
        ((sp0 - 80#64) ↦₆₄ w80) ∗ ((sp0 - 72#64) ↦₆₄ w72) ∗
        ((sp0 - 64#64) ↦₆₄ w64) ∗ ((sp0 - 56#64) ↦₆₄ w56) ∗
        ((sp0 - 48#64) ↦₆₄ w48) ∗ ((sp0 - 40#64) ↦₆₄ w40) ∗
        ((sp0 - 32#64) ↦₆₄ w32) ∗ ((sp0 - 24#64) ↦₆₄ w24) ∗
        ((sp0 - 16#64) ↦₆₄ w16) ∗ ((sp0 - 8#64) ↦₆₄ w8)) := by
    cells_unfold
  rw [h1, h2, hc10, sepConj_assoc]

theorem sp_sub_240_aligned_identityRootKeys {sp0 : BitVec 64} (h : sp0 &&& 15#64 = 0#64) :
    (sp0 - 240#64) &&& 15#64 = 0#64 := by
  have e : ∀ x : BitVec 64, (x &&& 15#64).toNat = x.toNat % 16 := fun x => by
    simp only [BitVec.toNat_and]
    exact Nat.and_two_pow_sub_one_eq_mod x.toNat 4
  have h' := congrArg BitVec.toNat h
  apply BitVec.eq_of_toNat_eq
  rw [e] at h' ⊢
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat] at h' ⊢
  have hlt := sp0.isLt
  omega

def prostSSRest_identityRootKeys (ss : BitVec 64) (v : SSV) : SepProp :=
  vecOf A0 104 8 (fun c a => prostChainAt A0 a c) (ss + 0x48#64) v.recv ∗
    vecU8 A0 (ss + 0x60#64) [] ∗ vecU8 A0 (ss + 0x78#64) [] ∗
    (match v.sender with
     | none => ((ss + 0x90#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x98#64) 96
     | some c => prostChainAt A0 (ss + 0x90#64) c) ∗
    (match v.pending with
     | none => ((ss + 0xf8#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x100#64) 40
     | some k => vecU8 A0 (ss + 0xf8#64) k ∗ ((ss + 0x110#64) ↦₃₂ 0#32) ∗
         memRegion (ss + 0x114#64) 4 ∗ ((ss + 0x118#64) ↦₆₄ 0#64) ∗
         ((ss + 0x120#64) ↦₃₂ 0#32) ∗ memRegion (ss + 0x124#64) 4) ∗
    ((ss + 0x128#64) ↦₆₄ noneCap) ∗ memRegion (ss + 0x130#64) 24 ∗
    ((ss + 0x148#64) ↦₃₂ v.version) ∗ ((ss + 0x14c#64) ↦₃₂ 0#32) ∗ ((ss + 0x150#64) ↦₆₄ 0#64)

theorem prostSSAt_eq_split_identityRootKeys (ss : BitVec 64) (v : SSV) :
    prostSSAt A0 ss v =
      vecU8 A0 ss v.lik ∗ vecU8 A0 (ss + 0x18#64) v.rik ∗ vecU8 A0 (ss + 0x30#64) v.root ∗
        prostSSRest_identityRootKeys ss v := by
  unfold prostSSAt prostSSRest_identityRootKeys
  ac_rfl

theorem of_sepWP_inImage_identityRootKeys {prog : Program} {img : Obj.Image} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h : SepWP prog mid s P
      (fun sm Pm => img.FrozenLoaded sm → sm.symtab = img.symtab →
        SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.of_sepWP_frozen hF hsym h

theorem step_epilogue_758_identityRootKeys (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (w56 : BitVec 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = mfEntry_identityRootKeys + 1880#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 .lr) s P Q Qp := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  mf234_fetches sessionImg0.base H
  change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) (s0.readReg64 .lr) s P Q Qp
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys H] at *
  examples_hide_fetches
  subst hP
  unfold mfSavedRegs_identityRootKeys
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  apply SepWPp.of_sepWP_ret
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

@[local arm64_norm]
theorem setWidth8_setWidth64_setWidth32_identityRootKeys (w : BitVec 64) :
    ((w.setWidth 32).setWidth 64).setWidth 8 = w.setWidth 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  omega

theorem pure_true_emp_identityRootKeys {φ : Prop} (h : φ) : (⌜φ⌝ : SepProp) = emp := by
  simp [h]

theorem stackAt_mergeField_unsplit_identityRootKeys (sp0 : BitVec 64) (s0 : State) (w56 : BitVec 64) :
    mfUnusedStack_identityRootKeys sp0 ∗ stackAt (sp0 - 240#64) Prost.bytesMergeStack ∗
      mfSavedRegs_identityRootKeys sp0 s0 w56 ⊢ stackAt sp0 mergeFieldStack := by
  rw [stackAt_mergeField_split_identityRootKeys sp0]
  refine sepConj_mono_right (sepConj_mono_right ?_)
  unfold mfSavedRegs_identityRootKeys
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x29))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x30))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x25))
  refine Entails.trans ?_ (Entails.sepExists_intro w56)
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x24))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x23))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x22))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x21))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x20))
  refine Entails.trans ?_ (Entails.sepExists_intro (s0.readReg64 .x19))
  exact Entails.refl _

theorem step_cbz_epilogue_identityRootKeys (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (retOff w56 : BitVec 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hret : retOff = 600#64 ∨ retOff = 556#64 ∨ retOff = 460#64)
    (hpc : s.pc = mfEntry_identityRootKeys + retOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 .lr) s P Q Qp := by
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  mf234_fetches sessionImg0.base H
  change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) (s0.readReg64 .lr) s P Q Qp
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys H] at *
  examples_hide_fetches
  apply SepWPp.of_sepWP (mid := mfEntry_identityRootKeys + 1880#64)
  rcases hret with rfl | rfl | rfl
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_identityRootKeys C ctl w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
      hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_identityRootKeys C ctl w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
      hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_identityRootKeys C ctl w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
      hP hnext

theorem finish_post_identityRootKeys (P : SeedField → Prop) (x : MergeFieldGhost)
    (valPtr w56 : BitVec 64) (b : List (BitVec 8))
    {s0 sf : State} {F_ss R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSAt A0 x.ss (x.v.apply x.fld))
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          vecU8 A0 valPtr b ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))) ∗ R) :
    sf.mem ⊨ (mergeFieldSeedSpec P).post x s0 sf ∗ R := by
  have h1 : sf.mem ⊨ mfRoBytes_identityRootKeys ∗
      ((mfUnusedStack_identityRootKeys s0.sp ∗ stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        ((vecU8 A0 valPtr b ∗ F_ss) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          R)) := by
    convert hmf using 1; ac_rfl
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys s0.sp s0 w56)) h2
  rw [hss, ← hpay] at h3
  dsimp only [mergeFieldSeedSpec]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; ac_rfl

theorem step_call_and_ret_identityRootKeys (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (P : SeedField → Prop)
    (hbytes : Prost.BytesMergeOk sessionImg0 C A0 ctl abs)
    (x : MergeFieldGhost) (retOff valPtr w56 : BitVec 64)
    (valBs b : List (BitVec 8))
    {s0 sm : State} {F_ss R : SepProp}
    (hret : retOff = 600#64 ∨ retOff = 556#64 ∨ retOff = 460#64)
    (hpcm : sm.pc = mfEntry_identityRootKeys + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>")))
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hFm : sessionImg0.FrozenLoaded sm)
    (hsymm : sm.symtab = sessionImg0.symtab)
    (htrm : sm.trace = s0.trace)
    (hlrm : sm.readReg64 .lr = mfEntry_identityRootKeys + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 2#8)
    (hx1m : sm.readReg64 .x1 = valPtr)
    (hx2m : sm.readReg64 .x2 = x.bufRef)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hb_lt : b.length < 128)
    (htail_lt : ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 32)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSAt A0 x.ss (x.v.apply x.fld)) :
    SepWPp (tripleRatchetProgAt sessionImg0.base C ctl abs) (s0.readReg64 .lr) sm
      (vecU8 A0 valPtr valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldSeedSpec P).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall : subroutine_ok (tripleRatchetProgAt sessionImg0.base C ctl abs)
      (mfEntry_identityRootKeys + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))) (Prost.bytesMergeSpec A0 sessionImg0) := by
    rw [bytesMerge_fnAddr_eq_identityRootKeys C ctl]
    exact hbytes
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim (fun cap0 => SepWPp.exists_elim (fun ptr0 => ?_))
  let g : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, cap0, ptr0, valBs, x.bufRef, x.slot, x.ptr,
     [BitVec.ofNat 8 b.length] ++ b ++ x.tail⟩
  refine SepWPp.call (x := g)
    (F := mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))
    hcall hpcm hrunm hspm_align hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, A0, g]
    have hp1 : sessionImg0.FrozenLoaded sm ∧ sm.symtab = sessionImg0.symtab := ⟨hFm, hsymm⟩
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
        sm.readReg64 .x1 = valPtr ∧ sm.readReg64 .x2 = x.bufRef ∧
        ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 63 ∧
        Prost.BytesMergeCapOk cap0 ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length :=
      ⟨hx0m, hx1m, hx2m, Nat.lt_of_lt_of_le htail_lt (by decide),
        Prost.bytesMergeCapOk_of_len_lt32 htail_lt⟩
    rw [hspm, pure_true_emp_identityRootKeys hp1, pure_true_emp_identityRootKeys hp2, emp_sepConj, emp_sepConj]
    convert hm using 1; ac_rfl
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, Serialization.allocPanic] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 hcs2
    dsimp only [Prost.bytesMergeSpec, Spec.inImage, Prost.bytesMergeRawSpec, g]
    rw [mergeBytes_lengthDelimited_of_lt_128_identityRootKeys hb_lt]
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_left (fun htr2 => ?_)
    have hpool : A0.pool = emp := rfl
    rw [hpool, hspm]
    simp only [emp_sepConj, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_left (fun hx0_2 => ?_)
    have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜Prost.BytesMergeCapOk cap' x.tail.length⌝ ∗ vecU8At A0 valPtr cap' ptr' b) ⊢
        vecU8 A0 valPtr b :=
      Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' =>
        Entails.pure_left fun _ =>
          Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvec))) ?_
    refine step_cbz_epilogue_identityRootKeys C ctl retOff w56
      (F := (x.bufRef ↦₆₄ x.slot) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        vecU8 A0 valPtr b ∗
        Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_identityRootKeys))
      hret hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2 (by reg_chain) (by reg_chain) (by reg_chain)
      (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_m)
      (by ac_rfl) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_identityRootKeys P x valPtr w56 b htrf hx0f hpay hss, hspf, hcsf⟩

end IdentityRootKeysStateSimp

open IdentityRootKeysStateSimp in
/-- `SessionStructure::merge_field` (`0x581c`) satisfies `mergeFieldSeedSpec` on tags `2`, `3`, and `4`
(`local_identity_public`, `remote_identity_public`, `root_key`) via `bytes::merge`. -/
theorem mergeFieldSeed234_ok (C : Crypto) (ctl : BitVec 64)
    {abs : String → Option (State → State)}
    (hC : DeserializeCallees C ctl abs) :
    MergeFieldSeedOk C ctl
      (fun fl => (∃ b, fl = .lik b) ∨ (∃ b, fl = .rik b) ∨ (∃ b, fl = .root b)) abs := by
  let P234 : SeedField → Prop :=
    fun fl => (∃ b, fl = .lik b) ∨ (∃ b, fl = .rik b) ∨ (∃ b, fl = .root b)
  unfold MergeFieldSeedOk Serialization.OkAt
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  dsimp only [mergeFieldSeedSpec] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨⟨hx0, hx1, hx2, hx3, _, hP, _, hfl, -, -, -, hlen, hF, hsym⟩, hmem⟩
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_identityRootKeys ∗ prostSSAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt s0.sp mergeFieldStack) ∗ R := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact rodata_intro_identityRootKeys hF.roData (by convert hmem using 1; ac_rfl)
  refine ⟨mfRoBytes_identityRootKeys ∗ prostSSAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
    Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s0.sp mergeFieldStack,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys s0.sp, prostSSAt_eq_split_identityRootKeys x.ss x.v]
  unfold mfRoBytes_identityRootKeys
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim (fun w80 => SepWPp.exists_elim (fun w72 =>
    SepWPp.exists_elim (fun w64 => SepWPp.exists_elim (fun w56 =>
      SepWPp.exists_elim (fun w48 => SepWPp.exists_elim (fun w40 =>
        SepWPp.exists_elim (fun w32 => SepWPp.exists_elim (fun w24 =>
          SepWPp.exists_elim (fun w16 => SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  let H := Rust.withPanics (tripleRatchetExterns C ctl abs)
  mf234_fetches sessionImg0.base H
  dsimp only [tripleRatchetProgAt] at hpc
  rw [fnAddr_mergeField_eq_mfEntry_identityRootKeys H] at *
  examples_hide_fetches
  rcases hP with ⟨b, hfl_eq⟩ | ⟨b, hfl_eq⟩ | ⟨b, hfl_eq⟩
  · have hb_lt : b.length < 128 := fld_234_length_lt_128_identityRootKeys (Or.inl (hfl_eq ▸ hfl))
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by rw [hfl_eq]; rfl
    have htag : x.fld.tag = 2 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym (mid := mfEntry_identityRootKeys + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))) ?_
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_identityRootKeys C ctl P234 hC.2.2.1 x 600#64 x.ss w56 x.v.lik b
        (F_ss := vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSRest_identityRootKeys x.ss x.v)
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSAt_eq_split_identityRootKeys]; rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · have hb_lt : b.length < 128 := fld_234_length_lt_128_identityRootKeys (Or.inr (Or.inl (hfl_eq ▸ hfl)))
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by rw [hfl_eq]; rfl
    have htag : x.fld.tag = 3 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym (mid := mfEntry_identityRootKeys + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))) ?_
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_identityRootKeys C ctl P234 hC.2.2.1 x 556#64 (x.ss + 0x18#64) w56 x.v.rik b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inl rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSAt_eq_split_identityRootKeys]; dsimp only [SSV.apply, prostSSRest_identityRootKeys]; ac_rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · have hb_lt : b.length < 128 := fld_234_length_lt_128_identityRootKeys (Or.inr (Or.inr (hfl_eq ▸ hfl)))
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by rw [hfl_eq]; rfl
    have htag : x.fld.tag = 4 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    change SepWPp (libsignalSessionCode.rebase sessionImg0.base H) _ _ _ _ _
    refine of_sepWP_inImage_identityRootKeys hF hsym (mid := mfEntry_identityRootKeys + bv% (2 ^ 64 + (ls_off% "prost::encoding::bytes::merge::<alloc::vec::Vec<u8>, &mut &[u8]> [local#1]") - (ls_off% "<libsignal_protocol::proto::storage::SessionStructure as prost::message::Message>::merge_field::<&mut &[u8]>"))) ?_
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    wp_step; wp_step; wp_step; wp_step; wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hFm hsymm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_identityRootKeys C ctl P234 hC.2.2.1 x 460#64 (x.ss + 0x30#64) w56 x.v.root b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗
          prostSSRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inr rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hFm hsymm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSAt_eq_split_identityRootKeys]; dsimp only [SSV.apply, prostSSRest_identityRootKeys]; ac_rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl

/-! ## Relocatable `[LibsignalPlacement]` Proof (`lsProg_15 H`) -/

namespace IdentityRootKeysStateSimp

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed

def mfRoBytes_placed_identityRootKeys [LibsignalPlacement] : SepProp :=
  ((lsmpl.ρ mergeFieldRodataSym + 1#64) ↦₈ᵣ 0x82#8) ∗
  ((lsmpl.ρ mergeFieldRodataSym + 2#64) ↦₈ᵣ 0x77#8) ∗
  ((lsmpl.ρ mergeFieldRodataSym + 3#64) ↦₈ᵣ 0x5f#8)

theorem rodata_placed_intro_identityRootKeys [LibsignalPlacement] {m : Memory} {P : SepProp}
    (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ mfRoBytes_placed_identityRootKeys ∗ P := by
  have h3 : m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 3#64) ↦₈ᵣ 0x5f#8) ∗ P :=
    lsro8_intro hro (by lsro_addr) (by decide +kernel) hP
  have h2 : m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 2#64) ↦₈ᵣ 0x77#8) ∗
      (((lsmpl.ρ mergeFieldRodataSym + 3#64) ↦₈ᵣ 0x5f#8) ∗ P) :=
    lsro8_intro hro (by lsro_addr) (by decide +kernel) h3
  have h1 : m ⊨ ((lsmpl.ρ mergeFieldRodataSym + 1#64) ↦₈ᵣ 0x82#8) ∗
      (((lsmpl.ρ mergeFieldRodataSym + 2#64) ↦₈ᵣ 0x77#8) ∗
        (((lsmpl.ρ mergeFieldRodataSym + 3#64) ↦₈ᵣ 0x5f#8) ∗ P)) :=
    lsro8_intro hro (by lsro_addr) (by decide +kernel) h2
  unfold mfRoBytes_placed_identityRootKeys
  simpa only [sepConj_assoc] using h1

theorem step_epilogue_758_placed_identityRootKeys [LibsignalPlacement]
    {H : String → Option (State → State)}
    (w56 : BitVec 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hpc : s.pc = (blkPl_15).base + 1880#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s P Q Qp := by
  subst hP
  unfold mfSavedRegs_identityRootKeys
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  apply SepWPp.of_sepWP_ret
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
  exact hnext _ (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    ⟨by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
      by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm]⟩

theorem step_cbz_epilogue_placed_identityRootKeys [LibsignalPlacement]
    {H : String → Option (State → State)}
    (retOff w56 : BitVec 64)
    {s0 s : State} {P F : SepProp} {Q Qp : State → SepProp → Prop}
    (hret : retOff = 600#64 ∨ retOff = 556#64 ∨ retOff = 460#64)
    (hpc : s.pc = (blkPl_15).base + retOff)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (htr : s.trace = s0.trace)
    (hx0 : s.readReg64 .x0 = 0#64)
    (hx26 : s.readReg64 .x26 = s0.readReg64 .x26)
    (hx27 : s.readReg64 .x27 = s0.readReg64 .x27)
    (hx28 : s.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hP : P = mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)
    (hnext : ∀ sf : State,
      sf.pc = s0.readReg64 .lr →
      sf.status = .Running →
      sf.sp = s0.sp →
      sf.trace = s0.trace →
      sf.readReg64 .x0 = 0#64 →
      CalleeSavedPreserved s0 sf →
      Q sf (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ F)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) s P Q Qp := by
  apply SepWPp.of_sepWP (mid := (blkPl_15).base + 1880#64)
  rcases hret with rfl | rfl | rfl
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_placed_identityRootKeys w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
      hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_placed_identityRootKeys w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
      hP hnext
  · wp_step
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    exact step_epilogue_758_placed_identityRootKeys w56
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      halign (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
      (by simp_all [arm64_norm])
      hP hnext

theorem finish_post_placed_identityRootKeys [LibsignalPlacement]
    (P : SeedField → Prop) (x : MergeFieldGhost)
    (valPtr w56 : BitVec 64) (b : List (BitVec 8))
    {s0 sf : State} {F_ss R : SepProp}
    (htrf : sf.trace = s0.trace)
    (hx0f : sf.readReg64 .x0 = 0#64)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSAt A0 x.ss (x.v.apply x.fld))
    (hmf : sf.mem ⊨
      (mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        ((x.bufRef ↦₆₄ x.slot) ∗
          stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          vecU8 A0 valPtr b ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_placed_identityRootKeys))) ∗ R) :
    sf.mem ⊨ (mergeFieldSeedPlacedSpec P).post x s0 sf ∗ R := by
  have h1 : sf.mem ⊨ mfRoBytes_placed_identityRootKeys ∗
      ((mfUnusedStack_identityRootKeys s0.sp ∗ stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
          mfSavedRegs_identityRootKeys s0.sp s0 w56) ∗
        ((vecU8 A0 valPtr b ∗ F_ss) ∗
          (x.bufRef ↦₆₄ x.slot) ∗
          Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
          R)) := by
    convert hmf using 1; ac_rfl
  have h2 := Satisfies.of_sep_right h1
  have h3 := Satisfies.mono (sepConj_mono_left (stackAt_mergeField_unsplit_identityRootKeys s0.sp s0 w56)) h2
  rw [hss, ← hpay] at h3
  dsimp only [mergeFieldSeedPlacedSpec, LibsignalTripleRatchet.withLsCodeRoLoaded, mergeFieldSeedRawSpec]
  rw [pure_true_emp_identityRootKeys ⟨htrf, hx0f⟩, emp_sepConj]
  convert h3 using 1; ac_rfl

theorem step_call_and_ret_placed_identityRootKeys [LibsignalPlacement]
    {H : String → Option (State → State)}
    (P : SeedField → Prop)
    (hbytes : subroutine_ok ((blkPC_7).rebase (blkPl_7).base H) (blkPl_7).base
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpec A0)))
    (x : MergeFieldGhost) (retOff valPtr w56 : BitVec 64)
    (valBs b : List (BitVec 8))
    {s0 sm : State} {F_ss R : SepProp}
    (hret : retOff = 600#64 ∨ retOff = 556#64 ∨ retOff = 460#64)
    (hpcm : sm.pc = lsmpl.base 7)
    (hrunm : sm.status = .Running)
    (hspm : sm.sp = s0.sp - 240#64)
    (halign : s0.sp &&& 15#64 = 0#64)
    (hcrlm : LibsignalCodeRoLoaded lsmpl sm.mem)
    (htrm : sm.trace = s0.trace)
    (hlrm : sm.readReg64 .lr = (blkPl_15).base + retOff)
    (hx0m : (sm.readReg64 .x0).setWidth 8 = 2#8)
    (hx1m : sm.readReg64 .x1 = valPtr)
    (hx2m : sm.readReg64 .x2 = x.bufRef)
    (hx26m : sm.readReg64 .x26 = s0.readReg64 .x26)
    (hx27m : sm.readReg64 .x27 = s0.readReg64 .x27)
    (hx28m : sm.readReg64 .x28 = s0.readReg64 .x28)
    (hvregs_m : calleeSavedVRegs sm = calleeSavedVRegs s0)
    (hb_lt : b.length < 128)
    (htail_lt : ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 32)
    (hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b)
    (hss : vecU8 A0 valPtr b ∗ F_ss = prostSSAt A0 x.ss (x.v.apply x.fld)) :
    SepWPp (lsProg_15 H) (s0.readReg64 .lr) sm
      (vecU8 A0 valPtr valBs ∗
        (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_placed_identityRootKeys))
      (fun sf P_f =>
        ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (mergeFieldSeedPlacedSpec P).post x s0 sf ∗ R)) ∧
          sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf)
      (fun sf P_f => (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ Serialization.allocPanic x s0 sf ∗ R)) := by
  have hcall : subroutine_ok (lsProg_15 H) (lsmpl.base 7)
      (LibsignalTripleRatchet.withLsCodeRoLoaded lsmpl (Prost.bytesMergeRawSpec A0)) :=
    ls_call_ro_of_block (callerProg := lsProg_15 H) hbytes
  have hspm_align : sm.spAligned = true := by
    simp only [State.spAligned, hspm, sp_sub_240_aligned_identityRootKeys halign, beq_self_eq_true]
  unfold vecU8
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim (fun cap0 => SepWPp.exists_elim (fun ptr0 => ?_))
  let g : Prost.BytesMergeGhost :=
    ⟨.lengthDelimited, valPtr, cap0, ptr0, valBs, x.bufRef, x.slot, x.ptr,
     [BitVec.ofNat 8 b.length] ++ b ++ x.tail⟩
  refine SepWPp.call_lscro (x := g)
    (F := mfSavedRegs_identityRootKeys s0.sp s0 w56 ∗ (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_placed_identityRootKeys))
    hcall hpcm hrunm hspm_align hcrlm hlrm ?_ ?_ ?_ ?_
  · intro R' hm
    have hpool : A0.pool = emp := rfl
    dsimp only [Prost.bytesMergeRawSpec, g]
    have hp2 : (sm.readReg64 .x0).setWidth 8 = BitVec.ofNat 8 WireType.lengthDelimited.toNat ∧
        sm.readReg64 .x1 = valPtr ∧ sm.readReg64 .x2 = x.bufRef ∧
        ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length < 2 ^ 63 ∧
        Prost.BytesMergeCapOk cap0 ([BitVec.ofNat 8 b.length] ++ b ++ x.tail).length :=
      ⟨hx0m, hx1m, hx2m, Nat.lt_of_lt_of_le htail_lt (by decide),
        Prost.bytesMergeCapOk_of_len_lt32 htail_lt⟩
    rw [hspm, hpool, pure_true_emp_identityRootKeys hp2]
    simp only [emp_sepConj]
    convert hm using 1; ac_rfl
  · intro sf code R' _ hex
    exact allowPanic_not_exited hex
  · intro sf _ hm
    dsimp only [Prost.bytesMergeRawSpec, Serialization.allocPanic] at hm ⊢
    refine allowPanic_frame (fun ⟨ha, hp⟩ => ?_) hm
    rw [allocFailedIn, htrm] at ha
    rw [htrm] at hp
    exact ⟨ha, hp⟩
  · intro s2 hpc2 hrun2 hsp2 _hcrl2 hcs2
    dsimp only [Prost.bytesMergeRawSpec, g]
    rw [mergeBytes_lengthDelimited_of_lt_128_identityRootKeys hb_lt]
    dsimp only
    rw [sepConj_assoc]
    refine SepWPp.pure_left (fun htr2 => ?_)
    have hpool : A0.pool = emp := rfl
    rw [hpool, hspm]
    simp only [emp_sepConj, sepConj_assoc, sepConj_pure_left_comm]
    refine SepWPp.pure_left (fun hx0_2 => ?_)
    have hvec : (∃∗ cap' : BitVec 64, ∃∗ ptr' : BitVec 64,
        ⌜Prost.BytesMergeCapOk cap' x.tail.length⌝ ∗ vecU8At A0 valPtr cap' ptr' b) ⊢
        vecU8 A0 valPtr b :=
      Entails.sepExists_elim fun cap' => Entails.sepExists_elim fun ptr' =>
        Entails.pure_left fun _ =>
          Entails.sepExists_right cap' (Entails.sepExists_right ptr' (Entails.refl _))
    refine SepWPp.weaken_pre
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hvec))) ?_
    refine step_cbz_epilogue_placed_identityRootKeys retOff w56
      (F := (x.bufRef ↦₆₄ x.slot) ∗
        stackAt (s0.sp - 240#64) Prost.bytesMergeStack ∗
        vecU8 A0 valPtr b ∗
        Prost.sliceCursorAfter x.slot x.ptr ([BitVec.ofNat 8 b.length] ++ b ++ x.tail) x.tail ∗
        (F_ss ∗ mfUnusedStack_identityRootKeys s0.sp ∗ mfRoBytes_placed_identityRootKeys))
      hret hpc2 hrun2
      (hsp2.trans hspm) halign (htr2.trans htrm) hx0_2 (by reg_chain) (by reg_chain) (by reg_chain)
      (hcs2.2.2.2.2.2.2.2.2.2.2.2.trans hvregs_m)
      (by ac_rfl) ?_
    intro sf _ _ hspf htrf hx0f hcsf
    exact ⟨finish_post_placed_identityRootKeys P x valPtr w56 b htrf hx0f hpay hss, hspf, hcsf⟩

end IdentityRootKeysStateSimp

open Arm64.Obj CryptoVerification CryptoVerification.E2E.Record.Placed IdentityRootKeysStateSimp in
/-- Relocatable `[LibsignalPlacement]` proof of `SessionStructure::merge_field` (block `15`,
`lsProg_15 H`) on seed's tag-2/3/4 fields (`local_identity_public`, `remote_identity_public`,
`root_key`). -/
theorem mergeFieldSeed234_placed_ok [LibsignalPlacement]
    {H : String → Option (State → State)}
    (hC : DeserializeCalleesPlaced H) :
    MergeFieldSeedPlacedOk
      (fun fl => (∃ b, fl = .lik b) ∨ (∃ b, fl = .rik b) ∨ (∃ b, fl = .root b)) H := by
  let P234 : SeedField → Prop :=
    fun fl => (∃ b, fl = .lik b) ∨ (∃ b, fl = .rik b) ∨ (∃ b, fl = .root b)
  unfold MergeFieldSeedPlacedOk
  apply subroutine_ok_of_sepWPp
  intro x R s0 hpc hrun hpre hsp_align
  have ⟨hcrl0, hpre_raw⟩ := LibsignalTripleRatchet.extract_withLsCodeRoLoaded hpre
  dsimp only [mergeFieldSeedRawSpec] at hpre_raw
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre_raw
  rcases hpre_raw with ⟨⟨hx0, hx1, hx2, hx3, _, hP, _, hfl, -, -, -, hlen⟩, hmem⟩
  have hmem_ro : s0.mem ⊨
      (mfRoBytes_placed_identityRootKeys ∗ prostSSAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
        Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗
        stackAt s0.sp mergeFieldStack) ∗ R := by
    rw [sepConj_assoc, sepConj_assoc, sepConj_assoc, sepConj_assoc]
    exact rodata_placed_intro_identityRootKeys hcrl0.2 (by convert hmem using 1; ac_rfl)
  refine ⟨mfRoBytes_placed_identityRootKeys ∗ prostSSAt A0 x.ss x.v ∗ (x.bufRef ↦₆₄ x.slot) ∗
    Prost.sliceCursorAt x.slot x.ptr (x.fld.payload ++ x.tail) ∗ stackAt s0.sp mergeFieldStack,
    R, hmem_ro, ?_⟩
  rw [stackAt_mergeField_split_identityRootKeys s0.sp, prostSSAt_eq_split_identityRootKeys x.ss x.v]
  unfold mfRoBytes_placed_identityRootKeys
  simp only [sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim (fun w80 => SepWPp.exists_elim (fun w72 =>
    SepWPp.exists_elim (fun w64 => SepWPp.exists_elim (fun w56 =>
      SepWPp.exists_elim (fun w48 => SepWPp.exists_elim (fun w40 =>
        SepWPp.exists_elim (fun w32 => SepWPp.exists_elim (fun w24 =>
          SepWPp.exists_elim (fun w16 => SepWPp.exists_elim (fun w8 => ?_))))))))))
  have halign : s0.sp &&& 15#64 = 0#64 := by
    simpa [State.spAligned] using hsp_align
  have hsp_align240 := sp_sub_240_aligned_identityRootKeys halign
  rcases hP with ⟨b, hfl_eq⟩ | ⟨b, hfl_eq⟩ | ⟨b, hfl_eq⟩
  · have hb_lt : b.length < 128 := fld_234_length_lt_128_identityRootKeys (Or.inl (hfl_eq ▸ hfl))
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by rw [hfl_eq]; rfl
    have htag : x.fld.tag = 2 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_placed_identityRootKeys P234 hC.2.2.1 x 600#64 x.ss w56 x.v.lik b
        (F_ss := vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSRest_identityRootKeys x.ss x.v)
        (Or.inl rfl)
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSAt_eq_split_identityRootKeys]; rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · have hb_lt : b.length < 128 := fld_234_length_lt_128_identityRootKeys (Or.inr (Or.inl (hfl_eq ▸ hfl)))
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by rw [hfl_eq]; rfl
    have htag : x.fld.tag = 3 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_placed_identityRootKeys P234 hC.2.2.1 x 556#64 (x.ss + 0x18#64) w56 x.v.rik b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x30#64) x.v.root ∗
          prostSSRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inl rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSAt_eq_split_identityRootKeys]; dsimp only [SSV.apply, prostSSRest_identityRootKeys]; ac_rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl
  · have hb_lt : b.length < 128 := fld_234_length_lt_128_identityRootKeys (Or.inr (Or.inr (hfl_eq ▸ hfl)))
    have hpay : x.fld.payload = [BitVec.ofNat 8 b.length] ++ b := by rw [hfl_eq]; rfl
    have htag : x.fld.tag = 4 := by rw [hfl_eq]; rfl
    have hwt : x.fld.wt = .lengthDelimited := by rw [hfl_eq]; rfl
    rw [htag] at hx1
    rw [hwt] at hx2
    rw [hpay] at hlen ⊢
    simp only [arm64_norm] at hx0 hx1 hx2 hx3
    refine LibsignalTripleRatchet.sepWPp_seq_lscro (mid := lsmpl.base 7) hcrl0 ?_
    wp_steps
    apply SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
    intro hcrlm
    refine SepWPp.congr_pre ?_
      (step_call_and_ret_placed_identityRootKeys P234 hC.2.2.1 x 460#64 (x.ss + 0x30#64) w56 x.v.root b
        (F_ss := vecU8 A0 x.ss x.v.lik ∗ vecU8 A0 (x.ss + 0x18#64) x.v.rik ∗
          prostSSRest_identityRootKeys x.ss x.v)
        (Or.inr (Or.inr rfl))
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        halign hcrlm (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) (by simp_all [arm64_norm])
        (by simp_all [arm64_norm])
        hb_lt hlen hpay
        (by rw [hfl_eq, prostSSAt_eq_split_identityRootKeys]; dsimp only [SSV.apply, prostSSRest_identityRootKeys]; ac_rfl))
    unfold mfSavedRegs_identityRootKeys mfRoBytes_placed_identityRootKeys
    simp only [Reg.x29, Reg.x30, Reg.x25, Reg.x24, Reg.x23, Reg.x22, Reg.x21, Reg.x20, Reg.x19]
    ac_rfl

end CryptoVerification.E2E.Record.DeserializeSeed
