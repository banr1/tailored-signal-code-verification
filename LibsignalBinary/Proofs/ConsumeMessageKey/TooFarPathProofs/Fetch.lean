/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import all Init.Data.String.Defs
import LibsignalBinary.Proofs.Placed.BridgeReloc

@[expose] public section

namespace CryptoVerification.LibsignalSession.TooFarPath

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

theorem rodata_0x41b58_eq :
    (libsignalSessionImage.data.drop (num% (ls_str% "message from too far into the future") - num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))).take 36 = tooFarInFutureStr := by
  rfl_kernel

theorem adrp_logFilter {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    (((b + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") + 388#64) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      b + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  bv_arith

theorem adrp_tooFarStr {b : BitVec 64} (hb : b &&& 0xfff#64 = 0#64) :
    (((b + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") + 564#64) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_str% "message from too far into the future") - page% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 296))) + bv% ((ls_str% "message from too far into the future") % 4096) =
      b + bv% (ls_str% "message from too far into the future") := by
  bv_arith

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 368) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 400)]

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 540) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 624)]

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1916) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 1944)]

gen_decodes libsignalSessionCode_tree libsignalSessionBin [(ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 2548) → (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key" + 2556)]

open Lean Elab Tactic in
/-- Introduce instruction-fetch hypotheses for byte offsets `kstart, kstart + 4, ..., kstart + len - 4`. -/
elab "tooFarPath_fetches_range " b:term:max H:term:max hfn:term:max off:term:max kstart:num len:num : tactic => do
  let off ← CryptoVerification.CodeLayout.evalNat off "fetches"
  let kstart := kstart.getNat
  let len := len.getNat
  let fetchAdd := mkIdent `_root_.CryptoVerification.libsignalSessionCode_fetch_fnAddr
  let decPrefix : Lean.Name := `CryptoVerification.LibsignalSession.TooFarPath.libsignalSessionBin
  for i in [0:len / 4] do
    let k := kstart + 4 * i
    let dec := mkIdent (decPrefix.appendAfter
      s!"_decode_0x{String.ofList (Nat.toDigits 16 (off + k))}")
    let kq := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic|
      have := $fetchAdd (b := $b) (H := $H) (k := $kq) $hfn (by decide) $dec))

theorem pointsToBytes_tooFarInFutureStr (p : BitVec 64) :
    (p ↦ₛ tooFarInFutureStr) =
      (p ↦₆₄ 0x206567617373656d#64) ∗
      ((p + 8#64) ↦₆₄ 0x6f6f74206d6f7266#64) ∗
      ((p + 16#64) ↦₆₄ 0x746e692072616620#64) ∗
      ((p + 24#64) ↦₆₄ 0x756620656874206f#64) ∗
      ((p + 32#64) ↦₃₂ 0x65727574#32) := by
  have heq : tooFarInFutureStr =
      unpack64 0x206567617373656d#64 ++
      (unpack64 0x6f6f74206d6f7266#64 ++
      (unpack64 0x746e692072616620#64 ++
      (unpack64 0x756620656874206f#64 ++
       unpack32 0x65727574#32))) := by rfl_kernel
  rw [heq, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append, pointsToBytes_append,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo64_eq_pointsToBytes, ← pointsTo64_eq_pointsToBytes,
    ← pointsTo32_eq_pointsToBytes]
  simp only [unpack64_length]
  have h16 : p + 8#64 + 8#64 = p + 16#64 := by bv_arith
  have h24 : p + 16#64 + 8#64 = p + 24#64 := by bv_arith
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_arith
  rw [h16, h24, h32]

theorem pointsToBytesRO_tooFarInFutureStr (p : BitVec 64) :
    (p ↦ᵣ tooFarInFutureStr) =
      (p ↦₆₄ᵣ 0x206567617373656d#64) ∗
      ((p + 8#64) ↦₆₄ᵣ 0x6f6f74206d6f7266#64) ∗
      ((p + 16#64) ↦₆₄ᵣ 0x746e692072616620#64) ∗
      ((p + 24#64) ↦₆₄ᵣ 0x756620656874206f#64) ∗
      ((p + 32#64) ↦₃₂ᵣ 0x65727574#32) := by
  have heq : tooFarInFutureStr =
      unpack64 0x206567617373656d#64 ++
      (unpack64 0x6f6f74206d6f7266#64 ++
      (unpack64 0x746e692072616620#64 ++
      (unpack64 0x756620656874206f#64 ++
       unpack32 0x65727574#32))) := by rfl_kernel
  rw [heq, pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append, pointsToBytesRO_append,
    ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
    ← pointsTo64RO_eq_pointsToBytesRO, ← pointsTo64RO_eq_pointsToBytesRO,
    ← pointsTo32RO_eq_pointsToBytesRO]
  simp only [unpack64_length]
  have h16 : p + 8#64 + 8#64 = p + 16#64 := by bv_arith
  have h24 : p + 16#64 + 8#64 = p + 24#64 := by bv_arith
  have h32 : p + 24#64 + 8#64 = p + 32#64 := by bv_arith
  rw [h16, h24, h32]

theorem rodata_tooFarInFuture_intro {img : Obj.Image} (himg : Obj.Loads libsignalSessionImage img)
    {m : Memory} {P : SepProp} (hro : img.RoDataLoaded m) (hP : m ⊨ P) :
    m ⊨ ((img.base + bv% (ls_str% "message from too far into the future")) ↦ᵣ tooFarInFutureStr) ∗ P := by
  have h := ProofLib.Satisfies.of_rodata_loads himg
    (secOff := num% (ls_str% "message from too far into the future")) (secLen := 36) (dataOff := num% (ls_xref% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 40) (ls_off% "core::ptr::drop_glue::<libsignal_protocol::error::SignalProtocolError> [local#1]" + 44)))
    rfl (List.mem_of_elem_eq_true (by rfl_kernel)) (by decide) (by decide)
    (Nat.le_of_ble_eq_true (by rfl_kernel)) (by rfl_kernel) hro hP
  rwa [rodata_0x41b58_eq] at h

theorem ratchetAt_expose_maxForwardJumps (A : RustAlloc) (self : BitVec 64)
    (G : RatchetGhost) (st : RatchetState) :
    ratchetAt A self G st =
      ⌜G.chains.length = st.receiverChains.length ∧ G.senderPad.length = 100 ∧
        st.maxForwardJumps < 2 ^ 64⌝ ∗
      ((self + 160#64) ↦₆₄ BitVec.ofNat 64 st.maxForwardJumps) ∗
      (vecAt A 104 8 (chainAt A) self G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
       ((self + 24#64) ↦ₛ optSenderChainBytes st.senderChain G.senderPad) ∗
       ((self + 128#64) ↦ₛ keyToBytes32 st.rootKey) ∗
       ((self + 168#64) ↦₃₂ st.previousCounter) ∗ memRegion (self + 172#64) 4) := by
  unfold ratchetAt
  ac_rfl

theorem memRegion_36_split (p : BitVec 64) :
    memRegion p 36 =
      ∃∗ v4 : BitVec 32, ∃∗ v3 : BitVec 64, ∃∗ v2 : BitVec 64, ∃∗ v1 : BitVec 64,
      ∃∗ v0 : BitVec 64,
        (p ↦₆₄ v0) ∗ ((p + 8#64) ↦₆₄ v1) ∗ ((p + 16#64) ↦₆₄ v2) ∗ ((p + 24#64) ↦₆₄ v3) ∗
        ((p + 32#64) ↦₃₂ v4) := by
  have h1 := memRegion_split p 8 28 (by decide)
  have h2 := memRegion_split (p + 8#64) 8 20 (by decide)
  have h3 := memRegion_split (p + 16#64) 8 12 (by decide)
  have h4 := memRegion_split (p + 24#64) 8 4 (by decide)
  have a16 : p + 8#64 + 8#64 = p + 16#64 := by bv_arith
  have a24 : p + 16#64 + 8#64 = p + 24#64 := by bv_arith
  have a32 : p + 24#64 + 8#64 = p + 32#64 := by bv_arith
  change memRegion p 36 = memRegion p 8 ∗ memRegion (p + 8#64) 28 at h1
  change memRegion (p + 8#64) 28 = memRegion (p + 8#64) 8 ∗ memRegion (p + 8#64 + 8#64) 20 at h2
  change memRegion (p + 16#64) 20 = memRegion (p + 16#64) 8 ∗ memRegion (p + 16#64 + 8#64) 12 at h3
  change memRegion (p + 24#64) 12 = memRegion (p + 24#64) 8 ∗ memRegion (p + 24#64 + 8#64) 4 at h4
  rw [a16] at h2
  rw [a24] at h3
  rw [a32] at h4
  rw [h1, h2, h3, h4, memRegion_eight p, memRegion_eight (p + 8#64),
    memRegion_eight (p + 16#64), memRegion_eight (p + 24#64), memRegion_four (p + 32#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem memRegion_88_ret_split (r : BitVec 64) :
    memRegion r 88 =
      ∃∗ r40 : BitVec 8, ∃∗ r32 : BitVec 64, ∃∗ r24 : BitVec 64, ∃∗ r16 : BitVec 64,
      ∃∗ r8 : BitVec 64, ∃∗ r0 : BitVec 32,
        (r ↦₃₂ r0) ∗ memRegion (r + 4#64) 4 ∗
        ((r + 8#64) ↦₆₄ r8) ∗ ((r + 16#64) ↦₆₄ r16) ∗
        ((r + 24#64) ↦₆₄ r24) ∗ ((r + 32#64) ↦₆₄ r32) ∗
        ((r + 40#64) ↦₈ r40) ∗ memRegion (r + 41#64) 47 := by
  have h1 := memRegion_split r 4 84 (by decide)
  have h2 := memRegion_split (r + 4#64) 4 80 (by decide)
  have h3 := memRegion_split (r + 8#64) 8 72 (by decide)
  have h4 := memRegion_split (r + 16#64) 8 64 (by decide)
  have h5 := memRegion_split (r + 24#64) 8 56 (by decide)
  have h6 := memRegion_split (r + 32#64) 8 48 (by decide)
  have h7 := memRegion_split (r + 40#64) 1 47 (by decide)
  have a8 : r + 4#64 + 4#64 = r + 8#64 := by bv_arith
  have a16 : r + 8#64 + 8#64 = r + 16#64 := by bv_arith
  have a24 : r + 16#64 + 8#64 = r + 24#64 := by bv_arith
  have a32 : r + 24#64 + 8#64 = r + 32#64 := by bv_arith
  have a40 : r + 32#64 + 8#64 = r + 40#64 := by bv_arith
  have a41 : r + 40#64 + 1#64 = r + 41#64 := by bv_arith
  change memRegion r 88 = memRegion r 4 ∗ memRegion (r + 4#64) 84 at h1
  change memRegion (r + 4#64) 84 = memRegion (r + 4#64) 4 ∗ memRegion (r + 4#64 + 4#64) 80 at h2
  change memRegion (r + 8#64) 80 = memRegion (r + 8#64) 8 ∗ memRegion (r + 8#64 + 8#64) 72 at h3
  change memRegion (r + 16#64) 72 = memRegion (r + 16#64) 8 ∗ memRegion (r + 16#64 + 8#64) 64 at h4
  change memRegion (r + 24#64) 64 = memRegion (r + 24#64) 8 ∗ memRegion (r + 24#64 + 8#64) 56 at h5
  change memRegion (r + 32#64) 56 = memRegion (r + 32#64) 8 ∗ memRegion (r + 32#64 + 8#64) 48 at h6
  change memRegion (r + 40#64) 48 = memRegion (r + 40#64) 1 ∗ memRegion (r + 40#64 + 1#64) 47 at h7
  rw [a8] at h2; rw [a16] at h3; rw [a24] at h4; rw [a32] at h5; rw [a40] at h6; rw [a41] at h7
  rw [h1, h2, h3, h4, h5, h6, h7,
    memRegion_four r, memRegion_eight (r + 8#64), memRegion_eight (r + 16#64),
    memRegion_eight (r + 24#64), memRegion_eight (r + 32#64), memRegion_one (r + 40#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem resultAt_tooFar_intro (A : RustAlloc) (r p : BitVec 64) (t : MessageType) (hp : p ≠ 0) :
    ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
     ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
     ((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
     A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr) ∗
     ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47) ⊢
    consumeMessageKeyResultAt A r (.error (.invalidMessage t .tooFarInFuture)) := by
  simp only [consumeMessageKeyResultAt, errInvalidMessage]
  have h1b : ((r + 40#64) ↦ₛ [msgTypeByte t]) = ((r + 40#64) ↦₈ msgTypeByte t) := by
    rw [pointsToBytes_cons, pointsToBytes_nil, sepConj_emp]
  rw [h1b]
  have hvec :
      (((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
       A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr)) ⊢
      vecU8 A (r + 16#64) tooFarInFutureStr := by
    unfold RustHeap.vecU8
    refine Entails.trans ?_ (Entails.sepExists_intro 36#64)
    refine Entails.trans ?_ (Entails.sepExists_intro p)
    unfold RustHeap.vecU8At RustHeap.vecHeader
    have hlen : tooFarInFutureStr.length = 36 := by rfl_kernel
    have hcap_ne : (36#64 : BitVec 64) ≠ 0#64 := by decide
    have hcap_nat : (36#64 : BitVec 64).toNat = 36 := rfl
    have a24 : r + 16#64 + 8#64 = r + 24#64 := by bv_arith
    have a32 : r + 16#64 + 16#64 = r + 32#64 := by bv_arith
    rw [a24, a32]
    simp only [hlen, hcap_ne, hcap_nat, ↓reduceIte, Nat.sub_self, memRegion_zero,
      BitVec.ofNat_eq_ofNat, sepConj_emp]
    have hpure : 36 ≤ 36 ∧ 36 < 2 ^ 63 ∧ p ≠ 0#64 := ⟨by decide, by decide, hp⟩
    have hpull :
        ((((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64)) ∗
         ⌜36 ≤ 36 ∧ 36 < 2 ^ 63 ∧ p ≠ 0#64⌝ ∗
         (A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr))) =
        (⌜36 ≤ 36 ∧ 36 < 2 ^ 63 ∧ p ≠ 0#64⌝ ∗
         (((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
          A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr))) := by ac_rfl
    rw [hpull]
    exact Entails.pure_right hpure (Entails.refl _)
  have hreord1 :
      ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
       ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
       ((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
       A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr) ∗
       ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47) =
      ((((r + 16#64) ↦₆₄ 36#64) ∗ ((r + 24#64) ↦₆₄ p) ∗ ((r + 32#64) ↦₆₄ 36#64) ∗
        A.live p 36 1 ∗ (p ↦ₛ tooFarInFutureStr)) ∗
       ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
        ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47)) := by ac_rfl
  have hreord2 :
      (vecU8 A (r + 16#64) tooFarInFutureStr ∗
       ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
        ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
        ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47)) =
      ((r ↦₃₂ 2#32) ∗ memRegion (r + 4#64) 4 ∗
       ((r + 8#64) ↦₆₄ 0x8000000000000018#64) ∗
       vecU8 A (r + 16#64) tooFarInFutureStr ∗
       ((r + 40#64) ↦₈ msgTypeByte t) ∗ memRegion (r + 41#64) 47) := by ac_rfl
  rw [hreord1, ← hreord2]
  exact sepConj_mono_left hvec

theorem memRegion_384_tooFarPath_split (sp0 : BitVec 64) :
    memRegion (sp0 - 480#64) 384 =
      ∃∗ v9 : BitVec 64,
        memRegion (sp0 - 480#64) 152 ∗
        ((sp0 - 328#64) ↦₆₄ v9) ∗
        memRegion (sp0 - 320#64) 224 := by
  have h1 := memRegion_split (sp0 - 480#64) 152 232 (by decide)
  have h2 := memRegion_split (sp0 - 328#64) 8 224 (by decide)
  have a328 : sp0 - 480#64 + 152#64 = sp0 - 328#64 := by bv_arith
  have a320 : sp0 - 328#64 + 8#64 = sp0 - 320#64 := by bv_arith
  change memRegion (sp0 - 480#64) 384 =
    memRegion (sp0 - 480#64) 152 ∗ memRegion (sp0 - 480#64 + 152#64) 232 at h1
  change memRegion (sp0 - 328#64) 232 =
    memRegion (sp0 - 328#64) 8 ∗ memRegion (sp0 - 328#64 + 8#64) 224 at h2
  rw [a328] at h1
  rw [a320] at h2
  rw [h1, h2, memRegion_eight (sp0 - 328#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]

theorem stackAt_7712_split (sp0 : BitVec 64) :
    stackAt (sp0 - 480#64) 7712 =
      memRegion (sp0 - 8192#64) 3616 ∗ stackAt (sp0 - 480#64) allocHookStack := by
  simp only [stackAt, allocHookStack]
  have h := memRegion_split (sp0 - 8192#64) 3616 4096 (by decide)
  have a1 : sp0 - 480#64 - 7712#64 = sp0 - 8192#64 := by bv_arith
  have a2 : sp0 - 8192#64 + 3616#64 = sp0 - 480#64 - 4096#64 := by bv_arith
  change memRegion (sp0 - 8192#64) 7712 =
    memRegion (sp0 - 8192#64) 3616 ∗ memRegion (sp0 - 8192#64 + 3616#64) 4096 at h
  rw [a2] at h
  change memRegion (sp0 - 480#64 - 7712#64) 7712 = _
  rw [a1]
  exact h

theorem cmkSavedRegs_entails_memRegion (sp0 : BitVec 64) (s0 : State) :
    cmkSavedRegs sp0 s0 ⊢ memRegion (sp0 - 96#64) 96 := by
  unfold cmkSavedRegs
  have h0 := pointsTo64_entails_memRegion (sp0 - 96#64) (s0.readReg64 .x29)
  have h1 := pointsTo64_entails_memRegion (sp0 - 88#64) (s0.readReg64 .x30)
  have h2 := pointsTo64_entails_memRegion (sp0 - 80#64) (s0.readReg64 .x28)
  have h3 := pointsTo64_entails_memRegion (sp0 - 72#64) (s0.readReg64 .x27)
  have h4 := pointsTo64_entails_memRegion (sp0 - 64#64) (s0.readReg64 .x26)
  have h5 := pointsTo64_entails_memRegion (sp0 - 56#64) (s0.readReg64 .x25)
  have h6 := pointsTo64_entails_memRegion (sp0 - 48#64) (s0.readReg64 .x24)
  have h7 := pointsTo64_entails_memRegion (sp0 - 40#64) (s0.readReg64 .x23)
  have h8 := pointsTo64_entails_memRegion (sp0 - 32#64) (s0.readReg64 .x22)
  have h9 := pointsTo64_entails_memRegion (sp0 - 24#64) (s0.readReg64 .x21)
  have h10 := pointsTo64_entails_memRegion (sp0 - 16#64) (s0.readReg64 .x20)
  have h11 := pointsTo64_entails_memRegion (sp0 - 8#64) (s0.readReg64 .x19)
  refine Entails.trans (sepConj_mono h0 (sepConj_mono h1 (sepConj_mono h2 (sepConj_mono h3
    (sepConj_mono h4 (sepConj_mono h5 (sepConj_mono h6 (sepConj_mono h7
    (sepConj_mono h8 (sepConj_mono h9 (sepConj_mono h10 h11))))))))))) ?_
  have s0_88 : sp0 - 96#64 + 8#64 = sp0 - 88#64 := by bv_arith
  have s0_80 : sp0 - 88#64 + 8#64 = sp0 - 80#64 := by bv_arith
  have s0_72 : sp0 - 80#64 + 8#64 = sp0 - 72#64 := by bv_arith
  have s0_64 : sp0 - 72#64 + 8#64 = sp0 - 64#64 := by bv_arith
  have s0_56 : sp0 - 64#64 + 8#64 = sp0 - 56#64 := by bv_arith
  have s0_48 : sp0 - 56#64 + 8#64 = sp0 - 48#64 := by bv_arith
  have s0_40 : sp0 - 48#64 + 8#64 = sp0 - 40#64 := by bv_arith
  have s0_32 : sp0 - 40#64 + 8#64 = sp0 - 32#64 := by bv_arith
  have s0_24 : sp0 - 32#64 + 8#64 = sp0 - 24#64 := by bv_arith
  have s0_16 : sp0 - 24#64 + 8#64 = sp0 - 16#64 := by bv_arith
  have s0_8 : sp0 - 16#64 + 8#64 = sp0 - 8#64 := by bv_arith
  rw [← s0_8, ← memRegion_split (sp0 - 16#64) 8 8 (by decide),
      ← s0_16, ← memRegion_split (sp0 - 24#64) 8 16 (by decide),
      ← s0_24, ← memRegion_split (sp0 - 32#64) 8 24 (by decide),
      ← s0_32, ← memRegion_split (sp0 - 40#64) 8 32 (by decide),
      ← s0_40, ← memRegion_split (sp0 - 48#64) 8 40 (by decide),
      ← s0_48, ← memRegion_split (sp0 - 56#64) 8 48 (by decide),
      ← s0_56, ← memRegion_split (sp0 - 64#64) 8 56 (by decide),
      ← s0_64, ← memRegion_split (sp0 - 72#64) 8 64 (by decide),
      ← s0_72, ← memRegion_split (sp0 - 80#64) 8 72 (by decide),
      ← s0_80, ← memRegion_split (sp0 - 88#64) 8 80 (by decide),
      ← s0_88, ← memRegion_split (sp0 - 96#64) 8 88 (by decide)]
  exact Entails.refl _

theorem stackAt_cmkStack_reassemble (sp0 : BitVec 64) (s0 : State) (v9 : BitVec 64) :
    (memRegion (sp0 - 8192#64) 3616 ∗
     stackAt (sp0 - 480#64) allocHookStack ∗
     memRegion (sp0 - 480#64) 152 ∗
     ((sp0 - 328#64) ↦₆₄ v9) ∗
     memRegion (sp0 - 320#64) 224 ∗
     cmkSavedRegs sp0 s0) ⊢
    stackAt sp0 cmkStack := by
  have hv9 := pointsTo64_entails_memRegion (sp0 - 328#64) v9
  have hsaved := cmkSavedRegs_entails_memRegion sp0 s0
  refine Entails.trans (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
    (sepConj_mono hv9 (sepConj_mono_right hsaved))))) ?_
  simp only [stackAt, allocHookStack, cmkStack]
  have a96 : sp0 - 320#64 + 224#64 = sp0 - 96#64 := by bv_arith
  have a320 : sp0 - 328#64 + 8#64 = sp0 - 320#64 := by bv_arith
  have a328 : sp0 - 480#64 + 152#64 = sp0 - 328#64 := by bv_arith
  have a4576 : sp0 - 480#64 - 4096#64 = sp0 - 4576#64 := by bv_arith
  have a480 : sp0 - 4576#64 + 4096#64 = sp0 - 480#64 := by bv_arith
  have a_top : sp0 - 8192#64 + 3616#64 = sp0 - 4576#64 := by bv_arith
  rw [← a96, ← memRegion_split (sp0 - 320#64) 224 96 (by decide),
      ← a320, ← memRegion_split (sp0 - 328#64) 8 320 (by decide),
      ← a328, ← memRegion_split (sp0 - 480#64) 152 328 (by decide),
      a4576, ← a480, ← memRegion_split (sp0 - 4576#64) 4096 480 (by decide),
      ← a_top, ← memRegion_split (sp0 - 8192#64) 3616 4576 (by decide)]
  exact Entails.refl _

abbrev cmkTooFarStrSym : String := "libsignal_protocol:.rodata..Lanon.285"

theorem rodata_placed_tooFarInFuture_intro [LibsignalPlacement]
    {m : Memory} {P : SepProp} (hro : LibsignalRoLoaded lsmpl m) (hP : m ⊨ P) :
    m ⊨ (lsρ cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ P :=
  lsro_slice_intro hro (by lsro_addr) (by decide +kernel) hP

end CryptoVerification.LibsignalSession.TooFarPath

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

def TooFarPathPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.ck.index ≤ x.counter →
      x.st.maxForwardJumps < (x.counter - x.ck.index).toNat →
      CmkTooFarState_placed A x ((lsρ TooFarPath.cmkTooFarStrSym ↦ᵣ tooFarInFutureStr) ∗ R) s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

end CryptoVerification.LibsignalSession
