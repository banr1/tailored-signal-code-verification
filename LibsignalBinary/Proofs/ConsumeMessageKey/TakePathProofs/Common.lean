/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import GeneratedLean.LibsignalSessionCode -- shake: keep

/-!
# Shared Fetch and Hook Helpers for the `consume_message_key` Take Path
-/

@[expose] public section

namespace CryptoVerification.LibsignalSession.TakePath

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

noncomputable abbrev SP (b : BitVec 64) (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State)) : Program :=
  libsignalSessionCode.rebase b (Rust.withPanics (sessionExterns F alloc))

abbrev cmkSym : String :=
  "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"

theorem sessionProg_eq_SP {img : Obj.Image} (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    sessionProg img F alloc = SP img.base F alloc :=
  libsignalSessionCode_ofImage himg

theorem cmkEntry_eq_fnAddr {img : Obj.Image} (F : ShaState → List (BitVec 8) → ShaState)
    (alloc : String → Option (State → State))
    (himg : Obj.Loads libsignalSessionImage img) :
    cmkEntry img = (SP img.base F alloc).fnAddr cmkSym := by
  rw [cmkEntry_eq himg, Program.fnAddr_rebase, cmkSym, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]

open Lean Elab Tactic in
/-- Introduce instruction-fetch hypotheses for `consume_message_key` byte offsets `lo, lo + 4, ..., hi`. -/
elab "cmk_fetches_range " b:term:max H:term:max lo:num hi:num : tactic => do
  let lo := lo.getNat
  let hi := hi.getNat
  let mut k := lo
  while k <= hi do
    let dec := mkIdent (Name.mkSimple s!"libsignalSessionBin_decode_0x{String.ofList (Nat.toDigits 16 (0xded8 + k))}")
    let kq := Syntax.mkNumLit (toString k)
    evalTactic (← `(tactic|
      have := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := $b) (H := $H) (k := $kq)
        (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") (by decide) $dec))
    k := k + 4

theorem dealloc_ok_at {A : RustAlloc} {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} (hA : AllocHooks A alloc) :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      (rustDeallocSpec A) :=
  hook_ok_at_raw (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide) (by decide)
    (ls_hook% "__rustc::__rust_dealloc")
    (allocHooks_sessionExterns F A alloc hA).dealloc

theorem memmove_ok_at {b : BitVec 64}
    {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} :
    subroutine_ok (SP b F alloc) ((SP b F alloc).fnAddr cmkSym + bv% (ls_off% "memmove" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      libcMemmoveSpec :=
  hook_ok_at (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") (k := num% (ls_off% "memmove" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) (by decide) (by decide)
    (ls_hook% "memmove")
    (by simp [Rust.isPanicSymbol])
    ⟨hookMemmove, rfl, hookMemmove_ok⟩

theorem find_index_ok_at {img : Obj.Image} {F : ShaState → List (BitVec 8) → ShaState}
    {alloc : String → Option (State → State)} {A : RustAlloc}
    (himg : Obj.Loads libsignalSessionImage img)
    (hFind : FindIndexOk img F alloc A) :
    subroutine_ok (SP img.base F alloc) ((SP img.base F alloc).fnAddr cmkSym + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      ((findIndexSpec img A).inImage img) := by
  have haddr : (SP img.base F alloc).fnAddr cmkSym + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key") = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::find_receiver_chain_index") := by
    rw [Program.fnAddr_rebase, cmkSym, (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")]
    bv_omega
  rw [haddr, ← sessionProg_eq_SP F alloc himg]
  exact hFind

/-- `ADRP`+`ADD` at `+0xc0` resolves to `logFilterAddr img`. -/
theorem adrp_0xc0_add_eq_logFilterAddr {img : Obj.Image}
    (himg : Obj.Loads libsignalSessionImage img)
    {entry : BitVec 64} (hentry : entry = img.base + bv% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) :
    ((entry + bv% (192) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<libsignal_protocol::state::kyber_prekey::KyberPreKeyRecord>::secret_key" + 52))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) =
      logFilterAddr img := by
  have hbal := ProofLib.base_aligned_of_loads himg
  rw [hentry, BitVec.add_assoc img.base, adrp_page_of_aligned hbal, logFilterAddr]
  have hmask : ((57048#64 + 192#64 : BitVec 64) &&& bv% (2 ^ 64 - 4096)) = 53248#64 := rfl
  rw [hmask]
  bv_omega

/-! ## Relocatable `[LibsignalPlacement]` Definitions and Hook Lemmas -/

abbrev cmkMemmoveSym : String := "memmove"

def TakePathPlacedSpec [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) : Prop :=
  CmkAllocHooks A H → H cmkMemmoveSym = some hookMemmove → FindIndexPlacedOk H A →
    ∀ (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 s : State),
      x.counter < x.ck.index →
      CmkTakeState_placed A x R s0 s →
      reaches_outcome ((blkPC_24).rebase (blkPl_24).base H) (cmkPlacedSpec F A) x R s0 s

set_option maxRecDepth 200000 in
theorem dealloc_placed_ok_at [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} (hA : CmkAllocHooks A H) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym)
      (rustDeallocSpec A) := by
  rcases hA with ⟨_, hdealloc, _, _, _, _⟩
  exact cmk_hook_ok_of_mem hdealloc

set_option maxRecDepth 200000 in
theorem memmove_placed_ok_at [LibsignalPlacement]
    {H : String → Option (State → State)} (hmemmove : H cmkMemmoveSym = some hookMemmove) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkMemmoveSym)
      libcMemmoveSpec :=
  cmk_hook_ok_of_mem ⟨hookMemmove, hmemmove, hookMemmove_ok⟩

end CryptoVerification.LibsignalSession.TakePath
