/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Defs
public import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.FromRecordCalleesCodeSym
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Placed.BridgeReloc
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.FromRecordCallees.Fetch
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Verification of `try_decrypt_from_record::{closure#0}` (`0x381ac`)

Proves fixed-image (`log_closure_ok`) and relocatable `[LibsignalFullPlacement]`
(`log_closure_placed_ok`, `log_closure_coins_placed_ok`) contracts for the log-off fast path of
`try_decrypt_from_record::{closure#0}` (blocks `159` and `462`).
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.FromRecordCallees

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames.LibsignalSession CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalSession

set_option maxRecDepth 200000
set_option maxHeartbeats 1600000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem stackAt_closure (sp : BitVec 64) :
    stackAt sp closureStack =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2)) ∗
      stackAt (sp - 64#64) 296 ∗
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
        ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
        ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) := by
  have h1 := stackAt_split_cells sp 320 8 (by decide)
  have h2 := stackAt_split_bottom (sp - 64#64) 296 24 (by decide)
  have hsub : (sp - 64#64) - BitVec.ofNat 64 (296 + 24) = sp - 384#64 := by
    rw [BitVec.sub_sub]; rfl
  rw [hsub, show (24 : Nat) = 8 * 3 by rfl, memRegion_cells (sp - 384#64) 3 (by decide)] at h2
  change stackAt sp closureStack = stackAt (sp - 64#64) 320 ∗ cells (sp - 64#64) 8 at h1
  have hc3 : cells (sp - 384#64) 3 =
      (∃∗ v0 : BitVec 64, ∃∗ v1 : BitVec 64, ∃∗ v2 : BitVec 64,
        ((sp - 384#64) ↦₆₄ v0) ∗ ((sp - 376#64) ↦₆₄ v1) ∗ ((sp - 368#64) ↦₆₄ v2)) := by
    cells_unfold
  have hc8 : cells (sp - 64#64) 8 =
      (∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64, ∃∗ w3 : BitVec 64,
       ∃∗ w4 : BitVec 64, ∃∗ w5 : BitVec 64, ∃∗ w6 : BitVec 64, ∃∗ w7 : BitVec 64,
        ((sp - 64#64) ↦₆₄ w0) ∗ ((sp - 56#64) ↦₆₄ w1) ∗ ((sp - 48#64) ↦₆₄ w2) ∗
        ((sp - 40#64) ↦₆₄ w3) ∗ ((sp - 32#64) ↦₆₄ w4) ∗ ((sp - 24#64) ↦₆₄ w5) ∗
        ((sp - 16#64) ↦₆₄ w6) ∗ ((sp - 8#64) ↦₆₄ w7)) := by
    cells_unfold
  rw [h1, h2, hc3, hc8, sepConj_assoc]

private theorem logClosure_adrp_addr_eq1 {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}")) :
    (((entry + bv% (28)) &&& bv% (2 ^ 64 - 4096)) + bv% (page% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) - page% (ls_off% "<&[u8] as hex::ToHex>::encode_hex::<alloc::string::String> [local#1]" + 12))) + bv% ((ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) % 4096) = base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  subst he; bv_arith

private theorem logClosure_adrp_addr_eq2 {base entry : BitVec 64}
    (hb : base &&& 0xfff#64 = 0#64) (he : entry = base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}")) :
    ((entry + bv% (28)) &&& bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - page% (ls_off% "<&[u8] as hex::ToHex>::encode_hex::<alloc::string::String> [local#1]" + 12)) = base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) := by
  subst he; bv_arith

theorem log_closure_ok_ext {img : Obj.Image} {ext : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    LogClosureOkExt img ext := by
  unfold LogClosureOkExt
  simp only [Spec.inImage, logClosureSpec, logOff, logFilterAddr, stackAt_closure,
    sepExists_sepConj_left, sepExists_sepConj_right]
  unfold tripleRatchetProgAtExt logClosureName
  have hfn := (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}")
  have hb : img.base &&& 0xfff#64 = 0#64 := ProofLib.ObjectLoad.base_aligned_of_loads himg
  have hentry : (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr
      "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}" =
      img.base + bv% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}") := by
    rw [Program.fnAddr_rebase, (ls_lemma% fnOff "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}")]
  have hadrp2 : (((libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr
      "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}" + 28#64) &&&
      bv% (2 ^ 64 - 4096)) + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256 - page% (ls_off% "<&[u8] as hex::ToHex>::encode_hex::<alloc::string::String> [local#1]" + 12)) = img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256) :=
    logClosure_adrp_addr_eq2 hb hentry
  clear hentry
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}")) 0 48
  code_fetches_from CryptoVerification.libsignalSessionCode fromRecordCalleesBin img.base
    (Rust.withPanics ext) hfn (num% (ls_off% "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}")) 0x19c 24
  clear hfn himg
  generalize_entry (libsignalSessionCode.rebase img.base
      (Rust.withPanics ext)).fnAddr
      "libsignal_protocol::session_management::try_decrypt_from_record::<libsignal_session::HookRng>::{closure#0}" = entry
  wp_init x s0
  examples_hide_fetches
  wp_steps
  wp_done

theorem log_closure_ok_trap {img : Obj.Image} {C : Crypto}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    LogClosureOk_trap img C abs :=
  log_closure_ok_ext himg

/-- `try_decrypt_from_record::<HookRng>::{closure#0}` (`0x381ac`) meets
`(logClosureSpec img).inImage img` on `tripleRatchetProgAt`. -/
theorem log_closure_ok {img : Obj.Image} {C : Crypto} {ctl : BitVec 64}
    {abs : String → Option (State → State)}
    (himg : Obj.Loads libsignalSessionImage img) :
    LogClosureOk img C ctl abs :=
  subroutine_ok_kit_of_trTrap (log_closure_ok_trap himg)

/-! ## Relocatable `[LibsignalFullPlacement]` Contracts (Blocks `159` and `462`) -/

@[simp, arm64_norm, wp_norm]
theorem ls_resolve_logFilterSym (pl : Arm64.Obj.MultiPlacement) :
    libsignalSessionLib.resolve pl lsLogFilterSym = pl.ρ lsLogFilterSym :=
  ls_resolve_data (by decide +kernel)

/-- Relocatable `MAX_LOG_LEVEL_FILTER == 0` assertion (`lsLogFilterAddr ↦₆₄ 0#64`). -/
def lsLogOff [LibsignalPlacement] : SepProp :=
  lsLogFilterAddr ↦₆₄ 0#64

/-- Relocatable specification of `try_decrypt_from_record::{closure#0}` on the log-off fast path. -/
def logClosurePlacedSpec [LibsignalPlacement] : Spec Unit where
  pre := fun _ s => lsLogOff ∗ stackAt s.sp closureStack
  post := fun _ s0 sf => ⌜sf.trace = s0.trace⌝ ∗ lsLogOff ∗ stackAt s0.sp closureStack

/-- Block `159`: `try_decrypt_from_record::<HookRng>::{closure#0}` meets
`logClosurePlacedSpec` under `[LibsignalFullPlacement]`. -/
theorem log_closure_placed_ok [LibsignalFullPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_159).rebase (blkPl_159).base H) (blkPl_159).base
      logClosurePlacedSpec := by
  unfold logClosurePlacedSpec lsLogOff lsLogFilterAddr
  simp only [stackAt_closure, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  wp_steps
  wp_done

/-- Block `462`: `try_decrypt_from_record::<Coins>::{closure#0}` meets
`logClosurePlacedSpec` under `[LibsignalFullPlacement]`. -/
theorem log_closure_coins_placed_ok [LibsignalFullPlacement]
    (H : String → Option (State → State)) :
    subroutine_ok ((blkPC_462).rebase (blkPl_462).base H) (blkPl_462).base
      logClosurePlacedSpec := by
  unfold logClosurePlacedSpec lsLogOff lsLogFilterAddr
  simp only [stackAt_closure, sepExists_sepConj_left, sepExists_sepConj_right]
  wp_init x s0
  wp_steps
  wp_done

end CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
