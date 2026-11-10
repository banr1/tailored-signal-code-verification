/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import LibsignalBinary.Proofs.TripleRatchet.ReceiveRatchet.From.Callees

/-!
# Stage P2 Matched-Session Basic Blocks: Part C

Proves `str_to_owned_local2_ok_ext` (`<str as ToOwned>::to_owned [local#2]`) and
`p2_err_tail_a_ext_wp` (`+0x1648 → drop_process_prekey_impl_state1`).
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderStore

set_option maxRecDepth 200000

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

ls_attribute [local simp, local arm64_norm ↓, local wp_norm ↓]
  (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")
  (ls_lemma% fnOff "<str as alloc::borrow::ToOwned>::to_owned")
  (ls_stub% "__rustc::__rust_no_alloc_shim_is_unstable_v2")
  (ls_stub% "__rustc::__rust_alloc")
  (ls_stub% "__rustc::__rust_dealloc")
  (ls_stub% "alloc::raw_vec::handle_error")
  (ls_stub% "memcpy")
  (ls_hook% "memcpy")

private theorem sepWPp_pure_mid {prog : Program} {ret_pc : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret_pc s (A ∗ B ∗ C) post Qp) :
    SepWPp prog ret_pc s (A ∗ B ∗ ⌜φ⌝ ∗ C) post Qp :=
  SepWPp.conseq_pre (by sep_focus) (SepWPp.pure_left h)

theorem str_to_owned_local2_ok_ext {A : RustAlloc} {b : BitVec 64}
    {ext : String → Option (State → State)}
    (hA : AllocContracts b A ext)
    (hRO : HookSat ext memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr strToOwnedLocal2Name)
      (strToOwnedLocal2Spec A) := by
  have hshim := hA.shim_ok_at strToOwnedLocal2Name
    (num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  have halloc := hA.alloc_ok_at strToOwnedLocal2Name
    (num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  have hpanic := panic_at_handle_error_ext b ext strToOwnedLocal2Name
    (num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  have hmemcpy := CryptoVerification.SpqrV1.Alloc.session_memcpy_region_ro_ok_at
    (b := b) (ext := ext) hRO strToOwnedLocal2Name
    (num% (ls_off% "memcpy" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  simp only [strToOwnedLocal2Spec, stackAt_strToOwnedLocal2, memRegion24_cells3]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff strToOwnedLocal2Name =
      (ls_off% "<str as alloc::borrow::ToOwned>::to_owned") :=
    (ls_lemma% fnOff "<str as alloc::borrow::ToOwned>::to_owned")
  responder_fetches_from_cli b (Rust.withPanics ext) hfn
    (ls_off% "<str as alloc::borrow::ToOwned>::to_owned") 0 100
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hmemcpy ⊢
  clear hfn hA hRO
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    strToOwnedLocal2Name = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  rcases x with ⟨outPtr, srcPtr, bs⟩
  dsimp only at *
  have hpos : 0 < bs.length := ‹0 < bs.length›
  have hlt : bs.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, by omega⟩
  apply SepWPp.of_sepWP (mid := entry + 0x2c#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (bs.length, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    rw [← sepConj_assoc]
    refine allowPanic_panicked (allocFailedIn_of_eq ?_) hm
    change sf_1.trace = s0.trace ++ [allocFailedEvent]
    rw [htrace, h_5]
  · have hp : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨_, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    have hlen_le64 : bs.length ≤ 2 ^ 64 := by omega
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), srcPtr, bs)
    wp_steps
    apply SepWP.replace_pre (by sep_focus)
      (vecU8_of_exact_alloc A outPtr (sf_1.readReg64 (Reg.gpr 0#5)) bs hpos hlt hp)
    wp_done

private theorem stackAt_split_ge_m2c {sp : BitVec 64} {inner stk : Nat}
    (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64) :
    stackAt sp stk =
      memRegion (sp - BitVec.ofNat 64 stk) (stk - inner) ∗ stackAt sp inner := by
  have h1 := stackAt_split_bottom sp inner (stk - inner) (by omega)
  rwa [Nat.add_sub_of_le hle] at h1

private theorem hookSat_memcpyRO_mono_stack {ext : String → Option (State → State)}
    {inner stk : Nat} (hle : inner ≤ stk) (hmax : stk ≤ 2 ^ 64)
    (hRO : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack inner)) :
    HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack stk) := by
  obtain ⟨f, hf, hok⟩ := hRO
  refine ⟨f, hf, fun ⟨dst, src, bs⟩ R s0 hrun hpre hsp => ?_⟩
  have hsplit := stackAt_split_ge_m2c (sp := s0.sp) hle hmax
  let R' : SepProp := memRegion (s0.sp - BitVec.ofNat 64 stk) (stk - inner) ∗ R
  have hpre' : s0.mem ⊨
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack inner).pre
        (dst, src, bs) s0 ∗ R' := by
    dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, R'] at hpre ⊢
    rw [hsplit] at hpre
    ac_nf at hpre ⊢
  obtain ⟨hkf, hsym, hout⟩ := hok (dst, src, bs) R' s0 hrun hpre' hsp
  refine ⟨hkf, hsym, ?_⟩
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨_, hp⟩ | ⟨_, _, hp⟩ | ⟨_, hp⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack, R'] at hpost ⊢
    rw [hsplit]
    ac_nf at hpost ⊢
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim
  · dsimp only [CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack] at hp
    rw [satisfies_pure_sepConj] at hp; exact hp.1.elim

/-- `AllocContractsX` + stacked `memcpyRO` generalization of `str_to_owned_local2_ok_ext`. -/
theorem str_to_owned_local2_ok_ext_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} {roStack : Nat}
    (hA : AllocContractsX img A ext)
    (hro_le : roStack ≤ extHookStack)
    (hRO : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStack)) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr strToOwnedLocal2Name)
      ((strToOwnedLocal2SpecWithStack extHookStack A).inImage img) := by
  have hRO_x : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack extHookStack) :=
    hookSat_memcpyRO_mono_stack hro_le (by decide) hRO
  have hshim := shim_ok_at2_ext_x hA (name := strToOwnedLocal2Name)
    (k := num% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  have halloc := alloc_ok_at_norm_ext_x hA (name := strToOwnedLocal2Name)
    (k := num% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  have hpanic := panic_at_handle_error_ext img.base ext strToOwnedLocal2Name
    (num% (ls_off% "alloc::raw_vec::handle_error" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  have hmemcpy := CryptoVerification.SpqrV1.Alloc.session_memcpy_region_ro_withStack_ok_at
    (b := img.base) (ext := ext) (stk := extHookStack) hRO_x strToOwnedLocal2Name
    (num% (ls_off% "memcpy" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
  unfold Spec.inImage
  simp only [strToOwnedLocal2SpecWithStack,
    stackAt_strToOwnedLocal2With extHookStack _ (by decide), memRegion24_cells3]
  cells_unfold
  have hfn : libsignalSessionCode.fnOff strToOwnedLocal2Name =
      (ls_off% "<str as alloc::borrow::ToOwned>::to_owned") :=
    (ls_lemma% fnOff "<str as alloc::borrow::ToOwned>::to_owned")
  responder_fetches_from_cli img.base (Rust.withPanics ext) hfn
    (ls_off% "<str as alloc::borrow::ToOwned>::to_owned") 0 100
  dsimp only [tripleRatchetProgAtExt] at hshim halloc hpanic hmemcpy ⊢
  clear hfn hA hRO hRO_x hro_le
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    strToOwnedLocal2Name = entry
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)) = prog
    reverting [Program.fetch, Program.externAt?, subroutine_ok]
  examples_hide_fetches
  wpp_init x s0
  have hinv0 : ImgCallInv img s0 := ⟨by assumption, by assumption⟩
  rcases x with ⟨outPtr, srcPtr, bs⟩
  dsimp only at *
  have hpos : 0 < bs.length := ‹0 < bs.length›
  have hlt : bs.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, by omega⟩
  apply SepWPp.of_sepWP_inImage (mid := entry + 0x2c#64) hinv0
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_no_alloc_shim_is_unstable_v2" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned")) hinv0
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv1
  apply SepWP.seq_inImage
    (mid := entry + bv% (ls_off% "__rustc::__rust_alloc" -
      ls_off% "<str as alloc::borrow::ToOwned>::to_owned")) hinv1
  wp_call hshim ()
  wp_steps
  apply SepWP.done (by rfl) (by wp_norm_lhs)
  intro hinv2
  wp_call halloc (bs.length, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  intro _hinv3
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun htrace => ?_
    apply SepWPp.of_sepWP
      (mid := entry + bv% (ls_off% "alloc::raw_vec::handle_error" -
        ls_off% "<str as alloc::borrow::ToOwned>::to_owned"))
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    rw [← sepConj_assoc]
    refine allowPanic_panicked (allocFailedIn_of_eq ?_) hm
    change sf_1.trace = s0.trace ++ [allocFailedEvent]
    rw [htrace, ‹sf.trace = s0.trace›]
  · have hp : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid fun ⟨_, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    have hlen_le64 : bs.length ≤ 2 ^ 64 := by omega
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), srcPtr, bs)
    wp_steps
    apply SepWP.replace_pre (by sep_focus)
      (vecU8_of_exact_alloc A outPtr (sf_1.readReg64 (Reg.gpr 0#5)) bs hpos hlt hp)
    wp_done

private theorem cond_ne_adds64_of_ne_neg3 {x : BitVec 64} (hne : x ≠ 0xfffffffffffffffd#64) :
    ConditionHolds CondCode.NE (addsPState64 x 3#64) = true := by
  rw [conditionHolds_ne_addsPState64, bne_iff_ne]
  bv_omega

/-- `+0x1648 → drop_process_prekey_impl_state1` at generic `ext`. -/
theorem p2_err_tail_a_ext_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (coroPtr errTag outPtr : BitVec 64)
    (b_4f2 : BitVec 8)
    (herr_ne_neg3 : errTag ≠ 0xfffffffffffffffd#64)
    (hpc : s.pc = (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1648#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr) (hx20 : s.readReg64 .x20 = errTag)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWP (tripleRatchetProgAtExt b ext)
      (b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>")) s
      (((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2))
      (fun s1 P_f =>
        (P_f ⊢
          ((s.sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((s.sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((s.sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = coroPtr + 0x398#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x20 = errTag ∧
        s1.readReg64 .x21 = s.readReg64 .x21 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x24 = ((s.readReg64 .x23).setWidth 32).zeroExtend 64 ||| (s.readReg64 .x22 <<< 32) ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x26 = outPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 =
          (tripleRatchetProgAtExt b ext).fnAddr
            CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName + 0x1698#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hcond := cond_ne_adds64_of_ne_neg3 herr_ne_neg3
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1648 0x1658
  closure_fetches_range_cli b (Rust.withPanics ext) 0x1678 0x1694
  dsimp only [tripleRatchetProgAtExt] at hpc ⊢
  have hentry : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName =
      b + bv% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") := by
    rw [Program.fnAddr_rebase,
      (ls_lemma% fnOff "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}")]
  have htarget : (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
      0x1694#64 + bv% ((2 ^ 64 + ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>" -
        (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 5780)) % 2 ^ 64) =
      b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") := by
    rw [hentry]; simp only [BitVec.add_assoc]; rfl
  rw [← htarget]
  clear hentry htarget
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr
    CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName = entry
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)) = prog
    reverting [Program.fetch]
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = errTag := hx20
  have hx26' : s.readReg64 (Reg.gpr 26#5) = outPtr := hx26
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨by sep_frame, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    rfl⟩

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
