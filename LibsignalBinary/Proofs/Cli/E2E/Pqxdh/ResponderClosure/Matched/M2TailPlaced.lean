/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsEPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Tail
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymA
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.Reloc.CliHandshakeCodeSymC
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.TripleRatchet.ChainKey.NextChainKey
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Relocatable Stage P2 Matched-Session Remote-Identity Mismatch Tail

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2Tail` on Block `518` (`lsProg_518 ext`,
`(blkPl_518).base = lsmpl.base 518`), including Block-`509` `drop_process_prekey_impl_state1` and
Block-`530` `<str as ToOwned>::to_owned [local#2]`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

noncomputable section

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

/-- Placed spatial precondition at `(blkPl_518).base + 0x12fc` for `stageP2_matched_mismatch_tail`
under `[LibsignalPlacement]`, using `lsLogFilterAddr ↦₆₄ 0#64`. -/
def stageP2MismatchTailPrePlaced [LibsignalPlacement] (A : RustAlloc)
    (s0 : State) (sp coroPtr outPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))) : SepProp :=
  prevSessionsEmptyAt A coroPtr g ∗
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
  ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3e0#64) 24 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  memRegion outPtr 48 ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt sp rootStack

/-- Placed spatial postcondition at `s0.readReg64 .x30` for `stageP2_matched_mismatch_tail`
under `[LibsignalPlacement]`, using `lsLogFilterAddr ↦₆₄ 0#64`. -/
def stageP2MismatchTailPostPlaced [LibsignalPlacement] (A : RustAlloc)
    (s0 : State) (sp coroPtr outPtr : BitVec 64) : SepProp :=
  memRegion (coroPtr + 0xe0#64) 368 ∗
  cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
  ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
  ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
  ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
  ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
  memRegion (sp + 0x370#64) 36 ∗
  memRegion (sp + 0x3e0#64) 24 ∗
  memRegion (sp + 0xa90#64) 48 ∗
  apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
  (lsLogFilterAddr ↦₆₄ 0#64) ∗
  decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
  A.pool ∗
  stackAt sp rootStack

theorem invalidMessage_prekey_out_entails_3_placed [LibsignalPlacement]
    (A : RustAlloc) (outPtr cap ptr e4 : BitVec 64) (bs : List (BitVec 8)) :
    (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
     ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
     ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
     ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 bs.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
     ((outPtr + 0x1c#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ (BitVec.ofNat 64 bs.length).extractLsb' 32 32)) ∗
     ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
     ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
     CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) ⊢
      apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) :=
  invalidMessage_prekey_out_entails_3 A outPtr cap ptr e4 bs

open CryptoVerification.CliHandshake.Placed

/-- Block `509` (`core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>`)
state `1` under `[LibsignalPlacement]`. -/
theorem drop_process_prekey_impl_state1_placed_ok [LibsignalPlacement]
    (H : LibsignalHooks) :
    subroutine_ok (lsProg_509 H) (blkPl_509).base dropProcessPrekeyImplState1Spec := by
  unfold dropProcessPrekeyImplState1Spec
  cells_unfold
  wp_init ptr s0
  wp_steps
  wp_done

theorem drop_process_prekey_impl_state1_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {H : LibsignalHooks}
    [IsLsBlockProg callerProg i H]
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 509)
      (withLsCodeLoaded lsmpl dropProcessPrekeyImplState1Spec) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (entry := lsmpl.base 509)
    (subroutine_ok_withLsCodeLoaded_of_plain (drop_process_prekey_impl_state1_placed_ok H)) hi

private theorem sepWPp_pure_mid_placed {prog : Program} {ret_pc : BitVec 64} {s : State}
    {A B C : SepProp} {φ : Prop} {post Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret_pc s (A ∗ B ∗ C) post Qp) :
    SepWPp prog ret_pc s (A ∗ B ∗ ⌜φ⌝ ∗ C) post Qp :=
  SepWPp.conseq_pre (by sep_focus) (SepWPp.pure_left h)

/-- Block `530` (`<str as alloc::borrow::ToOwned>::to_owned [local#2]`)
under `[LibsignalPlacement]`. -/
theorem str_to_owned_local2_placed_ok [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hshim : subroutine_ok (lsProg_530 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      sessionShimSpec)
    (halloc : subroutine_ok (lsProg_530 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_530 (Rust.withPanics ext))
      (lsρ "memcpy")
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hpan : Rust.withPanics ext "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" =
      some Rust.panicked) :
    subroutine_ok (lsProg_530 (Rust.withPanics ext)) (blkPl_530).base
      (strToOwnedLocal2Spec A) := by
  have hpanic : (lsProg_530 (Rust.withPanics ext)).externAt?
      (lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error") =
      some Rust.panicked :=
    (ls_externAt?_of_mem).trans hpan
  simp only [strToOwnedLocal2Spec, stackAt_strToOwnedLocal2, memRegion24_cells3]
  cells_unfold
  wpp_init x s0
  rcases x with ⟨outPtr, srcPtr, bs⟩
  dsimp only at *
  have hpos : 0 < bs.length := ‹0 < bs.length›
  have hlt : bs.length < 2 ^ 63 := by omega
  have hlen_toNat : (BitVec.ofNat 64 bs.length).toNat = bs.length := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hpow2 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlay : LayoutOk bs.length 1 := ⟨hpos, hpow2, by omega⟩
  apply SepWPp.of_sepWP (mid := (blkPl_530).base + 0x2c#64)
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (bs.length, 1)
  apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
  by_cases hoom : sf_1.readReg64 (Reg.gpr 0#5) = 0
  · simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun htrace => ?_
    apply SepWPp.of_sepWP (mid := lsρ "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error")
    wp_steps
    apply SepWP.done (by wp_norm_goal) (by wp_norm_lhs)
    refine SepWPp.panic (by wp_norm_lhs) (by simpa only [arm64_norm] using hpanic) fun hm => ?_
    rw [← sepConj_assoc]
    refine allowPanic_panicked (allocFailedIn_of_eq ?_) hm
    change sf_1.trace = s0.trace ++ [allocFailedEvent]
    rw [htrace, h_5]
  · have hp : sf_1.readReg64 (Reg.gpr 0#5) ≠ 0#64 := hoom
    simp only [hoom, ↓reduceIte, sepConj_assoc]
    refine sepWPp_pure_mid_placed fun ⟨_, htrace⟩ => ?_
    apply SepWPp.of_sepWP_ret
    wp_steps
    have hlen_le64 : bs.length ≤ 2 ^ 64 := by omega
    wp_call hmemcpy (sf_1.readReg64 (Reg.gpr 0#5), srcPtr, bs)
    wp_steps
    apply SepWP.replace_pre (by sep_focus)
      (vecU8_of_exact_alloc A outPtr (sf_1.readReg64 (Reg.gpr 0#5)) bs hpos hlt hp)
    wp_done

theorem str_to_owned_local2_placed_ok_at [LibsignalPlacement]
    {callerProg : Program} {i : Nat} {A : RustAlloc}
    {ext : String → Option (State → State)}
    [IsLsBlockProg callerProg i (Rust.withPanics ext)]
    (hshim : subroutine_ok (lsProg_530 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc35___rust_no_alloc_shim_is_unstable_v2")
      sessionShimSpec)
    (halloc : subroutine_ok (lsProg_530 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc12___rust_alloc")
      (rustAllocSpec A))
    (hmemcpy : subroutine_ok (lsProg_530 (Rust.withPanics ext))
      (lsρ "memcpy")
      CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hpan : Rust.withPanics ext "_RNvNtCs69KKACWg7bl_5alloc7raw_vec12handle_error" =
      some Rust.panicked)
    (hi : i < 619 := by decide) :
    subroutine_ok callerProg (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A)) :=
  ls_subroutine_ok_of_block (callerProg := callerProg) (entry := lsmpl.base 530)
    (subroutine_ok_withLsCodeLoaded_of_plain
      (str_to_owned_local2_placed_ok hshim halloc hmemcpy hpan)) hi

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P2 remote-identity mismatch tail
(`(blkPl_518).base + 0x12fc → s0.readReg64 .x30`). -/
theorem stageP2_matched_mismatch_tail_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)}
    (hto : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 530)
      (withLsCodeLoaded lsmpl (strToOwnedLocal2Spec A)))
    (hdealloc : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsρ "_RNvCs1njKG4L9aB3_7___rustc14___rust_dealloc")
      (rustDeallocSpec A))
    (hdrop_ss : subroutine_ok (lsProg_518 (Rust.withPanics ext))
      (lsmpl.base 512)
      (withLsCodeLoaded lsmpl (dropSessionStructureLocal2Spec A)))
    (s0 s : State)
    (sp coroPtr outPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x12fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) (s0.readReg64 .x30) s
      (prevSessionsEmptyAt A coroPtr g ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x2c0#64) ↦₈ b_2c0) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ u_d0) ∗
       memRegion (sp + 0x370#64) 36 ∗
       memRegion (sp + 0x3e0#64) 24 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       memRegion outPtr 48 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
       A.pool ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          memRegion (coroPtr + 0xe0#64) 368 ∗
          cells (coroPtr + 0x250#64) 6 ∗
          ((coroPtr + 0x2c0#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
          ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
          ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
          ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
          ((sp + 0xa8#64) ↦₆₄ 3#64) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          ((sp + 0xd0#64) ↦₆₄ 70#64) ∗
          memRegion (sp + 0x370#64) 36 ∗
          memRegion (sp + 0x3e0#64) 24 ∗
          memRegion (sp + 0xa90#64) 48 ∗
          apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp rootStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  let roAddr : BitVec 64 := lsρ "libsignal_cli_handshake:.rodata..Lanon.86"
  refine SepWPp.intro_rodata_mismatchRemoteIk_placed' hcro ?_
  have h12fc := p2_seg_12fc_placed_wp ext s coroPtr hpc hrun hx19
  refine bind_sepWP_lscro_steps_m2_placed hcro h12fc (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx1_1, hx2_1, hx19_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have htr1 : s0.trace <+: s1.trace := by rw [htr1_s]; exact htr
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwned sp hroot_le)) (by sep_focus) ?_
  refine call_lscro_oom_steps_m2_placed
    (spec := strToOwnedLocal2Spec A)
    (x := (sp + 0x3e0#64, roAddr, mismatchRemoteIkStrPlaced))
    (P_spec := memRegion (sp + 0x3e0#64) 24 ∗ (roAddr ↦ᵣ mismatchRemoteIkStrPlaced) ∗ A.pool ∗
      stackAt sp strToOwnedLocal2Stack)
    hcro1 htr1 (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded hto)
    hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [strToOwnedLocal2Spec, Spec.allowPanicWhen]
      rw [hsp1, mismatchRemoteIkStrPlaced_length]
      rw [hsp_eq] at hx0_1
      exact Entails.pure_right ⟨hx0_1, hx1_1, hx2_1, by decide, by decide⟩ (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 hsp2_al hcs2 hcro2 => ?_)
  dsimp only [strToOwnedLocal2Spec, Spec.allowPanicWhen]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwned sp hroot_le).symm) (by sep_focus) ?_
  refine SepWPp.drop_ro_frame (D := roAddr ↦ᵣ mismatchRemoteIkStrPlaced) (by sep_focus) ?_
  refine SepWPp.weaken_frame (vecU8_unpack_3e0_64 A sp mismatchRemoteIkStrPlaced) (by sep_focus) ?_
  rw [mismatchRemoteIkStrPlaced_length]
  sep_norm
  refine SepWPp.exists_elim fun cap => SepWPp.exists_elim fun ptr => ?_
  rcases hcs2 with ⟨hx19_cs2, _, _, _, _, _, hx25_cs2, hx26_cs2, _, hx28_cs2, _, hvregs_cs2⟩
  have hvregs2_s : calleeSavedVRegs s2 = calleeSavedVRegs s :=
    hvregs_cs2.trans (congrArg VRegFile.calleeSaved hvregs1)
  have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx19_2 : s2.readReg64 .x19 = coroPtr := hx19_cs2.trans hx19_1
  have hx25_2 : s2.readReg64 .x25 = sp + 0x210#64 := hx25_cs2.trans (hx25_1.trans hx25)
  have hx26_2 : s2.readReg64 .x26 = outPtr := hx26_cs2.trans (hx26_1.trans hx26)
  have hx28_2 : s2.readReg64 .x28 = sp + 0xa90#64 := hx28_cs2.trans (hx28_1.trans hx28)
  have h1310 := p2_seg_1310_to_drop_placed_wp ext s2 coroPtr outPtr cap ptr 70#64
    u_a8 outPtr u_d0 b_4f2 hpc2 hrun2 hsp2_align hx19_2 hx26_2
  rw [hsp2] at h1310
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h1310 (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hvregs3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, hx26_3, _, hx28_3, _, hx30_3⟩
  have hsp3 : s3.sp = sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by rw [State.spAligned, hsp3, ← hsp2]; exact hsp2_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le)) (by sep_focus) ?_
  refine call_lscro_nopanic_m2_placed
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hcro3
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (drop_process_prekey_impl_state1_placed_ok_at (callerProg := lsProg_518 (Rust.withPanics ext))))
    hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [dropProcessPrekeyImplState1Spec]; rw [hsp3, coro_398_add_15a])
    hx0_3 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp3, coro_398_add_15a, sepConj_assoc]
  refine SepWPp.pure_elim fun htr4_3 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, hx20_cs4, hx21_cs4, hx22_cs4, hx23_cs4, hx24_cs4,
    hx25_cs4, hx26_cs4, _, hx28_cs4, _, hvregs_cs4⟩
  have hvregs4_s : calleeSavedVRegs s4 = calleeSavedVRegs s :=
    hvregs_cs4.trans ((congrArg VRegFile.calleeSaved hvregs3).trans hvregs2_s)
  have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
  have hsp4_align : (s4.sp &&& 15#64 == 0#64) = true := by rw [hsp4, ← hsp_eq]; exact hsp_align
  have hx19_4 : s4.readReg64 .x19 = coroPtr := hx19_cs4.trans hx19_3
  have hx20_4 : s4.readReg64 .x20 = 0x8000000000000018#64 := hx20_cs4.trans hx20_3
  have hx21_4 : s4.readReg64 .x21 = 0#64 := hx21_cs4.trans hx21_3
  have hx22_4 : s4.readReg64 .x22 = ptr := hx22_cs4.trans hx22_3
  have hx23_4 : s4.readReg64 .x23 = (cap.extractLsb' 0 32).zeroExtend 64 := hx23_cs4.trans hx23_3
  have hx24_4 : s4.readReg64 .x24 = cap := hx24_cs4.trans hx24_3
  have hx25_4 : s4.readReg64 .x25 = s4.sp + 0x210#64 := by
    rw [hsp4]; exact hx25_cs4.trans (hx25_3.trans hx25_2)
  have hx26_4 : s4.readReg64 .x26 = outPtr := hx26_cs4.trans hx26_3
  have hx28_4 : s4.readReg64 .x28 = s4.sp + 0xa90#64 := by
    rw [hsp4]; exact hx28_cs4.trans (hx28_3.trans hx28_2)
  refine SepWPp.weaken_frame (memRegion_370_36_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (memRegion_a90_48_split sp) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (coro_250_cells6_eq coroPtr)) (by sep_focus) ?_
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 =>
    SepWPp.exists_elim fun ua90 => SepWPp.exists_elim fun ua98 =>
    SepWPp.exists_elim fun uaa0 => SepWPp.exists_elim fun uaa8 =>
    SepWPp.exists_elim fun uab0 => SepWPp.exists_elim fun uab8 =>
    SepWPp.exists_elim fun u370 => SepWPp.exists_elim fun u378 =>
    SepWPp.exists_elim fun u380 => SepWPp.exists_elim fun u388 =>
    SepWPp.exists_elim fun u390 => ?_
  have h1698 := p2_seg_1698_mismatch_to_3588_placed_wp ext s4 coroPtr outPtr cap ptr 70#64
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390 b_390 hpc4 hrun4 hsp4_align
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx28_4
  rw [hsp4] at h1698
  refine bind_sepWP_lscro_steps_m2_placed hcro4 h1698 (by sep_focus)
    fun s5 _ hpc5 hrun5 hcro5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hvregs5, hx19_5, hx22_5, hx25_5, hx26_5, hx28_5, _, _⟩
  have hvregs5_s : calleeSavedVRegs s5 = calleeSavedVRegs s :=
    hvregs5.trans hvregs4_s
  have hsp5 : s5.sp = sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_dropSS sp hroot_le)) (by sep_focus) ?_
  have hdrop_rec := closure_err_drop_record_tail_placed_ok (A := A) (ext := ext)
    (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)
    hdealloc hdrop_ss s0 s5 sp coroPtr outPtr 0x8000000000000018#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((70#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (70#64 : BitVec 64).extractLsb' 32 32)
    ((s4.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    (cap.extractLsb' 0 32) ((s4.readReg64 .x27).extractLsb' 32 32) b_2c0
    g recG recSt hcro5 hsp5 (Nat.le_trans (by decide) hsp_root)
    hpc5 hrun5 hsp5_align hx19_5 hx22_5 hx25_5 hx26_5 hx28_5
  refine SepWPp.bind_sepWPp_steps_frame hdrop_rec (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf_5, hcsf, hvregsf_5, hcrof⟩ => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, hspf,
    htrf_5.trans (htr5_4.trans (htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)))),
    hcsf, hvregsf_5.trans hvregs5_s, hcrof⟩
  refine Entails.trans (entails_replace_sub (Entails.of_eq (stack_root_to_dropSS sp hroot_le).symm)
    (by sep_focus) rfl) ?_
  have hout := invalidMessage_prekey_out_entails_3 A outPtr cap ptr (s4.readReg64 .x27)
    mismatchRemoteIkStrPlaced
  rw [mismatchRemoteIkStrPlaced_length] at hout
  refine Entails.trans (entails_replace_sub hout (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub
    (coro_250_6w_entails_cells6 coroPtr 0x8000000000000018#64 cap ptr 70#64 3#64 (s4.readReg64 .x27))
    (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub
    (w64_3_entails_memRegion24 (sp + 0x3e0#64) cap ptr 70#64)
    (by simp only [BitVec.add_assoc, BitVec.reduceAdd]; sep_focus) rfl) ?_
  exact entails_replace_sub
    (a90_mismatch_entails_memRegion48 sp cap ptr 70#64 (s4.readReg64 .x27))
    (by sep_focus) (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
end
