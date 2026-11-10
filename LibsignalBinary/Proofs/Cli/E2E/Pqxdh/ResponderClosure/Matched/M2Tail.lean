/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.Stmts
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsB
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderStore.SessionRecordCallees
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
public import LibsignalBinary.Proofs.PublicApi.MessageDecrypt.Seg.SegUntrusted
public import LibsignalBinary.Proofs.SpqrV1.Alloc.Concat
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Aux
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrSteps
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsA
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsC
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsE
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract

/-!
# Stage P2 Matched-Session Remote-Identity Mismatch Tail (`+0x12fc → x30`)

Proves `stageP2_matched_mismatch_tail` (and its `AllocContractsX` + stacked `memcpyRO` generalization
`stageP2_matched_mismatch_tail_x`), unwinding the remote-identity mismatch error path from `+0x12fc`
to `s0.readReg64 .x30` with `apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext)))`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

-- Repeat `-arm64_norm` attributes after importing `GenP3.StageP3Stmt`.
attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub)
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem dropProcessPrekeyImpl_addr_eq_ext (b : BitVec 64) (ext : String → Option (State → State)) :
    b + bv% (ls_off% "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>") =
    (tripleRatchetProgAtExt b ext).fnAddr
      CryptoVerification.Cli.E2E.Pqxdh.ResponderStore.dropProcessPrekeyImplName := by
  simp only [tripleRatchetProgAtExt, Program.fnAddr_rebase]
  rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::session::process_prekey_impl::{closure#0}>")]

theorem stack_root_to_strToOwned (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - strToOwnedLocal2Stack) ∗
        stackAt sp strToOwnedLocal2Stack :=
  stackAt_split_of_le sp rootStack strToOwnedLocal2Stack (by decide) hn

theorem closure_dealloc_ok_ext' {b : BitVec 64} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : AllocContracts b A ext) :
    subroutine_ok (tripleRatchetProgAtExt b ext)
      ((tripleRatchetProgAtExt b ext).fnAddr
        CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.decryptPrekeyClosureName +
        bv% (ls_off% "__rustc::__rust_dealloc" -
          ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}"))
      (rustDeallocSpec A) := by
  have heq :
      bv% (ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") =
      bv% ((2 ^ 64 + ls_off% "__rustc::__rust_dealloc" -
        ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}") % 2 ^ 64) := by
    decide
  rw [heq]
  exact closure_dealloc_ok_ext hA

theorem memRegion_3e0_368_split_24 (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 368 =
      memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 344 := by
  rw [ProofLib.memRegion_split (sp + 0x3e0#64) 24 344 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd]

theorem stack_root_to_cells48 (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - 48) ∗
        cells (sp - 48#64) 6 := by
  rw [stackAt_split_of_le sp rootStack 48 (by decide) hn]
  change _ ∗ memRegion (sp - 48#64) 48 = _
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp - 48#64) 6 (by decide)]

theorem coro_398_add_15a (coroPtr : BitVec 64) :
    (coroPtr + 0x398#64) + 0x15a#64 = coroPtr + 0x4f2#64 := by
  bv_omega

theorem stack_root_to_remoteIk (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack)
        (rootStack - CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyStack) ∗
        stackAt sp CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyStack :=
  stackAt_split_of_le sp rootStack
    CryptoVerification.LibsignalTripleRatchet.Getters.remoteIdentityKeyStack (by decide) hn

theorem stack_root_to_pkSerialize (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - publicKeySerializeStack) ∗
        stackAt sp publicKeySerializeStack :=
  stackAt_split_of_le sp rootStack publicKeySerializeStack (by decide) hn

theorem invalidMessage_prekey_out_entails_3 (A : RustAlloc) (outPtr cap ptr e4 : BitVec 64)
    (bs : List (BitVec 8)) :
    (((outPtr + 0x0#64) ↦₆₄ 0x8000000000000018#64) ∗
     ((outPtr + 0x8#64) ↦₃₂ cap.extractLsb' 0 32) ∗
     ((outPtr + 0xc#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
     ((outPtr + 0x14#64) ↦₆₄ ((BitVec.ofNat 64 bs.length).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
     ((outPtr + 0x1c#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ (BitVec.ofNat 64 bs.length).extractLsb' 32 32)) ∗
     ((outPtr + 0x24#64) ↦₆₄ (e4.extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
     ((outPtr + 0x2c#64) ↦₃₂ e4.extractLsb' 32 32) ∗
     CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs) ⊢
      apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext))) :=
  invalidMessage_prekey_out_entails A outPtr cap ptr 3#64 e4 bs
    [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 0#8] rfl (by decide)

theorem opkPacked_two_mask (w : BitVec 64) :
    ((((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32)) &&& 0xff#64) =
      ((2#32 : BitVec 32).zeroExtend 64 &&& 0xff#64) := by
  bv_bits

theorem opkPacked_two_lo32 (w : BitVec 64) :
    (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32)).extractLsb' 0 32 = 2#32 := by
  bv_bits

theorem coro_250_cells6_eq (coroPtr : BitVec 64) :
    cells (coroPtr + 0x250#64) 6 =
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ((coroPtr + 0x250#64) ↦₆₄ u0) ∗ ((coroPtr + 0x258#64) ↦₆₄ u1) ∗
        ((coroPtr + 0x260#64) ↦₆₄ u2) ∗ ((coroPtr + 0x268#64) ↦₆₄ u3) ∗
        ((coroPtr + 0x270#64) ↦₆₄ u4) ∗ ((coroPtr + 0x278#64) ↦₆₄ u5) := by
  simp only [cells, BitVec.add_assoc, BitVec.reduceAdd, sepConj_emp,
    sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]

theorem coro_250_6w_entails_cells6 (coroPtr u0 u1 u2 u3 u4 u5 : BitVec 64) :
    ((coroPtr + 0x250#64) ↦₆₄ u0) ∗ ((coroPtr + 0x258#64) ↦₆₄ u1) ∗
    ((coroPtr + 0x260#64) ↦₆₄ u2) ∗ ((coroPtr + 0x268#64) ↦₆₄ u3) ∗
    ((coroPtr + 0x270#64) ↦₆₄ u4) ∗ ((coroPtr + 0x278#64) ↦₆₄ u5) ⊢
      cells (coroPtr + 0x250#64) 6 := by
  rw [coro_250_cells6_eq]
  exact Entails.sepExists_right u0 (Entails.sepExists_right u1
    (Entails.sepExists_right u2 (Entails.sepExists_right u3
      (Entails.sepExists_right u4 (Entails.sepExists_right u5 (Entails.refl _))))))

theorem w64_3_entails_memRegion24 (a w0 w1 w2 : BitVec 64) :
    (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗ ((a + 16#64) ↦₆₄ w2) ⊢
      memRegion a 24 := by
  rw [ProofLib.memRegion_split a 8 16 (by decide),
      ProofLib.memRegion_split (a + 8#64) 8 8 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _) (pointsTo64_entails_memRegion _ _))

theorem memRegion_a90_48_split (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 48 ⊢
      ∃∗ u0 : BitVec 64, ∃∗ u1 : BitVec 64, ∃∗ u2 : BitVec 64,
      ∃∗ u3 : BitVec 64, ∃∗ u4 : BitVec 64, ∃∗ u5 : BitVec 64,
        ((sp + 0xa90#64) ↦₆₄ u0) ∗ ((sp + 0xa98#64) ↦₆₄ u1) ∗ ((sp + 0xaa0#64) ↦₆₄ u2) ∗
        ((sp + 0xaa8#64) ↦₆₄ u3) ∗ ((sp + 0xab0#64) ↦₆₄ u4) ∗ ((sp + 0xab8#64) ↦₆₄ u5) := by
  rw [show (48 : Nat) = 8 * 6 by decide, ProofLib.memRegion_cells (sp + 0xa90#64) 6 (by decide)]
  simp only [cells, sepConj_emp, sepExists_sepConj_right, BitVec.add_assoc, BitVec.reduceAdd,
    sepConj_assoc]
  exact Entails.refl _

theorem a90_mismatch_entails_memRegion48 (sp cap ptr len x27 : BitVec 64) :
    ((sp + 0xa90#64) ↦₆₄ 0x8000000000000018#64) ∗
    ((sp + 0xa98#64) ↦₃₂ cap.extractLsb' 0 32) ∗
    ((sp + 0xa9c#64) ↦₆₄ (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)) ∗
    ((sp + 0xaa4#64) ↦₆₄ (len.extractLsb' 0 32 ++ ptr.extractLsb' 32 32)) ∗
    ((sp + 0xaac#64) ↦₆₄ ((3#64 : BitVec 64).extractLsb' 0 32 ++ len.extractLsb' 32 32)) ∗
    ((sp + 0xab4#64) ↦₆₄ (x27.extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)) ∗
    ((sp + 0xabc#64) ↦₃₂ x27.extractLsb' 32 32) ⊢
      memRegion (sp + 0xa90#64) 48 := by
  rw [ProofLib.memRegion_split (sp + 0xa90#64) 8 40 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64) 4 36 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64) 8 28 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64 + 8#64) 8 20 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64 + 8#64 + 8#64) 8 12 (by decide),
      ProofLib.memRegion_split (sp + 0xa90#64 + 8#64 + 4#64 + 8#64 + 8#64 + 8#64) 8 4 (by decide)]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo64_entails_memRegion _ _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (pointsTo32_entails_memRegion _ _))))))

theorem memRegion_370_36_split (sp : BitVec 64) :
    memRegion (sp + 0x370#64) 36 ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64, ∃∗ w2 : BitVec 64,
      ∃∗ w3 : BitVec 64, ∃∗ w4 : BitVec 32,
        ((sp + 0x370#64) ↦₆₄ w0) ∗ ((sp + 0x378#64) ↦₆₄ w1) ∗
        ((sp + 0x380#64) ↦₆₄ w2) ∗ ((sp + 0x388#64) ↦₆₄ w3) ∗
        ((sp + 0x390#64) ↦₃₂ w4) := by
  rw [sp370_36_split_eq sp]
  apply Entails.sepExists_elim; intro u20
  apply Entails.sepExists_elim; intro u18
  apply Entails.sepExists_elim; intro u10
  apply Entails.sepExists_elim; intro u8
  apply Entails.sepExists_elim; intro u0
  exact Entails.sepExists_right u0 (Entails.sepExists_right u8
    (Entails.sepExists_right u10 (Entails.sepExists_right u18
      (Entails.sepExists_right u20 (Entails.refl _)))))

theorem vecU8_unpack_3e0_64 (A : RustAlloc) (sp : BitVec 64) (bs : List (BitVec 8)) :
    vecU8 A (sp + 0x3e0#64) bs ⊢
      ∃∗ cap : BitVec 64, ∃∗ ptr : BitVec 64,
        ((sp + 0x3e0#64) ↦₆₄ cap) ∗
        ((sp + 0x3e8#64) ↦₆₄ ptr) ∗
        ((sp + 0x3f0#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
        CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf A cap ptr bs := by
  unfold vecU8 vecU8At vecHeader
    CryptoVerification.LibsignalPublicApi.MessageDecrypt.Pf.SegUntrusted.vecU8Buf
  apply Entails.sepExists_elim; intro cap
  apply Entails.sepExists_elim; intro ptr
  refine Entails.sepExists_right cap (Entails.sepExists_right ptr ?_)
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  exact Entails.refl _

theorem SepWPp.drop_ro_frame {prog : Program} {ret : BitVec 64} {s : State}
    {P D F : SepProp} {Q Qp : State → SepProp → Prop}
    (hP : P = D ∗ F)
    (h : SepWPp prog ret s F Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  exact h R (Satisfies.of_sep_right hm) hL

set_option maxHeartbeats 1200000 in
/-- Stage P2 remote-identity mismatch tail (`+0x12fc → s0.readReg64 .x30`): allocates the
70-byte `.rodata` mismatch message via `<str as ToOwned>::to_owned` (or panics on OOM), drops
state-1 `process_prekey_impl`, drops `SessionStructure` and `prevSessionsEmptyAt`, and writes
`apiDecResultAt A outPtr (.error (.protocol (.invalidMessage .preKey .badCiphertext)))`. -/
theorem stageP2_matched_mismatch_tail {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)}
    (hA : AllocContracts img.base A ext)
    (hRO : HookSat ext memcpyName CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpec)
    (hdrop_ss : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        DropSS3.dropSessionStructure3Name)
      (dropSessionStructureLocal2Spec A))
    (himg : Obj.Loads libsignalSessionImage img)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (s0 s : State)
    (sp coroPtr outPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hinv : ImgCallInv img s)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = closureEntry img ext + 0x12fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
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
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
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
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp rootStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ImgCallInv img sf)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  let roAddr : BitVec 64 :=
    img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 4860) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 4864))
  refine SepWPp.intro_rodata_mismatchRemoteIk himg hinv.1 ?_
  have h12fc := p2_seg_12fc_ext_wp img.base ext s coroPtr hb hpc hrun hx19
  refine SepWPp.bind_sepWP_steps_frame hinv h12fc (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx1_1, hx2_1, hx19_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have htr1 : s0.trace <+: s1.trace := by rw [htr1_s]; exact htr
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwned sp hroot_le)) (by sep_focus) ?_
  have hto := str_to_owned_local2_ok_ext (A := A) (b := img.base) (ext := ext) hA hRO
  refine SepWPp.call_oom_steps_frame
    (spec := strToOwnedLocal2Spec A)
    (x := (sp + 0x3e0#64, roAddr, mismatchRemoteIkStr))
    (P_spec := memRegion (sp + 0x3e0#64) 24 ∗ (roAddr ↦ᵣ mismatchRemoteIkStr) ∗ A.pool ∗
      stackAt sp strToOwnedLocal2Stack)
    hinv1 htr1 hto hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [strToOwnedLocal2Spec, Spec.allowPanicWhen]
      rw [hsp1, mismatchRemoteIkStr_length]
      rw [hsp_eq] at hx0_1
      exact Entails.pure_right ⟨hx0_1, hx1_1, hx2_1, by decide, by decide⟩ (Entails.refl _))
    (by sep_focus)
    (fun _ => Entails.refl _)
    (hexit_false := fun _ _ => rfl)
    (hoom_false := fun _ => rfl)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 hsp2_al hcs2 hinv2 => ?_)
  dsimp only [strToOwnedLocal2Spec, Spec.allowPanicWhen]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwned sp hroot_le).symm) (by sep_focus) ?_
  refine SepWPp.drop_ro_frame (D := roAddr ↦ᵣ mismatchRemoteIkStr) (by sep_focus) ?_
  refine SepWPp.weaken_frame (vecU8_unpack_3e0_64 A sp mismatchRemoteIkStr) (by sep_focus) ?_
  rw [mismatchRemoteIkStr_length]
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
  have h1310 := p2_seg_1310_to_drop_ext_wp img.base ext s2 coroPtr outPtr cap ptr 70#64
    u_a8 outPtr u_d0 b_4f2 hpc2 hrun2 hsp2_align hx19_2 hx26_2
  rw [hsp2] at h1310
  refine SepWPp.bind_sepWP_steps_frame hinv2 h1310 (by sep_focus)
    fun s3 _ hpc3 hrun3 hinv3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hvregs3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, hx26_3, _, hx28_3, _, hx30_3⟩
  have hsp3 : s3.sp = sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by rw [State.spAligned, hsp3, ← hsp2]; exact hsp2_align
  rw [dropProcessPrekeyImpl_addr_eq_ext img.base ext] at hpc3
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le)) (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hinv3 (drop_process_prekey_impl_state1_ok_ext (b := img.base) (ext := ext))
    hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [dropProcessPrekeyImplState1Spec]; rw [hsp3, coro_398_add_15a])
    hx0_3 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hinv4 => ?_)
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
  have h1698 := p2_seg_1698_mismatch_to_3588_ext_wp img.base ext s4 coroPtr outPtr cap ptr 70#64
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390 b_390 hb hpc4 hrun4 hsp4_align
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx28_4
  rw [hsp4] at h1698
  refine SepWPp.bind_sepWP_steps_frame hinv4 h1698 (by sep_focus)
    fun s5 _ hpc5 hrun5 hinv5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hvregs5, hx19_5, hx22_5, hx25_5, hx26_5, hx28_5, _, _⟩
  have hvregs5_s : calleeSavedVRegs s5 = calleeSavedVRegs s :=
    hvregs5.trans hvregs4_s
  have hsp5 : s5.sp = sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5, ← hsp_eq]; exact hsp_align
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_dropSS sp hroot_le)) (by sep_focus) ?_
  have hdrop_rec := closure_err_drop_record_tail_ext_ok (A := A) (img := img) (ext := ext)
    (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)
    hA hdrop_ss s0 s5 sp coroPtr outPtr 0x8000000000000018#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((70#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (70#64 : BitVec 64).extractLsb' 32 32)
    ((s4.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    (cap.extractLsb' 0 32) ((s4.readReg64 .x27).extractLsb' 32 32) b_2c0
    g recG recSt hinv5 hsp5 (Nat.le_trans (by decide) hsp_root)
    hpc5 hrun5 hsp5_align hx19_5 hx22_5 hx25_5 hx26_5 hx28_5
  refine SepWPp.bind_sepWPp_steps_frame hdrop_rec (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf_5, hcsf, hvregsf_5, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, hspf,
    htrf_5.trans (htr5_4.trans (htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)))),
    hcsf, hvregsf_5.trans hvregs5_s, hinvf⟩
  refine Entails.trans (entails_replace_sub (Entails.of_eq (stack_root_to_dropSS sp hroot_le).symm)
    (by sep_focus) rfl) ?_
  have hout := invalidMessage_prekey_out_entails_3 A outPtr cap ptr (s4.readReg64 .x27)
    mismatchRemoteIkStr
  rw [mismatchRemoteIkStr_length] at hout
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

/-! ## `AllocContractsX` and stacked `memcpyRO` generalizations -/

theorem stack_root_to_strToOwnedX (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack)
        (rootStack - strToOwnedLocal2StackWith extHookStack) ∗
        stackAt sp (strToOwnedLocal2StackWith extHookStack) :=
  stackAt_split_of_le sp rootStack (strToOwnedLocal2StackWith extHookStack) (by decide) hn

set_option maxHeartbeats 1200000 in
/-- Stage P2 remote-identity mismatch tail (`+0x12fc → s0.readReg64 .x30`) under
`AllocContractsX` and stacked `memcpyRO`. -/
theorem stageP2_matched_mismatch_tail_x {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} {roStack dssStack : Nat}
    (hA : AllocContractsX img A ext)
    (hro_le : roStack ≤ extHookStack)
    (hRO : HookSat ext memcpyName
      (CryptoVerification.SpqrV1.Alloc.sessionMemcpyRegionROSpecWithStack roStack))
    (hdss : dssStack ≤ rootStack)
    (hdrop_ss : subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr DropSS3.dropSessionStructure3Name)
      ((dropSessionStructureLocal2SpecWithStack dssStack A).inImage img))
    (himg : Obj.Loads libsignalSessionImage img)
    (hb : img.base &&& 0xfff#64 = 0#64)
    (s0 s : State)
    (sp coroPtr outPtr u_a8 u_d0 : BitVec 64)
    (b_4f2 b_390 b_2c0 : BitVec 8)
    (g : RecordGhost) (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hinv : ImgCallInv img s)
    (htr : s0.trace <+: s.trace)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = closureEntry img ext + 0x12fc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx26 : s.readReg64 .x26 = outPtr)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (tripleRatchetProgAtExt img.base ext) (s0.readReg64 .x30) s
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
       ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
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
          ((img.base + bv% (ls_sym% "core::unicode::unicode_data::white_space::WHITESPACE_MAP" + 256)) ↦₆₄ 0#64) ∗
          decryptPrekeySavedRegsAt (sp + 0xcd0#64) s0 ∗
          A.pool ∗
          stackAt sp rootStack) ∧
        sf.sp = sp + 0xcd0#64 ∧
        sf.trace = s.trace ∧
        ClosureCalleeSaved s0 sf ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        ImgCallInv img sf)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  let roAddr : BitVec 64 :=
    img.base + bv% (ls_xref% (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 4860) (ls_off% "libsignal_protocol::session_management::message_decrypt_prekey::<libsignal_cli_handshake::Coins>::{closure#0}" + 4864))
  refine SepWPp.intro_rodata_mismatchRemoteIk himg hinv.1 ?_
  have h12fc := p2_seg_12fc_ext_wp img.base ext s coroPtr hb hpc hrun hx19
  refine SepWPp.bind_sepWP_steps_frame hinv h12fc (by sep_focus)
    fun s1 _ hpc1 hrun1 hinv1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx0_1, hx1_1, hx2_1, hx19_1, hx25_1, hx26_1, _, hx28_1, _, hx30_1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp_eq
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_align
  have htr1 : s0.trace <+: s1.trace := by rw [htr1_s]; exact htr
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwnedX sp hroot_le)) (by sep_focus) ?_
  have hto := str_to_owned_local2_ok_ext_x hA hro_le hRO
  refine SepWPp.call_oom_steps_frame
    (spec := (strToOwnedLocal2SpecWithStack extHookStack A).inImage img)
    (x := (sp + 0x3e0#64, roAddr, mismatchRemoteIkStr))
    (P_spec := memRegion (sp + 0x3e0#64) 24 ∗ (roAddr ↦ᵣ mismatchRemoteIkStr) ∗ A.pool ∗
      stackAt sp (strToOwnedLocal2StackWith extHookStack))
    hinv1 htr1 hto hpc1 hrun1 hsp1_al hx30_1
    (by
      dsimp only [Spec.inImage, strToOwnedLocal2SpecWithStack, Spec.allowPanicWhen]
      rw [hsp1, mismatchRemoteIkStr_length]
      rw [hsp_eq] at hx0_1
      exact Entails.pure_right hinv1
        (Entails.pure_right ⟨hx0_1, hx1_1, hx2_1, by decide, by decide⟩ (Entails.refl _)))
    (by sep_focus)
    (fun _ => by dsimp only [Spec.inImage]; exact Entails.refl _)
    (hnext := fun s2 _ hpc2 hrun2 hsp2_1 hsp2_al hcs2 hinv2 => ?_)
  dsimp only [Spec.inImage, strToOwnedLocal2SpecWithStack, Spec.allowPanicWhen]
  rw [hsp1, sepConj_assoc]
  refine SepWPp.pure_elim fun htr2_1 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_strToOwnedX sp hroot_le).symm) (by sep_focus) ?_
  refine SepWPp.drop_ro_frame (D := roAddr ↦ᵣ mismatchRemoteIkStr) (by sep_focus) ?_
  refine SepWPp.weaken_frame (vecU8_unpack_3e0_64 A sp mismatchRemoteIkStr) (by sep_focus) ?_
  rw [mismatchRemoteIkStr_length]
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
  have h1310 := p2_seg_1310_to_drop_ext_wp img.base ext s2 coroPtr outPtr cap ptr 70#64
    u_a8 outPtr u_d0 b_4f2 hpc2 hrun2 hsp2_align hx19_2 hx26_2
  rw [hsp2] at h1310
  refine SepWPp.bind_sepWP_steps_frame hinv2 h1310 (by sep_focus)
    fun s3 _ hpc3 hrun3 hinv3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hvregs3, hx0_3, hx19_3, hx20_3, hx21_3, hx22_3,
    hx23_3, hx24_3, hx25_3, hx26_3, _, hx28_3, _, hx30_3⟩
  have hsp3 : s3.sp = sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by rw [State.spAligned, hsp3, ← hsp2]; exact hsp2_align
  rw [dropProcessPrekeyImpl_addr_eq_ext img.base ext] at hpc3
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le)) (by sep_focus) ?_
  refine SepWPp.call_nopanic_steps_frame
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hinv3 (drop_process_prekey_impl_state1_ok_ext (b := img.base) (ext := ext))
    hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [dropProcessPrekeyImplState1Spec]; rw [hsp3, coro_398_add_15a])
    hx0_3 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hinv4 => ?_)
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
  have h1698 := p2_seg_1698_mismatch_to_3588_ext_wp img.base ext s4 coroPtr outPtr cap ptr 70#64
    u250 u258 u260 u268 u270 u278 ua90 ua98 uaa0 uaa8 uab0 uab8
    u370 u378 u380 u388 u390 b_390 hb hpc4 hrun4 hsp4_align
    hx19_4 hx20_4 hx21_4 hx22_4 hx23_4 hx24_4 hx25_4 hx28_4
  rw [hsp4] at h1698
  refine SepWPp.bind_sepWP_steps_frame hinv4 h1698 (by sep_focus)
    fun s5 _ hpc5 hrun5 hinv5 hregs5 => ?_
  rcases hregs5 with ⟨hsp5_4, htr5_4, hvregs5, hx19_5, hx22_5, hx25_5, hx26_5, hx28_5, _, _⟩
  have hvregs5_s : calleeSavedVRegs s5 = calleeSavedVRegs s :=
    hvregs5.trans hvregs4_s
  have hsp5 : s5.sp = sp := hsp5_4
  have hsp5_align : (s5.sp &&& 15#64 == 0#64) = true := by rw [hsp5, ← hsp_eq]; exact hsp_align
  have hdrop_rec := closure_err_drop_record_tail_ext_x_ok (A := A) (img := img) (ext := ext)
    (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0)
    hA hdss hdrop_ss s0 s5 sp coroPtr outPtr 0x8000000000000018#64
    (ptr.extractLsb' 0 32 ++ cap.extractLsb' 32 32)
    ((70#64 : BitVec 64).extractLsb' 0 32 ++ ptr.extractLsb' 32 32)
    ((3#64 : BitVec 64).extractLsb' 0 32 ++ (70#64 : BitVec 64).extractLsb' 32 32)
    ((s4.readReg64 .x27).extractLsb' 0 32 ++ (3#64 : BitVec 64).extractLsb' 32 32)
    (cap.extractLsb' 0 32) ((s4.readReg64 .x27).extractLsb' 32 32) b_2c0
    g recG recSt hinv5 hsp5 hsp_root
    hpc5 hrun5 hsp5_align hx19_5 hx22_5 hx25_5 hx26_5 hx28_5
  refine SepWPp.bind_sepWPp_steps_frame hdrop_rec (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf_5, hcsf, hvregsf_5, hinvf⟩ => ?_
  refine SepWPp.done hpcf hrunf ⟨?_, hspf,
    htrf_5.trans (htr5_4.trans (htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)))),
    hcsf, hvregsf_5.trans hvregs5_s, hinvf⟩
  have hout := invalidMessage_prekey_out_entails_3 A outPtr cap ptr (s4.readReg64 .x27)
    mismatchRemoteIkStr
  rw [mismatchRemoteIkStr_length] at hout
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
