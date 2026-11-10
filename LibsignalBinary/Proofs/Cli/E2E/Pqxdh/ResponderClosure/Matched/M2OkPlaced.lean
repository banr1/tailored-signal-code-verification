/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M1Placed
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2TailPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsCPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2StepsDPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2ErrStepsAPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Matched.M2Ok
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.RespClosureCodeSym
public import LibsignalBinary.Proofs.PublicApi.StoreKit.Placed
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.Kits.StageP1Comb
import LibsignalBinary.Proofs.E2E.Bin.Hooks
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3b2
import LibsignalBinary.Proofs.TripleRatchet.Glue
import ProofLib.SepLogic.WPp
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.TripleRatchet.ConsumeMessageKeyTransfer.CtEqRO

/-!
# Relocatable Stage P2 Matched-Session `Some ik` Check and Match Branch

Relocatable `[LibsignalPlacement]` counterpart of `Matched.M2Ok` on Block `518` (`lsProg_518 ext`,
`(blkPl_518).base = lsmpl.base 518`).
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
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSession CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet.Glue
open CryptoVerification.LibsignalTripleRatchet.FromRecordCallees
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalPublicApi CryptoVerification.LibsignalPublicApiRepr
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageDecrypt
open CryptoVerification.E2E.Bin
open CryptoVerification.E2E.Pqxdh.ResponderStore
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4 (entails_replace_sub)
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Kits
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
open CryptoVerification.SignalSession

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

theorem coro_298_split_two_placed [LibsignalPlacement] (coroPtr w : BitVec 64) :
    ((coroPtr + 0x298#64) ↦₆₄ (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| (w <<< 32))) ⊢
      ∃∗ hi : BitVec 32,
        ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
        ((coroPtr + 0x29c#64) ↦₃₂ hi) :=
  coro_298_split_two coroPtr w

theorem memRegion_32_eq_chunks32_placed [LibsignalPlacement] (base : BitVec 64) :
    memRegion base 32 =
      ∃∗ w0 : BitVec 32, ∃∗ h1 : BitVec 16,
      ∃∗ q2 : BitVec 64, ∃∗ q3 : BitVec 64, ∃∗ q4 : BitVec 64, ∃∗ h5 : BitVec 16,
        chunks32At base w0 h1 q2 q3 q4 h5 :=
  memRegion_32_eq_chunks32 base

theorem chunks32_entails_memRegion_32_placed [LibsignalPlacement] (base : BitVec 64)
    (w0 : BitVec 32) (h1 : BitVec 16) (q2 q3 q4 : BitVec 64) (h5 : BitVec 16) :
    chunks32At base w0 h1 q2 q3 q4 h5 ⊢ memRegion base 32 :=
  chunks32_entails_memRegion_32 base w0 h1 q2 q3 q4 h5

theorem rem34_bytes_entails_memRegion34_placed [LibsignalPlacement] (sp : BitVec 64) (b0 b1 : BitVec 8)
    (w0 : BitVec 32) (h1 : BitVec 16) (q2 q3 q4 : BitVec 64) (h5 : BitVec 16) :
    ((sp + 0x3e0#64) ↦₈ b0) ∗ ((sp + 0x3e1#64) ↦₈ b1) ∗
      chunks32At (sp + 0x3e2#64) w0 h1 q2 q3 q4 h5 ⊢
      memRegion (sp + 0x3e0#64) 34 :=
  rem34_bytes_entails_memRegion34 sp b0 b1 w0 h1 q2 q3 q4 h5

theorem memRegion_34_split_32_2_placed [LibsignalPlacement] (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 34 =
      memRegion (sp + 0x3e0#64) 32 ∗ memRegion (sp + 0x400#64) 2 :=
  memRegion_34_split_32_2 sp

theorem memRegion_34_split_24_10_placed [LibsignalPlacement] (sp : BitVec 64) :
    memRegion (sp + 0x3e0#64) 34 =
      memRegion (sp + 0x3e0#64) 24 ∗ memRegion (sp + 0x3f8#64) 10 :=
  memRegion_34_split_24_10 sp

theorem memRegion_920_6_split_placed [LibsignalPlacement] (sp : BitVec 64) :
    memRegion (sp + 0x920#64) 6 =
      ∃∗ u_920 : BitVec 32, ∃∗ u_924 : BitVec 16,
        ((sp + 0x920#64) ↦₃₂ u_920) ∗ ((sp + 0x924#64) ↦₁₆ u_924) :=
  memRegion_920_6_split sp

theorem memRegion_920_6_join_placed [LibsignalPlacement] (sp : BitVec 64)
    (u_920 : BitVec 32) (u_924 : BitVec 16) :
    ((sp + 0x920#64) ↦₃₂ u_920) ∗ ((sp + 0x924#64) ↦₁₆ u_924) ⊢
      memRegion (sp + 0x920#64) 6 :=
  memRegion_920_6_join sp u_920 u_924

theorem memRegion_a90_48_split_10_38_placed [LibsignalPlacement] (sp : BitVec 64) :
    memRegion (sp + 0xa90#64) 48 =
      (∃∗ u_a90 : BitVec 64, ∃∗ u_a98 : BitVec 16,
        ((sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((sp + 0xa98#64) ↦₁₆ u_a98)) ∗
      memRegion (sp + 0xa9a#64) 38 :=
  memRegion_a90_48_split_10_38 sp

theorem memRegion_a90_48_join_10_38_placed [LibsignalPlacement] (sp : BitVec 64)
    (u_a90 : BitVec 64) (u_a98 : BitVec 16) :
    ((sp + 0xa90#64) ↦₆₄ u_a90) ∗ ((sp + 0xa98#64) ↦₁₆ u_a98) ∗
      memRegion (sp + 0xa9a#64) 38 ⊢
      memRegion (sp + 0xa90#64) 48 :=
  memRegion_a90_48_join_10_38 sp u_a90 u_a98

theorem stack_root_to_pkEq_placed [LibsignalPlacement] (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - 64) ∗
      stackFrameFor libsignalSessionImage
        "<libsignal_core::curve::PublicKey as core::cmp::PartialEq>::eq" sp ∗
      stackFrameFor libsignalSessionImage
        "<[u8] as subtle::ConstantTimeEq>::ct_eq" (sp - 16#64) :=
  stack_root_to_pkEq sp hn

theorem stack_root_to_pkEq_mem_placed (sp : BitVec 64) (hn : rootStack ≤ 2 ^ 64) :
    stackAt sp rootStack =
      memRegion (sp - BitVec.ofNat 64 rootStack) (rootStack - 64) ∗
      memRegion (sp - 16#64) 16 ∗
      memRegion (sp - 16#64 - 48#64) 48 := by
  rw [stackAt_split_of_le sp rootStack 64 (by decide) hn]
  unfold stackAt
  have h64 : memRegion (sp - 64#64) 64 =
      memRegion (sp - 16#64) 16 ∗ memRegion (sp - 16#64 - 48#64) 48 := by
    have ha : sp - 16#64 - 48#64 = sp - 64#64 := by bv_omega
    rw [ha, ProofLib.memRegion_split' (b := sp - 64#64) (n := 48) (k := 16)
      (b' := sp - 16#64) rfl (by bv_omega) (by decide)]
    ac_rfl
  rw [h64]

theorem remoteIdentityOkAt_none_eq_placed [LibsignalPlacement] (sp : BitVec 64) :
    Getters.remoteIdentityOkAt (sp + 0x3e0#64) none =
      ((sp + 0x3e0#64) ↦₈ 0#8) ∗ ((sp + 0x3e1#64) ↦₈ 0#8) ∗
      memRegion (sp + 0x3e2#64) 32 :=
  remoteIdentityOkAt_none_eq sp

theorem remoteIdentityOkAt_some_eq_placed [LibsignalPlacement] (sp : BitVec 64) (ik : IdentityKey) :
    Getters.remoteIdentityOkAt (sp + 0x3e0#64) (some ik) =
      ((sp + 0x3e0#64) ↦₈ 0#8) ∗ ((sp + 0x3e1#64) ↦₈ 1#8) ∗
      ((sp + 0x3e2#64) ↦ₛ ik.publicKey.bytes.toList) :=
  remoteIdentityOkAt_some_eq sp ik

def stageP2MatchedOk10ccPrePlaced [LibsignalPlacement] (A : RustAlloc)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))) : SepProp :=
  sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
  ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
  ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
  ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
  ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
  ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
  ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
  ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
  ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
  ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
  ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
  ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
  ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
  ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
  ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
  ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
  stackAt sp rootStack

def stageP2MatchedOk1778PostPlaced [LibsignalPlacement] (A : RustAlloc)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388 v_d0 : BitVec 64)
    (msgVerByte : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8))) : SepProp :=
  ∃∗ opkHi : BitVec 32, ∃∗ kyberPacked : BitVec 64,
    sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
    ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
    ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
    ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
    ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗ ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
    ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗ ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
    ((coroPtr + 0x390#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
    ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
    ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
    ((sp + 0x90#64) ↦₆₄ v_388) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
    ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗ ((sp + 0xa8#64) ↦₆₄ v_330) ∗
    ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
    ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
    ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
    ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗ ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
    ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗ ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
    ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗ ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
    stackAt sp rootStack

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P2 remote-identity match tail
(`(blkPl_518).base + 0x10cc → +0x1778` when `x0 = 1#64`). -/
theorem stageP2_matched_ok_10cc_to_1778_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 _u_a0 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x10cc#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx26 : s.readReg64 .x26 = outPtr) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x1778#64) s
      (sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗ ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗ ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗ ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗ ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗ ((sp + 0x88#64) ↦₆₄ u_88) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗ ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗ ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗ ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗ ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗ ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗ ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       stackAt sp rootStack)
      (fun s4 P_f =>
        (P_f ⊢
          ∃∗ opkHi : BitVec 32, ∃∗ kyberPacked : BitVec 64,
            sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
            ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗ ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
            ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗ cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗ ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
            ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗ ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
            ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗ ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗ ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
            ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗ ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((sp + 0x90#64) ↦₆₄ v_388) ∗ ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗ ((sp + 0xa8#64) ↦₆₄ v_330) ∗
            ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗ ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗ ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗ ((sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗ ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
            ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗ ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗ ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            stackAt sp rootStack) ∧
        s4.sp = sp ∧
        s4.trace = s.trace ∧
        s4.readReg64 .x19 = coroPtr ∧
        s4.readReg64 .x27 = sp + 0x370#64 ∧
        s4.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s4 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem)
      Qp := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  have h10cc := p2_seg_10cc_match_placed_wp ext s coroPtr u_a8 hpc hrun hsp_align hx0 hx19
  rw [hsp_eq] at h10cc
  refine bind_sepWP_lscro_steps_m2_placed hcro h10cc (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx20_1, _, hx23_1, _, hx26_1, _, _, hx29_1, _⟩
  have hsp1 : s1.sp = sp := hsp1_s
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hx26_1' : s1.readReg64 .x26 = outPtr := hx26_1.trans hx26
  have h1648 := p2_err_tail_a_placed_wp ext s1 coroPtr 0xfffffffffffffffe#64 outPtr b_4f2
    (by decide) hpc1 hrun1 hsp1_align hx19_1 hx20_1 hx26_1'
  rw [hsp1] at h1648
  refine bind_sepWP_lscro_steps_m2_placed hcro1 h1648 (by sep_focus)
    fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, hx0_2, hx19_2, hx20_2, _, hx23_2, hx24_2, _, _, _, _, hx29_2, hx30_2, hvregs2_1⟩
  have hsp2 : s2.sp = sp := hsp2_1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned] using hsp2_align
  rw [hx23_1] at hx23_2 hx24_2
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le)) (by sep_focus) ?_
  refine call_lscro_nopanic_m2_placed
    (spec := dropProcessPrekeyImplState1Spec)
    (x := coroPtr + 0x398#64)
    (T := ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗ cells (sp - 48#64) 6)
    hcro2
    (StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
      (drop_process_prekey_impl_state1_placed_ok_at (callerProg := lsProg_518 (Rust.withPanics ext))))
    hpc2 hrun2 hsp2_al hx30_2
    (by dsimp only [dropProcessPrekeyImplState1Spec]; rw [hsp2, coro_398_add_15a])
    hx0_2 (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s3 _ hpc3 hrun3 hsp3_2 _ hcs3 hcro3 => ?_)
  dsimp only [dropProcessPrekeyImplState1Spec]
  rw [hsp2, coro_398_add_15a, sepConj_assoc]
  refine SepWPp.pure_elim fun htr3_2 => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_cells48 sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs3 with ⟨hx19_cs3, hx20_cs3, _, _, hx23_cs3, hx24_cs3, _, _, _, _, hx29_cs3, hvregs_cs3⟩
  have hvregs3_s : calleeSavedVRegs s3 = calleeSavedVRegs s :=
    hvregs_cs3.trans (hvregs2_1.trans (congrArg VRegFile.calleeSaved hvregs1))
  have hsp3 : s3.sp = sp := hsp3_2.trans hsp2
  have hsp3_align : (s3.sp &&& 15#64 == 0#64) = true := by rw [hsp3, ← hsp_eq]; exact hsp_align
  have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
  have hx20_3 : s3.readReg64 .x20 = 0xfffffffffffffffe#64 := hx20_cs3.trans hx20_2
  have hx23_3 : s3.readReg64 .x23 = (2#32 : BitVec 32).zeroExtend 64 := hx23_cs3.trans hx23_2
  have hx24_3 : s3.readReg64 .x24 =
      (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| ((s1.readReg64 .x22) <<< 32)) :=
    hx24_cs3.trans hx24_2
  obtain ⟨R_ss, hss_fwd, hss_bwd⟩ := sessionStateAt_split_localIk_cap A (coroPtr + 0xf8#64) recG recSt
  refine SepWPp.weaken_frame hss_fwd (by sep_focus) ?_
  sep_norm
  refine SepWPp.pure_elim fun hcap_lt => ?_
  conv => arg 4; rw [coro_250_cells6_eq coroPtr]
  sep_norm
  refine SepWPp.exists_elim fun u250 => SepWPp.exists_elim fun u258 =>
    SepWPp.exists_elim fun u260 => SepWPp.exists_elim fun u268 =>
    SepWPp.exists_elim fun u270 => SepWPp.exists_elim fun u278 => ?_
  conv => arg 4; rw [pointsTo64_split32 (coroPtr + 0x268#64) u268]
  sep_norm
  have hss0_ne : recG.localIk.cap + 1#64 ≠ 0#64 := by bv_omega
  have hseg6f := p2_seg6f_placed_wp ext s3 coroPtr msgPtr remoteAddrPtr localAddrPtr
    (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| ((s1.readReg64 .x22) <<< 32))
    (s3.readReg64 .x22) recG.localIk.cap v_330 v_388
    u250 u258 u260 u270 u278 u_298 u_2a0
    u_80 u_88 u_90 (coroPtr + 0x4f2#64) 0#64 u_b0 v_d0
    u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8
    2#32 (u268.extractLsb' 0 32) (u268.extractLsb' 32 32) u_2a8 u_b8
    msgVerByte b_390 b_3ac hss0_ne (opkPacked_two_mask (s1.readReg64 .x22))
    hpc3 hrun3 hsp3_align hx19_3 hx20_3 rfl hx23_3 hx24_3
  rw [hsp3] at hseg6f
  refine ret_sepWP_lscro_steps_m2_placed hcro3 hseg6f (by sep_focus)
    fun s4 _ _ _ hcro4 hregs4 => ?_
  rcases hregs4 with ⟨hsp4_3, htr4_3, _, _, _, _, hx19_4, _, _, _, _, _, _, hx27_4, _, hx29_4, hvregs4_3⟩
  refine ⟨?_, hsp4_3,
    htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)),
    hx19_4, hx27_4,
    hx29_4.trans (hx29_cs3.trans (hx29_2.trans hx29_1)),
    hvregs4_3.trans hvregs3_s, hcro4⟩
  refine Entails.trans (entails_replace_sub hss_bwd (by sep_focus) rfl) ?_
  have h268_join :
      ((coroPtr + 0x268#64) ↦₃₂ v_d0.truncate 32) ∗
      ((coroPtr + 0x26c#64) ↦₃₂ (s3.readReg64 (Reg.gpr 11#5)).truncate 32) ⊢
        ((coroPtr + 0x268#64) ↦₆₄ ((s3.readReg64 (Reg.gpr 11#5)).truncate 32 ++ v_d0.truncate 32)) := by
    have hlo : ((s3.readReg64 (Reg.gpr 11#5)).truncate 32 ++ v_d0.truncate 32).extractLsb' 0 32 =
        v_d0.truncate 32 := by bv_bits
    have hhi : ((s3.readReg64 (Reg.gpr 11#5)).truncate 32 ++ v_d0.truncate 32).extractLsb' 32 32 =
        (s3.readReg64 (Reg.gpr 11#5)).truncate 32 := by bv_bits
    rw [pointsTo64_split32, hlo, hhi]
    simp only [BitVec.add_assoc, BitVec.reduceAdd]
    exact Entails.refl _
  refine Entails.trans (entails_replace_sub h268_join (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub
    (coro_250_6w_entails_cells6 coroPtr 0xfffffffffffffffe#64
      (((2#64 : BitVec 64).setWidth 32).zeroExtend 64 ||| ((s1.readReg64 .x22) <<< 32))
      (s3.readReg64 .x22)
      ((s3.readReg64 (Reg.gpr 11#5)).truncate 32 ++ v_d0.truncate 32)
      v_330 v_388)
    (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub
    (coro_298_split_two coroPtr (s1.readReg64 .x22))
    (by sep_focus) rfl) ?_
  sep_norm
  refine Entails.sepExists_elim fun opkHi => Entails.sepExists_right opkHi ?_
  refine Entails.sepExists_right (s3.readReg64 .x22) ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P2 remote-identity `Some ik` check
(`(blkPl_518).base + 0x094c → +0x10cc`). -/
theorem stageP2_matched_094c_some_to_10cc_placed [LibsignalPlacement]
    {ext : String → Option (State → State)} {Qp : State → SepProp → Prop}
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook)
    (s : State)
    (sp coroPtr outPtr msgPtr : BitVec 64)
    (remIdKey ik : IdentityKey)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x10cc#64) s
      (Getters.remoteIdentityOkAt (sp + 0x3e0#64) (some ik) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       stackAt sp rootStack)
      (fun s4 P_f =>
        (P_f ⊢
          memRegion (sp + 0x3e0#64) 34 ∗
          ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
          ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
          ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
          memRegion (sp + 0x920#64) 6 ∗
          memRegion (sp + 0xa90#64) 48 ∗
          stackAt sp rootStack) ∧
        s4.sp = sp ∧
        s4.trace = s.trace ∧
        s4.readReg64 .x0 = (if remIdKey.publicKey == ik.publicKey then 1#64 else 0#64) ∧
        s4.readReg64 .x19 = coroPtr ∧
        s4.readReg64 .x25 = sp + 0x210#64 ∧
        s4.readReg64 .x26 = outPtr ∧
        s4.readReg64 .x28 = sp + 0xa90#64 ∧
        s4.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s4 = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s4.mem)
      Qp := by
  have hroot_le : rootStack ≤ 2 ^ 64 := Nat.le_trans hsp_root (Nat.le_of_lt sp.isLt)
  let bs := ik.publicKey.bytes.toList
  have hbs_len : bs.length = 32 := ik.publicKey.bytes.property
  let w0 := pack32LE (bs.take 4)
  let h1 := pack16LE ((bs.drop 4).take 2)
  let q2 := pack64LE ((bs.drop 6).take 8)
  let q3 := pack64LE ((bs.drop 14).take 8)
  let q4 := pack64LE ((bs.drop 22).take 8)
  let h5 := pack16LE (bs.drop 30)
  conv => arg 4; rw [remoteIdentityOkAt_some_eq sp ik,
      show ik.publicKey.bytes.toList = bs from rfl,
      pointsToBytes_32_eq_chunks32 (sp + 0x3e2#64) bs hbs_len,
      memRegion_920_6_split sp, memRegion_a90_48_split_10_38 sp]
  dsimp only [chunks32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_norm
  refine SepWPp.exists_elim fun u_920 => SepWPp.exists_elim fun u_924 =>
    SepWPp.exists_elim fun u_a90 => SepWPp.exists_elim fun u_a98 => ?_
  have h094c := p2_seg_094c_ok_placed_wp ext s coroPtr outPtr hpc hrun hsp_align hx19
  rw [hsp_eq] at h094c
  refine bind_sepWP_lscro_steps_m2_placed hcro h094c (by sep_focus)
    fun s1 _ hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hvregs1, hx19_1, hx21_1, _, _, hx25_1, hx26_1, _, hx28_1, hx29_1, _⟩
  have hsp1 : s1.sp = sp := hsp1_s
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have hx21_1' : s1.readReg64 .x21 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx21_1.trans hx21
  have h1064 := p2_seg_1064_some_load_placed_wp ext s1 coroPtr q2 q3 q4 u_a90
    w0 u_920 h1 h5 u_924 u_a98 hpc1 hrun1 hsp1_align hx19_1 hx21_1'
  rw [hsp1] at h1064
  refine bind_sepWP_lscro_steps_m2_placed hcro1 h1064 (by sep_focus)
    fun s2 _ hpc2 hrun2 hcro2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2_1, htr2_1, hvregs2, hx8_2, hx9_2, hx19_2, hx21_2, hx25_2, hx26_2, _, hx28_2, hx29_2, _⟩
  have hsp2 : s2.sp = sp := hsp2_1
  have hsp2_align : (s2.sp &&& 15#64 == 0#64) = true := by rw [hsp2, ← hsp_eq]; exact hsp_align
  have hx21_2' : s2.readReg64 .x21 = s2.sp + 0x370#64 := by rw [hsp2]; exact hx21_2
  have hrepack34 :
      ((sp + 0x3e0#64) ↦₈ 0#8) ∗ ((sp + 0x3e1#64) ↦₈ 1#8) ∗
        chunks32At (sp + 0x3e2#64) w0 h1 q2 q3 q4 h5 ⊢
        memRegion (sp + 0x3e0#64) 32 ∗ memRegion (sp + 0x400#64) 2 := by
    rw [← memRegion_34_split_32_2 sp]
    exact rem34_bytes_entails_memRegion34 sp 0#8 1#8 w0 h1 q2 q3 q4 h5
  dsimp only [chunks32At] at hrepack34
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hrepack34
  refine SepWPp.weaken_frame hrepack34 (by sep_focus) ?_
  conv => arg 4; rw [memRegion_32_eq_chunks32 (sp + 0x3e0#64)]
  dsimp only [chunks32At]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  sep_norm
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 =>
    SepWPp.exists_elim fun d4 => SepWPp.exists_elim fun d5 => ?_
  have h1094 := p2_seg_1094_some_store_placed_wp ext s2 coroPtr msgPtr q2 q3 q4 d2 d3 d4
    w0 d0 h1 h5 d1 d5 hpc2 hrun2 hsp2_align hx8_2 hx9_2 hx19_2 hx21_2'
  rw [hsp2] at h1094
  refine bind_sepWP_lscro_steps_m2_placed hcro2 h1094 (by sep_focus)
    fun s3 _ hpc3 hrun3 hcro3 hregs3 => ?_
  rcases hregs3 with ⟨hsp3_2, htr3_2, hvregs3, hx0_3, hx1_3, hx19_3, _, hx25_3, hx26_3, _, hx28_3, hx29_3, hx30_3⟩
  have hsp3 : s3.sp = sp := hsp3_2
  have hsp3_al : s3.spAligned = true := by
    simpa only [State.spAligned, hsp3, ← hsp_eq] using hsp_align
  have hfold_bs :
      ((sp + 0x3e0#64) ↦₃₂ w0) ∗ ((sp + 0x3e4#64) ↦₁₆ h1) ∗
      ((sp + 0x3e6#64) ↦₆₄ q2) ∗ ((sp + 0x3ee#64) ↦₆₄ q3) ∗
      ((sp + 0x3f6#64) ↦₆₄ q4) ∗ ((sp + 0x3fe#64) ↦₁₆ h5) =
      ((sp + 0x3e0#64) ↦ₛ ik.publicKey.bytes.toList) := by
    rw [show ik.publicKey.bytes.toList = bs from rfl,
        pointsToBytes_32_eq_chunks32 (sp + 0x3e0#64) bs hbs_len]
    dsimp only [chunks32At, w0, h1, q2, q3, q4, h5]
    simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  refine SepWPp.weaken_frame (Entails.of_eq hfold_bs) (by sep_focus) ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkEq_mem_placed sp hroot_le)) (by sep_focus) ?_
  have hpkeq := StoreKit.subroutine_ok_withLsCodeRoLoaded_of_withLsCodeLoaded
    (ls_subroutine_ok_of_block (callerProg := lsProg_518 (Rust.withPanics ext))
      (j := 212) (entry := lsmpl.base 212)
      (_root_.CryptoVerification.LibsignalTripleRatchet.ConsumeMessageKeyTransfer.publicKey_eq_mem_placed_ok h_bb)
      (by decide))
  refine call_lscro_nopanic_m2_placed
    (spec := _root_.CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec)
    (x := (msgPtr + 0xc8#64, remIdKey.publicKey, sp + 0x3e0#64, ik.publicKey, sp))
    (T := ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
      ((sp + 0x3e0#64) ↦ₛ ik.publicKey.bytes.toList) ∗
      memRegion (sp - 16#64) 16 ∗
      memRegion (sp - 16#64 - 48#64) 48)
    hcro3 hpkeq hpc3 hrun3 hsp3_al hx30_3
    (by dsimp only [_root_.CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec])
    (And.intro hx0_3 (And.intro hx1_3 hsp3)) (by sep_focus)
    (hoom_false := fun _ => rfl)
    (hnext := fun s4 _ hpc4 hrun4 hsp4_3 _ hcs4 hcro4 => ?_)
  dsimp only [_root_.CryptoVerification.LibsignalSession.FindReceiverChainIndex.publicKeyEqMemSpec]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hx0_4, htr4_3⟩ => ?_
  refine SepWPp.weaken_frame (Entails.of_eq (stack_root_to_pkEq_mem_placed sp hroot_le).symm) (by sep_focus) ?_
  rcases hcs4 with ⟨hx19_cs4, _, _, _, _, _, hx25_cs4, hx26_cs4, _, hx28_cs4, hx29_cs4, hvregs_cs4⟩
  refine SepWPp.done hpc4 hrun4 ⟨?_, hsp4_3.trans hsp3,
    htr4_3.trans (htr3_2.trans (htr2_1.trans htr1_s)),
    hx0_4, hx19_cs4.trans hx19_3,
    hx25_cs4.trans (hx25_3.trans (hx25_2.trans (hx25_1.trans hx25))),
    hx26_cs4.trans (hx26_3.trans (hx26_2.trans hx26_1)),
    hx28_cs4.trans (hx28_3.trans (hx28_2.trans (hx28_1.trans hx28))),
    hx29_cs4.trans (hx29_3.trans (hx29_2.trans hx29_1)),
    hvregs_cs4.trans (congrArg VRegFile.calleeSaved (hvregs3.trans (hvregs2.trans hvregs1))),
    hcro4⟩
  have hbs34 :
      ((sp + 0x3e0#64) ↦ₛ ik.publicKey.bytes.toList) ∗ memRegion (sp + 0x400#64) 2 ⊢
        memRegion (sp + 0x3e0#64) 34 := by
    rw [memRegion_34_split_32_2 sp]
    refine sepConj_mono_left ?_
    simpa only [hbs_len] using ProofLib.pointsToBytes_entails_memRegion (sp + 0x3e0#64) bs
  refine Entails.trans (entails_replace_sub hbs34 (by sep_focus) rfl) ?_
  refine Entails.trans (entails_replace_sub (memRegion_920_6_join sp w0 h1) (by sep_focus) rfl) ?_
  exact entails_replace_sub (memRegion_a90_48_join_10_38 sp q4 h5) (by sep_focus)
    (eq_of_sep_emp (by sep_focus))

set_option maxHeartbeats 1200000 in
/-- Relocatable `[LibsignalPlacement]` Stage P2 remote-identity match branch
(`(blkPl_518).base + 0x094c → +0x1778` when `recSt.remoteIdentity = some remIdKey`). -/
theorem stageP2_matched_094c_match_placed [LibsignalPlacement] {A : RustAlloc}
    {ext : String → Option (State → State)} {s0 : State}
    (h_bb : Rust.withPanics ext lsBlackBoxU8Sym =
      some CryptoVerification.LibsignalSession.blackBoxHook)
    (s : State)
    (sp coroPtr outPtr msgPtr remoteAddrPtr localAddrPtr v_330 v_388
      u_80 u_88 u_90 u_a8 u_b0 v_d0
      u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 : BitVec 64)
    (u_2a8 u_b8 : BitVec 32)
    (msgVerByte b_4f2 b_390 b_3ac : BitVec 8)
    (remIdKey : IdentityKey)
    (recG : SessionGhost) (recSt : SessionState (List (BitVec 8)))
    (hrem_eq : recSt.remoteIdentity = some remIdKey)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hsp_eq : s.sp = sp)
    (hsp_root : rootStack ≤ sp.toNat)
    (hpc : s.pc = (blkPl_518).base + 0x94c#64)
    (hrun : s.status = .Running)
    (hsp_align : (s.sp &&& 15#64 == 0#64) = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx21 : s.readReg64 .x21 = sp + 0x370#64)
    (hx25 : s.readReg64 .x25 = sp + 0x210#64)
    (hx28 : s.readReg64 .x28 = sp + 0xa90#64) :
    SepWPp (lsProg_518 (Rust.withPanics ext)) ((blkPl_518).base + 0x1778#64) s
      (Getters.remoteIdentityOkAt (sp + 0x3e0#64) recSt.remoteIdentity ∗
       sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
       ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
       ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
       cells (coroPtr + 0x250#64) 6 ∗
       ((coroPtr + 0x298#64) ↦₆₄ u_298) ∗
       ((coroPtr + 0x2a0#64) ↦₆₄ u_2a0) ∗
       ((coroPtr + 0x2a8#64) ↦₃₂ u_2a8) ∗
       ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
       ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
       ((coroPtr + 0x390#64) ↦₈ b_390) ∗
       ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
       ((coroPtr + 0x4f2#64) ↦₈ b_4f2) ∗
       ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
       ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
       ((sp + 0x80#64) ↦₆₄ u_80) ∗
       ((sp + 0x88#64) ↦₆₄ u_88) ∗
       ((sp + 0x90#64) ↦₆₄ u_90) ∗
       ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
       ((sp + 0xa0#64) ↦₆₄ (coroPtr + 0x4f2#64)) ∗
       ((sp + 0xa8#64) ↦₆₄ u_a8) ∗
       ((sp + 0xb0#64) ↦₆₄ u_b0) ∗
       ((sp + 0xb8#64) ↦₃₂ u_b8) ∗
       ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
       ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
       ((sp + 0x3a0#64) ↦₆₄ u_3a0) ∗
       ((sp + 0x3ac#64) ↦₈ b_3ac) ∗
       ((sp + 0x3b0#64) ↦₆₄ u_3b0) ∗
       ((sp + 0x3b8#64) ↦₆₄ u_3b8) ∗
       ((sp + 0x3c0#64) ↦₆₄ u_3c0) ∗
       ((sp + 0x3c8#64) ↦₆₄ u_3c8) ∗
       ((sp + 0x3d0#64) ↦₆₄ u_3d0) ∗
       ((sp + 0x3d8#64) ↦₆₄ u_3d8) ∗
       memRegion (sp + 0x920#64) 6 ∗
       memRegion (sp + 0xa90#64) 48 ∗
       stackAt sp rootStack)
      (fun sf P_f =>
        (P_f ⊢
          ∃∗ opkHi : BitVec 32, ∃∗ kyberPacked : BitVec 64,
            memRegion (sp + 0x3e0#64) 34 ∗
            sessionStateAt A (coroPtr + 0xf8#64) recG recSt ∗
            ((coroPtr + 0x70#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x78#64) ↦₆₄ remoteAddrPtr) ∗
            ((coroPtr + 0x80#64) ↦₆₄ localAddrPtr) ∗
            cells (coroPtr + 0x250#64) 6 ∗
            ((coroPtr + 0x298#64) ↦₃₂ 2#32) ∗
            ((coroPtr + 0x29c#64) ↦₃₂ opkHi) ∗
            ((coroPtr + 0x2a0#64) ↦₆₄ kyberPacked) ∗
            ((coroPtr + 0x2a8#64) ↦₃₂ v_d0.truncate 32) ∗
            ((coroPtr + 0x330#64) ↦₆₄ v_330) ∗
            ((coroPtr + 0x388#64) ↦₆₄ v_388) ∗
            ((coroPtr + 0x390#64) ↦₈ 1#8) ∗
            ((coroPtr + 0x468#64) ↦₆₄ msgPtr) ∗
            ((coroPtr + 0x4f2#64) ↦₈ 1#8) ∗
            ((msgPtr + 0x70#64) ↦₈ msgVerByte) ∗
            ((msgPtr + 0xc8#64) ↦ₛ remIdKey.publicKey.bytes.toList) ∗
            ((sp + 0x80#64) ↦₆₄ (coroPtr + 0xf8#64)) ∗
            ((sp + 0x88#64) ↦₆₄ (coroPtr + 0xe0#64)) ∗
            ((sp + 0x90#64) ↦₆₄ v_388) ∗
            ((sp + 0x98#64) ↦₆₄ (coroPtr + 0x398#64)) ∗
            ((sp + 0xa0#64) ↦₆₄ localAddrPtr) ∗
            ((sp + 0xa8#64) ↦₆₄ v_330) ∗
            ((sp + 0xb0#64) ↦₆₄ msgPtr) ∗
            ((sp + 0xb8#64) ↦₃₂ msgVerByte.zeroExtend 32) ∗
            ((sp + 0xc8#64) ↦₆₄ outPtr) ∗
            ((sp + 0xd0#64) ↦₆₄ v_d0) ∗
            ((sp + 0x3a0#64) ↦₆₄ remoteAddrPtr) ∗
            ((sp + 0x3ac#64) ↦₈ 3#8) ∗
            ((sp + 0x3b0#64) ↦₆₄ (sp + 0x3ac#64)) ∗
            ((sp + 0x3b8#64) ↦₆₄ msgPtr) ∗
            ((sp + 0x3c0#64) ↦₆₄ (sp + 0x3a0#64)) ∗
            ((sp + 0x3c8#64) ↦₆₄ 0#64) ∗
            ((sp + 0x3d0#64) ↦₆₄ 8#64) ∗
            ((sp + 0x3d8#64) ↦₆₄ 0#64) ∗
            memRegion (sp + 0x920#64) 6 ∗
            memRegion (sp + 0xa90#64) 48 ∗
            stackAt sp rootStack) ∧
        sf.sp = sp ∧
        sf.trace = s.trace ∧
        sf.readReg64 .x19 = coroPtr ∧
        sf.readReg64 .x27 = sp + 0x370#64 ∧
        sf.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sf = calleeSavedVRegs s ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl sf.mem)
      (CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) := by
  conv =>
    arg 4
    rw [hrem_eq]
  have hchk := stageP2_matched_094c_some_to_10cc_placed
    (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) h_bb s sp coroPtr outPtr msgPtr
    remIdKey remIdKey hcro hsp_eq hsp_root hpc hrun hsp_align hx19 hx21 hx25 hx28
  refine SepWPp.bind_sepWPp_steps_frame hchk (by sep_focus)
    fun s1 _ hpc1 hrun1 ⟨hsp1, htr1, hx0_1, hx19_1, _, hx26_1, _, hx29_1, hvregs1, hcro1⟩ => ?_
  have hx0_one : s1.readReg64 .x0 = 1#64 := by
    simpa [beq_self_eq_true] using hx0_1
  have hsp1_align : (s1.sp &&& 15#64 == 0#64) = true := by rw [hsp1, ← hsp_eq]; exact hsp_align
  have htail := stageP2_matched_ok_10cc_to_1778_placed (A := A) (ext := ext)
    (Qp := CryptoVerification.E2E.Pqxdh.ResponderClosure.PanicOomProp s0) s1 sp coroPtr outPtr msgPtr
    remoteAddrPtr localAddrPtr v_330 v_388 u_80 u_88 u_90 (coroPtr + 0x4f2#64) u_a8 u_b0 v_d0
    u_298 u_2a0 u_3a0 u_3b0 u_3b8 u_3c0 u_3c8 u_3d0 u_3d8 u_2a8 u_b8 msgVerByte b_4f2 b_390 b_3ac
    recG recSt hcro1 hsp1 hsp_root hpc1 hrun1 hsp1_align hx0_one hx19_1 hx26_1
  refine SepWPp.bind_sepWPp_steps_frame htail (by sep_focus)
    fun sf _ hpcf hrunf ⟨hspf, htrf, hx19_f, hx27_f, hx29_f, hvregsf_1, hcrof⟩ => ?_
  refine SepWPp.done hpcf hrunf
    ⟨?_, hspf, htrf.trans htr1, hx19_f, hx27_f, hx29_f.trans hx29_1, hvregsf_1.trans hvregs1, hcrof⟩
  sep_norm
  refine Entails.sepExists_elim fun opkHi => Entails.sepExists_right opkHi ?_
  refine Entails.sepExists_elim fun kyberPacked => Entails.sepExists_right kyberPacked ?_
  exact Entails.of_eq (eq_of_sep_emp (by sep_focus))

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
end
