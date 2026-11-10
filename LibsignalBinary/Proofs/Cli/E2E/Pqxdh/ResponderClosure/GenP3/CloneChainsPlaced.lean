/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneKeysFrontPlaced
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.GenP3.CloneChains
public import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.Assembly
import Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.RawByteMove.Move
import LibsignalBinary.Proofs.TripleRatchet.Wire.NewPrologue
import LibsignalBinary.Proofs.SpqrV1.Kdf.HkdfToSliceExtract
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.IdentityKeyStoreFutures.SaveIdentity
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Pqxdh.ResponderClosure.AssemblyP3
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Layout.Stubs
import LibsignalBinary.Proofs.SpqrV1.Poly.EncoderFromPb.Defs
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

@[expose] public section

set_option autoImplicit false

/-!
# General Stage P3 Clone — Placed Segment 2: `receiver_chains`

Relocatable `[LibsignalPlacement]` Segment 2 (`cloneChains_vregs_placed_ok`, `+0x19b0 → +0x1a5c`,
`genP3J1Placed → genP3J2Placed`) on `lsProg_518 ext`.
-/

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a2

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000
set_option linter.unusedSimpArgs false

attribute [-arm64_norm]
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg688_eq_hsp
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_sub_96_eq_hsp_592
  CryptoVerification.SpqrV1.Kdf.HkdfToSliceProof.sp_add_neg96_eq_hsp_592

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.add_assoc BitVec.toNat_zero

private def m3a2SessionStatePure (G : SessionGhost) (st : SessionState (List (BitVec 8))) : Prop :=
  PublicKey.deserialize G.localIk.bytes = .ok st.localIdentity.publicKey ∧
    (match st.remoteIdentity with
     | none => G.remoteIk.bytes = []
     | some ik => PublicKey.deserialize G.remoteIk.bytes = .ok ik.publicKey) ∧
    G.chains.length = st.receiverChains.length ∧
    G.pending.isSome = st.pendingPreKey ∧ G.regIds.length = 8 ∧
    G.localIk.bytes.length = 33 ∧
    (st.remoteIdentity.isSome → G.remoteIk.bytes.length = 33)

private def m3a2SessionStateRestAt' (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) : SepProp :=
  vecGhostAt A G.localIk (coroPtr + 0xf8#64) ∗
    vecGhostAt A G.remoteIk (coroPtr + 0x110#64) ∗
    vecU8At A (coroPtr + 0x128#64) G.root.cap G.root.ptr (keyToBytes32 st.rootKey) ∗
    vecGhostAt A G.alice (coroPtr + 0x158#64) ∗
    vecU8At A (coroPtr + 0x170#64) G.pq.cap G.pq.ptr st.pqRatchetState ∗
    optSenderChainAt A (coroPtr + 0x188#64) G.sender st.senderChain ∗
    optTailVecAt A 48 (coroPtr + 0x1f0#64) G.pending ∗
    optTailVecAt A 32 (coroPtr + 0x220#64) G.kyber ∗
    ((coroPtr + 0x240#64) ↦₃₂ st.sessionVersion) ∗
    ((coroPtr + 0x244#64) ↦₃₂ st.previousCounter) ∗
    ((coroPtr + 0x248#64) ↦ₛ G.regIds)

private theorem sessionStateAt_coro_placed_eq (A : RustAlloc) (coroPtr : BitVec 64)
    (G : SessionGhost) (st : SessionState (List (BitVec 8))) :
    sessionStateAt A (coroPtr + 0xf8#64) G st =
      ⌜m3a2SessionStatePure G st⌝ ∗
        ((coroPtr + 0x140#64) ↦₆₄ G.chainsCap) ∗
        ((coroPtr + 0x148#64) ↦₆₄ G.chainsPtr) ∗
        ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (G.chains.zip st.receiverChains).length) ∗
        vecBuf A 104 8 (chainAt A) G.chainsCap G.chainsPtr (G.chains.zip st.receiverChains) ∗
        m3a2SessionStateRestAt' A coroPtr G st := by
  unfold sessionStateAt vecAt vecHeader m3a2SessionStatePure m3a2SessionStateRestAt'
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  ac_rfl

private theorem chunks104_6QWAt_sp_0x3e0_placed (sp : BitVec 64)
    (q0 q1 q2 q3 q4 q5 : BitVec 128) (w6 : BitVec 64) :
    chunks104_6QWAt (sp + 0x3e0#64) q0 q1 q2 q3 q4 q5 w6 =
      ((sp + 0x3e0#64) ↦₆₄ q0.extractLsb' 0 64) ∗
        ((sp + 0x3e8#64) ↦₆₄ q0.extractLsb' 64 64) ∗
        ((sp + 0x3f0#64) ↦₆₄ q1.extractLsb' 0 64) ∗
        ((sp + 0x3f8#64) ↦₆₄ q1.extractLsb' 64 64) ∗
        ((sp + 0x400#64) ↦₆₄ q2.extractLsb' 0 64) ∗
        ((sp + 0x408#64) ↦₆₄ q2.extractLsb' 64 64) ∗
        ((sp + 0x410#64) ↦₆₄ q3.extractLsb' 0 64) ∗
        ((sp + 0x418#64) ↦₆₄ q3.extractLsb' 64 64) ∗
        ((sp + 0x420#64) ↦₆₄ q4.extractLsb' 0 64) ∗
        ((sp + 0x428#64) ↦₆₄ q4.extractLsb' 64 64) ∗
        ((sp + 0x430#64) ↦₆₄ q5.extractLsb' 0 64) ∗
        ((sp + 0x438#64) ↦₆₄ q5.extractLsb' 64 64) ∗
        ((sp + 0x440#64) ↦₆₄ w6) := by
  unfold chunks104_6QWAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]

/-! ## 1. Basic-Block `SepWP` Lemmas (`+0x19b0..+0x1a58` and `+0x3780..+0x3788`) -/

private theorem oom_tail_3780_placed_ok [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (s0 s : State) (ret : BitVec 64) (P : SepProp) (Q : State → SepProp → Prop)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x3780#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace ++ [allocFailedEvent]) :
    SepWPp (lsProg_518 ext) ret s P Q (P3P4.PanicOomProp s0) := by
  have hpanic' := closure_panic_at_handle_error_placed ext hpanic
  have hstep : SepWP (lsProg_518 ext) (lsρ lsHandleErrorSym)
      s emp (fun s1 P_f => (P_f ⊢ emp) ∧ s1.trace = s.trace) := by
    wp_steps
    refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl⟩
  refine bind_sepWP_lscro_frame_placed hcro hstep (emp_sepConj P).symm
    fun s1 hpc1 hrun1 _ htr1 => ?_
  refine SepWPp.panic hrun1 (hpc1 ▸ hpanic') fun R hm => ?_
  exact allowPanic_panicked (LibsignalTripleRatchet.allocFailedIn_of_eq (by
    simp only [Rust.panicked, htr1, htr])) hm

private theorem rc_prebranch_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State) (coroPtr rcsLen newLocIdPtr remIdLen newRemIdPtr u_60 u_68 u_70 : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x19b0#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = newLocIdPtr)
    (hx24 : s.readReg64 .x24 = remIdLen)
    (hx25 : s.readReg64 .x25 = newRemIdPtr) :
    SepWP (lsProg_518 ext)
      (if (rcsLen == 0#64) = true then
         (blkPl_518).base + 0x1a58#64
       else
         (blkPl_518).base + 0x19c4#64)
      s
      (((coroPtr + 0x150#64) ↦₆₄ rcsLen) ∗
        ((s.sp + 0x60#64) ↦₆₄ u_60) ∗
        ((s.sp + 0x68#64) ↦₆₄ u_68) ∗
        ((s.sp + 0x70#64) ↦₆₄ u_70) ∗
        ((s.sp + 0x98#64) ↦₆₄ 32#64))
      (fun s1 P_f =>
        (P_f ⊢
          ((coroPtr + 0x150#64) ↦₆₄ rcsLen) ∗
          ((s.sp + 0x60#64) ↦₆₄ newRemIdPtr) ∗
          ((s.sp + 0x68#64) ↦₆₄ remIdLen) ∗
          ((s.sp + 0x70#64) ↦₆₄ newLocIdPtr) ∗
          ((s.sp + 0x98#64) ↦₆₄ 32#64)) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x23 = rcsLen ∧
        s1.readReg64 .x25 = newRemIdPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 32#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = newLocIdPtr := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = remIdLen := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = newRemIdPtr := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem rc_empty_placed_wp [LibsignalPlacement] (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (blkPl_518).base + 0x1a58#64)
    (hrun : s.status = .Running) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1a5c#64) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x23 = s.readReg64 .x23 ∧
        s1.readReg64 .x25 = 8#64 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = s.readReg64 .x28 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem rc_alloc_prep_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (hshim_raw : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (s : State) (coroPtr chainsPtr rcsLen : BitVec 64)
    (hpc : s.pc = (blkPl_518).base + 0x19c4#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx23 : s.readReg64 .x23 = rcsLen) :
    SepWP (lsProg_518 ext) (lsρ lsAllocSym) s
      ((coroPtr + 0x148#64) ↦₆₄ chainsPtr)
      (fun s1 P_f =>
        (P_f ⊢ (coroPtr + 0x148#64) ↦₆₄ chainsPtr) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = rcsLen * 104#64 ∧
        s1.readReg64 .x1 = 8#64 ∧
        s1.readReg64 .x19 = coroPtr ∧
        s1.readReg64 .x21 = rcsLen * 104#64 ∧
        s1.readReg64 .x23 = rcsLen ∧
        s1.readReg64 .x24 = chainsPtr ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x19e0#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hshim := closure_shim_placed_ok ext hshim_raw
  have hx19' : s.readReg64 (Reg.gpr 19#5) = coroPtr := hx19
  have hx23' : s.readReg64 (Reg.gpr 23#5) = rcsLen := hx23
  wp_steps
  wp_call hshim ()
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem rc_alloc_oom_cbz_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (blkPl_518).base + 0x19e0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = 0#64) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x3780#64) s emp
      (fun s1 P_f => (P_f ⊢ emp) ∧ s1.sp = s.sp ∧ s1.trace = s.trace) := by
  have hx0' : s.readReg64 (Reg.gpr 0#5) = 0#64 := hx0
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ⟨Entails.refl _, rfl, rfl⟩

private theorem rc_alloc_prehdr_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (ptr' rcsLen chainsPtr : BitVec 64)
    (hptr : ptr' ≠ 0#64)
    (hpc : s.pc = (blkPl_518).base + 0x19e0#64)
    (hrun : s.status = .Running)
    (hx0 : s.readReg64 .x0 = ptr')
    (hx23 : s.readReg64 .x23 = rcsLen)
    (hx24 : s.readReg64 .x24 = chainsPtr) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x19fc#64) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x1 = chainsPtr ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = rcsLen ∧
        s1.readReg64 .x21 = 0#64 ∧
        s1.readReg64 .x22 = rcsLen * 104#64 ∧
        s1.readReg64 .x23 = rcsLen ∧
        s1.readReg64 .x25 = ptr' ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hptr_beq : (ptr' == 0#64) = false := beq_eq_false_iff_ne.mpr hptr
  have hx0' : s.readReg64 (Reg.gpr 0#5) = ptr' := hx0
  have hx23' : s.readReg64 (Reg.gpr 23#5) = rcsLen := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = chainsPtr := hx24
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem rc_loop_head_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (rem : Nat) (src dst_base off : BitVec 64)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x19fc#64)
    (hrun : s.status = .Running)
    (hx1 : s.readReg64 .x1 = src)
    (hx21 : s.readReg64 .x21 = off)
    (hx22 : s.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (rem + 1))
    (hx25 : s.readReg64 .x25 = dst_base) :
    SepWP (lsProg_518 ext) (lsmpl.base 524) s emp
      (fun s1 P_f =>
        (P_f ⊢ emp) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x0 = s.sp + 0x3e0#64 ∧
        s1.readReg64 .x1 = src ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = off ∧
        s1.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64 ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 rem ∧
        s1.readReg64 .x24 = src + 0x68#64 ∧
        s1.readReg64 .x25 = dst_base ∧
        s1.readReg64 .x26 = dst_base + off ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        s1.readReg64 .x30 = (blkPl_518).base + 0x1a18#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hsub_eq : (off + BitVec.ofNat 64 (rem + 1) * 104#64) - off =
      BitVec.ofNat 64 (rem + 1) * 104#64 := by bv_arith
  have hmul_beq : (BitVec.ofNat 64 (rem + 1) * 104#64 == 0#64) = false :=
    segClone_bv_ofNat_mul_104_beq_zero (Nat.succ_pos rem) hmul_lt
  have hx1' : s.readReg64 (Reg.gpr 1#5) = src := hx1
  have hx21' : s.readReg64 (Reg.gpr 21#5) = off := hx21
  have hx22' : s.readReg64 (Reg.gpr 22#5) = off + BitVec.ofNat 64 (rem + 1) * 104#64 := hx22
  have hx23' : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 (rem + 1) := hx23
  have hx25' : s.readReg64 (Reg.gpr 25#5) = dst_base := hx25
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.refl _, rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by rw [← segClone_bv_ofNat_succ_sub_one rem]; simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem rc_copy_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State) (rem : Nat) (nextSrc dst off : BitVec 64)
    (sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 : BitVec 128)
    (sw6 dw6 : BitVec 64)
    (hrem_lt : rem < 2 ^ 63)
    (hpc : s.pc = (blkPl_518).base + 0x1a18#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = off)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 rem)
    (hx24 : s.readReg64 .x24 = nextSrc)
    (hx26 : s.readReg64 .x26 = dst)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64) :
    SepWP (lsProg_518 ext)
      (if rem = 0 then
         (blkPl_518).base + 0x1a4c#64
       else
         (blkPl_518).base + 0x19fc#64)
      s
      (chunks104_6QWAt (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
        chunks104_6QWAt dst dq0 dq1 dq2 dq3 dq4 dq5 dw6)
      (fun s1 P_f =>
        (P_f ⊢
          chunks104_6QWAt (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chunks104_6QWAt dst sq0 sq1 sq2 sq3 sq4 sq5 sw6) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x1 = nextSrc ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x20 = s.readReg64 .x20 ∧
        s1.readReg64 .x21 = off + 0x68#64 ∧
        s1.readReg64 .x22 = s.readReg64 .x22 ∧
        s1.readReg64 .x23 = BitVec.ofNat 64 rem ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.sp + 0x370#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  have hpc_rem :
      (if !(BitVec.ofNat 64 rem == 0#64) = true then (blkPl_518).base + 0x19fc#64 else (blkPl_518).base + 0x1a4c#64) =
      (if rem = 0 then (blkPl_518).base + 0x1a4c#64 else (blkPl_518).base + 0x19fc#64) := by
    rcases Nat.eq_zero_or_pos rem with rfl | hpos
    · simp
    · have hne : rem ≠ 0 := Nat.ne_of_gt hpos
      have hne0 : BitVec.ofNat 64 rem ≠ 0#64 := ofNat_ne_zero_of_pos hpos (by omega)
      have hbeq : (BitVec.ofNat 64 rem == 0#64) = false := beq_false_of_ne hne0
      simp [hne, hbeq]
  rw [chunks104_6QWAt_sp_0x3e0_placed s.sp sq0 sq1 sq2 sq3 sq4 sq5 sw6]
  unfold chunks104_6QWAt
  simp only [pointsTo128_eq_pointsTo64, BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  have hx21' : s.readReg64 (Reg.gpr 21#5) = off := hx21
  have hx23' : s.readReg64 (Reg.gpr 23#5) = BitVec.ofNat 64 rem := hx23
  have hx24' : s.readReg64 (Reg.gpr 24#5) = nextSrc := hx24
  have hx26' : s.readReg64 (Reg.gpr 26#5) = dst := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = s.sp + 0x370#64 := hx27
  wp_steps
  refine SepWP.done (by rw [← hpc_rem]; simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private theorem rc_epilogue_placed_wp [LibsignalPlacement]
    (ext : String → Option (State → State))
    (s : State)
    (hpc : s.pc = (blkPl_518).base + 0x1a4c#64)
    (hrun : s.status = .Running)
    (hsp_align : s.spAligned = true) :
    SepWP (lsProg_518 ext) ((blkPl_518).base + 0x1a5c#64) s
      ((s.sp + 0x98#64) ↦₆₄ 32#64)
      (fun s1 P_f =>
        (P_f ⊢ (s.sp + 0x98#64) ↦₆₄ 32#64) ∧
        s1.sp = s.sp ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = s.readReg64 .x19 ∧
        s1.readReg64 .x23 = s.readReg64 .x20 ∧
        s1.readReg64 .x25 = s.readReg64 .x25 ∧
        s1.readReg64 .x27 = s.readReg64 .x27 ∧
        s1.readReg64 .x28 = 32#64 ∧
        s1.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), rfl, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

/-! ## 2. Loop Iteration & Induction (`+0x19fc → +0x1a4c`) -/

private theorem rc_iter_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hcc : ChainClone3OkPlaced A ext)
    (s0 s : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (g : ChainGhost) (rc : ReceiverChain) (rem : Nat)
    (coroPtr totalLen src dst_base off fp : BitVec 64) (F : SepProp)
    (hmul_lt : (rem + 1) * 104 < 2 ^ 63)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = (blkPl_518).base + 0x19fc#64)
    (hrun : s.status = .Running)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hx1 : s.readReg64 .x1 = src)
    (hx19 : s.readReg64 .x19 = coroPtr)
    (hx20 : s.readReg64 .x20 = totalLen)
    (hx21 : s.readReg64 .x21 = off)
    (hx22 : s.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 (rem + 1))
    (hx25 : s.readReg64 .x25 = dst_base)
    (hx27 : s.readReg64 .x27 = s.sp + 0x370#64)
    (hx29 : s.readReg64 .x29 = fp)
    (hnext : ∀ (s1 : State) (g' : ChainGhost),
      s1.pc = (if rem = 0 then (blkPl_518).base + 0x1a4c#64
               else (blkPl_518).base + 0x19fc#64) →
      s1.status = .Running →
      StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
      s1.sp = s.sp →
      s1.spAligned = true →
      s1.trace = s0.trace →
      s1.readReg64 .x1 = src + 0x68#64 →
      s1.readReg64 .x19 = coroPtr →
      s1.readReg64 .x20 = totalLen →
      s1.readReg64 .x21 = off + 0x68#64 →
      s1.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64 →
      s1.readReg64 .x23 = BitVec.ofNat 64 rem →
      s1.readReg64 .x25 = dst_base →
      s1.readReg64 .x27 = s.sp + 0x370#64 →
      s1.readReg64 .x29 = fp →
      calleeSavedVRegs s1 = calleeSavedVRegs s →
      SepWPp (lsProg_518 ext) ret s1
        (A.pool ∗
          chainAt A (g, rc) src ∗
          chainAt A (g', rc) (dst_base + off) ∗
          memRegion (s.sp + 0x3e0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (P3P4.PanicOomProp s0)) :
    SepWPp (lsProg_518 ext) ret s
      (A.pool ∗
        chainAt A (g, rc) src ∗
        memRegion (dst_base + off) 104 ∗
        memRegion (s.sp + 0x3e0#64) 104 ∗
        stackAt s.sp chainCloneStack ∗
        F)
      Q (P3P4.PanicOomProp s0) := by
  have hrem_lt : rem < 2 ^ 63 := by omega
  have hhead := rc_loop_head_placed_wp ext s rem src dst_base off hmul_lt
    hpc hrun hx1 hx21 hx22 hx23 hx25
  refine bind_sepWP_lscro_frame_placed hcro hhead (emp_sepConj _).symm
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1, htr1, hx0_1, hx1_1, hx19_1, hx20_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx29_1, hx30_1, hvregs1⟩
  rw [emp_sepConj]
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1] using hsp
  have htr1_0 : s1.trace = s0.trace := htr1.trans htr
  refine call_lscl_oom_placed
    (x := (⟨s.sp + 0x3e0#64, src, (g, rc)⟩ : ChainCloneGhost))
    (T := memRegion (s.sp + 0x3e0#64) 104 ∗ chainAt A (g, rc) src ∗ A.pool ∗
            stackAt s.sp chainCloneStack)
    (F := memRegion (dst_base + off) 104 ∗ F)
    hcro1 htr1_0 (chainClone3_at_518 ext hcc) hpc1 hrun1 hsp1_al hx30_1
    (by dsimp only [chainCloneSpec]; rw [hsp1])
    (And.intro hx0_1 hx1_1)
    (by sep_focus)
    (hnext := fun sf hpcf hrunf hspf hsp_alf hcsf hcrof => ?_)
  dsimp only [chainCloneSpec]
  rw [hsp1]
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun htr_sf => ?_
  rw [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun g' => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun _ => ?_
  have hsf_sp : sf.sp = s.sp := hspf.trans hsp1
  have hsf_tr : sf.trace = s0.trace := htr_sf.trans htr1_0
  rcases hcsf with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, _, hcs29, hvregsf_1⟩
  have hsf19 : sf.readReg64 .x19 = coroPtr := by rw [hcs19, hx19_1, hx19]
  have hsf20 : sf.readReg64 .x20 = totalLen := by rw [hcs20, hx20_1, hx20]
  have hsf21 : sf.readReg64 .x21 = off := hcs21.trans hx21_1
  have hsf22 : sf.readReg64 .x22 = off + BitVec.ofNat 64 (rem + 1) * 104#64 :=
    hcs22.trans hx22_1
  have hsf23 : sf.readReg64 .x23 = BitVec.ofNat 64 rem := hcs23.trans hx23_1
  have hsf24 : sf.readReg64 .x24 = src + 0x68#64 := hcs24.trans hx24_1
  have hsf25 : sf.readReg64 .x25 = dst_base := hcs25.trans hx25_1
  have hsf26 : sf.readReg64 .x26 = dst_base + off := hcs26.trans hx26_1
  have hsf27 : sf.readReg64 .x27 = sf.sp + 0x370#64 := by rw [hcs27, hx27_1, hx27, hsf_sp]
  have hsf29 : sf.readReg64 .x29 = fp := by rw [hcs29, hx29_1, hx29]
  rw [← hsf_sp]
  refine SepWPp.weaken_pre
    (sepConj_mono_left (chainAt_entails_chunks104_6QW A (g', rc) (sf.sp + 0x3e0#64))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun sq0 => SepWPp.exists_elim fun sq1 =>
    SepWPp.exists_elim fun sq2 => SepWPp.exists_elim fun sq3 =>
    SepWPp.exists_elim fun sq4 => SepWPp.exists_elim fun sq5 =>
    SepWPp.exists_elim fun sw6 => ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun hch_inl => ?_
  refine SepWPp.weaken_pre
    (P' := memRegion (dst_base + off) 104 ∗
            chunks104_6QWAt (sf.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
            chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
            stackAt sf.sp chainCloneStack ∗ F)
    (Entails.of_eq (by ac_rfl)) ?_
  refine SepWPp.weaken_pre
    (sepConj_mono_left (memRegion_104_entails_chunks104_6QWAt (dst_base + off))) ?_
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun dq0 => SepWPp.exists_elim fun dq1 =>
    SepWPp.exists_elim fun dq2 => SepWPp.exists_elim fun dq3 =>
    SepWPp.exists_elim fun dq4 => SepWPp.exists_elim fun dq5 =>
    SepWPp.exists_elim fun dw6 => ?_
  have hcopy := rc_copy_placed_wp ext sf rem (src + 0x68#64) (dst_base + off) off
    sq0 sq1 sq2 sq3 sq4 sq5 dq0 dq1 dq2 dq3 dq4 dq5 sw6 dw6
    hrem_lt hpcf hrunf hsp_alf hsf21 hsf23 hsf24 hsf26 hsf27
  refine bind_sepWP_lscro_frame_placed hcrof hcopy
    (F := chainHeap A (g', rc) ∗ chainAt A (g, rc) src ∗ A.pool ∗
            stackAt sf.sp chainCloneStack ∗ F)
    (by ac_rfl)
    fun s2 hpc2 hrun2 hcro2 hregs2 => ?_
  rcases hregs2 with ⟨hsp2, htr2, hx1_2, hx19_2, hx20_2, hx21_2, hx22_2,
    hx23_2, hx25_2, hx27_2, hx29_2, hvregs2⟩
  rw [hsf_sp] at hsp2 hx27_2 ⊢
  have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2] using hsp
  refine SepWPp.weaken_pre ?_
    (hnext s2 g' hpc2 hrun2 hcro2 hsp2 hsp2_al (htr2.trans hsf_tr)
      hx1_2 (hx19_2.trans hsf19) (hx20_2.trans hsf20) hx21_2 (hx22_2.trans hsf22)
      hx23_2 (hx25_2.trans hsf25) hx27_2 (hx29_2.trans hsf29)
      (hvregs2.trans (hvregsf_1.trans hvregs1)))
  have h104 := chunks104_6QWAt_entails_memRegion (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6
  have hdst_chain := chainAt_of_chunks104_6QW A (g', rc) (dst_base + off) hch_inl
  refine Entails.trans
    (Q := chunks104_6QWAt (s.sp + 0x3e0#64) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗
          (chunks104_6QWAt (dst_base + off) sq0 sq1 sq2 sq3 sq4 sq5 sw6 ∗ chainHeap A (g', rc)) ∗
          chainAt A (g, rc) src ∗ A.pool ∗ stackAt s.sp chainCloneStack ∗ F)
    (Entails.of_eq (by ac_rfl)) ?_
  refine Entails.trans (sepConj_mono h104 (sepConj_mono_left hdst_chain)) ?_
  exact Entails.of_eq (by ac_rfl)

private theorem pure_elim_3_placed {prog : Program} {ret : BitVec 64} {s : State}
    {P₁ P₂ P₃ : SepProp} {φ : Prop} {Q Qp : State → SepProp → Prop}
    (h : φ → SepWPp prog ret s (P₁ ∗ P₂ ∗ P₃) Q Qp) :
    SepWPp prog ret s (P₁ ∗ P₂ ∗ ⌜φ⌝ ∗ P₃) Q Qp :=
  SepWPp.weaken_pre (Entails.of_eq (by ac_rfl)) (SepWPp.pure_elim h)

private theorem rc_loop_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hcc : ChainClone3OkPlaced A ext)
    (s0 : State) (ret : BitVec 64) (Q : State → SepProp → Prop)
    (coroPtr totalLen dst_base fp : BitVec 64)
    (rcs_tl : List ReceiverChain) :
    ∀ (s : State) (rc : ReceiverChain) (g : ChainGhost) (gs_tl : List ChainGhost)
      (src off : BitVec 64) (F : SepProp),
      gs_tl.length = rcs_tl.length →
      (rcs_tl.length + 1) * 104 < 2 ^ 63 →
      (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 →
      StoreKit.LibsignalCodeRoLoaded lsmpl s.mem →
      s.pc = (blkPl_518).base + 0x19fc#64 →
      s.status = .Running →
      s.spAligned = true →
      s.trace = s0.trace →
      s.readReg64 .x1 = src →
      s.readReg64 .x19 = coroPtr →
      s.readReg64 .x20 = totalLen →
      s.readReg64 .x21 = off →
      s.readReg64 .x22 = off + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 →
      s.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) →
      s.readReg64 .x25 = dst_base →
      s.readReg64 .x27 = s.sp + 0x370#64 →
      s.readReg64 .x29 = fp →
      (∀ (s1 : State) (gs' : List ChainGhost),
        gs'.length = (rc :: rcs_tl).length →
        s1.pc = (blkPl_518).base + 0x1a4c#64 →
        s1.status = .Running →
        StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem →
        s1.sp = s.sp →
        s1.spAligned = true →
        s1.trace = s0.trace →
        s1.readReg64 .x19 = coroPtr →
        s1.readReg64 .x20 = totalLen →
        s1.readReg64 .x25 = dst_base →
        s1.readReg64 .x27 = s.sp + 0x370#64 →
        s1.readReg64 .x29 = fp →
        calleeSavedVRegs s1 = calleeSavedVRegs s →
        SepWPp (lsProg_518 ext) ret s1
          (A.pool ∗
            arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
            arrayAt (chainAt A) 104 (dst_base + off) (gs'.zip (rc :: rcs_tl)) ∗
            memRegion (s.sp + 0x3e0#64) 104 ∗
            stackAt s.sp chainCloneStack ∗
            F)
          Q (P3P4.PanicOomProp s0)) →
      SepWPp (lsProg_518 ext) ret s
        (A.pool ∗
          arrayAt (chainAt A) 104 src ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
          memRegion (dst_base + off) ((rcs_tl.length + 1) * 104) ∗
          memRegion (s.sp + 0x3e0#64) 104 ∗
          stackAt s.sp chainCloneStack ∗
          F)
        Q (P3P4.PanicOomProp s0) := by
  induction rcs_tl with
  | nil =>
    intro s rc g gs_tl src off F hgs hmul_lt _ hcro hpc hrun hsp htr
      hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29 hnext
    cases gs_tl with
    | cons _ _ => simp at hgs
    | nil =>
      simp only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil,
        sepConj_emp, List.length_nil, Nat.zero_add, Nat.one_mul] at *
      refine rc_iter_placed_ok ext hcc s0 s ret Q g rc 0 coroPtr totalLen src dst_base off fp F
        hmul_lt hcro hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29
        fun s1 g' hpc1 hrun1 hcro1 hsp1 hspA1 htr1 _ hx19_1 hx20_1 _ _ _
          hx25_1 hx27_1 hx29_1 hvregs1 => ?_
      simp only [↓reduceIte] at hpc1
      have h1 := hnext s1 [g'] rfl hpc1 hrun1 hcro1 hsp1 hspA1 htr1
        hx19_1 hx20_1 hx25_1 hx27_1 hx29_1 hvregs1
      simpa only [List.zip_cons_cons, List.zip_nil_right, arrayAt_cons, arrayAt_nil, sepConj_emp]
        using h1
  | cons rc2 rcs2 ih =>
    intro s rc g gs_tl src off F hgs hmul_lt hsz_le hcro hpc hrun hsp htr
      hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29 hnext
    cases gs_tl with
    | nil => simp at hgs
    | cons g2 gs2 =>
      have hgs2 : gs2.length = rcs2.length := by simpa using hgs
      have hmul2_lt : (rcs2.length + 1) * 104 < 2 ^ 63 := by simp [Nat.add_mul] at hmul_lt; omega
      have hsz2_le : (rcs2.length + 1) * 104 ≤ 2 ^ 64 := by simp [Nat.add_mul] at hsz_le; omega
      have hsplit_mr :
          memRegion (dst_base + off) (((rc2 :: rcs2).length + 1) * 104) =
            memRegion (dst_base + off) 104 ∗
              memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) := by
        refine memRegion_split' (n := 104) (k := (rcs2.length + 1) * 104) ?_
          (by bv_arith) hsz_le
        simp [List.length_cons, Nat.add_mul]; omega
      rw [List.zip_cons_cons, arrayAt_cons, hsplit_mr]
      refine SepWPp.weaken_pre
        (P' := A.pool ∗
                chainAt A (g, rc) src ∗
                memRegion (dst_base + off) 104 ∗
                memRegion (s.sp + 0x3e0#64) 104 ∗
                stackAt s.sp chainCloneStack ∗
                (arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                  memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗ F))
        (Entails.of_eq (by ac_rfl)) ?_
      refine rc_iter_placed_ok ext hcc s0 s ret Q g rc (rcs2.length + 1)
        coroPtr totalLen src dst_base off fp _
        hmul_lt hcro hpc hrun hsp htr hx1 hx19 hx20 hx21 hx22 hx23 hx25 hx27 hx29
        fun s1 g' hpc1 hrun1 hcro1 hsp1 hspA1 htr1 hx1_1 hx19_1 hx20_1 hx21_1
          hx22_1 hx23_1 hx25_1 hx27_1 hx29_1 hvregs1 => ?_
      have hne0 : rcs2.length + 1 ≠ 0 := Nat.succ_ne_zero _
      simp only [hne0, ↓reduceIte] at hpc1
      have hx22_next : s1.readReg64 .x22 =
          (off + 0x68#64) + BitVec.ofNat 64 (rcs2.length + 1) * 104#64 := by
        rw [hx22_1]
        exact segClone_off_add_succ_mul_104 off (rcs2.length + 1)
      have hx27_1' : s1.readReg64 .x27 = s1.sp + 0x370#64 := by rw [hsp1]; exact hx27_1
      rw [← hsp1]
      refine SepWPp.weaken_pre
        (P' := A.pool ∗
                arrayAt (chainAt A) 104 (src + 0x68#64) ((g2 :: gs2).zip (rc2 :: rcs2)) ∗
                memRegion (dst_base + (off + 0x68#64)) ((rcs2.length + 1) * 104) ∗
                memRegion (s1.sp + 0x3e0#64) 104 ∗
                stackAt s1.sp chainCloneStack ∗
                (chainAt A (g, rc) src ∗ chainAt A (g', rc) (dst_base + off) ∗ F))
        (Entails.of_eq (by ac_rfl)) ?_
      refine ih s1 rc2 g2 gs2 (src + 0x68#64) (off + 0x68#64) _
        hgs2 hmul2_lt hsz2_le hcro1 hpc1 hrun1 hspA1 htr1
        hx1_1 hx19_1 hx20_1 hx21_1 hx22_next hx23_1 hx25_1 hx27_1' hx29_1
        fun s2 gs2' hgs2' hpc2 hrun2 hcro2 hsp2 hspA2 htr2
          hx19_2 hx20_2 hx25_2 hx27_2 hx29_2 hvregs2 => ?_
      rw [hsp1] at hsp2 hx27_2 ⊢
      refine SepWPp.weaken_pre ?_
        (hnext s2 (g' :: gs2') (by simp [hgs2']) hpc2 hrun2 hcro2 hsp2 hspA2 htr2
          hx19_2 hx20_2 hx25_2 hx27_2 hx29_2 (hvregs2.trans hvregs1))
      simp only [List.zip_cons_cons, arrayAt_cons]
      have hd_add : dst_base + off + BitVec.ofNat 64 104 = dst_base + (off + 0x68#64) := by
        bv_arith
      rw [hd_add]
      exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a2

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.FromRecordChainClone
open CryptoVerification.LibsignalTripleRatchet.RawByteMove
open CryptoVerification.LibsignalTripleRatchet.Record
open CryptoVerification.LibsignalTripleRatchet.Record.SegCloneSteps
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.Matched
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a1
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3.M3a2
open CryptoVerification.CliHandshake.RespClosurePlaced
open CryptoVerification.CliHandshake.Placed

set_option maxRecDepth 200000

set_option maxHeartbeats 800000 in
theorem cloneChains_vregs_placed_ok [LibsignalPlacement] {A : RustAlloc}
    (ext : String → Option (State → State))
    (hshim : subroutine_ok (lsProg_518 ext) (lsρ lsShimSym) noAllocShimSpec)
    (halloc : subroutine_ok (lsProg_518 ext) (lsρ lsAllocSym) (rustAllocSpec A))
    (hpanic : ext lsHandleErrorSym = some Rust.panicked)
    (hcc : ChainClone3OkPlaced A ext)
    (s0 s : State)
    (sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur : BitVec 64)
    (msgVer : BitVec 32) (rest : List (BitVec 8))
    (recG : SessionGhost) (st : SessionState (List (BitVec 8)))
    (rem loc : AddrGhost) (msgG : SignalMessageGhost) (msg : SignalMessage)
    (hrc_len : st.receiverChains.length < 2 ^ 32)
    (hsp_align : (sp &&& 15#64 == 0#64) = true)
    (_hsp_root : rootStack ≤ sp.toNat)
    (hcro : StoreKit.LibsignalCodeRoLoaded lsmpl s.mem)
    (hpc : s.pc = dpClosureEntryM3Placed + 0x19b0#64)
    (hrun : s.status = .Running)
    (htr : s.trace = s0.trace) :
    SepWPp (lsProg_518 ext)
      (dpClosureEntryM3Placed + 0x1a5c#64) s
      (genP3J1Placed A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
        recG st rem loc msgG msg s)
      (fun s1 P_f =>
        (P_f ⊢ genP3J2Placed A sp fp coroPtr ctxPtr remAddrPtr locAddrPtr whisperMsgPtr cur msgVer
          rest recG st rem loc msgG msg s1) ∧
        s1.trace = s0.trace ∧
        StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s)
      (P3P4.PanicOomProp s0) := by
  dsimp only [dpClosureEntryM3Placed] at hpc ⊢
  dsimp only [genP3J1Placed, genP3ChainsSpillScratch]
  refine SepWPp.exists_elim fun w => ?_
  refine SepWPp.pure_elim fun ⟨hsp, hx19, hx23, hx24, hx25, hx27, hx29, hsc_rel, hsc_inl⟩ => ?_
  have hsp_al : s.spAligned = true := by simpa only [State.spAligned, hsp] using hsp_align
  rw [sessionStateAt_coro_placed_eq A coroPtr recG st]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, sepConj_assoc]
  refine SepWPp.exists_elim fun cs => ?_
  refine SepWPp.pure_elim fun hpure => ?_
  have hchains_len : recG.chains.length = st.receiverChains.length := hpure.2.2.1
  have hzip_len : (recG.chains.zip st.receiverChains).length = st.receiverChains.length := by
    simp [hchains_len]
  rw [hzip_len, ← hsp]
  have hpre := rc_prebranch_placed_wp ext s coroPtr
    (BitVec.ofNat 64 st.receiverChains.length)
    w.newLocIdPtr (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
    cs.u_60 cs.u_68 cs.u_70
    hpc hrun hsp_al hx19 hx23 hx24 hx25
  refine bind_sepWP_lscro_frame_placed hcro hpre (by sep_focus)
    fun s1 hpc1 hrun1 hcro1 hregs1 => ?_
  rcases hregs1 with ⟨hsp1_s, htr1_s, hx19_1, hx23_1, hx25_1, hx27_1, hx28_1, hx29_1, hvregs1⟩
  have hsp1 : s1.sp = sp := hsp1_s.trans hsp
  have hsp1_al : s1.spAligned = true := by simpa only [State.spAligned, hsp1_s] using hsp_al
  have htr1 : s1.trace = s0.trace := htr1_s.trans htr
  have hx27_1' : s1.readReg64 .x27 = sp + 0x370#64 := hx27_1.trans hx27
  have hx29_1' : s1.readReg64 .x29 = fp := hx29_1.trans hx29
  rw [hsp]
  cases hrc_eq : st.receiverChains with
  | nil =>
    simp only [hrc_eq, List.length_nil, beq_self_eq_true, ↓reduceIte]
      at hpc1 hx23_1 ⊢
    have hemp := rc_empty_placed_wp ext s1 hpc1 hrun1
    refine ret_sepWP_lscro_frame_placed hcro1 hemp (emp_sepConj _).symm
      fun sf _ _ hcrof hregsf => ?_
    rcases hregsf with ⟨hspf_1, htrf_1, hx19_f, hx23_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregsf_1⟩
    refine ⟨?_, htrf_1.trans htr1, hcrof, hvregsf_1.trans hvregs1⟩
    rw [emp_sepConj]
    let w' : GenP3J2Witness := { toGenP3J1Witness := w, newRcPtr := 8#64, chains' := [] }
    refine Entails.sepExists_right w' ?_
    apply Entails.pure_right
      ⟨hspf_1.trans hsp1, hx19_f.trans hx19_1,
       by simp [hrc_eq, hx23_f, hx23_1],
       hx25_f, hx27_f.trans hx27_1', hx28_f.trans hx28_1, hx29_f.trans hx29_1',
       by simp [w', hrc_eq], hsc_rel, hsc_inl⟩
    dsimp only [genP3J2Placed, w']
    rw [sessionStateAt_coro_placed_eq A coroPtr recG st, hrc_eq]
    simp only [List.zip_nil_right, List.length_nil,
      segClone_vecBuf_chain_nil_eq A, emp_sepConj, sepConj_assoc]
    refine Entails.trans
      (Q := ⌜m3a2SessionStatePure recG st⌝ ∗
        (((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
          ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
          ((coroPtr + 0x150#64) ↦₆₄ 0#64) ∗
          vecBuf A 104 8 (chainAt A) recG.chainsCap recG.chainsPtr [] ∗
          m3a2SessionStateRestAt' A coroPtr recG st ∗
          A.pool ∗
          stackAt sp chainCloneStack ∗
          memRegion (sp + 0x3e0#64) 104 ∗
          ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
          genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem loc
            msgG msg ∗
          vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr recG.localIk.bytes ∗
          vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
            recG.remoteIk.bytes ∗
          vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
          optSenderChainHeap A w.sender' st.senderChain ∗
          genP3PendSpillScratch sp ∗
          genP3TailSpillScratch sp ∗
          ((sp + 0x48#64) ↦₆₄ w.c0) ∗
          ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
          ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
          ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
          ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
          ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
          ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
          ((sp + 0x98#64) ↦₆₄ 32#64) ∗
          ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
          genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
      ?_ (Entails.of_eq (by ac_rfl))
    apply Entails.pure_right hpure
    exact Entails.of_eq (by ac_rfl)
  | cons rc rcs_tl =>
    have hn_pos : 0 < (rc :: rcs_tl).length := by simp
    have hn_lt32 : (rc :: rcs_tl).length < 2 ^ 32 := by rw [← hrc_eq]; exact hrc_len
    have hmul_lt : (rc :: rcs_tl).length * 104 < 2 ^ 63 := by simp [List.length_cons] at hn_lt32 ⊢; omega
    have hmul_lt' : (rcs_tl.length + 1) * 104 < 2 ^ 63 := hmul_lt
    have hsz_le : (rcs_tl.length + 1) * 104 ≤ 2 ^ 64 := by omega
    have hpos_mul : 0 < (rc :: rcs_tl).length * 104 := by simp [List.length_cons]
    have hsz_le63 : (rc :: rcs_tl).length * 104 + 8 ≤ 2 ^ 63 := by omega
    have hlay : LayoutOk ((rc :: rcs_tl).length * 104) 8 := ⟨hpos_mul, ⟨3, rfl⟩, hsz_le63⟩
    have htoNat_mul : (BitVec.ofNat 64 (rc :: rcs_tl).length * 104#64).toNat =
        (rc :: rcs_tl).length * 104 := segClone_bv_ofNat_mul_104_toNat hmul_lt
    have hlen_beq : (BitVec.ofNat 64 (rc :: rcs_tl).length == 0#64) = false :=
      beq_ofNat_zero_eq_false hn_pos (by omega)
    rw [hrc_eq] at hpc1 hx23_1
    simp only [hlen_beq, Bool.false_eq_true, ↓reduceIte] at hpc1
    cases hgs_eq : recG.chains with
    | nil => rw [hgs_eq, hrc_eq] at hchains_len; simp at hchains_len
    | cons g gs_tl =>
      have hgs_tl : gs_tl.length = rcs_tl.length := by
        rw [hgs_eq, hrc_eq] at hchains_len; simpa using hchains_len
      have hexpose :=
        segClone_vecBuf_expose_arrayAt A (stride := 104) 8 (chainAt A)
          recG.chainsCap recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) emp
      rw [sepConj_emp, sepConj_emp] at hexpose
      refine P3P4.SepWPp.weaken_frame hexpose (by sep_focus) ?_
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun _ => ?_
      have hprep := rc_alloc_prep_placed_wp ext hshim s1 coroPtr recG.chainsPtr
        (BitVec.ofNat 64 (rc :: rcs_tl).length)
        hpc1 hrun1 hsp1_al hx19_1 hx23_1
      refine bind_sepWP_lscro_frame_placed hcro1 hprep (by sep_focus)
        fun s2 hpc2 hrun2 hcro2 hregs2 => ?_
      rcases hregs2 with ⟨hsp2_1, htr2_1, hx0_2, hx1_2, hx19_2, hx21_2,
        hx23_2, hx24_2, hx27_2, hx29_2, hx30_2, hvregs2_1⟩
      have hsp2 : s2.sp = sp := hsp2_1.trans hsp1
      have hsp2_al : s2.spAligned = true := by simpa only [State.spAligned, hsp2_1] using hsp1_al
      have htr2 : s2.trace = s0.trace := htr2_1.trans htr1
      have hx27_2' : s2.readReg64 .x27 = sp + 0x370#64 := hx27_2.trans hx27_1'
      have hx29_2' : s2.readReg64 .x29 = fp := hx29_2.trans hx29_1'
      rw [stackAt_chainClone_eq_alloc sp]
      simp only [sepConj_assoc]
      have hφ : (s2.readReg64 .x0).toNat = (rc :: rcs_tl).length * 104 ∧
          (s2.readReg64 .x1).toNat = 8 ∧ LayoutOk ((rc :: rcs_tl).length * 104) 8 :=
        ⟨by rw [hx0_2, htoNat_mul], by rw [hx1_2]; rfl, hlay⟩
      refine call_raw_nopanic_placed
        (spec := rustAllocSpec A)
        (x := ((rc :: rcs_tl).length * 104, 8))
        (T := A.pool ∗ stackAt sp allocHookStack)
        hcro2 halloc hpc2 hrun2 hsp2_al hx30_2
        (by dsimp only [rustAllocSpec]; rw [hsp2])
        hφ (by sep_focus)
        (hnext := fun s3 hpc3 hrun3 hsp3_2 hsp3_al hcs3 hcro3 => ?_)
      have hsp3 : s3.sp = sp := hsp3_2.trans hsp2
      rcases hcs3 with ⟨hx19_cs3, _, _, _, hx23_cs3, hx24_cs3, _, _, hx27_cs3, _, hx29_cs3, hvregs3_2⟩
      have hx19_3 : s3.readReg64 .x19 = coroPtr := hx19_cs3.trans hx19_2
      have hx23_3 : s3.readReg64 .x23 = BitVec.ofNat 64 (rc :: rcs_tl).length :=
        hx23_cs3.trans hx23_2
      have hx24_3 : s3.readReg64 .x24 = recG.chainsPtr := hx24_cs3.trans hx24_2
      have hx27_3 : s3.readReg64 .x27 = sp + 0x370#64 := hx27_cs3.trans hx27_2'
      have hx29_3 : s3.readReg64 .x29 = fp := hx29_cs3.trans hx29_2'
      dsimp only [rustAllocSpec]
      rw [hsp2]
      by_cases hoom : s3.readReg64 .x0 = 0#64
      · have hoom0 : (s3.readReg64 .x0 = 0) = True := eq_true hoom
        simp only [hoom0, ↓reduceIte, P3P4.pull_pure_alloc_oom]
        refine SepWPp.pure_elim fun htr3_2 => ?_
        have hcbz := rc_alloc_oom_cbz_placed_wp ext s3 hpc3 hrun3 hoom
        refine bind_sepWP_lscro_frame_placed hcro3 hcbz (emp_sepConj _).symm
          fun s4 hpc4 hrun4 hcro4 ⟨_, htr4_3⟩ => ?_
        exact oom_tail_3780_placed_ok ext hpanic s0 s4 _ _ _ hcro4 hpc4 hrun4
          (by rw [htr4_3, htr3_2, htr2])
      · set ptr' := s3.readReg64 .x0
        have hoom0 : (ptr' = 0) = False := eq_false hoom
        simp only [hoom0, ↓reduceIte, sepConj_assoc]
        refine pure_elim_3_placed fun ⟨_, htr3_2⟩ => ?_
        have htr3 : s3.trace = s0.trace := htr3_2.trans htr2
        refine P3P4.SepWPp.weaken_frame
          (Entails.of_eq (stackAt_chainClone_eq_alloc sp).symm) (by sep_focus) ?_
        have hprehdr := rc_alloc_prehdr_placed_wp ext s3 ptr'
          (BitVec.ofNat 64 (rc :: rcs_tl).length) recG.chainsPtr
          hoom hpc3 hrun3 rfl hx23_3 hx24_3
        refine bind_sepWP_lscro_frame_placed hcro3 hprehdr (emp_sepConj _).symm
          fun s4 hpc4 hrun4 hcro4 hregs4 => ?_
        rcases hregs4 with ⟨hsp4_3, htr4_3, hx1_4, hx19_4, hx20_4, hx21_4,
          hx22_4, hx23_4, hx25_4, hx27_4, hx29_4, hvregs4_3⟩
        rw [emp_sepConj]
        have hsp4 : s4.sp = sp := hsp4_3.trans hsp3
        have hsp4_al : s4.spAligned = true := by simpa only [State.spAligned, hsp4_3] using hsp3_al
        have htr4 : s4.trace = s0.trace := htr4_3.trans htr3
        have hx19_4' : s4.readReg64 .x19 = coroPtr := hx19_4.trans hx19_3
        have hx22_4' : s4.readReg64 .x22 =
            0#64 + BitVec.ofNat 64 (rcs_tl.length + 1) * 104#64 := by
          rw [hx22_4, List.length_cons, BitVec.zero_add]
        have hx23_4' : s4.readReg64 .x23 = BitVec.ofNat 64 (rcs_tl.length + 1) := hx23_4
        have hx27_4' : s4.readReg64 .x27 = s4.sp + 0x370#64 := by
          rw [hsp4]; exact hx27_4.trans hx27_3
        have hx29_4' : s4.readReg64 .x29 = fp := hx29_4.trans hx29_3
        have hptr_zero : ptr' + 0#64 = ptr' := by bv_arith
        have hsz_eq : (rc :: rcs_tl).length * 104 = (rcs_tl.length + 1) * 104 := rfl
        have hmr_eq : memRegion ptr' ((rc :: rcs_tl).length * 104) =
            memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) := by
          rw [hptr_zero, hsz_eq]
        rw [hmr_eq, hsz_eq, ← hsp4]
        refine SepWPp.weaken_pre
          (P' := A.pool ∗
                  arrayAt (chainAt A) 104 recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  memRegion (ptr' + 0#64) ((rcs_tl.length + 1) * 104) ∗
                  memRegion (s4.sp + 0x3e0#64) 104 ∗
                  stackAt s4.sp chainCloneStack ∗
                  (A.live ptr' ((rcs_tl.length + 1) * 104) 8 ∗
                    ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
                    ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (rc :: rcs_tl).length) ∗
                    ((s4.sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
                    ((s4.sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
                    ((s4.sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
                    ((s4.sp + 0x98#64) ↦₆₄ 32#64) ∗
                    segClone_vecBufRest A 104 8 recG.chainsCap recG.chainsPtr
                      ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                    ((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
                    m3a2SessionStateRestAt' A coroPtr recG st ∗
                    ((s4.sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                    genP3CallFramePlaced A s4.sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest
                      rem loc msgG msg ∗
                    vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr
                      recG.localIk.bytes ∗
                    vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
                      recG.remoteIk.bytes ∗
                    vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
                    optSenderChainHeap A w.sender' st.senderChain ∗
                    genP3PendSpillScratch s4.sp ∗
                    genP3TailSpillScratch s4.sp ∗
                    ((s4.sp + 0x48#64) ↦₆₄ w.c0) ∗
                    ((s4.sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
                    ((s4.sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
                    ((s4.sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
                    ((s4.sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
                    genP3SenderInlineWords s4.sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
          (Entails.of_eq (by ac_rfl)) ?_
        refine rc_loop_placed_ok ext hcc s0 _ _ coroPtr
          (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr' fp rcs_tl
          s4 rc g gs_tl recG.chainsPtr 0#64 _
          hgs_tl hmul_lt' hsz_le hcro4 hpc4 hrun4 hsp4_al htr4
          hx1_4 hx19_4' hx20_4 hx21_4 hx22_4' hx23_4' hx25_4 hx27_4' hx29_4'
          fun s5 gs' hgs'_len hpc5 hrun5 hcro5 hsp5_4 hsp5_al htr5
            hx19_5 hx20_5 hx25_5 hx27_5 hx29_5 hvregs5_4 => ?_
        have hsp5 : s5.sp = sp := hsp5_4.trans hsp4
        rw [hsp4] at hx27_5 ⊢
        rw [hptr_zero, ← hsp5]
        have hepi := rc_epilogue_placed_wp ext s5 hpc5 hrun5 hsp5_al
        refine ret_sepWP_lscro_frame_placed hcro5 hepi (by sep_focus)
          fun sf _ _ hcrof hregsf => ?_
        rcases hregsf with
          ⟨hspf_5, htrf_5, hx19_f, hx23_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregsf_5⟩
        refine ⟨?_, htrf_5.trans htr5, hcrof,
          hvregsf_5.trans (hvregs5_4.trans (hvregs4_3.trans (hvregs3_2.trans (hvregs2_1.trans hvregs1))))⟩
        rw [hsp5]
        let w' : GenP3J2Witness :=
          { toGenP3J1Witness := w, newRcPtr := ptr', chains' := gs' }
        refine Entails.sepExists_right w' ?_
        apply Entails.pure_right
          ⟨hspf_5.trans hsp5,
           hx19_f.trans hx19_5,
           by rw [hx23_f, hx20_5, hrc_eq],
           hx25_f.trans hx25_5,
           hx27_f.trans hx27_5,
           hx28_f,
           hx29_f.trans hx29_5,
           by rw [hrc_eq]; exact hgs'_len,
           hsc_rel, hsc_inl⟩
        dsimp only [genP3J2Placed, w']
        rw [sessionStateAt_coro_placed_eq A coroPtr recG st, hgs_eq, hrc_eq]
        have hzip_src_len : ((g :: gs_tl).zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
          simp [hgs_tl]
        have hzip_dst_len : (gs'.zip (rc :: rcs_tl)).length = (rc :: rcs_tl).length := by
          simp [hgs'_len]
        rw [hzip_src_len]
        have hsrc_buf := segClone_vecBuf_reassemble_arrayAt A 104 8 (chainAt A)
          recG.chainsCap recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl))
        have hdst_buf :
            (A.live ptr' ((rcs_tl.length + 1) * 104) 8 ∗
              arrayAt (chainAt A) 104 ptr' (gs'.zip (rc :: rcs_tl))) ⊢
            vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr'
              (gs'.zip (rc :: rcs_tl)) := by
          have h := segClone_vecBuf_chain_of_arrayAt A ptr' (gs'.zip (rc :: rcs_tl))
            (by rw [hzip_dst_len]; exact hn_pos)
            (by rw [hzip_dst_len]; exact hmul_lt)
            hoom
          rwa [hzip_dst_len, hsz_eq] at h
        refine Entails.trans
          (Q := (arrayAt (chainAt A) 104 recG.chainsPtr ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
                  segClone_vecBufRest A 104 8 recG.chainsCap recG.chainsPtr
                    ((g :: gs_tl).zip (rc :: rcs_tl))) ∗
                (A.live ptr' ((rcs_tl.length + 1) * 104) 8 ∗
                  arrayAt (chainAt A) 104 ptr' (gs'.zip (rc :: rcs_tl))) ∗
                (((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
                  ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
                  ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (rc :: rcs_tl).length) ∗
                  m3a2SessionStateRestAt' A coroPtr recG st ∗
                  A.pool ∗
                  stackAt sp chainCloneStack ∗
                  memRegion (sp + 0x3e0#64) 104 ∗
                  ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
                  genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem
                    loc msgG msg ∗
                  vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr
                    recG.localIk.bytes ∗
                  vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
                    recG.remoteIk.bytes ∗
                  vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
                  optSenderChainHeap A w.sender' st.senderChain ∗
                  genP3PendSpillScratch sp ∗
                  genP3TailSpillScratch sp ∗
                  ((sp + 0x48#64) ↦₆₄ w.c0) ∗
                  ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
                  ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
                  ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
                  ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
                  ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
                  ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
                  ((sp + 0x98#64) ↦₆₄ 32#64) ∗
                  ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
                  genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
          (Entails.of_eq (by ac_rfl)) ?_
        refine Entails.trans (sepConj_mono hsrc_buf (sepConj_mono_left hdst_buf)) ?_
        refine Entails.trans
          (Q := ⌜m3a2SessionStatePure recG st⌝ ∗
            (vecBuf A 104 8 (chainAt A) recG.chainsCap recG.chainsPtr
                ((g :: gs_tl).zip (rc :: rcs_tl)) ∗
              vecBuf A 104 8 (chainAt A) (BitVec.ofNat 64 (rc :: rcs_tl).length) ptr'
                (gs'.zip (rc :: rcs_tl)) ∗
              ((coroPtr + 0x140#64) ↦₆₄ recG.chainsCap) ∗
              ((coroPtr + 0x148#64) ↦₆₄ recG.chainsPtr) ∗
              ((coroPtr + 0x150#64) ↦₆₄ BitVec.ofNat 64 (rc :: rcs_tl).length) ∗
              m3a2SessionStateRestAt' A coroPtr recG st ∗
              A.pool ∗
              stackAt sp chainCloneStack ∗
              memRegion (sp + 0x3e0#64) 104 ∗
              ((sp + 0xc0#64) ↦₆₄ ctxPtr) ∗
              genP3CallFramePlaced A sp remAddrPtr locAddrPtr whisperMsgPtr cur msgVer rest rem
                loc msgG msg ∗
              vecU8Buf A (BitVec.ofNat 64 recG.localIk.bytes.length) w.newLocIdPtr
                recG.localIk.bytes ∗
              vecU8Buf A (BitVec.ofNat 64 recG.remoteIk.bytes.length) w.newRemIdPtr
                recG.remoteIk.bytes ∗
              vecU8Buf A 32#64 w.newRootKeyPtr (keyToBytes32 st.rootKey) ∗
              optSenderChainHeap A w.sender' st.senderChain ∗
              genP3PendSpillScratch sp ∗
              genP3TailSpillScratch sp ∗
              ((sp + 0x48#64) ↦₆₄ w.c0) ∗
              ((sp + 0x50#64) ↦₆₄ w.newRootKeyPtr) ∗
              ((sp + 0x5c#64) ↦₃₂ st.previousCounter) ∗
              ((sp + 0x60#64) ↦₆₄ w.newRemIdPtr) ∗
              ((sp + 0x68#64) ↦₆₄ BitVec.ofNat 64 recG.remoteIk.bytes.length) ∗
              ((sp + 0x70#64) ↦₆₄ w.newLocIdPtr) ∗
              ((sp + 0x7c#64) ↦₃₂ st.sessionVersion) ∗
              ((sp + 0x98#64) ↦₆₄ 32#64) ∗
              ((sp + 0xd0#64) ↦₆₄ BitVec.ofNat 64 recG.localIk.bytes.length) ∗
              genP3SenderInlineWords sp w.sq0 w.sq1 w.sq2 w.sq3 w.sq4 w.sq5))
          ?_ (by simp only [sepConj_assoc]; exact Entails.of_eq (by ac_rfl))
        apply Entails.pure_right hpure
        exact Entails.of_eq (by ac_rfl)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.GenP3
