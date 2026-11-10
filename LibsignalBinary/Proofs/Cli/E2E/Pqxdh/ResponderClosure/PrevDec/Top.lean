/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Bridge -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Merge -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.SpqrH.SkipField6 -- shake: keep
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.LoopDefs
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.DecInterface
public import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.VerNe.Chain3.Defs
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmBytesTR
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmChainRecvOk
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.ArmVarint
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Compose
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Entry
import LibsignalBinary.Proofs.Cli.E2E.Pqxdh.ResponderClosure.PrevDec.Key
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.Loop
import LibsignalBinary.Proofs.E2E.InMem.HashbrownBin.SessionStoreFutures.StoreCommon
import LibsignalBinary.Proofs.E2E.Record.Serialization.SessionCloneAux.Base
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry

/-!
# Top-Level CLI Inlined `SessionStructure::decode`

Assembles the verified entry, loop-head, key, varint, bytes, sender-chain (tag 6), and
receiver-chain (tag 7) contracts into the unconditional `OverPrevDecodeStmt` (`+0x1ee8 → +0x2620`)
for `message_decrypt_prekey::<signal_session_handshake::Coins>::{closure#0}`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec

open Arm64 ProofLib ProofLib.ObjectLoad ProofLib.ProgramReflection SepProp
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.E2E.Pqxdh.ResponderClosure
open CryptoVerification.E2E.Pqxdh.ResponderClosure.P3P4
open CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure (decryptPrekeyClosureName decryptPrekeyClosure_fnOff)
open Symbolic.Swarm.TRREF.B3DeserQ (SSGQ GenFieldQ prostSSGQAt)

section HeadExt

attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
attribute [local simp, local arm64_norm ↓, local wp_norm ↓] decryptPrekeyClosure_fnOff
attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff

private theorem top_SepWPp_bind_sepWP_frame {prog : Program} {img : Obj.Image}
    {mid ret : BitVec 64} {s : State}
    {P P_step P_step_post F : SepProp} {Q_regs : State → Prop}
    {Q Qp : State → SepProp → Prop}
    (hF : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hstep : SepWP prog mid s P_step
      (fun sm P_step' => (P_step' ⊢ P_step_post) ∧ Q_regs sm))
    (hP : P = P_step ∗ F)
    (hnext : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q_regs sm →
      SepWPp prog ret sm (P_step_post ∗ F) Q Qp) :
    SepWPp prog ret s P Q Qp := by
  intro R hm hL
  rw [hP, sepConj_assoc] at hm
  obtain ⟨sm, hsteps, ⟨hpc, hrun, P_step', hmm, hent, hregs⟩ | ⟨_, _hoom⟩⟩ := hstep.elim hm hL
  rotate_left; · first | exact False.elim _hoom | exact (not_satisfies_false_sepConj _hoom).elim
  have hmm' : sm.mem ⊨ (P_step_post ∗ F) ∗ R := by
    rw [sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left hent) hmm
  obtain ⟨sf, hsteps', hout'⟩ :=
    hnext sm hpc hrun (hF.of_keepsFrozen hsteps.keepsFrozen)
      (hsteps.symtab_eq.trans hsym) hregs R hmm' (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout'⟩

private theorem top_rest_len_ofNat64_ne_zero {rest enc : List (BitVec 8)}
    (hne : rest ≠ []) (hsuf : rest <:+ enc) (hlen : enc.length < 2 ^ 62) :
    BitVec.ofNat 64 rest.length ≠ 0#64 := by
  have hpos : 0 < rest.length := List.length_pos_iff.mpr hne
  rcases hsuf with ⟨t, ht⟩
  have hle : rest.length ≤ enc.length := by rw [← ht, List.length_append]; omega
  intro h0
  have hnat := congrArg BitVec.toNat h0
  rw [BitVec.toNat_ofNat, BitVec.toNat_zero, Nat.mod_eq_of_lt (by omega : rest.length < 2 ^ 64)] at hnat
  omega

set_option maxHeartbeats 400000 in
private theorem top_head_cons_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG) (rest : List (BitVec 8))
    (hlen_nz : BitVec.ofNat 64 rest.length ≠ 0#64)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x216c#64) s
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
       Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest)
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2160 0x2168
  dsimp only [contractProg, Prost.sliceCursorAfter] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

set_option maxHeartbeats 400000 in
private theorem top_head_nil_wp (b : BitVec 64) (ext : String → Option (State → State))
    (s : State) (g : OverDecG)
    (hpc : s.pc = (contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2160#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = g.q)
    (hx19 : s.readReg64 .x19 = g.r19)
    (hx20 : s.readReg64 .x20 = g.r20)
    (hx21 : s.readReg64 .x21 = g.q + 0x930#64)
    (hx24 : s.readReg64 .x24 = 1#64)
    (hx25 : s.readReg64 .x25 = 0xffffffffffffffff#64)
    (hx26 : s.readReg64 .x26 = g.r26)
    (hx27 : s.readReg64 .x27 = g.prevPtr)
    (hx28 : s.readReg64 .x28 = g.q + 0xa90#64)
    (hx29 : s.readReg64 .x29 = g.q + 0xc70#64) :
    SepWP (contractProg b ext)
      ((contractProg b ext).fnAddr decryptPrekeyClosureName + 0x2620#64) s
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
       Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc [])
      (fun s1 P_f =>
        (P_f ⊢
          ((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
          Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc []) ∧
        s1.sp = g.q ∧
        s1.trace = s.trace ∧
        s1.readReg64 .x19 = g.r19 ∧
        s1.readReg64 .x20 = g.r20 ∧
        s1.readReg64 .x21 = g.q + 0x930#64 ∧
        s1.readReg64 .x24 = 1#64 ∧
        s1.readReg64 .x25 = 0xffffffffffffffff#64 ∧
        s1.readReg64 .x26 = g.r26 ∧
        s1.readReg64 .x27 = g.prevPtr ∧
        s1.readReg64 .x28 = g.q + 0xa90#64 ∧
        s1.readReg64 .x29 = g.q + 0xc70#64 ∧
        calleeSavedVRegs s1 = calleeSavedVRegs s) := by
  closure_fetches_range_cli b (Rust.withPanics ext) 0x2160 0x2168
  dsimp only [contractProg, Prost.sliceCursorAfter, List.length_nil, BitVec.ofNat_eq_ofNat] at hpc ⊢
  generalize_entry (libsignalSessionCode.rebase b (Rust.withPanics ext)).fnAddr decryptPrekeyClosureName = entry
  examples_hide_fetches
  have hx19' : s.readReg64 (Reg.gpr 19#5) = g.r19 := hx19
  have hx20' : s.readReg64 (Reg.gpr 20#5) = g.r20 := hx20
  have hx21' : s.readReg64 (Reg.gpr 21#5) = g.q + 0x930#64 := hx21
  have hx24' : s.readReg64 (Reg.gpr 24#5) = 1#64 := hx24
  have hx25' : s.readReg64 (Reg.gpr 25#5) = 0xffffffffffffffff#64 := hx25
  have hx26' : s.readReg64 (Reg.gpr 26#5) = g.r26 := hx26
  have hx27' : s.readReg64 (Reg.gpr 27#5) = g.prevPtr := hx27
  have hx28' : s.readReg64 (Reg.gpr 28#5) = g.q + 0xa90#64 := hx28
  have hx29' : s.readReg64 (Reg.gpr 29#5) = g.q + 0xc70#64 := hx29
  wp_steps
  refine SepWP.done (by simp_all [arm64_norm]) (by simp_all [arm64_norm]) ?_
  refine ⟨Entails.of_eq (by ac_rfl), hsp, rfl,
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm], by simp_all [arm64_norm], by simp_all [arm64_norm],
    by simp_all [arm64_norm]⟩

private def top_headFrameRestExt (A : RustAlloc) (g : OverDecG) (v : SSGQ) : SepProp :=
  overPrevElemRestExt A g.prevCap g.prevPtr g.encCap g.encPtr g.enc ∗
    prostSSGQAt A (g.q + 0x930#64) v ∗
    memRegion (g.q + 0xa88#64) 8 ∗ memRegion (g.q + 0xa90#64) 344 ∗
    memRegion (g.q + 0xbf0#64) 128 ∗
    stackAt g.q overDecStackX ∗ A.pool

private theorem top_overDecHeapExt_eq_head_split (A : RustAlloc) (g : OverDecG)
    (rest : List (BitVec 8)) (v : SSGQ) :
    overDecHeapExt A g rest v =
      (((g.q + 0xbe8#64) ↦₆₄ (g.q + 0x920#64)) ∗
        Prost.sliceCursorAfter (g.q + 0x920#64) g.encPtr g.enc rest) ∗
      top_headFrameRestExt A g v := by
  unfold overDecHeapExt top_headFrameRestExt
  ac_rfl

/-- Loop head (`+0x2160 → +0x216c`) when `rest ≠ []`, parameterized over `A : RustAlloc`. -/
theorem overDecHeadCons_ext {A : RustAlloc} : OverDecHeadConsStmtExt A := by
  intro img ext _himg s0 s g v rest hne hsuf hlen hregs
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hlen_nz := top_rest_len_ofNat64_ne_zero hne hsuf hlen
  have hstep := top_head_cons_wp img.base ext s g rest hlen_nz
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  refine top_SepWPp_bind_sepWP_frame hF hsym hstep
    (top_overDecHeapExt_eq_head_split A g rest v)
    fun sf hpcf hrunf hFf hsymf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hFf, hsymf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (top_overDecHeapExt_eq_head_split A g rest v).symm

/-- Loop head (`+0x2160 → +0x2620`) when `rest = []`, parameterized over `A : RustAlloc`. -/
theorem overDecHeadNil_ext {A : RustAlloc} : OverDecHeadNilStmtExt A := by
  intro img ext _himg s0 s g v _hlen hregs
  rcases hregs with ⟨hpc, hrun, hsp, hal, htr, hF, hsym,
    hx19, hx20, hx26, hx21, hx24, hx25, hx27, hx28, hx29, hvregs⟩
  have hstep := top_head_nil_wp img.base ext s g
    hpc hrun hsp hx19 hx20 hx21 hx24 hx25 hx26 hx27 hx28 hx29
  refine top_SepWPp_bind_sepWP_frame hF hsym hstep
    (top_overDecHeapExt_eq_head_split A g [] v)
    fun sf hpcf hrunf hFf hsymf hpost => ?_
  rcases hpost with ⟨hsp_f, htr_f, hx19_f, hx20_f, hx21_f, hx24_f, hx25_f, hx26_f, hx27_f, hx28_f, hx29_f, hvregs_f⟩
  have hal_f : (sf.sp &&& 15#64 == 0#64) = true := by rwa [hsp_f, ← hsp]
  refine SepWPp.done hpcf hrunf ⟨⟨hpcf, hrunf, hsp_f, hal_f, htr_f.trans htr, hFf, hsymf,
    hx19_f, hx20_f, hx26_f, hx21_f, hx24_f, hx25_f, hx27_f, hx28_f, hx29_f, hvregs_f.trans hvregs⟩, ?_⟩
  exact Entails.of_eq (top_overDecHeapExt_eq_head_split A g [] v).symm

end HeadExt

/-- `OverPrevDecodeStmtExt A` from the key step and the four arm groups (`OverDecArmStmtTRExt A`). -/
theorem overPrevDecode_of_key_arms_ext {A : RustAlloc} (hK : OverDecKeyStmtExt A)
    (hV : OverDecArmStmtTRExt A OverDecVarintField) (hB : OverDecArmStmtTRExt A OverDecBytesField)
    (hS : OverDecArmStmtTRExt A OverDecSenderField) (hR : OverDecArmStmtTRExt A OverDecRecvField) :
    OverPrevDecodeStmtExt A :=
  overPrevDecode_of_steps_ext overDecEntry_ext
    (overDecField_of_key_arm_ext hK (overDecArm_any_ext hV hB hS hR) (fun _ h => h))
    overDecHeadCons_ext overDecHeadNil_ext

theorem overPrevDecode_of_key_arms (hK : OverDecKeyStmt)
    (hV : OverDecArmStmtTR OverDecVarintField) (hB : OverDecArmStmtTR OverDecBytesField)
    (hS : OverDecArmStmtTR OverDecSenderField) (hR : OverDecArmStmtTR OverDecRecvField) :
    OverPrevDecodeStmt :=
  overPrevDecode_of_key_arms_ext hK hV hB hS hR

/-- Top-level CLI `OverPrevDecodeStmtExt A` (`+0x1ee8 → +0x2620`), parameterized over the tag-6
(`OverDecSenderField`) and tag-7 (`OverDecRecvField`) arm contracts. -/
theorem overPrevDecode_cli_of_arms_ext {A : RustAlloc}
    (hSender : OverDecArmStmtTRExt A OverDecSenderField)
    (hRecv : OverDecArmStmtTRExt A OverDecRecvField) :
    OverPrevDecodeStmtExt A :=
  overPrevDecode_of_key_arms_ext overDecKey_cli_ok_ext
    overDecArm_varint_cli_okTR_ext overDecArm_bytes_cli_okTR_ext hSender hRecv

theorem overPrevDecode_cli_of_arms
    (hSender : OverDecArmStmtTR OverDecSenderField)
    (hRecv : OverDecArmStmtTR OverDecRecvField) :
    OverPrevDecodeStmt :=
  overPrevDecode_cli_of_arms_ext hSender hRecv

/-- Convert a `VerNe.Chain3.OverDecArmStmtTRExt A` arm contract to `PrevDec.OverDecArmStmtTRExt A`. -/
theorem overDecArmStmtTRExt_of_chain3 {A : RustAlloc} {P Q : GenFieldQ → Prop}
    (hPQ : ∀ fl, P fl → Q fl)
    (h : VerNe.Chain3.OverDecArmStmtTRExt A Q) :
    OverDecArmStmtTRExt A P := by
  intro img ext himg hAX s0 s g v fl rest hP hok hfr hsuf hlen hregs hx0 hx22
  cases g with
  | mk q r19 r20 r26 prevCap prevPtr encCap encPtr enc sv =>
    exact h img ext himg hAX s0 s
      ⟨q, r19, r20, r26, prevCap, prevPtr, encCap, encPtr, enc, sv⟩
      v fl rest (hPQ fl hP) hok hfr hsuf hlen hregs hx0 hx22

private theorem overDecArmStmtTR_of_chain3 {P Q : GenFieldQ → Prop}
    (hPQ : ∀ fl, P fl → Q fl)
    (h : VerNe.Chain3.OverDecArmStmtTR Q) :
    OverDecArmStmtTR P :=
  overDecArmStmtTRExt_of_chain3 hPQ h

/-- Top-level CLI `OverPrevDecodeStmtExt A` derived from the `VerNe.Chain3` sender-arm and
`Chain3OkAtWExt A` contracts. -/
theorem overPrevDecode_cli_of_chain3_ext {A : RustAlloc}
    (hSender : VerNe.Chain3.OverDecArmStmtTRExt A VerNe.Chain3.OverDecSenderField)
    (hChain3 : ∀ img ext, Obj.Loads libsignalSessionImage img →
      CryptoVerification.LibsignalTripleRatchet.AllocContractsX img A ext →
      Chain3OkAtWExt A img ext) :
    OverPrevDecodeStmtExt A :=
  overPrevDecode_cli_of_arms_ext
    (overDecArmStmtTRExt_of_chain3
      (fun fl h => match fl, h with | .base (.sender _), _ => trivial)
      hSender)
    (overDecArmStmtTRExt_of_chain3
      (fun fl h => match fl, h with | .base (.recv _), _ => trivial)
      (overDecArm_recv_of_chain3_ext hChain3))

/-- Unconditional CLI `OverPrevDecodeStmt` (`+0x1ee8 → +0x2620`) for the handshake closure. -/
theorem overPrevDecode_cli : OverPrevDecodeStmt :=
  overPrevDecode_cli_of_arms
    (overDecArmStmtTR_of_chain3
      (fun fl h => match fl, h with | .base (.sender _), _ => trivial)
      overDecArmSender_cli)
    (overDecArmStmtTR_of_chain3
      (fun fl h => match fl, h with | .base (.recv _), _ => trivial)
      overDecArmRecv_cli)

end CryptoVerification.Cli.E2E.Pqxdh.ResponderClosure.PrevDec
