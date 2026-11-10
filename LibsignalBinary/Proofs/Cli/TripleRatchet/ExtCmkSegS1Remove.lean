/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.TripleRatchet.ExtCmkSeams
public import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import GeneratedLean.LibsignalSessionCode -- shake: keep
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.DuplicatedMessageReturn
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.TakePathProofs.Remove
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp
public meta import Lean -- shake: keep

/-!
# `SP2Ext` Segment S1 Message-Key Removal Block

Proves the `Vec::remove(p)`, buffer deallocation, and `Ok` return-staging block (`+0x5e4 .. +0x778`)
of `RatchetState::consume_message_key` on `SP2Ext img.base ext` at `cmkStackX = 20480` bytes.
-/

@[expose] public section

set_option maxRecDepth 2000000
set_option maxHeartbeats 400000
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Proofs.libsignal.Stage1X.CmkX

open Arm64 ProofLib ProofLib.SepSolver
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification CryptoVerification.RustHeap
open CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.SessionModel
open CryptoVerification.LibsignalSession.TakePath
open Proofs.libsignal.Hooks2 (SP2Ext SP2Ext_fnAddr sub_ok_at_caller)
open Proofs.libsignal.Stage1X

attribute [local irreducible] Program.fetch Program.externAt? Program.fnOff
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

theorem L1_SegS1Remove : True := trivial

open Lean Elab Tactic in
elab "cmk_fetches_range_x " b:term:max ext:term:max lo:num hi:num : tactic => do
  let loVal := lo.getNat
  let lenq := Syntax.mkNumLit (toString (hi.getNat + 4 - loVal))
  evalTactic (← `(tactic|
    code_fetches_range libsignalSessionCode CryptoVerification.LibsignalSession.TakePath.libsignalSessionBin
      $b (Rust.withPanics $ext)
      (ls_lemma% fnOff "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")
      (num% (ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
      $lo $lenq))

/-! ## Stack Helpers and `cmkPreLoopHeapX` -/

theorem cmkStackX_recombine (sp0 : BitVec 64) (s0 : State) :
    (stackAt (sp0 - 480#64) 20000 ∗ memRegion (sp0 - 480#64) 384 ∗ cmkSavedRegs sp0 s0) ⊢
      stackAt sp0 cmkStackX := by
  rw [← stackAt_7712_sep_low_eq_20000 sp0, stackAt_cmkStackX_eq_cmkStack_sep_low sp0]
  have hre :
      ((stackAt (sp0 - 480#64) 7712 ∗ cmkLowStack sp0) ∗
        memRegion (sp0 - 480#64) 384 ∗ cmkSavedRegs sp0 s0) =
      ((stackAt (sp0 - 480#64) 7712 ∗ memRegion (sp0 - 480#64) 384 ∗ cmkSavedRegs sp0 s0) ∗
        cmkLowStack sp0) := by ac_rfl
  rw [hre]
  exact sepConj_mono_left (cmkStack_recombine sp0 s0)

theorem stackAt_20000_split_ext (sp : BitVec 64) :
    stackAt sp 20000 = stackAt sp extHookStack ∗ stackAt (sp - 16384#64) 3616 := by
  rw [show extHookStack = 16384 from rfl]
  unfold stackAt
  rw [show sp - 16384#64 - 3616#64 = sp - 20000#64 by bv_omega,
      show sp - 16384#64 = (sp - 20000#64) + 3616#64 by bv_omega,
      sepConj_comm,
      ← memRegion_split (sp - 20000#64) 3616 16384 (by decide)]

def cmkPreLoopHeapX (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost) (s0 : State) : SepProp :=
  ratchetAt A x.self x.G x.st ∗
  (x.theirA ↦ₛ x.their.bytes.toList) ∗
  (x.ckA ↦ₛ chainKeyBytes x.ck) ∗
  memRegion x.ret 88 ∗
  (logFilterAddr img ↦₆₄ 0#64) ∗
  stackAt (s0.sp - 480#64) 20000 ∗
  memRegion (s0.sp - 480#64) 384 ∗
  cmkSavedRegs s0.sp s0 ∗
  A.pool

theorem cmkPreLoopHeap_sep_low_eq_x (A : RustAlloc) (img : Obj.Image) (x : ConsumeMessageKeyGhost)
    (s0 : State) (R : SepProp) :
    cmkPreLoopHeap A img x s0 ∗ (cmkLowStack s0.sp ∗ R) =
      cmkPreLoopHeapX A img x s0 ∗ R := by
  unfold cmkPreLoopHeap cmkPreLoopHeapX
  rw [← stackAt_7712_sep_low_eq_20000 s0.sp]
  ac_rfl

/-! ## `remove(p)` and `Ok` Staging Block (`+0x5e4 .. +0x778`) -/

theorem sepWP_seq_frame_img {prog : Program} {img : Obj.Image} {mid target : BitVec 64}
    {s : State} {P P1 Frame : SepProp}
    {Post1 : State → SepProp → Prop} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hP : P = P1 ∗ Frame)
    (h1 : SepWP prog mid s P1 Post1)
    (h2 : ∀ s1 P_out, s1.pc = mid → s1.status = .Running →
      img.FrozenLoaded s1 → s1.symtab = img.symtab → Post1 s1 P_out →
      SepWP prog target s1 (P_out ∗ Frame) post) :
    SepWP prog target s P post := by
  rw [hP]
  unfold SepWP at h1 ⊢
  intro R hm
  rw [sepConj_assoc] at hm
  intro hL
  rcases h1 (Frame ∗ R) hm hL with ⟨s1, hsteps1, ⟨hpc1, hrun1, P_out, hm1, hPost1⟩ | ⟨_, hoom⟩⟩
  swap; · exact (not_satisfies_false_sepConj hoom).elim
  rw [← sepConj_assoc] at hm1
  have h2' := h2 s1 P_out hpc1 hrun1 (hsteps1.frozenLoaded hfrozen)
    (hsteps1.symtab_eq.trans hsym) hPost1
  unfold SepWP at h2'
  exact reaches_pc_steps hsteps1 (h2' R hm1) hL

private meta partial def flattenSepConjX (e : Lean.Expr) : List Lean.Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``sepConj 2 then
    flattenSepConjX e.appFn!.consumeMData.appArg! ++ flattenSepConjX e.appArg!
  else
    [e]

private meta def removeFirstDefEqX (x : Lean.Expr) : List Lean.Expr → Lean.MetaM (List Lean.Expr)
  | [] => return []
  | y :: ys => do
    if ← Lean.Meta.isDefEq x y then return ys
    else return y :: (← removeFirstDefEqX x ys)

private meta def mkSepConjChainX : List Lean.Expr → Lean.MetaM Lean.Expr
  | [] => Lean.Meta.mkConstWithFreshMVarLevels ``emp
  | [x] => return x
  | x :: xs => do
    let rest ← mkSepConjChainX xs
    Lean.Meta.mkAppM ``sepConj #[x, rest]

elab "wp_seq_frame_img " hfrozen:term:max hsym:term:max h:term : tactic =>
  Lean.Elab.Tactic.withMainContext do
    let goalType := (← Lean.instantiateMVars (← Lean.Elab.Tactic.getMainTarget)).consumeMData
    let P := (goalType.getAppArgs)[3]!.consumeMData
    let hExpr ← Lean.Elab.Tactic.elabTerm h none
    let hType := (← Lean.instantiateMVars (← Lean.Meta.inferType hExpr)).consumeMData
    let P1 := (hType.getAppArgs)[3]!.consumeMData
    let pAtoms := flattenSepConjX P
    let p1Atoms := flattenSepConjX P1
    let remAtoms ← p1Atoms.foldlM (fun acc x => removeFirstDefEqX x acc) pAtoms
    let frameExpr ← mkSepConjChainX remAtoms
    let frameExpr ← Lean.instantiateMVars frameExpr
    let frameStx ← Lean.Elab.Term.exprToSyntax frameExpr
    Lean.Elab.Tactic.evalTactic (← `(tactic|
      refine sepWP_seq_frame_img $hfrozen $hsym (Frame := $frameStx) (by ac_rfl) $h ?_))

theorem cmk_remove_pre_memmove_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    {A : RustAlloc}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (elemAddr chAddr ret : BitVec 64)
    (remBytes mkLen : BitVec 64)
    (v424 v416 v408 v400 v384 v376 v368 v224 v216 : BitVec 64)
    (v388 : BitVec 32)
    (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = remBytes)
    (hx8 : s.readReg64 .x8 = elemAddr + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = mkLen)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkName + 1580#64) s
      (messageKeyAt A gk elemAddr ∗
       ((s0.sp - 424#64) ↦₆₄ v424) ∗
       ((s0.sp - 416#64) ↦₆₄ v416) ∗
       ((s0.sp - 408#64) ↦₆₄ v408) ∗
       ((s0.sp - 400#64) ↦₆₄ v400) ∗
       ((s0.sp - 388#64) ↦₃₂ v388) ∗
       ((s0.sp - 384#64) ↦₆₄ v384) ∗
       ((s0.sp - 376#64) ↦₆₄ v376) ∗
       ((s0.sp - 368#64) ↦₆₄ v368) ∗
       ((s0.sp - 224#64) ↦₆₄ v224) ∗
       ((s0.sp - 216#64) ↦₆₄ v216))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x0 = elemAddr ∧
        s1.readReg64 .x1 = elemAddr + 104#64 ∧
        s1.readReg64 .x2 = remBytes ∧
        s1.readReg64 .x19 = chAddr ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length ∧
        s1.readReg64 .x22 = s0.sp - 224#64 ∧
        s1.readReg64 .x23 = 0#64 ∧
        s1.readReg64 .x24 = mkLen ∧
        s1.readReg64 .x25 = 0#64 ∧
        s1.readReg64 .x26 = gk.1.cipher.cap ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          messageKeyAt A gk elemAddr ∗
          ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
          ((s0.sp - 416#64) ↦₆₄ gk.1.mac.ptr) ∗
          ((s0.sp - 408#64) ↦₆₄ gk.1.iv.ptr) ∗
          ((s0.sp - 400#64) ↦₆₄ gk.1.cipher.ptr) ∗
          ((s0.sp - 388#64) ↦₃₂ gk.2.counter) ∗
          ((s0.sp - 384#64) ↦₆₄ gk.1.mac.cap) ∗
          ((s0.sp - 376#64) ↦₆₄ gk.1.iv.cap) ∗
          ((s0.sp - 368#64) ↦₆₄ ret) ∗
          ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))) := by
  cmk_fetches_range_x b ext 0x5e4 0x628
  generalize_entry (SP2Ext b ext).fnAddr cmkName = entry
  examples_hide_fetches
  rw [messageKeyAt_eq_cells_sep_heap]
  simp only [sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm, hx8], by simp only [wp_norm, arm64_norm, hx8],
    by simp only [wp_norm, arm64_norm, hx2], by simp only [wp_norm, arm64_norm, hx19],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hsp],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx24],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [calleeSavedVRegs, wp_norm, arm64_norm]⟩, ?_⟩
  exact Entails.refl _

@[local simp] theorem zeroExtend_64_truncate_32_zeroExtend_64_x (x : BitVec 32) :
    ((x.zeroExtend 64).truncate 32).zeroExtend 64 = x.zeroExtend 64 := by
  bv_kernel

theorem cmk_remove_post_memmove_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (chAddr : BitVec 64) (mkLen : Nat)
    (v320 v312 : BitVec 64)
    (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1584#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx21 : s.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length)
    (hx22 : s.readReg64 .x22 = s0.sp - 224#64)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 mkLen)
    (hx26 : s.readReg64 .x26 = gk.1.cipher.cap)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (hcipher_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hseed_ne : gk.2.seed ≠ [])
    (hseed_le : gk.2.seed.length ≤ gk.1.seed.cap.toNat)
    (hseed_lt : gk.1.seed.cap.toNat < 2 ^ 63) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkName + 1648#64) s
      (((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 mkLen) ∗
       ((s0.sp - 320#64) ↦₆₄ v320) ∗
       ((s0.sp - 312#64) ↦₆₄ v312) ∗
       ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
       ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 =
          (gk.1.seed.ptr.extractLsb' 16 8 ++ gk.1.seed.ptr.extractLsb' 8 8 ++
           gk.1.seed.ptr.extractLsb' 0 8 ++ gk.1.seed.cap.extractLsb' 56 8 ++
           gk.1.seed.cap.extractLsb' 48 8 ++ gk.1.seed.cap.extractLsb' 40 8 ++
           gk.1.seed.cap.extractLsb' 32 8 ++ gk.1.seed.cap.extractLsb' 24 8) ∧
        s1.readReg64 .x21 = BitVec.ofNat 64 gk.2.seed.length ∧
        s1.readReg64 .x22 = (gk.1.seed.ptr.extractLsb' 56 8).zeroExtend 64 ∧
        s1.readReg64 .x23 =
          (gk.1.seed.ptr.extractLsb' 48 8 ++ gk.1.seed.ptr.extractLsb' 40 8 ++
           gk.1.seed.ptr.extractLsb' 32 8 ++ gk.1.seed.ptr.extractLsb' 24 8).zeroExtend 64 ∧
        s1.readReg64 .x24 = BitVec.ofNat 64 mkLen ∧
        s1.readReg64 .x26 = gk.1.cipher.cap ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          ((chAddr + 64#64) ↦₆₄ (BitVec.ofNat 64 mkLen - 1#64)) ∗
          ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr) ∗
          ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
          ((s0.sp - 216#64) ↦₆₄ gk.1.seed.ptr))) := by
  have hcipher_ne : gk.1.cipher.cap + 1#64 ≠ 0#64 := cipher_cap_add_one_ne_zero hcipher_lt
  have hseed_nz : BitVec.ofNat 64 gk.2.seed.length ≠ 0#64 :=
    seed_len_ofNat_ne_zero hseed_ne hseed_le hseed_lt
  cmk_fetches_range_x b ext 0x630 0x66c
  generalize_entry (SP2Ext b ext).fnAddr cmkName = entry
  examples_hide_fetches
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [hcipher_ne])
  wp_step
  wp_step
  wp_step
  wp_step
  apply SepWP.ite_false (by rfl) (by simp [hseed_nz])
  have h312 : (s0.sp - 320#64) + 8#64 = s0.sp - 312#64 := (RemoveBvArith.bv_sub_add_eq).symm
  have h216 : (s0.sp - 224#64) + 8#64 = s0.sp - 216#64 := (RemoveBvArith.bv_sub_add_eq).symm
  wp_simp_pre only [arm64_norm]
  conv =>
    arg 4
    rw [← sepConj_assoc ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr),
        ← h312, pointsTo64_pair_eq_unaligned_16 (s0.sp - 320#64) gk.1.seed.cap gk.1.seed.ptr,
        ← h216, pointsTo64_pair_eq_unaligned_16 (s0.sp - 224#64) gk.1.seed.cap gk.1.seed.ptr]
    simp only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx24], by simp only [wp_norm, arm64_norm, hx26],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [calleeSavedVRegs, wp_norm, arm64_norm]⟩, ?_⟩
  conv =>
    rhs
    rw [← sepConj_assoc ((s0.sp - 320#64) ↦₆₄ gk.1.seed.cap) ((s0.sp - 312#64) ↦₆₄ gk.1.seed.ptr),
        ← h312, pointsTo64_pair_eq_unaligned_16 (s0.sp - 320#64) gk.1.seed.cap gk.1.seed.ptr,
        ← h216, pointsTo64_pair_eq_unaligned_16 (s0.sp - 224#64) gk.1.seed.cap gk.1.seed.ptr]
    simp only [bv_sub_add_lit, Nat.reduceSub, sepConj_assoc]
  simp only [arm64_norm, truncate_16_zeroExtend_32]
  exact Entails.refl _

@[irreducible] def DeallocAtX (img : Obj.Image) (A : RustAlloc)
    (ext : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok (SP2Ext img.base ext) addr
    ((Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack A extHookStack).inImage img)

theorem deallocAtX_of_contracts {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    DeallocAtX img A ext ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) := by
  unfold DeallocAtX
  exact dealloc_ok_at_x hA (name := cmkName) (k := num% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))

theorem call_dealloc_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)}
    {entry target_pc : BitVec 64}
    (hdealloc : DeallocAtX img A ext (entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")))
    (p : BitVec 64) (size align : Nat) (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = p)
    (hx1 : (s.readReg64 .x1).toNat = size)
    (hx2 : (s.readReg64 .x2).toNat = align)
    (hlayout : LayoutOk size align)
    (hpc : s.pc = entry + bv% (ls_off% "__rustc::__rust_dealloc" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_val)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP (SP2Ext img.base ext) target_pc sf (A.pool ∗ stackAt sp_val extHookStack ∗ Frame) post) :
    SepWP (SP2Ext img.base ext) target_pc s
      ((A.pool ∗ A.live p size align ∗ memRegion p size ∗ stackAt sp_val extHookStack) ∗ Frame) post := by
  unfold DeallocAtX at hdealloc
  refine SepWP.call_subroutine_frame hdealloc (x := (p, size, align)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, hsp, sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hfrozen, hsym⟩, ⟨hx0, hx1, hx2, hlayout⟩, ?_⟩
    exact Satisfies.of_eq hm
  · intro R' sf _ hp
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [Spec.inImage, Proofs.libsignal.Stage1X.rustDeallocExternSpecWithStack, hsp, sepConj_assoc]
    exact SepWP.pure_elim (fun htr => hnext sf h1 h2 (h3.trans hsp) h4 htr)

private theorem layoutOk_of_cap_ne_zero {cap : BitVec 64} (hcap : cap ≠ 0) (hlt : cap.toNat < 2 ^ 63) :
    LayoutOk cap.toNat 1 := by
  refine ⟨Nat.pos_of_ne_zero fun h0 => hcap (BitVec.eq_of_toNat_eq (by simpa using h0)), ⟨0, rfl⟩, hlt⟩

theorem cmk_dealloc_cipher_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (cap ptr : BitVec 64) (s0 s : State)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx26 : s.readReg64 .x26 = cap) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1668#64) s
      (A.pool ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) extHookStack ∗
       ((s0.sp - 400#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        CalleeSavedPreserved s s1 ∧
        s1.trace = s.trace ∧
        (P1 ⊢ A.pool ∗ stackAt (s0.sp - 480#64) extHookStack ∗ ((s0.sp - 400#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocAtX_of_contracts hA
  cmk_fetches_range_x img.base ext 0x670 0x680
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx26]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align, ?_,
      by simp only [wp_norm, arm64_norm], Entails.refl _⟩
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm]
  · simp only [hcap, ↓reduceIte]
    wp_step
    apply SepWP.ite_false (by rfl) (by simp; exact hcap)
    wp_steps
    have hre :
        (A.pool ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
          stackAt (s0.sp - 480#64) extHookStack ∗ ((s0.sp - 400#64) ↦₆₄ ptr)) =
        ((A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
          stackAt (s0.sp - 480#64) extHookStack) ∗ ((s0.sp - 400#64) ↦₆₄ ptr)) := by ac_rfl
    rw [hre]
    refine call_dealloc_wp_x hdealloc ptr cap.toNat 1 (s0.sp - 480#64) (entry + bv% (1668))
      (by rw [Obj.Image.frozenLoaded_iff] at hfrozen ⊢; exact hfrozen)
      (by simp only [wp_norm, arm64_norm, hsym])
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx26])
      (by simp only [wp_norm, arm64_norm]) (layoutOk_of_cap_ne_zero hcap hlt)
      (by simp only [wp_norm, arm64_norm, hpc])
      (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
      (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
    intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
    have hsp_align' : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      simpa [State.spAligned, hsp] using hsp_align
    refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf, hsp_align', ?_, by simp only [wp_norm, arm64_norm, htr_sf], Entails.refl _⟩
    simpa (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm] using hcs

theorem cmk_dealloc_mac_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (cap ptr : BitVec 64) (s0 s : State)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1688#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = cap) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1704#64) s
      (A.pool ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) extHookStack ∗
       ((s0.sp - 416#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        CalleeSavedPreserved s s1 ∧
        s1.trace = s.trace ∧
        (P1 ⊢ A.pool ∗ stackAt (s0.sp - 480#64) extHookStack ∗ ((s0.sp - 416#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocAtX_of_contracts hA
  cmk_fetches_range_x img.base ext 0x698 0x6a4
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align, ?_,
      by simp only [wp_norm, arm64_norm], Entails.refl _⟩
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm]
  · simp only [hcap, ↓reduceIte]
    wp_step
    apply SepWP.ite_false (by rfl) (by simp; exact hcap)
    wp_steps
    have hre :
        (A.pool ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
          stackAt (s0.sp - 480#64) extHookStack ∗ ((s0.sp - 416#64) ↦₆₄ ptr)) =
        ((A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
          stackAt (s0.sp - 480#64) extHookStack) ∗ ((s0.sp - 416#64) ↦₆₄ ptr)) := by ac_rfl
    rw [hre]
    refine call_dealloc_wp_x hdealloc ptr cap.toNat 1 (s0.sp - 480#64) (entry + bv% (1704))
      (by rw [Obj.Image.frozenLoaded_iff] at hfrozen ⊢; exact hfrozen)
      (by simp only [wp_norm, arm64_norm, hsym])
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx1])
      (by simp only [wp_norm, arm64_norm]) (layoutOk_of_cap_ne_zero hcap hlt)
      (by simp only [wp_norm, arm64_norm, hpc])
      (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
      (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
    intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
    have hsp_align' : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      simpa [State.spAligned, hsp] using hsp_align
    refine SepWP.done hpc_sf hrun_sf ⟨hsp_sf, hsp_align', ?_, by simp only [wp_norm, arm64_norm, htr_sf], Entails.refl _⟩
    simpa (config := { decide := true }) only [Arm64.CalleeSavedPreserved, arm64_norm] using hcs

theorem cmk_dealloc_iv_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (cap ptr v19 v22 v23 v26 v27 v29 : BitVec 64) (counter : BitVec 32) (s0 s : State)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hlt : cap.toNat < 2 ^ 63)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1724#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx1 : s.readReg64 .x1 = cap)
    (hx9 : s.readReg64 .x9 = counter.zeroExtend 64)
    (hx19 : s.readReg64 .x19 = v19)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx25 : s.readReg64 .x25 = counter.zeroExtend 64)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1768#64) s
      (A.pool ∗
       (if cap = 0 then emp else A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
       stackAt (s0.sp - 480#64) extHookStack ∗
       ((s0.sp - 408#64) ↦₆₄ ptr))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x23 = v23 ∧
        s1.readReg64 .x25 = counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ A.pool ∗ stackAt (s0.sp - 480#64) extHookStack ∗ ((s0.sp - 408#64) ↦₆₄ ptr))) := by
  have hdealloc := deallocAtX_of_contracts hA
  cmk_fetches_range_x img.base ext 0x6bc 0x6e4
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  by_cases hcap : cap = 0
  · subst hcap
    simp only [↓reduceIte, emp_sepConj]
    wp_step
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc, hx1]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
      by simp only [wp_norm, arm64_norm, hx19], by simp only [wp_norm, arm64_norm, hx22],
      by simp only [wp_norm, arm64_norm, hx23], by simp only [wp_norm, arm64_norm, hx25],
      by simp only [wp_norm, arm64_norm, hx26], by simp only [wp_norm, arm64_norm, hx27],
      by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [calleeSavedVRegs, wp_norm, arm64_norm]⟩, Entails.refl _⟩
  · simp only [hcap, ↓reduceIte]
    wp_step
    apply SepWP.ite_false (by rfl) (by simp; exact hcap)
    wp_steps
    have hre :
        (A.pool ∗ (A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat) ∗
          stackAt (s0.sp - 480#64) extHookStack ∗ ((s0.sp - 408#64) ↦₆₄ ptr)) =
        ((A.pool ∗ A.live ptr cap.toNat 1 ∗ memRegion ptr cap.toNat ∗
          stackAt (s0.sp - 480#64) extHookStack) ∗ ((s0.sp - 408#64) ↦₆₄ ptr)) := by ac_rfl
    rw [hre]
    refine call_dealloc_wp_x hdealloc ptr cap.toNat 1 (s0.sp - 480#64) (entry + bv% (1752))
      (by rw [Obj.Image.frozenLoaded_iff] at hfrozen ⊢; exact hfrozen)
      (by simp only [wp_norm, arm64_norm, hsym])
      (by simp only [wp_norm, arm64_norm]) (by simp only [wp_norm, arm64_norm, hx1])
      (by simp only [wp_norm, arm64_norm]) (layoutOk_of_cap_ne_zero hcap hlt)
      (by simp only [wp_norm, arm64_norm, hpc])
      (by simp only [wp_norm, arm64_norm, hrun]) (by simp only [wp_norm, arm64_norm, hsp])
      (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
    intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
    have hsp_align' : sf.spAligned = true := by
      rw [State.spAligned, hsp_sf]
      simpa [State.spAligned, hsp] using hsp_align
    simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
      hx9, hx19, hx22, hx23, hx26, hx27, hx29] at hcs
    rcases hcs with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩
    wp_steps
    refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc_sf]) (by simp only [wp_norm, arm64_norm, hrun_sf]) ?_
    refine ⟨by simp only [wp_norm, arm64_norm, hsp_sf], by simpa only [wp_norm, arm64_norm] using hsp_align',
      by simp only [wp_norm, arm64_norm, hcs19], by simp only [wp_norm, arm64_norm, hcs22],
      by simp only [wp_norm, arm64_norm, hcs23], by simp only [wp_norm, arm64_norm, hcs25],
      by simp only [wp_norm, arm64_norm, hcs26], by simp only [wp_norm, arm64_norm, hcs27],
      by simp only [wp_norm, arm64_norm, hcs29], ⟨by simp only [wp_norm, arm64_norm, htr_sf], by simp only [calleeSavedVRegs, wp_norm, arm64_norm, hcsv]⟩, Entails.refl _⟩

theorem cmk_remove_prep_mac_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (v19 v21 v22 v23 v29 macCap v424 : BitVec 64) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1668#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkName + 1688#64) s
      (((s0.sp - 424#64) ↦₆₄ v424) ∗ ((s0.sp - 384#64) ↦₆₄ macCap))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x1 = macCap ∧
        s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x26 = v19 >>> 40 ∧
        s1.readReg64 .x27 = v23 ||| (v22 <<< 32) ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((s0.sp - 424#64) ↦₆₄ ((v21 &&& 16777215#64) <<< 40)) ∗
              ((s0.sp - 384#64) ↦₆₄ macCap))) := by
  cmk_fetches_range_x b ext 0x684 0x694
  generalize_entry (SP2Ext b ext).fnAddr cmkName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21],
    by simp only [wp_norm, arm64_norm, hx19], by simp only [wp_norm, arm64_norm, hx22, hx23],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [calleeSavedVRegs, wp_norm, arm64_norm]⟩, ?_⟩
  rw [shiftLeft_40_eq_and_mask24 v21]
  exact Entails.refl _

theorem cmk_remove_prep_iv_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    (v21 v26 v27 v29 ivCap ret : BitVec 64) (counter : BitVec 32) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1704#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx21 : s.readReg64 .x21 = v21)
    (hx26 : s.readReg64 .x26 = v26)
    (hx27 : s.readReg64 .x27 = v27)
    (hx29 : s.readReg64 .x29 = v29) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkName + 1724#64) s
      (((s0.sp - 388#64) ↦₃₂ counter) ∗
       ((s0.sp - 376#64) ↦₆₄ ivCap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x1 = ivCap ∧
        s1.readReg64 .x9 = counter.zeroExtend 64 ∧
        s1.readReg64 .x19 = 1#64 ∧
        s1.readReg64 .x22 = ret ∧
        s1.readReg64 .x23 = v21 >>> 24 ∧
        s1.readReg64 .x25 = counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x27 = v27 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ ((s0.sp - 388#64) ↦₃₂ counter) ∗
              ((s0.sp - 376#64) ↦₆₄ ivCap) ∗
              ((s0.sp - 368#64) ↦₆₄ ret))) := by
  cmk_fetches_range_x b ext 0x6a8 0x6b8
  generalize_entry (SP2Ext b ext).fnAddr cmkName = entry
  examples_hide_fetches
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm], by simp only [wp_norm, arm64_norm, hx21], by simp only [wp_norm, arm64_norm],
    by simp only [wp_norm, arm64_norm, hx26], by simp only [wp_norm, arm64_norm, hx27],
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [calleeSavedVRegs, wp_norm, arm64_norm]⟩, Entails.refl _⟩

@[local simp] theorem bv_add_add_lit_x (x : BitVec 64) (a b : Nat) :
    x + BitVec.ofNat 64 a + BitVec.ofNat 64 b = x + BitVec.ofNat 64 (a + b) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

theorem cmk_remove_write_ok_wp_x {b : BitVec 64} {ext : String → Option (State → State)}
    {A : RustAlloc}
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (ret : BitVec 64) (s0 s : State)
    (hpc : s.pc = (SP2Ext b ext).fnAddr cmkName + 1768#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx22 : s.readReg64 .x22 = ret)
    (hx23 : s.readReg64 .x23 = (BitVec.ofNat 64 gk.2.seed.length) >>> 24)
    (hx25 : s.readReg64 .x25 = gk.2.counter.zeroExtend 64)
    (hx26 : s.readReg64 .x26 =
      (gk.1.seed.ptr.extractLsb' 16 8 ++ gk.1.seed.ptr.extractLsb' 8 8 ++
       gk.1.seed.ptr.extractLsb' 0 8 ++ gk.1.seed.cap.extractLsb' 56 8 ++
       gk.1.seed.cap.extractLsb' 48 8 ++ gk.1.seed.cap.extractLsb' 40 8 ++
       gk.1.seed.cap.extractLsb' 32 8 ++ gk.1.seed.cap.extractLsb' 24 8) >>> 40)
    (hx27 : s.readReg64 .x27 =
      ((gk.1.seed.ptr.extractLsb' 48 8 ++ gk.1.seed.ptr.extractLsb' 40 8 ++
        gk.1.seed.ptr.extractLsb' 32 8 ++ gk.1.seed.ptr.extractLsb' 24 8).zeroExtend 64) |||
      (((gk.1.seed.ptr.extractLsb' 56 8).zeroExtend 64) <<< 32))
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (SP2Ext b ext) ((SP2Ext b ext).fnAddr cmkName + 1916#64) s
      (memRegion (s0.sp - 480#64) 56 ∗
       ((s0.sp - 424#64) ↦₆₄ (((BitVec.ofNat 64 gk.2.seed.length) &&& 16777215#64) <<< 40)) ∗
       memRegion (s0.sp - 304#64) 80 ∗
       ((s0.sp - 224#64) ↦₆₄ gk.1.seed.cap) ∗
       memRegion ret 88 ∗
       vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          memRegion (s0.sp - 480#64) 64 ∗
          memRegion (s0.sp - 304#64) 88 ∗
          consumeMessageKeyResultAt A ret (.ok gk.2))) := by
  cmk_fetches_range_x b ext 0x6e8 0x778
  generalize_entry (SP2Ext b ext).fnAddr cmkName = entry
  examples_hide_fetches
  refine SepWP.weaken_pre
    (sepConj_mono (memRegion_56_entails_write_ok_slots s0.sp)
      (sepConj_mono_right
        (sepConj_mono (memRegion_80_entails_write_ok_slots s0.sp)
          (sepConj_mono_right
            (sepConj_mono_left (memRegion_88_entails_ret_ok_slots ret)))))) ?_
  wp_pull_exists
  conv =>
    arg 4
    rw [pointsTo64_eq_unaligned_2_1_4_1 (ret + 24#64)]
    simp only [bv_add_add_lit_x, sepConj_assoc]
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step; wp_step; wp_step
  wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [arm64_norm]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (shift_sp_256 s0.sp))))))))))) ?_
  wp_pull_exists
  wp_step; wp_step; wp_step; wp_step
  wp_simp_pre only [arm64_norm]
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                  (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                      (shift_ret_68 ret))))))))))))))))))))))))))))))))))))) ?_
  wp_pull_exists
  wp_steps
  refine SepWP.done (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun]) ?_
  refine ⟨by simp only [wp_norm, arm64_norm, hsp], by simpa only [wp_norm, arm64_norm] using hsp_align,
    by simp only [wp_norm, arm64_norm, hx29], ⟨by simp only [wp_norm, arm64_norm], by simp only [calleeSavedVRegs, wp_norm, arm64_norm]⟩, ?_⟩
  simp only [arm64_norm, seed_ptr_reassemble, seed_len_lo16_eq, seed_len_b2_eq,
    seed_len_b3456_eq, seed_len_b7_eq]
  exact write_ok_post_entails s0.sp ret gk

@[irreducible] def MemmoveAtX (img : Obj.Image)
    (ext : String → Option (State → State)) (addr : BitVec 64) : Prop :=
  subroutine_ok (SP2Ext img.base ext) addr ((sessionMemmoveSpec extHookStack).inImage img)

theorem memmoveAtX_of_contracts {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext) :
    MemmoveAtX img ext ((SP2Ext img.base ext).fnAddr cmkName + bv% (ls_off% "memmove" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")) := by
  unfold MemmoveAtX
  exact session_memmove_ok_at_x hA (name := cmkName) (k := num% (ls_off% "memmove" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))

theorem call_memmove_wp_x {img : Obj.Image}
    {ext : String → Option (State → State)}
    {entry target_pc : BitVec 64}
    (hmemmove : MemmoveAtX img ext (entry + bv% (ls_off% "memmove" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key")))
    (base : BitVec 64) (bs : List (BitVec 8)) (dst src len : Nat)
    (sp_val ret_pc : BitVec 64)
    {s : State} {Frame : SepProp} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s)
    (hsym : s.symtab = img.symtab)
    (hx0 : s.readReg64 .x0 = base + BitVec.ofNat 64 dst)
    (hx1 : s.readReg64 .x1 = base + BitVec.ofNat 64 src)
    (hx2 : (s.readReg64 .x2).toNat = len)
    (hdst : dst + len ≤ bs.length)
    (hsrc : src + len ≤ bs.length)
    (hpc : s.pc = entry + bv% (ls_off% "memmove" - ls_off% "<libsignal_protocol::double_ratchet::RatchetState>::consume_message_key"))
    (hrun : s.status = .Running)
    (hsp : s.sp = sp_val)
    (hsp_align : s.spAligned = true)
    (hlr : s.readReg64 .lr = ret_pc)
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = sp_val → CalleeSavedPreserved s sf → sf.trace = s.trace →
      SepWP (SP2Ext img.base ext) target_pc sf
        (((base ↦ₛ listMove bs dst src len) ∗ stackAt sp_val extHookStack) ∗ Frame) post) :
    SepWP (SP2Ext img.base ext) target_pc s
      (((base ↦ₛ bs) ∗ stackAt sp_val extHookStack) ∗ Frame) post := by
  unfold MemmoveAtX at hmemmove
  refine SepWP.call_subroutine_frame hmemmove (x := (base, bs, dst, src, len)) (F := Frame)
    hpc hrun hsp_align hlr ?_ ?_ ?_ ?_
  · intro R hm
    simp only [Spec.inImage, sessionMemmoveSpec, libcMemmoveSpec, hsp, sepConj_assoc,
      satisfies_pure_sepConj]
    refine ⟨⟨hfrozen, hsym⟩, ⟨hx0, hx1, hx2, hdst, hsrc⟩, ?_⟩
    simpa only [sepConj_assoc] using hm
  · intro R' sf _ hp
    simp only [Spec.inImage, sessionMemmoveSpec, libcMemmoveSpec] at hp
    exact not_satisfies_false_sepConj hp
  · intro R' code sf _ he
    simp only [Spec.inImage, sessionMemmoveSpec, libcMemmoveSpec] at he
    exact not_satisfies_false_sepConj he
  · intro sf h1 h2 h3 h4
    simp only [Spec.inImage, sessionMemmoveSpec, libcMemmoveSpec, hsp, sepConj_assoc]
    refine SepWP.pure_elim fun ⟨_, htr⟩ => ?_
    simpa only [sepConj_assoc] using hnext sf h1 h2 (h3.trans hsp) h4 htr

theorem cmk_memmove_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (mkPtr : BitVec 64) (bs : List (BitVec 8)) (p mkLen : Nat)
    (v19 v21 v22 v24 v26 v29 : BitVec 64)
    (s0 s : State)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1580#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx0 : s.readReg64 .x0 = mkPtr + BitVec.ofNat 64 (p * 104))
    (hx1 : s.readReg64 .x1 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104))
    (hx2 : (s.readReg64 .x2).toNat = (mkLen - 1 - p) * 104)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx24 : s.readReg64 .x24 = v24)
    (hx26 : s.readReg64 .x26 = v26)
    (hx29 : s.readReg64 .x29 = v29)
    (hp : p < mkLen)
    (hbs_len : bs.length = mkLen * 104) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1584#64) s
      ((mkPtr ↦ₛ bs) ∗ stackAt (s0.sp - 480#64) extHookStack)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = v19 ∧
        s1.readReg64 .x21 = v21 ∧
        s1.readReg64 .x22 = v22 ∧
        s1.readReg64 .x24 = v24 ∧
        s1.readReg64 .x26 = v26 ∧
        s1.readReg64 .x29 = v29 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢ (mkPtr ↦ₛ listMove bs (p * 104) ((p + 1) * 104) ((mkLen - 1 - p) * 104)) ∗
              stackAt (s0.sp - 480#64) extHookStack)) := by
  have hmemmove := memmoveAtX_of_contracts hA
  have hdst : p * 104 + (mkLen - 1 - p) * 104 ≤ bs.length := by omega
  have hsrc : (p + 1) * 104 + (mkLen - 1 - p) * 104 ≤ bs.length := by omega
  cmk_fetches_range_x img.base ext 0x62c 0x62c
  generalize_entry (SP2Ext img.base ext).fnAddr cmkName = entry
  examples_hide_fetches
  wp_step
  rw [← sepConj_emp ((mkPtr ↦ₛ bs) ∗ stackAt (s0.sp - 480#64) extHookStack)]
  refine call_memmove_wp_x hmemmove mkPtr bs (p * 104) ((p + 1) * 104) ((mkLen - 1 - p) * 104)
    (s0.sp - 480#64) (entry + bv% (1584))
    (by rw [Obj.Image.frozenLoaded_iff] at hfrozen ⊢; exact hfrozen)
    (by simp only [wp_norm, arm64_norm, hsym])
    (by simp only [wp_norm, arm64_norm, hx0]) (by simp only [wp_norm, arm64_norm, hx1]) (by simp only [wp_norm, arm64_norm, hx2])
    hdst hsrc (by simp only [wp_norm, arm64_norm, hpc]) (by simp only [wp_norm, arm64_norm, hrun])
    (by simp only [wp_norm, arm64_norm, hsp]) (by simpa only [wp_norm, arm64_norm] using hsp_align) (by simp only [wp_norm, arm64_norm, hpc]) ?_
  intro sf hpc_sf hrun_sf hsp_sf hcs htr_sf
  have hsp_align' : sf.spAligned = true := by
    rw [State.spAligned, hsp_sf]
    simpa [State.spAligned, hsp] using hsp_align
  simp (config := { decide := true }) only [Arm64.CalleeSavedPreserved, calleeSavedVRegs, wp_norm, arm64_norm,
    hx19, hx21, hx22, hx24, hx26, hx29] at hcs
  rcases hcs with ⟨hcs19, hcs20, hcs21, hcs22, hcs23, hcs24, hcs25, hcs26, hcs27, hcs28, hcs29, hcsv⟩
  rw [sepConj_emp]
  refine SepWP.done hpc_sf hrun_sf ?_
  refine ⟨hsp_sf, hsp_align', hcs19, hcs21, hcs22, hcs24, hcs26, hcs29, ⟨htr_sf, hcsv⟩, Entails.refl _⟩

theorem messageKeyHeap_entails_remove_resources_x (A : RustAlloc)
    (gk : MessageKeyGhost × MessageKeyGenerator) :
    messageKeyHeap A gk ⊢
      ⌜gk.2.seed ≠ [] ∧ gk.1.cipher.cap.toNat < 2 ^ 63 ∧
        gk.1.mac.cap.toNat < 2 ^ 63 ∧ gk.1.iv.cap.toNat < 2 ^ 63 ∧
        gk.2.seed.length ≤ gk.1.seed.cap.toNat ∧ gk.1.seed.cap.toNat < 2 ^ 63⌝ ∗
      (if gk.1.cipher.cap = 0 then emp
       else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗
         memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat) ∗
      (if gk.1.mac.cap = 0 then emp
       else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗
         memRegion gk.1.mac.ptr gk.1.mac.cap.toNat) ∗
      (if gk.1.iv.cap = 0 then emp
       else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗
         memRegion gk.1.iv.ptr gk.1.iv.cap.toNat) ∗
      vecU8Buf A gk.1.seed.cap gk.1.seed.ptr gk.2.seed := by
  unfold messageKeyHeap
  refine Entails.trans
    (sepConj_mono_right
      (sepConj_mono (vecU8Buf_entails_dealloc A gk.1.cipher.cap gk.1.cipher.ptr [])
        (sepConj_mono (vecU8Buf_entails_dealloc A gk.1.mac.cap gk.1.mac.ptr [])
          (sepConj_mono_left (vecU8Buf_entails_dealloc A gk.1.iv.cap gk.1.iv.ptr []))))) ?_
  unfold vecU8Buf
  simp only [sepConj_assoc]
  apply Entails.pure_left
  intro hseed_ne
  apply Entails.pure_left
  rintro ⟨_, hcipher_lt, _⟩
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨_, hmac_lt, _⟩
  rw [← sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨_, hiv_lt, _⟩
  rw [← sepConj_assoc, sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hseed_le, hseed_lt, hseed_ptr⟩
  apply Entails.pure_right ⟨hseed_ne, hcipher_lt, hmac_lt, hiv_lt, hseed_le, hseed_lt⟩
  simp only [sepConj_assoc]
  apply sepConj_mono_right
  apply sepConj_mono_right
  apply sepConj_mono_right
  exact Entails.pure_right ⟨hseed_le, hseed_lt, hseed_ptr⟩ (Entails.refl _)

theorem vecBuf_split_entails_remove_ready_x (A : RustAlloc) (mkCap mkPtr : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator)) {p : Nat} (hp : p < gks.length) :
    (messageKeyAt A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
      (⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
        A.live mkPtr (mkCap.toNat * 104) 8 ∗
        (arrayAt (messageKeyAt A) 104 mkPtr (gks.take p) ∗
         arrayAt (messageKeyAt A) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104)) (gks.drop (p + 1))) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) ⊢
      ∃∗ bs : List (BitVec 8),
        ⌜MessageKeyArrayBytes gks bs ∧ bs.length = gks.length * 104 ∧
          gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧
          gks[p].2.seed ≠ [] ∧ gks[p].1.cipher.cap.toNat < 2 ^ 63 ∧
          gks[p].1.mac.cap.toNat < 2 ^ 63 ∧ gks[p].1.iv.cap.toNat < 2 ^ 63 ∧
          gks[p].2.seed.length ≤ gks[p].1.seed.cap.toNat ∧ gks[p].1.seed.cap.toNat < 2 ^ 63⌝ ∗
        A.live mkPtr (mkCap.toNat * 104) 8 ∗
        (mkPtr ↦ₛ bs) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104) ∗
        (if gks[p].1.cipher.cap = 0 then emp
         else A.live gks[p].1.cipher.ptr gks[p].1.cipher.cap.toNat 1 ∗
           memRegion gks[p].1.cipher.ptr gks[p].1.cipher.cap.toNat) ∗
        (if gks[p].1.mac.cap = 0 then emp
         else A.live gks[p].1.mac.ptr gks[p].1.mac.cap.toNat 1 ∗
           memRegion gks[p].1.mac.ptr gks[p].1.mac.cap.toNat) ∗
        (if gks[p].1.iv.cap = 0 then emp
         else A.live gks[p].1.iv.ptr gks[p].1.iv.cap.toNat 1 ∗
           memRegion gks[p].1.iv.ptr gks[p].1.iv.cap.toNat) ∗
        vecU8Buf A gks[p].1.seed.cap gks[p].1.seed.ptr gks[p].2.seed ∗
        messageKeyHeaps A (gks.eraseIdx p) := by
  refine Entails.trans (vecBuf_reassemble_self A 104 8 (messageKeyAt A) mkCap mkPtr gks hp) ?_
  refine Entails.trans (vecBuf_messageKeyAt_expose_for_remove A mkCap mkPtr gks hp) ?_
  apply Entails.sepExists_elim
  intro bs
  apply Entails.pure_left
  rintro ⟨hbs, hbs_len, hlen, hcap_lt, hptr⟩
  refine Entails.trans
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_left (messageKeyHeap_entails_remove_resources_x A gks[p]))))) ?_
  simp only [sepConj_assoc]
  rw [← sepConj_assoc (A.live _ _ _) (mkPtr ↦ₛ bs),
      ← sepConj_assoc _ (memRegion _ _),
      sepConj_pure_left_comm]
  apply Entails.pure_left
  rintro ⟨hseed_ne, hcipher_lt, hmac_lt, hiv_lt, hseed_le, hseed_lt⟩
  apply Entails.sepExists_right bs
  apply Entails.pure_right
    ⟨hbs, hbs_len, hlen, hcap_lt, hptr, hseed_ne, hcipher_lt, hmac_lt, hiv_lt, hseed_le, hseed_lt⟩
  simp only [sepConj_assoc]
  exact Entails.refl _

theorem cmk_remove_deallocVecs_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (gk : MessageKeyGhost × MessageKeyGenerator)
    (ret v19 v21 v22 v23 : BitVec 64) (s0 s : State)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hcipher_lt : gk.1.cipher.cap.toNat < 2 ^ 63)
    (hmac_lt : gk.1.mac.cap.toNat < 2 ^ 63)
    (hiv_lt : gk.1.iv.cap.toNat < 2 ^ 63)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1648#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx19 : s.readReg64 .x19 = v19)
    (hx21 : s.readReg64 .x21 = v21)
    (hx22 : s.readReg64 .x22 = v22)
    (hx23 : s.readReg64 .x23 = v23)
    (hx26 : s.readReg64 .x26 = gk.1.cipher.cap)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1768#64) s
      (A.pool ∗
       stackAt (s0.sp - 480#64) extHookStack ∗
       (if gk.1.cipher.cap = 0 then emp
        else A.live gk.1.cipher.ptr gk.1.cipher.cap.toNat 1 ∗
          memRegion gk.1.cipher.ptr gk.1.cipher.cap.toNat) ∗
       (if gk.1.mac.cap = 0 then emp
        else A.live gk.1.mac.ptr gk.1.mac.cap.toNat 1 ∗
          memRegion gk.1.mac.ptr gk.1.mac.cap.toNat) ∗
       (if gk.1.iv.cap = 0 then emp
        else A.live gk.1.iv.ptr gk.1.iv.cap.toNat 1 ∗
          memRegion gk.1.iv.ptr gk.1.iv.cap.toNat) ∗
       ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ gk.1.mac.ptr) ∗
       ((s0.sp - 408#64) ↦₆₄ gk.1.iv.ptr) ∗
       ((s0.sp - 400#64) ↦₆₄ gk.1.cipher.ptr) ∗
       memRegion (s0.sp - 392#64) 4 ∗
       ((s0.sp - 388#64) ↦₃₂ gk.2.counter) ∗
       ((s0.sp - 384#64) ↦₆₄ gk.1.mac.cap) ∗
       ((s0.sp - 376#64) ↦₆₄ gk.1.iv.cap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret))
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x19 = 1#64 ∧
        s1.readReg64 .x22 = ret ∧
        s1.readReg64 .x23 = v21 >>> 24 ∧
        s1.readReg64 .x25 = gk.2.counter.zeroExtend 64 ∧
        s1.readReg64 .x26 = v19 >>> 40 ∧
        s1.readReg64 .x27 = v23 ||| (v22 <<< 32) ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          A.pool ∗
          stackAt (s0.sp - 480#64) extHookStack ∗
          ((s0.sp - 424#64) ↦₆₄ ((v21 &&& 16777215#64) <<< 40)) ∗
          memRegion (s0.sp - 416#64) 56)) := by
  wp_seq_frame_img hfrozen hsym
    (cmk_dealloc_cipher_wp_x hA gk.1.cipher.cap gk.1.cipher.ptr s0 s hfrozen hsym hcipher_lt hpc hrun hsp hsp_align hx26)
  rintro s1 P1 hpc1 hrun1 hfrozen1 hsym1 ⟨hsp1, halign1, hcs1, htr1, hP1⟩
  rcases hcs1 with ⟨h19_1, _, h21_1, h22_1, h23_1, _, _, _, _, _, h29_1, hcsv_1⟩
  refine sepWP_weaken_left hP1 ?_
  wp_seq_frame_img hfrozen1 hsym1
    (cmk_remove_prep_mac_wp_x v19 v21 v22 v23 (s0.sp - 96#64) gk.1.mac.cap 0#64 s0 s1
      hpc1 hrun1 hsp1 halign1 (h19_1.trans hx19) (h21_1.trans hx21) (h22_1.trans hx22)
      (h23_1.trans hx23) (h29_1.trans hx29))
  rintro s2 P2 hpc2 hrun2 hfrozen2 hsym2 ⟨hsp2, halign2, hx1_2, h21_2, h26_2, h27_2, h29_2, ⟨htr2, hcsv_2⟩, hP2⟩
  refine sepWP_weaken_left hP2 ?_
  wp_seq_frame_img hfrozen2 hsym2
    (cmk_dealloc_mac_wp_x hA gk.1.mac.cap gk.1.mac.ptr s0 s2 hfrozen2 hsym2 hmac_lt hpc2 hrun2 hsp2 halign2 hx1_2)
  rintro s3 P3 hpc3 hrun3 hfrozen3 hsym3 ⟨hsp3, halign3, hcs3, htr3, hP3⟩
  rcases hcs3 with ⟨_, _, h21_3, _, _, _, _, h26_3, h27_3, _, h29_3, hcsv_3⟩
  refine sepWP_weaken_left hP3 ?_
  wp_seq_frame_img hfrozen3 hsym3
    (cmk_remove_prep_iv_wp_x v21 (v19 >>> 40) (v23 ||| (v22 <<< 32)) (s0.sp - 96#64)
      gk.1.iv.cap ret gk.2.counter s0 s3 hpc3 hrun3 hsp3 halign3
      (h21_3.trans h21_2) (h26_3.trans h26_2) (h27_3.trans h27_2) (h29_3.trans h29_2))
  rintro s4 P4 hpc4 hrun4 hfrozen4 hsym4 ⟨hsp4, halign4, hx1_4, hx9_4, h19_4, h22_4, h23_4, h25_4, h26_4, h27_4, h29_4, ⟨htr4, hcsv_4⟩, hP4⟩
  refine sepWP_weaken_left hP4 ?_
  wp_seq_frame_img hfrozen4 hsym4
    (cmk_dealloc_iv_wp_x hA gk.1.iv.cap gk.1.iv.ptr 1#64 ret
      (v21 >>> 24) (v19 >>> 40) (v23 ||| (v22 <<< 32)) (s0.sp - 96#64) gk.2.counter
      s0 s4 hfrozen4 hsym4 hiv_lt hpc4 hrun4 hsp4 halign4 hx1_4 hx9_4 h19_4 h22_4 h23_4 h25_4 h26_4 h27_4 h29_4)
  rintro s5 P5 hpc5 hrun5 _ _ ⟨hsp5, halign5, h19_5, h22_5, h23_5, h25_5, h26_5, h27_5, h29_5, ⟨htr5, hcsv_5⟩, hP5⟩
  refine sepWP_weaken_left hP5 ?_
  refine SepWP.done hpc5 hrun5 ?_
  refine ⟨hsp5, halign5, h19_5, h22_5, h23_5, h25_5, h26_5, h27_5, h29_5,
    ⟨htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1))),
     hcsv_5.trans (hcsv_4.trans (hcsv_3.trans (hcsv_2.trans hcsv_1)))⟩, ?_⟩
  exact entails_of_eq (by ac_rfl)
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (deallocVecs_slots_entails_memRegion_56 s0.sp gk.1.mac.ptr gk.1.iv.ptr gk.1.cipher.ptr
        gk.1.mac.cap gk.1.iv.cap ret gk.2.counter))))

theorem cmk_remove_0x5e4_wp_x {img : Obj.Image} {A : RustAlloc}
    {ext : String → Option (State → State)} (hA : Proofs.libsignal.Stage1X.AllocContractsX img A ext)
    (mkCap mkPtr chAddr ret : BitVec 64)
    (gks : List (MessageKeyGhost × MessageKeyGenerator))
    (p : Nat) (hp : p < gks.length)
    (s0 s : State)
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (hpc : s.pc = (SP2Ext img.base ext).fnAddr cmkName + 1508#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = s0.sp - 480#64)
    (hsp_align : s.spAligned = true)
    (hx2 : s.readReg64 .x2 = BitVec.ofNat 64 ((gks.length - 1 - p) * 104))
    (hx8 : s.readReg64 .x8 = mkPtr + BitVec.ofNat 64 (p * 104) + 56#64)
    (hx19 : s.readReg64 .x19 = chAddr)
    (hx22 : s.readReg64 .x22 = ret)
    (hx24 : s.readReg64 .x24 = BitVec.ofNat 64 gks.length)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64) :
    SepWP (SP2Ext img.base ext) ((SP2Ext img.base ext).fnAddr cmkName + 1916#64) s
      (A.pool ∗
       stackAt (s0.sp - 480#64) extHookStack ∗
       memRegion (s0.sp - 480#64) 384 ∗
       memRegion ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
       vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr gks)
      (fun s1 P1 =>
        s1.sp = s0.sp - 480#64 ∧
        s1.spAligned = true ∧
        s1.readReg64 .x29 = s0.sp - 96#64 ∧
        (s1.trace = s.trace ∧ calleeSavedVRegs s1 = calleeSavedVRegs s) ∧
        (P1 ⊢
          A.pool ∗
          stackAt (s0.sp - 480#64) extHookStack ∗
          memRegion (s0.sp - 480#64) 384 ∗
          consumeMessageKeyResultAt A ret (.ok gks[p].2) ∗
          ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 (gks.length - 1)) ∗
          vecBuf A 104 8 (messageKeyAt A) mkCap mkPtr (gks.eraseIdx p))) := by
  refine SepWP.weaken_pre
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (memRegion_384_entails_pre_memmove_slots s0.sp)
        (sepConj_mono_right (sepConj_mono_right
          (vecBuf_split_at A 104 8 (messageKeyAt A) mkCap mkPtr gks hp)))))) ?_
  wp_pull_exists
  wp_seq_frame_img hfrozen hsym
    (cmk_remove_pre_memmove_wp_x gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) chAddr ret
      (BitVec.ofNat 64 ((gks.length - 1 - p) * 104)) (BitVec.ofNat 64 gks.length)
      _ _ _ _ _ _ _ _ _ _ s0 s
      hpc hrun hsp hsp_align hx2 hx8 hx19 hx22 hx24 hx29)
  rintro s1 P1 hpc1 hrun1 hfrozen1 hsym1 ⟨hsp1, halign1, hx0_1, hx1_1, hx2_1, hx19_1, hx21_1, hx22_1,
    hx23_1, hx24_1, hx25_1, hx26_1, hx29_1, ⟨htr1, hcsv_1⟩, hP1⟩
  refine sepWP_weaken_left hP1 ?_
  have hre1 :
      ((messageKeyAt A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
         ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
         ((s0.sp - 416#64) ↦₆₄ gks[p].1.mac.ptr) ∗
         ((s0.sp - 408#64) ↦₆₄ gks[p].1.iv.ptr) ∗
         ((s0.sp - 400#64) ↦₆₄ gks[p].1.cipher.ptr) ∗
         ((s0.sp - 388#64) ↦₃₂ gks[p].2.counter) ∗
         ((s0.sp - 384#64) ↦₆₄ gks[p].1.mac.cap) ∗
         ((s0.sp - 376#64) ↦₆₄ gks[p].1.iv.cap) ∗
         ((s0.sp - 368#64) ↦₆₄ ret) ∗
         ((s0.sp - 224#64) ↦₆₄ gks[p].1.seed.cap) ∗
         ((s0.sp - 216#64) ↦₆₄ gks[p].1.seed.ptr)) ∗
       (A.pool ∗
        stackAt (s0.sp - 480#64) extHookStack ∗
        memRegion (s0.sp - 480#64) 56 ∗
        memRegion (s0.sp - 392#64) 4 ∗
        memRegion (s0.sp - 360#64) 136 ∗
        memRegion (s0.sp - 208#64) 112 ∗
        memRegion ret 88 ∗
        ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length) ∗
        ⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
        A.live mkPtr (mkCap.toNat * 104) 8 ∗
        arrayAt (messageKeyAt A) 104 mkPtr (gks.take p) ∗
        arrayAt (messageKeyAt A) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104)) (gks.drop (p + 1)) ∗
        memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) =
      ((messageKeyAt A gks[p] (mkPtr + BitVec.ofNat 64 (p * 104)) ∗
        (⌜gks.length ≤ mkCap.toNat ∧ mkCap.toNat * 104 < 2 ^ 63 ∧ mkPtr ≠ 0 ∧ mkCap ≠ 0⌝ ∗
          A.live mkPtr (mkCap.toNat * 104) 8 ∗
          (arrayAt (messageKeyAt A) 104 mkPtr (gks.take p) ∗
           arrayAt (messageKeyAt A) 104 (mkPtr + BitVec.ofNat 64 ((p + 1) * 104)) (gks.drop (p + 1))) ∗
          memRegion (mkPtr + BitVec.ofNat 64 (gks.length * 104)) ((mkCap.toNat - gks.length) * 104))) ∗
       memRegion (s0.sp - 360#64) 136 ∗
       A.pool ∗
       stackAt (s0.sp - 480#64) extHookStack ∗
       memRegion (s0.sp - 480#64) 56 ∗
       ((s0.sp - 424#64) ↦₆₄ 0#64) ∗
       ((s0.sp - 416#64) ↦₆₄ gks[p].1.mac.ptr) ∗
       ((s0.sp - 408#64) ↦₆₄ gks[p].1.iv.ptr) ∗
       ((s0.sp - 400#64) ↦₆₄ gks[p].1.cipher.ptr) ∗
       memRegion (s0.sp - 392#64) 4 ∗
       ((s0.sp - 388#64) ↦₃₂ gks[p].2.counter) ∗
       ((s0.sp - 384#64) ↦₆₄ gks[p].1.mac.cap) ∗
       ((s0.sp - 376#64) ↦₆₄ gks[p].1.iv.cap) ∗
       ((s0.sp - 368#64) ↦₆₄ ret) ∗
       ((s0.sp - 224#64) ↦₆₄ gks[p].1.seed.cap) ∗
       ((s0.sp - 216#64) ↦₆₄ gks[p].1.seed.ptr) ∗
       memRegion (s0.sp - 208#64) 112 ∗
       memRegion ret 88 ∗
       ((chAddr + 64#64) ↦₆₄ BitVec.ofNat 64 gks.length)) := by
    ac_rfl
  rw [hre1]
  refine SepWP.weaken_pre
    (sepConj_mono (vecBuf_split_entails_remove_ready_x A mkCap mkPtr gks hp)
      (sepConj_mono_left (memRegion_136_entails_post_memmove_slots s0.sp))) ?_
  wp_pull_exists
  refine SepWP.pure_elim ?_
  rintro ⟨hbs, hbs_len, hlen_le, hcap_lt, hptr_ne, hseed_ne, hcipher_lt, hmac_lt, hiv_lt, hseed_le, hseed_lt⟩
  have hx1_1' : s1.readReg64 .x1 = mkPtr + BitVec.ofNat 64 ((p + 1) * 104) := by
    rw [hx1_1, elemAddr_add_104]
  have hx2_1' : (s1.readReg64 .x2).toNat = (gks.length - 1 - p) * 104 := by
    rw [hx2_1, remBytes_toNat_eq hlen_le hcap_lt]
  wp_seq_frame_img hfrozen1 hsym1
    (cmk_memmove_wp_x hA mkPtr _ p gks.length chAddr (BitVec.ofNat 64 gks[p].2.seed.length)
      (s0.sp - 224#64) (BitVec.ofNat 64 gks.length) gks[p].1.cipher.cap (s0.sp - 96#64)
      s0 s1 hfrozen1 hsym1 hpc1 hrun1 hsp1 halign1 hx0_1 hx1_1' hx2_1'
      hx19_1 hx21_1 hx22_1 hx24_1 hx26_1 hx29_1 hp hbs_len)
  rintro s2 P2 hpc2 hrun2 hfrozen2 hsym2 ⟨hsp2, halign2, hx19_2, hx21_2, hx22_2, hx24_2, hx26_2, hx29_2, ⟨htr2, hcsv_2⟩, hP2⟩
  refine sepWP_weaken_left hP2 ?_
  wp_seq_frame_img hfrozen2 hsym2
    (cmk_remove_post_memmove_wp_x gks[p] chAddr gks.length _ _ s0 s2
      hpc2 hrun2 hsp2 halign2 hx19_2 hx21_2 hx22_2 hx24_2 hx26_2 hx29_2
      hcipher_lt hseed_ne hseed_le hseed_lt)
  rintro s3 P3 hpc3 hrun3 hfrozen3 hsym3 ⟨hsp3, halign3, hx19_3, hx21_3, hx22_3, hx23_3, hx24_3, hx26_3, hx29_3, ⟨htr3, hcsv_3⟩, hP3⟩
  refine sepWP_weaken_left hP3 ?_
  wp_seq_frame_img hfrozen3 hsym3
    (cmk_remove_deallocVecs_wp_x hA gks[p] ret _ _ _ _ s0 s3
      hfrozen3 hsym3 hcipher_lt hmac_lt hiv_lt hpc3 hrun3 hsp3 halign3 hx19_3 hx21_3 hx22_3 hx23_3 hx26_3 hx29_3)
  rintro s4 P4 hpc4 hrun4 hfrozen4 hsym4 ⟨hsp4, halign4, hx19_4, hx22_4, hx23_4, hx25_4, hx26_4, hx27_4, hx29_4, ⟨htr4, hcsv_4⟩, hP4⟩
  refine sepWP_weaken_left hP4 ?_
  wp_seq_frame_img hfrozen4 hsym4
    (cmk_remove_write_ok_wp_x gks[p] ret s0 s4
      hpc4 hrun4 hsp4 halign4 hx19_4 hx22_4 hx23_4 hx25_4 hx26_4 hx27_4 hx29_4)
  rintro s5 P5 hpc5 hrun5 _ _ ⟨hsp5, halign5, hx29_5, ⟨htr5, hcsv_5⟩, hP5⟩
  refine sepWP_weaken_left hP5 ?_
  refine SepWP.done hpc5 hrun5 ?_
  refine ⟨hsp5, halign5, hx29_5,
    ⟨htr5.trans (htr4.trans (htr3.trans (htr2.trans htr1))),
     hcsv_5.trans (hcsv_4.trans (hcsv_3.trans (hcsv_2.trans hcsv_1)))⟩, ?_⟩
  rw [ofNat_mkLen_sub_one hp]
  exact entails_of_eq (by ac_rfl)
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono (remove_final_stack_entails_memRegion_384 s0.sp
        gks[p].1.seed.cap gks[p].1.seed.ptr gks[p].1.seed.ptr)
        (sepConj_mono_right (sepConj_mono_right
          (vecBuf_messageKeyAt_of_remove A mkCap mkPtr hbs hp hlen_le hcap_lt hptr_ne))))))

end Proofs.libsignal.Stage1X.CmkX
