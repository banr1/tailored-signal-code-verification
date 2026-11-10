/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import GeneratedLean.LibsignalSessionCode -- shake: keep
public import LibsignalBinary.Proofs.TripleRatchet.Hooks2
import LibsignalBinary.Proofs.CodeLayout
import LibsignalBinary.Proofs.ConsumeMessageKey.Heap
import LibsignalBinary.Proofs.TripleRatchet.Alloc.Defs
import LibsignalBinary.Proofs.TripleRatchet.GeneralizeEntry
import ProofLib.SepLogic.WPp

/-!
# Exact-Stack Symbolic Execution for `SignalMessage` Drop Glue

Decomposes `signalMessageAt` (120 bytes) into deallocatable slice capabilities and proves the
exact-stack contract for `core::ptr::drop_glue::<SignalMessage>` at `32 + extHookStack`.
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000

namespace CryptoVerification.SignalSession.Cli.RunProofs.DropSignalMessageHelpers

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet

attribute [local irreducible] Program.fetch Program.externAt?

gen_decodes CryptoVerification.libsignalSessionCode_tree smDropDec
  [(ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>") →
   (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 116)]

/-! ## Arithmetic and stack helpers -/

private theorem ofNat_beq_zero_false {n : Nat} (h0 : 0 < n) (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n == 0#64) = false := by
  apply beq_false_of_ne
  intro h
  have ht := congrArg BitVec.toNat h
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt] at ht
  change n = 0 at ht
  omega

private theorem ofNat_toNat_eq {n : Nat} (hlt : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]

theorem stackAt_split_ge (sp : BitVec 64) {n m : Nat} (hle : n ≤ m) (hlt : m ≤ 2 ^ 64) :
    stackAt sp m = memRegion (sp - BitVec.ofNat 64 m) (m - n) ∗ stackAt sp n := by
  have h := ProofLib.stackAt_split_bottom sp n (m - n) (by omega)
  have heq : n + (m - n) = m := by omega
  simpa only [heq] using h

theorem subroutine_ok_frame_weaken {α : Type} {prog : Program} {fn : BitVec 64}
    {spec spec' : Spec α} (F : α → State → SepProp)
    (h : subroutine_ok prog fn spec)
    (hpre : ∀ x s0, spec'.pre x s0 ⊢ spec.pre x s0 ∗ F x s0)
    (hpost : ∀ x s0 sf, spec.post x s0 sf ∗ F x s0 ⊢ spec'.post x s0 sf)
    (hpan : ∀ x s0 sf, spec.onPanic x s0 sf ∗ F x s0 ⊢ spec'.onPanic x s0 sf)
    (hexit : ∀ x code s0 sf, spec.onExit x code s0 sf = ⌜False⌝)
    (hoom : ∀ x s0 sf, spec.onOom x s0 sf = ⌜False⌝ := by intros; rfl) :
    subroutine_ok prog fn spec' := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hp hsp
  have hp' : s0.mem ⊨ spec.pre x s0 ∗ (F x s0 ∗ R) := by
    rw [← sepConj_assoc]
    exact Satisfies.mono (sepConj_mono_left (hpre x s0)) hp
  refine h.mono_outcome x (F x s0 ∗ R) s0 hpc hrun hp' hsp fun sf hout => ?_
  rcases hout with ⟨hret, hcc, hq⟩ | ⟨hpan_st, hq⟩ | ⟨code, _, hq⟩ | ⟨_, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpost x s0 sf)) hq
  · refine Or.inr (Or.inl ⟨hpan_st, ?_⟩)
    rw [← sepConj_assoc] at hq
    exact Satisfies.mono (sepConj_mono_left (hpan x s0 sf)) hq
  · rw [hexit] at hq
    exact (not_satisfies_false_sepConj hq).elim
  · rw [hoom] at hq
    exact (not_satisfies_false_sepConj hq).elim

private theorem stackAt_smDrop_split (sp : BitVec 64) :
    stackAt sp (32 + extHookStack) =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  simpa only [Nat.add_comm 32 extHookStack] using
    ProofLib.stackAt_split_cells sp extHookStack 4 (by decide)

private theorem tail_stack_32_from_bottom (sp : BitVec 64) :
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack =
      stackAt (sp - 32#64) extHookStack ∗ cells (sp - 32#64) 4 := by
  rw [show (16416#64 : BitVec 64) = BitVec.ofNat 64 (extHookStack + 32) from rfl,
      ← ProofLib.stackAt_split_bottom sp extHookStack 32 (by decide),
      show extHookStack + 32 = 32 + extHookStack from Nat.add_comm _ _,
      ← stackAt_smDrop_split sp]

private theorem cells4_entails_stack_bottom (sp fp lr x19 w3 : BitVec 64) :
    stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3) ⊢
    memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack := by
  rw [tail_stack_32_from_bottom sp]
  cells_unfold
  exact Entails.sepExists_right fp (Entails.sepExists_right lr
    (Entails.sepExists_right x19 (Entails.sepExists_right w3 (Entails.refl _))))

private theorem sm_tail_post_weaken (a : BitVec 64) (pool : SepProp) (sp : BitVec 64) :
    pool ∗ stackAt sp extHookStack ∗ memRegion a 120 ∗ memRegion (sp - 16416#64) 32 ⊢
      memRegion a 120 ∗ pool ∗ stackAt sp (32 + extHookStack) := by
  rw [stackAt_smDrop_split sp, ← tail_stack_32_from_bottom sp]
  exact Entails.of_eq (by ac_rfl)

/-! ## `SignalMessage` layout decomposition -/

@[reducible]
private def deallocOpt (A : RustAlloc) (sz ptr : BitVec 64) : SepProp :=
  if (sz == 0#64) = true then emp
  else ⌜LayoutOk sz.toNat 1⌝ ∗ A.live ptr sz.toNat 1 ∗ memRegion ptr sz.toNat

private theorem sep_pull_third (P Q R S : SepProp) : P ∗ Q ∗ R ∗ S = R ∗ P ∗ Q ∗ S := by
  ac_rfl

private theorem vecU8At_entails_deallocOpt (A : RustAlloc) (a cap ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    vecU8At A a cap ptr bs ⊢
      (a ↦₆₄ cap) ∗ ((a + 8#64) ↦₆₄ ptr) ∗ memRegion (a + 16#64) 8 ∗
      deallocOpt A cap ptr := by
  refine Entails.trans (vecU8At_entails_dealloc A a cap ptr bs) ?_
  unfold vecHeader deallocOpt
  rw [sepConj_pure_left_comm]
  apply Entails.pure_left; rintro ⟨_, hcap_lt, _⟩
  have hbeq : ((cap == 0#64) = true) ↔ cap = 0 := beq_iff_eq
  simp only [hbeq]
  rw [sepConj_assoc, sepConj_assoc]
  refine sepConj_mono_right (sepConj_mono_right (sepConj_mono (pointsTo64_entails_memRegion _ _) ?_))
  by_cases hc : cap = 0
  · simp only [hc, ↓reduceIte]
    exact Entails.refl _
  · simp only [hc, ↓reduceIte]
    have hpos : 0 < cap.toNat := Nat.pos_of_ne_zero (fun h0 => hc (BitVec.eq_of_toNat_eq h0))
    have hlay : LayoutOk cap.toNat 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
    exact Entails.pure_right hlay (Entails.refl _)

private theorem boxU8At_entails_deallocOpt (A : RustAlloc) (a ptr : BitVec 64)
    (bs : List (BitVec 8)) :
    boxU8At A a ptr bs ⊢
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      deallocOpt A (BitVec.ofNat 64 bs.length) ptr := by
  unfold boxU8At deallocOpt
  rw [sep_pull_third]
  apply Entails.pure_left; rintro ⟨_, hlt⟩
  cases bs with
  | nil =>
    simp only [List.length_nil, beq_self_eq_true, ↓reduceIte]
    exact Entails.refl _
  | cons b tl =>
    have hpos : 0 < (b :: tl).length := Nat.succ_pos _
    have hlt64 : (b :: tl).length < 2 ^ 64 := by omega
    have hbeq : (BitVec.ofNat 64 (b :: tl).length == 0#64) = false :=
      ofNat_beq_zero_false hpos hlt64
    have htonat : (BitVec.ofNat 64 (b :: tl).length).toNat = (b :: tl).length :=
      ofNat_toNat_eq hlt64
    simp only [List.cons_ne_nil, ↓reduceIte, hbeq, Bool.false_eq_true, htonat]
    have hlay : LayoutOk (b :: tl).length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
    exact sepConj_mono_right (sepConj_mono_right
      (Entails.pure_right hlay
        (sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr (b :: tl)))))

private theorem optBoxU8At_entails_deallocOpt (A : RustAlloc) (a ptr : BitVec 64)
    (mbs : Option (List (BitVec 8))) :
    optBoxU8At A a ptr mbs ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        (a ↦₆₄ w0) ∗ ((a + 8#64) ↦₆₄ w1) ∗
        deallocOpt A (if (w0 == 0#64) = true then 0#64 else w1) w0 := by
  cases mbs with
  | none =>
    unfold optBoxU8At deallocOpt
    rw [ProofLib.memRegion_eight (a + 8#64), sepExists_sepConj_right]
    apply Entails.sepExists_elim; intro w1
    refine Entails.sepExists_right 0#64 (Entails.sepExists_right w1 ?_)
    simp only [beq_self_eq_true, ↓reduceIte, sepConj_emp]
    exact Entails.refl _
  | some bs =>
    unfold optBoxU8At
    have hne : boxU8At A a ptr bs ⊢ ⌜(ptr == 0#64) = false⌝ ∗ boxU8At A a ptr bs := by
      unfold boxU8At
      nth_rw 1 [sep_pull_third]
      apply Entails.pure_left; intro hp
      exact Entails.pure_right (beq_false_of_ne hp.1)
        (sepConj_mono_right (sepConj_mono_right (Entails.pure_right hp (Entails.refl _))))
    refine Entails.trans hne ?_
    apply Entails.pure_left; intro hp0
    refine Entails.trans (boxU8At_entails_deallocOpt A a ptr bs) ?_
    refine Entails.sepExists_right ptr (Entails.sepExists_right (BitVec.ofNat 64 bs.length) ?_)
    simp only [hp0, Bool.false_eq_true, ↓reduceIte]
    exact Entails.refl _

private theorem boxU8At_serialized_expose (A : RustAlloc) (a ptr : BitVec 64)
    (bs : List (BitVec 8)) (hmin : macLength + 1 ≤ bs.length) :
    boxU8At A a ptr bs ⊢
      ⌜(BitVec.ofNat 64 bs.length == 0#64) = false ∧
        LayoutOk (BitVec.ofNat 64 bs.length).toNat 1⌝ ∗
      (a ↦₆₄ ptr) ∗ ((a + 8#64) ↦₆₄ BitVec.ofNat 64 bs.length) ∗
      A.live ptr (BitVec.ofNat 64 bs.length).toNat 1 ∗
      memRegion ptr (BitVec.ofNat 64 bs.length).toNat := by
  unfold boxU8At
  rw [sep_pull_third]
  apply Entails.pure_left; rintro ⟨_, hlt⟩
  have hpos : 0 < bs.length := by omega
  have hlt64 : bs.length < 2 ^ 64 := by omega
  have hne : bs ≠ [] := List.ne_nil_of_length_pos hpos
  have hbeq : (BitVec.ofNat 64 bs.length == 0#64) = false := ofNat_beq_zero_false hpos hlt64
  have htonat : (BitVec.ofNat 64 bs.length).toNat = bs.length := ofNat_toNat_eq hlt64
  have hlay : LayoutOk bs.length 1 := ⟨hpos, ⟨0, rfl⟩, by omega⟩
  simp only [hne, ↓reduceIte, htonat]
  exact Entails.pure_right ⟨hbeq, hlay⟩
    (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (ProofLib.pointsToBytes_entails_memRegion ptr bs))))

@[reducible]
private def smHeadersAt (a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 : BitVec 64) : SepProp :=
  (a ↦₆₄ pqCap) ∗ ((a + 8#64) ↦₆₄ pqPtr) ∗ memRegion (a + 16#64) 8 ∗
  ((a + 24#64) ↦₆₄ ctPtr) ∗ ((a + 32#64) ↦₆₄ ctLen) ∗
  ((a + 40#64) ↦₆₄ serPtr) ∗ ((a + 48#64) ↦₆₄ serLen) ∗
  memRegion (a + 56#64) 32 ∗
  ((a + 88#64) ↦₆₄ w0) ∗ ((a + 96#64) ↦₆₄ w1) ∗
  memRegion (a + 104#64) 16

private theorem smHeadersAt_entails_memRegion_120
    (a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 : BitVec 64) :
    smHeadersAt a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ⊢ memRegion a 120 := by
  unfold smHeadersAt
  rw [ProofLib.memRegion_split' (b := a) (n := 8) (k := 112) (b' := a + 8#64) rfl rfl (by decide),
      ProofLib.memRegion_split' (b := a + 8#64) (n := 8) (k := 104) (b' := a + 16#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 16#64) (n := 8) (k := 96) (b' := a + 24#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 24#64) (n := 8) (k := 88) (b' := a + 32#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 32#64) (n := 8) (k := 80) (b' := a + 40#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 40#64) (n := 8) (k := 72) (b' := a + 48#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 48#64) (n := 8) (k := 64) (b' := a + 56#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 56#64) (n := 32) (k := 32) (b' := a + 88#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 88#64) (n := 8) (k := 24) (b' := a + 96#64) rfl (by bv_omega) (by decide),
      ProofLib.memRegion_split' (b := a + 96#64) (n := 8) (k := 16) (b' := a + 104#64) rfl (by bv_omega) (by decide)]
  exact sepConj_mono (pointsTo64_entails_memRegion _ _)
    (sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo64_entails_memRegion _ _)
          (sepConj_mono (pointsTo64_entails_memRegion _ _)
            (sepConj_mono (pointsTo64_entails_memRegion _ _)
              (sepConj_mono (pointsTo64_entails_memRegion _ _)
                (sepConj_mono (Entails.refl _)
                  (sepConj_mono (pointsTo64_entails_memRegion _ _)
                    (sepConj_mono (pointsTo64_entails_memRegion _ _) (Entails.refl _))))))))))

private theorem signalMessageAt_expose (A : RustAlloc) (g : SignalMessageGhost)
    (a : BitVec 64) (m : SignalMessage) :
    signalMessageAt A g a m ⊢
      ∃∗ w0 : BitVec 64, ∃∗ w1 : BitVec 64,
        ⌜(BitVec.ofNat 64 m.serialized.length == 0#64) = false ∧
          LayoutOk (BitVec.ofNat 64 m.serialized.length).toNat 1⌝ ∗
        smHeadersAt a g.pqCap g.pqPtr g.ctPtr (BitVec.ofNat 64 m.ciphertext.length)
          g.serPtr (BitVec.ofNat 64 m.serialized.length) w0 w1 ∗
        deallocOpt A (BitVec.ofNat 64 m.ciphertext.length) g.ctPtr ∗
        deallocOpt A g.pqCap g.pqPtr ∗
        deallocOpt A (if (w0 == 0#64) = true then 0#64 else w1) w0 ∗
        A.live g.serPtr (BitVec.ofNat 64 m.serialized.length).toNat 1 ∗
        memRegion g.serPtr (BitVec.ofNat 64 m.serialized.length).toNat := by
  unfold signalMessageAt
  apply Entails.pure_left; rintro ⟨hmin, _, _, _, _⟩
  have hpq := vecU8At_entails_deallocOpt A a g.pqCap g.pqPtr m.pqRatchet
  have hct := boxU8At_entails_deallocOpt A (a + 24#64) g.ctPtr m.ciphertext
  have hser := boxU8At_serialized_expose A (a + 40#64) g.serPtr m.serialized hmin
  have hsrk : ((a + 56#64) ↦ₛ m.senderRatchetKey.bytes.toList) ⊢ memRegion (a + 56#64) 32 := by
    simpa only [m.senderRatchetKey.bytes.toList_length] using
      ProofLib.pointsToBytes_entails_memRegion (a + 56#64) m.senderRatchetKey.bytes.toList
  have haddr := optBoxU8At_entails_deallocOpt A (a + 88#64) g.addrPtr m.addresses
  have htail :
      ((a + 104#64) ↦₃₂ m.counter) ∗
      (((a + 108#64) ↦₃₂ m.previousCounter) ∗
      (((a + 112#64) ↦₈ m.messageVersion) ∗ memRegion (a + 113#64) 7)) ⊢
      memRegion (a + 104#64) 16 := by
    rw [ProofLib.memRegion_split' (b := a + 104#64) (n := 4) (k := 12) (b' := a + 108#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 108#64) (n := 4) (k := 8) (b' := a + 112#64) rfl (by bv_omega) (by decide),
        ProofLib.memRegion_split' (b := a + 112#64) (n := 1) (k := 7) (b' := a + 113#64) rfl (by bv_omega) (by decide)]
    exact sepConj_mono (pointsTo32_entails_memRegion _ _)
      (sepConj_mono (pointsTo32_entails_memRegion _ _)
        (sepConj_mono_left (ProofLib.pointsTo8_entails_memRegion _ _)))
  have h32 : (a + 24#64) + 8#64 = a + 32#64 := by bv_omega
  have h48 : (a + 40#64) + 8#64 = a + 48#64 := by bv_omega
  have h96 : (a + 88#64) + 8#64 = a + 96#64 := by bv_omega
  rw [h32] at hct
  rw [h48] at hser
  simp only [h96] at haddr
  refine Entails.trans
    (sepConj_mono hpq
      (sepConj_mono hct
        (sepConj_mono hser
          (sepConj_mono hsrk
            (sepConj_mono haddr htail))))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  apply Entails.sepExists_elim; intro w0
  apply Entails.sepExists_elim; intro w1
  refine Entails.sepExists_right w0 (Entails.sepExists_right w1 ?_)
  dsimp only [smHeadersAt]
  exact Entails.of_eq (by ac_rfl)

/-! ## Callee-saved register and sequencing helpers -/

@[reducible]
private def Saved32Preserved (s0 s : State) (fsp : BitVec 64) : Prop :=
  s.readReg64 (Reg.gpr 20#5) = s0.readReg64 (Reg.gpr 20#5) ∧
  s.readReg64 (Reg.gpr 21#5) = s0.readReg64 (Reg.gpr 21#5) ∧
  s.readReg64 (Reg.gpr 22#5) = s0.readReg64 (Reg.gpr 22#5) ∧
  s.readReg64 (Reg.gpr 23#5) = s0.readReg64 (Reg.gpr 23#5) ∧
  s.readReg64 (Reg.gpr 24#5) = s0.readReg64 (Reg.gpr 24#5) ∧
  s.readReg64 (Reg.gpr 25#5) = s0.readReg64 (Reg.gpr 25#5) ∧
  s.readReg64 (Reg.gpr 26#5) = s0.readReg64 (Reg.gpr 26#5) ∧
  s.readReg64 (Reg.gpr 27#5) = s0.readReg64 (Reg.gpr 27#5) ∧
  s.readReg64 (Reg.gpr 28#5) = s0.readReg64 (Reg.gpr 28#5) ∧
  s.sp = fsp ∧
  s.trace = s0.trace ∧
  calleeSavedVRegs s = calleeSavedVRegs s0

private theorem seq_clean32 {prog : Program} {img : Obj.Image} {mid target : BitVec 64} {s : State}
    {P P_mid : SepProp} {Q : State → Prop} {post : State → SepProp → Prop}
    (hfrozen : img.FrozenLoaded s) (hsym : s.symtab = img.symtab)
    (h1 : SepWP prog mid s P (fun sm Pm => (Pm ⊢ P_mid) ∧ Q sm))
    (h2 : ∀ sm : State, sm.pc = mid → sm.status = .Running →
      img.FrozenLoaded sm → sm.symtab = img.symtab → Q sm →
      SepWP prog target sm P_mid post) :
    SepWP prog target s P post := by
  unfold SepWP reaches_pc
  intro R hm hL
  obtain ⟨sm, hsteps1, ⟨hpcm, hrunm, P_m, hm_m, hent, hQ⟩ | ⟨hoom1, hfalse1⟩⟩ := h1.elim hm hL
  · have hfrozen_m : img.FrozenLoaded sm := hfrozen.of_keepsFrozen hsteps1.keepsFrozen
    have hsym_m : sm.symtab = img.symtab := hsteps1.symtab_eq.trans hsym
    have hm_m' : sm.mem ⊨ P_mid ∗ R := Satisfies.mono (sepConj_mono_left hent) hm_m
    obtain ⟨sf, hsteps2, hout2⟩ :=
      (h2 sm hpcm hrunm hfrozen_m hsym_m hQ).elim hm_m' (hsteps1.codeLoaded hL)
    exact ⟨sf, Steps.trans hsteps1 hsteps2, hout2⟩
  · exact ⟨sm, hsteps1, Or.inr ⟨hoom1, hfalse1⟩⟩

private theorem sm_tail_pre_weaken
    (a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 : BitVec 64)
    (live1 live2 pool : SepProp) (sp fp lr x19 w3 : BitVec 64) :
    smHeadersAt a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ∗
      live1 ∗ live2 ∗ pool ∗
      stackAt (sp - 32#64) extHookStack ∗
      ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
      ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3) ⊢
    memRegion a 120 ∗ pool ∗ memRegion (sp - 16416#64) 32 ∗ stackAt sp extHookStack ∗
      (live1 ∗ live2) := by
  have ha := smHeadersAt_entails_memRegion_120 a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1
  have hst := cells4_entails_stack_bottom sp fp lr x19 w3
  have hreord :
      (smHeadersAt a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ∗
        live1 ∗ live2 ∗ pool ∗
        stackAt (sp - 32#64) extHookStack ∗
        ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
        ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3)) =
      (smHeadersAt a pqCap pqPtr ctPtr ctLen serPtr serLen w0 w1 ∗
        pool ∗
        (stackAt (sp - 32#64) extHookStack ∗
          ((sp - 32#64) ↦₆₄ fp) ∗ ((sp - 24#64) ↦₆₄ lr) ∗
          ((sp - 16#64) ↦₆₄ x19) ∗ ((sp - 8#64) ↦₆₄ w3)) ∗
        (live1 ∗ live2)) := by ac_rfl
  rw [hreord]
  refine Entails.trans (sepConj_mono ha (sepConj_mono_right (sepConj_mono_left hst))) ?_
  exact Entails.of_eq (by ac_rfl)

/-! ## Exact-stack proof (`32 + extHookStack`) -/

def smDropRawSpec (A : RustAlloc) (stk : Nat) :
    Spec (BitVec 64 × SignalMessageGhost × SignalMessage) where
  pre := fun (a, g, m) s =>
    ⌜s.readReg64 .x0 = a⌝ ∗ signalMessageAt A g a m ∗ A.pool ∗ stackAt s.sp stk
  post := fun (a, _, _) s0 sf =>
    ⌜sf.trace = s0.trace⌝ ∗ memRegion a 120 ∗ A.pool ∗ stackAt s0.sp stk

set_option maxHeartbeats 1600000 in
theorem smDropRaw_exact_ok {A : RustAlloc} {img : Obj.Image}
    {ext : String → Option (State → State)} (hA : AllocContractsX img A ext) :
    subroutine_ok (tripleRatchetProgAtExt img.base ext)
      ((tripleRatchetProgAtExt img.base ext).fnAddr
        "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>")
      ((smDropRawSpec A (32 + extHookStack)).inImage img) := by
  simp only [Spec.inImage, smDropRawSpec]
  have hdealloc := hA.dealloc_ok_at
    "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>"
    (num% (ls_off% "__rustc::__rust_dealloc" -
      ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>"))
    (by
      rw [(ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>")]
      simp only [arm64_norm])
  simp only [Spec.inImage, rustDeallocExternSpecWithStack] at hdealloc
  have hfnOff := ls_lemma% fnOff "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>"
  have f0 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 0) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 0))
  have f4 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 4) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 4))
  have f8 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 8) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 8))
  have f12 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 12) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 12))
  have f16 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 16) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 16))
  have f20 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 20) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 20))
  have f24 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 24) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 24))
  have f28 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 28) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 28))
  have f32 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 32) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 32))
  have f36 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 36) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 36))
  have f40 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 40) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 40))
  have f44 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 44) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 44))
  have f48 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 48) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 48))
  have f52 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 52) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 52))
  have f56 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 56) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 56))
  have f60 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 60) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 60))
  have f64 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 64) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 64))
  have f68 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 68) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 68))
  have f72 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 72) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 72))
  have f76 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 76) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 76))
  have f80 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 80) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 80))
  have f84 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 84) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 84))
  have f88 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 88) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 88))
  have f92 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 92) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 92))
  have f96 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 96) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 96))
  have f100 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 100) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 100))
  have f104 := CryptoVerification.libsignalSessionCode_fetch_fnAddr (b := img.base) (H := Rust.withPanics ext) (k := 104) hfnOff (by decide) (ls_decode% smDropDec (ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" + 104))
  dsimp only [tripleRatchetProgAtExt, BitVec.ofNat_eq_ofNat] at hdealloc f0 f4 f8 f12 f16 f20 f24 f28 f32 f36 f40 f44 f48 f52 f56 f60 f64 f68 f72 f76 f80 f84 f88 f92 f96 f100 f104 ⊢
  generalize_entry (libsignalSessionCode.rebase img.base (Rust.withPanics ext)).fnAddr
    "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>" = pEntry
  rw [BitVec.add_zero] at f0
  examples_hide_fetches
  wp_init x s0
  rcases x with ⟨a, g, msg⟩
  dsimp only at *
  subst h
  have hfsp_align : ((s0.sp - 32#64) &&& 15#64 == 0#64) = true :=
    ProofLib.spAligned_sub s0.sp 32#64 (by assumption)
  nth_rw 1 [stackAt_smDrop_split s0.sp]
  cells_unfold
  wp_pull_exists
  rename_i st0 st1 st2 w3
  refine SepWP.weaken_pre
    (sepConj_mono_left (signalMessageAt_expose A g (s0.readReg64 (Reg.gpr 0#5)) msg)) ?_
  wp_pull_exists
  rename_i w0 w1
  refine SepWP.pure_elim ?_
  rintro ⟨hser_ne0, _, _, _⟩
  refine seq_clean32 (mid := pEntry + bv% (20))
    (P_mid :=
      smHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g.pqCap g.pqPtr
        g.ctPtr (BitVec.ofNat 64 msg.ciphertext.length)
        g.serPtr (BitVec.ofNat 64 msg.serialized.length) w0 w1 ∗
      deallocOpt A (BitVec.ofNat 64 msg.ciphertext.length) g.ctPtr ∗
      deallocOpt A g.pqCap g.pqPtr ∗
      deallocOpt A (if (w0 == 0#64) = true then 0#64 else w1) w0 ∗
      A.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
      memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat ∗
      A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ w3))
    (Q := fun sm =>
      Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 0#5) ∧
      sm.readReg64 (Reg.gpr 1#5) = BitVec.ofNat 64 msg.ciphertext.length)
    h_2 h_1
    (by
      dsimp only [smHeadersAt]
      wp_steps
      wp_done) ?_
  intro sp0 hpcp0 hrunp0 hfrozenp0 hsymp0 ⟨⟨hx20_0, hx21_0, hx22_0, hx23_0, hx24_0, hx25_0, hx26_0, hx27_0, hx28_0, hsp_0, htrace_0, hvregs_0⟩, hx19_0, hx1_0⟩
  refine seq_clean32 (mid := pEntry + bv% (36))
    (P_mid :=
      smHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g.pqCap g.pqPtr
        g.ctPtr (BitVec.ofNat 64 msg.ciphertext.length)
        g.serPtr (BitVec.ofNat 64 msg.serialized.length) w0 w1 ∗
      deallocOpt A g.pqCap g.pqPtr ∗
      deallocOpt A (if (w0 == 0#64) = true then 0#64 else w1) w0 ∗
      A.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
      memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat ∗
      A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗
      ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
      ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
      ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
      ((s0.sp - 8#64) ↦₆₄ w3))
    (Q := fun sm =>
      Saved32Preserved s0 sm (s0.sp - 32#64) ∧
      sm.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 0#5))
    hfrozenp0 hsymp0 ?_ ?_
  · dsimp only [smHeadersAt, deallocOpt]
    by_cases hct : (BitVec.ofNat 64 msg.ciphertext.length == 0#64) = true <;>
      simp only [hct, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
    · wp_steps
      wp_done
    · refine SepWP.focus_pure (by sep_focus) ?_
      rintro ⟨_, _, _⟩
      wp_steps
      wp_call hdealloc (g.ctPtr, (BitVec.ofNat 64 msg.ciphertext.length).toNat, 1)
      wp_done
  · intro s1 hpc1 hrun1 hfrozen1 hsym1 ⟨⟨hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1, hx26_1, hx27_1, hx28_1, hsp_1, htrace_1, hvregs_1⟩, hx19_1⟩
    refine seq_clean32 (mid := pEntry + bv% (56))
      (P_mid :=
        smHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g.pqCap g.pqPtr
          g.ctPtr (BitVec.ofNat 64 msg.ciphertext.length)
          g.serPtr (BitVec.ofNat 64 msg.serialized.length) w0 w1 ∗
        deallocOpt A (if (w0 == 0#64) = true then 0#64 else w1) w0 ∗
        A.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
        memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat ∗
        A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗
        ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
        ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
        ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
        ((s0.sp - 8#64) ↦₆₄ w3))
      (Q := fun sm =>
        Saved32Preserved s0 sm (s0.sp - 32#64) ∧
        sm.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 0#5))
      hfrozen1 hsym1 ?_ ?_
    · dsimp only [smHeadersAt, deallocOpt]
      by_cases hpq : (g.pqCap == 0#64) = true <;>
        simp only [hpq, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
      · wp_steps
        wp_done
      · refine SepWP.focus_pure (by sep_focus) ?_
        rintro ⟨_, _, _⟩
        wp_steps
        wp_call hdealloc (g.pqPtr, g.pqCap.toNat, 1)
        wp_done
    · intro s2 hpc2 hrun2 hfrozen2 hsym2 ⟨⟨hx20_2, hx21_2, hx22_2, hx23_2, hx24_2, hx25_2, hx26_2, hx27_2, hx28_2, hsp_2, htrace_2, hvregs_2⟩, hx19_2⟩
      refine seq_clean32 (mid := pEntry + bv% (80))
        (P_mid :=
          smHeadersAt (s0.readReg64 (Reg.gpr 0#5)) g.pqCap g.pqPtr
            g.ctPtr (BitVec.ofNat 64 msg.ciphertext.length)
            g.serPtr (BitVec.ofNat 64 msg.serialized.length) w0 w1 ∗
          A.live g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat 1 ∗
          memRegion g.serPtr (BitVec.ofNat 64 msg.serialized.length).toNat ∗
          A.pool ∗ stackAt (s0.sp - 32#64) extHookStack ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 (Reg.gpr 29#5)) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 (Reg.gpr 30#5)) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 (Reg.gpr 19#5)) ∗
          ((s0.sp - 8#64) ↦₆₄ w3))
        (Q := fun sm =>
          Saved32Preserved s0 sm (s0.sp - 32#64) ∧
          sm.readReg64 (Reg.gpr 19#5) = s0.readReg64 (Reg.gpr 0#5))
        hfrozen2 hsym2 ?_ ?_
      · dsimp only [smHeadersAt, deallocOpt]
        by_cases hw0 : (w0 == 0#64) = true
        · simp only [hw0, beq_self_eq_true, ↓reduceIte, emp_sepConj]
          wp_steps
          wp_done
        · simp only [hw0, Bool.false_eq_true, ↓reduceIte]
          by_cases hw1 : (w1 == 0#64) = true <;>
            simp only [hw1, Bool.false_eq_true, ↓reduceIte, emp_sepConj]
          · wp_steps
            wp_done
          · refine SepWP.focus_pure (by sep_focus) ?_
            rintro ⟨_, _, _⟩
            wp_steps
            wp_call hdealloc (w0, w1.toNat, 1)
            wp_done
      · intro s3 hpc3 hrun3 hfrozen3 hsym3 ⟨⟨hx20_3, hx21_3, hx22_3, hx23_3, hx24_3, hx25_3, hx26_3, hx27_3, hx28_3, hsp_3, htrace_3, hvregs_3⟩, hx19_3⟩
        apply SepWP.seq_inImage (img := img) ⟨hfrozen3, hsym3⟩
          (mid := pEntry + bv% (ls_off% "__rustc::__rust_dealloc" -
            ls_off% "core::ptr::drop_glue::<libsignal_protocol::protocol::SignalMessage>"))
        dsimp only [smHeadersAt]
        wp_steps
        refine SepWP.weaken_pre
          (sm_tail_pre_weaken (s0.readReg64 (Reg.gpr 0#5)) g.pqCap g.pqPtr
            g.ctPtr (BitVec.ofNat 64 msg.ciphertext.length)
            g.serPtr (BitVec.ofNat 64 msg.serialized.length) w0 w1
            _ _ A.pool s0.sp
            (s0.readReg64 (Reg.gpr 29#5)) (s0.readReg64 (Reg.gpr 30#5))
            (s0.readReg64 (Reg.gpr 19#5)) w3) ?_
        apply SepWP.done (by rfl)
          (by simp only [State.status_setPC, State.status_writeReg64, hrun3])
        rintro ⟨hfrozen_tail, hsym_tail⟩
        wp_call hdealloc (g.serPtr, (BitVec.ofNat 64 msg.serialized.length).toNat, 1)
        refine SepWP.weaken_pre (sm_tail_post_weaken (s0.readReg64 (Reg.gpr 0#5)) A.pool s0.sp) ?_
        wp_done

end CryptoVerification.SignalSession.Cli.RunProofs.DropSignalMessageHelpers
