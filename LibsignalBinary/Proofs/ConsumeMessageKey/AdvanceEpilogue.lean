/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Core
public import LibsignalBinary.Proofs.ConsumeMessageKey.AdvanceEpilogueProofs.Fetch
import LibsignalBinary.Proofs.ConsumeMessageKey.FindIndexProofs.FindIndexCodeSym
import LibsignalBinary.Proofs.ConsumeMessageKey.HmacProofs.HmacCodeSym
import ProofLib.SepLogic.WPp

@[expose] public section

set_option maxRecDepth 200000
set_option autoImplicit false

/-!
# Epilogue of `RatchetState::consume_message_key`

Symbolic execution of the `consume_message_key` epilogue from `cmkEpiloguePC` (`+0x4dc` to
`+0x5e0` and shared return `+0x77c .. +0x798`): derives the next chain key via `hmac_sha256` on
`[0x02]`, locates receiver chain `ci`, replaces its `chain_key` buffer and increments its index,
derives the message-key seed via `hmac_sha256` on `[0x01]`, and writes `Ok(Seed(seed, counter))`.
-/

namespace CryptoVerification.LibsignalSession.AdvanceEpilogue

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.SessionModel

attribute [local irreducible] Program.fetch Program.externAt? cmkDummyImg
attribute [-simp, -arm64_norm, -wp_norm] logFilterAddr_cmkDummyImg
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero
  Int64_mk_toBitVec UInt64_ofNat_toBitVec UInt64_mk_toBitVec BitVec_ofFin_eq_ofNat

theorem sepWPp_seq_lscl {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {pl : Obj.MultiPlacement} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeLoaded pl sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => h.of_keepsFrozen hkf) hcl h

theorem introduce_withLsCodeLoaded {α : Type} {pl : Obj.MultiPlacement} {spec : Spec α}
    {x : α} {R : SepProp} {s : State}
    (hcl : LibsignalCodeLoaded pl s.mem)
    (h : s.mem ⊨ spec.pre x s ∗ R) :
    s.mem ⊨ (withLsCodeLoaded pl spec).pre x s ∗ R := by
  dsimp only [withLsCodeLoaded]
  rw [sepConj_assoc, sepConj_left_comm (spec.pre x s), satisfies_pure_sepConj]
  exact ⟨hcl, h⟩

private class EpInvClass [LibsignalPlacement] (Inv : Memory → Prop) : Prop where
  of_keepsFrozen : ∀ {m m' : Memory}, Inv m → m.KeepsFrozen m' → Inv m'
  to_lscl : ∀ {m : Memory}, Inv m → LibsignalCodeLoaded lsmpl m

private instance [LibsignalPlacement] : EpInvClass (LibsignalCodeLoaded lsmpl) where
  of_keepsFrozen h hkf := h.of_keepsFrozen hkf
  to_lscl h := h

private instance [LibsignalPlacement] :
    EpInvClass (fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m) where
  of_keepsFrozen h hkf := ⟨h.1.of_keepsFrozen hkf, libsignalRoLoaded_of_keepsFrozen h.2 hkf⟩
  to_lscl h := h.1

private theorem sepWPp_seq_epInv [LibsignalPlacement] {Inv : Memory → Prop} [EpInvClass Inv]
    {prog : Program} {ret mid : BitVec 64} {s : State} {P : SepProp}
    {Q Qp : State → SepProp → Prop}
    (hinv : Inv s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      Inv sm.mem → SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  SepWPp.seq_frozen (fun _ _ h hkf => EpInvClass.of_keepsFrozen h hkf) hinv h

def hmacAtStateSpec (F : ShaState → List (BitVec 8) → ShaState) (s : State) :
    Spec (BitVec 64 × BitVec 64 × List (BitVec 8) × BitVec 64 × List (BitVec 8)) where
  pre := fun (out, ka, key, ia, inp) s' =>
    ⌜s'.mem = s.mem ∧
      s'.readReg64 .x0 = out ∧ s'.readReg64 .x1 = ka ∧ (s'.readReg64 .x2).toNat = key.length ∧
      s'.readReg64 .x3 = ia ∧ (s'.readReg64 .x4).toNat = inp.length ∧ key.length = 32 ∧
      inp.length = 1⌝ ∗
    memRegion out 32 ∗ (ka ↦ₛ key) ∗ (ia ↦ₛ inp) ∗ stackAt s'.sp 2048
  post := (hmacSpec F).post

theorem hmac_placed_ok_at_state [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {s : State}
    (hhmac : HmacPlacedOk H F)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s) := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [hmacAtStateSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hloaded) ?_
  dsimp only [hmacSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

theorem hmac_placed_ro_ok_at_state [LibsignalPlacement] {F : ShaState → List (BitVec 8) → ShaState}
    {H : String → Option (State → State)} {s : State}
    (hhmac : HmacPlacedRoOk H F)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem ∧ LibsignalRoLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s) := by
  refine subroutine_ok_mono hhmac (fun ⟨out, ka, key, ia, inp⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only [hmacAtStateSpec] at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hloaded.1) ?_
  dsimp only
  rw [sepConj_assoc, sepConj_left_comm ((hmacSpec F).pre (out, ka, key, ia, inp) s0), satisfies_pure_sepConj]
  refine ⟨hmem ▸ hloaded.2, ?_⟩
  dsimp only [hmacSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

abbrev advanceEpiloguePostPlaced [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 sf : State) (P_f : SepProp) : Prop :=
  ((sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cmkPlacedSpec F A).post x s0 sf ∗ R)) ∧
  sf.sp = s0.sp ∧ CalleeSavedPreserved s0 sf

abbrev advanceEpiloguePanicPlaced [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 sf : State) (P_f : SepProp) : Prop :=
  (sf.mem ⊨ P_f ∗ R) → (sf.mem ⊨ (cmkPlacedSpec F A).onPanic x s0 sf ∗ R)

theorem advanceEpiloguePost_eq [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State) :
    advanceEpiloguePostPlaced F A x R s0 =
    advanceEpiloguePost F A cmkDummyImg x R s0 := by
  funext sf P_f
  unfold advanceEpiloguePostPlaced advanceEpiloguePost cmkPlacedSpec withLsCodeLoaded
    consumeMessageKeySpec Spec.inImage
  dsimp only
  rw [logFilterAddr_cmkDummyImg]

theorem advanceEpiloguePanic_eq [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (x : ConsumeMessageKeyGhost) (R : SepProp) (s0 : State) :
    advanceEpiloguePanicPlaced F A x R s0 =
    advanceEpiloguePanic F A cmkDummyImg x R s0 := rfl

theorem findIndex_placed_ok_at_state_ls [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {s : State}
    (hfind : FindIndexPlacedOk H A)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (findIndexPlacedSpec A).post } := by
  refine subroutine_ok_mono hfind (fun ⟨p, cs, theirA, their⟩ R s0 hm => ?_)
    (fun _ _ _ _ hpost => hpost)
  dsimp only at hm
  rw [sepConj_assoc, satisfies_pure_sepConj] at hm
  rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
  refine introduce_withLsCodeLoaded (hmem ▸ hloaded) ?_
  dsimp only [findIndexPlacedSpec]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hrest, hspatial⟩

theorem findIndex_placed_ok_at_state [LibsignalPlacement] {A : RustAlloc}
    {H : String → Option (State → State)} {s : State}
    (hfind : FindIndexPlacedOk H A)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem) :
    subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 26)
      { pre := fun (p, cs, theirA, their) s' =>
          ⌜s'.mem = s.mem ∧
            s'.readReg64 .x0 = p ∧ (s'.readReg64 .x1).toNat = cs.length ∧ s'.readReg64 .x2 = theirA ∧
            cs.length * 104 < 2 ^ 63⌝ ∗
          arrayAt (chainAt A) 104 p cs ∗ (theirA ↦ₛ their.bytes.toList) ∗
          (logFilterAddr cmkDummyImg ↦₆₄ 0#64) ∗ stackAt s'.sp 1024
        post := (findIndexSpec cmkDummyImg A).post } := by
  refine subroutine_ok_mono hfind (fun ⟨p, cs, theirA, their⟩ R s0 hm => ?_)
    (fun ⟨p, cs, theirA, their⟩ R s0 sf hpost => ?_)
  · dsimp only at hm
    rw [logFilterAddr_cmkDummyImg, sepConj_assoc, satisfies_pure_sepConj] at hm
    rcases hm with ⟨⟨hmem, hrest⟩, hspatial⟩
    refine introduce_withLsCodeLoaded (hmem ▸ hloaded) ?_
    dsimp only [findIndexPlacedSpec]
    rw [sepConj_assoc, satisfies_pure_sepConj]
    exact ⟨hrest, hspatial⟩
  · dsimp only [findIndexSpec, withLsCodeLoaded, findIndexPlacedSpec] at hpost ⊢
    rwa [logFilterAddr_cmkDummyImg]

theorem advanceEpilogue_oom_panic_placed_ls [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)} (hA : CmkAllocHooks A H)
    (x : ConsumeMessageKeyGhost) (R P : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 2484#64)
    (hrun : s.status = .Running)
    (_hsp : s.spAligned = true)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem)
    (hfail : allocFailedIn s0 s ∧ s0.trace <+: s.trace) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s P
      (advanceEpiloguePostPlaced F A x R s0) (advanceEpiloguePanicPlaced F A x R s0) := by
  have hpanic : ((blkPC_24).rebase (blkPl_24).base H).externAt? (lsρ cmkHandleErrorSym) = some Rust.panicked :=
    (cmk_externAt?_of_mem).trans hA.2.2.2.1
  refine sepWPp_seq_lscl (mid := lsρ cmkHandleErrorSym) hloaded ?_
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro _hloaded'
  refine SepWPp.panic (by simp only [wp_norm, arm64_norm, *]) hpanic fun hm' => ?_
  simpa only [cmkPlacedSpec, withLsCodeLoaded, sepConj_assoc] using
    allowPanic_panicked (⟨Or.inr (by simpa [allocFailedIn, Rust.panicked] using hfail.1),
      by simpa [Rust.panicked] using hfail.2⟩) hm'

theorem advanceEpilogue_oom_panic_placed [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)} (hA : CmkAllocHooks A H)
    (x : ConsumeMessageKeyGhost) (R P : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 2484#64)
    (hrun : s.status = .Running)
    (_hsp : s.spAligned = true)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem)
    (hfail : allocFailedIn s0 s ∧ s0.trace <+: s.trace) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s P
      (advanceEpiloguePost F A cmkDummyImg x R s0) (advanceEpiloguePanic F A cmkDummyImg x R s0) := by
  rw [← advanceEpiloguePost_eq, ← advanceEpiloguePanic_eq]
  exact advanceEpilogue_oom_panic_placed_ls hA x R P s0 s hpc hrun _hsp hloaded hfail

theorem advanceEpilogue_ret_epilogue_placed_ls [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)}
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1916#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmodel_ok : (x.model F).1 ≠ .error .panic)
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetAt A x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostPlaced F A x R s0) (advanceEpiloguePanicPlaced F A x R s0) := by
  unfold cmkSavedRegs
  refine sepWPp_seq_lscl (mid := s0.readReg64 Reg.lr) hloaded ?_
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro _hloaded'
  refine SepWPp.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    ⟨fun hm => ?_, rfl, by advanceEpilogue_cc_close⟩
  refine Satisfies.mono (sepConj_mono_left ?_) hm
  unfold cmkPlacedSpec withLsCodeLoaded
  dsimp only
  have hstk := stackAt_cmkStack_repack s0.sp s0
  unfold cmkSavedRegs at hstk
  have hex :
      ratchetAt A x.self G' (x.model F).2 ⊢
        ∃∗ G'' : RatchetGhost,
          ⌜x.G.AgreeExcept G'' (x.touched F)⌝ ∗ ratchetAt A x.self G'' (x.model F).2 :=
    Entails.sepExists_right G' (Entails.pure_right hagree (Entails.refl _))
  refine Entails.pure_right ⟨hmodel_ok, htr⟩ ?_
  refine Entails.trans ?_ (sepConj_mono_left hex)
  refine Entails.trans ?_
    (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hstk))))))
  have hpull :
      (ratchetAt A x.self G' (x.model F).2 ∗
        consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ckA 36 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        memRegion (s0.sp - 480#64) 384 ∗
        (((s0.sp - 96#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
         ((s0.sp - 88#64) ↦₆₄ s0.readReg64 Reg.x30) ∗
         ((s0.sp - 80#64) ↦₆₄ s0.readReg64 Reg.x28) ∗
         ((s0.sp - 72#64) ↦₆₄ s0.readReg64 Reg.x27) ∗
         ((s0.sp - 64#64) ↦₆₄ s0.readReg64 Reg.x26) ∗
         ((s0.sp - 56#64) ↦₆₄ s0.readReg64 Reg.x25) ∗
         ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x24) ∗
         ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.x23) ∗
         ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x22) ∗
         ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
         ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
         ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19)) ∗
        A.pool) =
      (ratchetAt A x.self G' (x.model F).2 ∗
        consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        memRegion x.ckA 36 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        (stackAt (s0.sp - 480#64) 7712 ∗
         memRegion (s0.sp - 480#64) 384 ∗
         (((s0.sp - 96#64) ↦₆₄ s0.readReg64 Reg.x29) ∗
          ((s0.sp - 88#64) ↦₆₄ s0.readReg64 Reg.x30) ∗
          ((s0.sp - 80#64) ↦₆₄ s0.readReg64 Reg.x28) ∗
          ((s0.sp - 72#64) ↦₆₄ s0.readReg64 Reg.x27) ∗
          ((s0.sp - 64#64) ↦₆₄ s0.readReg64 Reg.x26) ∗
          ((s0.sp - 56#64) ↦₆₄ s0.readReg64 Reg.x25) ∗
          ((s0.sp - 48#64) ↦₆₄ s0.readReg64 Reg.x24) ∗
          ((s0.sp - 40#64) ↦₆₄ s0.readReg64 Reg.x23) ∗
          ((s0.sp - 32#64) ↦₆₄ s0.readReg64 Reg.x22) ∗
          ((s0.sp - 24#64) ↦₆₄ s0.readReg64 Reg.x21) ∗
          ((s0.sp - 16#64) ↦₆₄ s0.readReg64 Reg.x20) ∗
          ((s0.sp - 8#64) ↦₆₄ s0.readReg64 Reg.x19))) ∗
        A.pool) := by ac_rfl
  rw [hpull]
  exact Entails.refl _

theorem advanceEpilogue_ret_epilogue_placed [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)}
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1916#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hmodel_ok : (x.model F).1 ≠ .error .panic)
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetAt A x.self G' (x.model F).2 ∗
       consumeMessageKeyResultAt A x.ret (x.model F).1 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       memRegion x.ckA 36 ∗
       (logFilterAddr cmkDummyImg ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       memRegion (s0.sp - 480#64) 384 ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePost F A cmkDummyImg x R s0) (advanceEpiloguePanic F A cmkDummyImg x R s0) := by
  rw [logFilterAddr_cmkDummyImg, ← advanceEpiloguePost_eq, ← advanceEpiloguePanic_eq]
  exact advanceEpilogue_ret_epilogue_placed_ls x G' R s0 s hpc hrun hsp_eq hsp htr hloaded
    hvregs hmodel_ok hagree

set_option maxHeartbeats 1600000 in
theorem advanceEpilogue_after_hmac1_placed_ls [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A H)
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (ckc : ChainKey) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1448#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetAt A x.self G' (x.model F).2 ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦ₛ [1#8]) ∗
       memRegion (s0.sp - 319#64) 31 ∗
       ((s0.sp - 224#64) ↦ₛ (ckc.messageKeys F).seed) ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostPlaced F A x R s0) (advanceEpiloguePanicPlaced F A x R s0) := by
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have halloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym) (rustAllocSpec A) :=
    cmk_hook_ok_of_mem hA.1
  have hoom_fn := @advanceEpilogue_oom_panic_placed_ls _ F A H hA x R
  have hret_fn := @advanceEpilogue_ret_epilogue_placed_ls _ F A H x G' R s0
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  obtain ⟨w0, w1, w2, w3, _, hw_seed⟩ := exists_unpack64_of_length_32 (length_messageKeys_seed F ckc)
  rw [hw_seed (s0.sp - 224#64), stackAt_7712_split_4096 (s0.sp - 480#64)]
  refine SepWPp.conseq_pre (sepConj_mono_right (sepConj_mono_left (memRegion88_unpack x.ret))) ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun t0 => SepWPp.exists_elim fun c0 =>
    SepWPp.exists_elim fun p0 => SepWPp.exists_elim fun l0 => SepWPp.exists_elim fun i0 => ?_
  refine sepWPp_seq_lscl (mid := (blkPl_24).base + bv% (1468)) hloaded ?_
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded1
  have hsp_sf1 : sf_1.spAligned = true := by
    unfold State.spAligned at *
    simp only [wp_norm, arm64_norm, *]
  by_cases hoom : sf_1.readReg64 Reg.x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_elim3 fun htr_oom => ?_
    refine sepWPp_seq_lscl (mid := (blkPl_24).base + bv% (2484)) hloaded1 ?_
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hloaded2
    exact hoom_fn _ s0 _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      hsp_sf1 hloaded2
      (allocFailedIn_of_eq (by simp only [wp_norm, arm64_norm, *]))
  · simp only [hoom, ite_false, sepConj_assoc]
    refine SepWPp.pure_elim3 fun ⟨_halign, htr_alloc⟩ => ?_
    have hoom' : ¬sf_1.readReg64 (Reg.gpr 0#5) = 0#64 := hoom
    rw [memRegion32_eq_exists_cells4 (sf_1.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
    refine sepWPp_seq_lscl (mid := (blkPl_24).base + bv% (1916)) hloaded1 ?_
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hloaded2
    have hmodel_ok : (x.model F).1 ≠ .error .panic := by rw [hm1]; nofun
    refine SepWPp.conseq_pre ?_
      (hret_fn _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
        (by simp only [wp_norm, arm64_norm, *])
        (by simpa [State.spAligned] using hsp_sf1)
        (by simp only [wp_norm, arm64_norm, *]) hloaded2 (by simp only [wp_norm, arm64_norm, *]) hmodel_ok hagree)
    have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
    have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
    rw [hm1, stackAt_7712_split_4096 (s0.sp - 480#64), h8192, hsf_sp]
    have hres := resultAt_ok_of_parts A x.ret (sf_1.readReg64 Reg.x0) (ckc.messageKeys F)
      (length_messageKeys_seed F ckc) hoom
    rw [hw_seed (sf_1.readReg64 Reg.x0)] at hres
    have hck_mem := chainKey_key_idx_entails_memRegion x.ckA ckc
    have hfrm_mem := cmkLoopFrame_repack s0.sp x.ret x.counter 1#8
    rw [← pointsTo8_eq_pointsToBytes1] at hfrm_mem
    have h224 :
        ((s0.sp - 224#64) ↦₆₄ w0) ∗ ((s0.sp - 216#64) ↦₆₄ w1) ∗
          ((s0.sp - 208#64) ↦₆₄ w2) ∗ ((s0.sp - 200#64) ↦₆₄ w3) ⊢
          memRegion (s0.sp - 224#64) 32 := by
      have := cells4_entails_memRegion32 (s0.sp - 224#64) w0 w1 w2 w3
      have ha1 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_arith
      have ha2 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_arith
      have ha3 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_arith
      rwa [ha1, ha2, ha3] at this
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono hres
        (sepConj_mono_right (sepConj_mono hck_mem
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left hfrm_mem)))))))
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_left h224))))))))))))
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by ac_rfl)

theorem advanceEpilogue_after_hmac1_placed [LibsignalPlacement]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A H)
    (x : ConsumeMessageKeyGhost) (G' : RatchetGhost) (ckc : ChainKey) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1448#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (htr : s.trace = s0.trace)
    (hloaded : LibsignalCodeLoaded lsmpl s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = 1#64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hagree : x.G.AgreeExcept G' (x.touched F)) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetAt A x.self G' (x.model F).2 ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (logFilterAddr cmkDummyImg ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦ₛ [1#8]) ∗
       memRegion (s0.sp - 319#64) 31 ∗
       ((s0.sp - 224#64) ↦ₛ (ckc.messageKeys F).seed) ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePost F A cmkDummyImg x R s0) (advanceEpiloguePanic F A cmkDummyImg x R s0) := by
  rw [logFilterAddr_cmkDummyImg, ← advanceEpiloguePost_eq, ← advanceEpiloguePanic_eq]
  exact advanceEpilogue_after_hmac1_placed_ls hA x G' ckc R s0 s hpc hrun hsp_eq hsp0 _hsp htr
    hloaded hvregs hx19 hx21 hx27 hm1 hagree

set_option maxHeartbeats 1600000 in
private theorem advanceEpilogue_set_chain_and_hmac1_placed_inv [LibsignalPlacement]
    {Inv : Memory → Prop} [EpInvClass Inv]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A H)
    (hhmac_at : ∀ {s : State}, Inv s.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (ptr_ck c0 p0 l0 : BitVec 64) (idx0 : BitVec 32)
    (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1400#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hloaded : Inv s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx19 : s.readReg64 .x19 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104))
    (hx20 : s.readReg64 .x20 = (ckc.index + 1#32).zeroExtend 64)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx22 : s.readReg64 .x22 = ptr_ck)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hptr_nz : ptr_ck ≠ 0)
    (hci : ci < stc.receiverChains.length)
    (hgi : ci < Gc.chains.length)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hsrk : PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    let c_Addr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (ratchetRestAtChain A x.self Gc stc ci chc hgi ∗
       ((c_Addr + 72#64) ↦₆₄ c0) ∗
       ((c_Addr + 80#64) ↦₆₄ p0) ∗
       ((c_Addr + 88#64) ↦₆₄ l0) ∗
       ((c_Addr + 96#64) ↦₃₂ idx0) ∗
       memRegion (c_Addr + 100#64) 4 ∗
       A.live ptr_ck 32 1 ∗
       (ptr_ck ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       memRegion (s0.sp - 320#64) 32 ∗
       memRegion (s0.sp - 224#64) 32 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostPlaced F A x R s0) (advanceEpiloguePanicPlaced F A x R s0) := by
  intro c_Addr
  have hafter_fn := @advanceEpilogue_after_hmac1_placed_ls _ F A H hA x
  have hsplit320 :
      memRegion (s0.sp - 320#64) 32 =
        (∃∗ b0 : BitVec 8, ((s0.sp - 320#64) ↦₈ b0)) ∗ memRegion (s0.sp - 319#64) 31 := by
    have h319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_arith
    rw [show (32 : Nat) = 1 + 31 from rfl,
        memRegion_split (s0.sp - 320#64) 1 31 (by decide),
        memRegion_one (s0.sp - 320#64), h319]
  rw [hsplit320, stackAt_7712_split_2048 (s0.sp - 480#64)]
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  refine sepWPp_seq_epInv (mid := lsmpl.base 73) hloaded ?_
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded1
  have hhmac1 := hhmac_at hloaded1
  have hlen_key : (keyToBytes32 ckc.key).length = 32 := length_keyToBytes32 ckc.key
  have hlen_inp : ([1#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 1#8]
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1448)) hloaded1 ?_
  wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [1#8])
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded2
  have hsp_sf : sf.spAligned = true := by
    simpa [State.spAligned, hsp_sf, hsp_eq] using hsp
  have hopt := optChainKeyAt_some_of_parts A (c_Addr + 72#64) ptr_ck (chainStepN F 1 ckc) hptr_nz
  have hrepack := repack_optChainKeyAt A x.self Gc stc ci chc hci hgi
    ⟨32#64, ptr_ck⟩ (some (chainStepN F 1 ckc))
    hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne hsrk hmax hklen
  have hst_eq : stc.setChain ci { chc with chainKey := some (chainStepN F 1 ckc) } = (x.model F).2 := by
    rw [hm2]; rfl
  rw [hst_eq] at hrepack
  have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
  have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
  have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
  have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
  rw [hc80, hc88, hc96, hc100] at hopt
  have hidx_eq : ckc.index + 1#32 = (chainStepN F 1 ckc).index := by
    simp [chainStepN_one]
  let G' := Gc.setChain ci { Gc.chains[ci]'hgi with ck := ⟨32#64, ptr_ck⟩ }
  have hagree' : x.G.AgreeExcept G' (x.touched F) := by
    rw [htouched]
    exact RatchetGhost.AgreeExcept.setChain_of_agreeExcept hagree_Gc hgi
      { Gc.chains[ci]'hgi with ck := ⟨32#64, ptr_ck⟩ } rfl rfl
  refine SepWPp.conseq_pre ?_
    (hafter_fn G' ckc R s0 sf
      hpc_sf hrun_sf (by simp only [wp_norm, arm64_norm, *]) hsp0 hsp_sf (by simp only [wp_norm, arm64_norm, *])
      (EpInvClass.to_lscl hloaded2)
      (by simp only [wp_norm, arm64_norm, *])
      (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      hm1 hagree')
  have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  rw [hmacWith_one_eq_messageKeys_seed F ckc,
      stackAt_7712_split_2048 (s0.sp - 480#64), h8192, hidx_eq, hsp_eq,
      pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 1#8]
  have hchain_pack :
      (((c_Addr + 72#64) ↦₆₄ 32#64) ∗
       ((c_Addr + 80#64) ↦₆₄ ptr_ck) ∗
       ((c_Addr + 88#64) ↦₆₄ 32#64) ∗
       ((c_Addr + 96#64) ↦₃₂ (chainStepN F 1 ckc).index) ∗
       memRegion (c_Addr + 100#64) 4 ∗
       A.live ptr_ck 32 1 ∗
       (ptr_ck ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key)) ∗
      ratchetRestAtChain A x.self Gc stc ci chc hgi ⊢
      ratchetAt A x.self G' (x.model F).2 :=
    Entails.trans (sepConj_mono_left hopt) hrepack
  refine Entails.trans ?_ (sepConj_mono_left hchain_pack)
  have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
  exact heq (by ac_rfl)

set_option maxHeartbeats 1600000 in
private theorem advanceEpilogue_after_find_index_placed_inv [LibsignalPlacement]
    {Inv : Memory → Prop} [EpInvClass Inv]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A H)
    (hhmac_at : ∀ {s : State}, Inv s.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1312#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hloaded : Inv s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx0 : s.readReg64 .x0 = 1#64)
    (hx1 : s.readReg64 .x1 = BitVec.ofNat 64 ci)
    (hx20 : s.readReg64 .x20 = Gc.chainsPtr)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx23 : s.readReg64 .x23 = BitVec.ofNat 64 stc.receiverChains.length)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : s.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hci : ci < stc.receiverChains.length)
    (hgi : ci < Gc.chains.length)
    (hchains_len : Gc.chains.length = stc.receiverChains.length)
    (hpad_len : Gc.senderPad.length = 100)
    (hmax_jumps : stc.maxForwardJumps < 2 ^ 64)
    (hcap_le : stc.receiverChains.length ≤ Gc.chainsCap.toNat)
    (hcap_lt : Gc.chainsCap.toNat * 104 < 2 ^ 63)
    (hptr_ne : Gc.chainsPtr ≠ 0)
    (hsrk : PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey)
    (hmax : chc.messageKeys.length ≤ maxMessageKeys)
    (hklen : (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    let c_Addr := Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey (c_Addr + 72#64) ∗
       ratchetRestAtChain A x.self Gc stc ci chc hgi ∗
       memRegion x.ret 88 ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       memRegion (s0.sp - 224#64) 32 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool)
      (advanceEpiloguePostPlaced F A x R s0) (advanceEpiloguePanicPlaced F A x R s0) := by
  intro c_Addr
  have hshim : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustNoAllocShimSym) cmkShimSpec :=
    cmk_hook_ok_of_mem hA.2.2.1
  have halloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustAllocSym) (rustAllocSpec A) :=
    cmk_hook_ok_of_mem hA.1
  have hdealloc : subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsρ cmkRustDeallocSym) (rustDeallocSpec A) :=
    cmk_hook_ok_of_mem hA.2.1
  have hoom_fn := @advanceEpilogue_oom_panic_placed_ls _ F A H hA x R
  have hset_fn := @advanceEpilogue_set_chain_and_hmac1_placed_inv _ Inv _ F A H hA hhmac_at x Gc stc ckc ci chc
  have hpow1 : ∃ k, 1 = 2 ^ k := ⟨0, rfl⟩
  have hlayout32 : LayoutOk 32 1 := ⟨by decide, hpow1, by decide⟩
  obtain ⟨w0, w1, w2, w3, _, hw_ck⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 (chainStepN F 1 ckc).key)
  rw [hw_ck (s0.sp - 320#64), stackAt_7712_split_4096 (s0.sp - 480#64)]
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1340)) hloaded ?_
  wp_steps
  wp_call hshim ()
  wp_steps
  wp_call halloc (32, 1)
  apply SepWP.done hpc_sf_1 hrun_sf_1
  intro hloaded1
  have hsp_sf1 : sf_1.spAligned = true := by
    unfold State.spAligned at *
    simp only [wp_norm, arm64_norm, *]
  by_cases hoom : sf_1.readReg64 Reg.x0 = 0
  · simp only [hoom, ite_true]
    refine SepWPp.pure_elim3 fun htr_oom => ?_
    refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (2484)) hloaded1 ?_
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hloaded2
    exact hoom_fn _ s0 _ (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      (by simpa [State.spAligned] using hsp_sf1) (EpInvClass.to_lscl hloaded2)
      (allocFailedIn_of_eq (by simp only [wp_norm, arm64_norm, *]))
  · simp only [hoom, ite_false, sepConj_assoc]
    have hoom_false : (sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = false :=
      beq_false_of_ne hoom
    have hoom_not_true : ¬((sf_1.readReg64 (Reg.gpr 0#5) == 0#64) = true) := by
      rw [hoom_false]; decide
    refine SepWPp.pure_elim3 fun ⟨_halign, htr_alloc⟩ => ?_
    rw [memRegion32_eq_exists_cells4 (sf_1.readReg64 Reg.x0)]
    simp only [sepExists_sepConj_left, sepExists_sepConj_right]
    refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
      SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
    have hci_bv : BitVec.ofNat 64 ci < BitVec.ofNat 64 stc.receiverChains.length := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      exact hci
    have hci_not_le : ¬(BitVec.ofNat 64 stc.receiverChains.length ≤ BitVec.ofNat 64 ci) := by
      bv_omega
    have hci_ule : (BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = false :=
      ule_false_of_lt hci_bv
    have hci_not_ule : ¬((BitVec.ofNat 64 stc.receiverChains.length).ule (BitVec.ofNat 64 ci) = true) := by
      rw [hci_ule]; decide
    refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1376)) hloaded1 ?_
    wp_steps
    apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    intro hloaded2
    have hc_addr_eq :
        Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = c_Addr := by
      change Gc.chainsPtr + BitVec.ofNat 64 ci * 104#64 = Gc.chainsPtr + BitVec.ofNat 64 (ci * 104)
      rw [BitVec.ofNat_mul]
    have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
    have h320_mem :
        ((s0.sp - 320#64) ↦₆₄ w0) ∗ ((s0.sp - 312#64) ↦₆₄ w1) ∗
          ((s0.sp - 304#64) ↦₆₄ w2) ∗ ((s0.sp - 296#64) ↦₆₄ w3) ⊢
          memRegion (s0.sp - 320#64) 32 := by
      have := cells4_entails_memRegion32 (s0.sp - 320#64) w0 w1 w2 w3
      have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
      have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
      have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
      rwa [ha1, ha2, ha3] at this
    simp only [sepConj_assoc]
    cases hck_opt : chc.chainKey with
    | none =>
      have hnone_unpack := optChainKeyAt_none_unpack A (Gc.chains[ci]'hgi).ck (c_Addr + 72#64)
      have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
      have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
      have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
      have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
      rw [hc80, hc88, hc96, hc100] at hnone_unpack
      refine SepWPp.conseq_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hnone_unpack)))))))) ?_
      simp only [sepExists_sepConj_left, sepExists_sepConj_right]
      refine SepWPp.exists_elim fun idx0 => SepWPp.exists_elim fun l0 =>
        SepWPp.exists_elim fun p0 => ?_
      have hslt_none : BitVec.slt optChainKeyNone 1#64 = true := by decide
      refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1400)) hloaded2 ?_
      wp_steps
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hloaded3
      refine SepWPp.conseq_pre ?_
        (hset_fn (sf_1.readReg64 Reg.x0) optChainKeyNone p0 l0 idx0 R s0 _
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hsp0
          (by simpa [State.spAligned] using hsp_sf1)
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hloaded3
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [c_Addr, wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          hoom hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
          hsrk hmax hklen hagree_Gc hm1 hm2 htouched)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left h320_mem)))))))))))))))))
      dsimp only [c_Addr]
      have hsf_sp : sf.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
      rw [hw_ck (sf_1.readReg64 Reg.x0), stackAt_7712_split_4096 (s0.sp - 480#64), h8192, hsf_sp]
      have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
      exact heq (by ac_rfl)
    | some old_ck =>
      have hsome_unpack := optChainKeyAt_some_entails_dealloc A (Gc.chains[ci]'hgi).ck old_ck (c_Addr + 72#64)
      unfold vecHeader at hsome_unpack
      have hc80 : c_Addr + 72#64 + 8#64 = c_Addr + 80#64 := by bv_arith
      have hc88 : c_Addr + 72#64 + 16#64 = c_Addr + 88#64 := by bv_arith
      have hc96 : c_Addr + 72#64 + 24#64 = c_Addr + 96#64 := by bv_arith
      have hc100 : c_Addr + 72#64 + 28#64 = c_Addr + 100#64 := by bv_arith
      rw [hc80, hc88, hc96, hc100] at hsome_unpack
      refine SepWPp.conseq_pre
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_left hsome_unpack)))))))) ?_
      have hpull_pure :
          (A.pool ∗
            stackAt sf.sp allocHookStack ∗
            A.live (sf_1.readReg64 Reg.x0) 32 1 ∗
            (sf_1.readReg64 Reg.x0 ↦₆₄ w0) ∗
            ((sf_1.readReg64 Reg.x0 + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 Reg.x0 + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 Reg.x0 + 24#64) ↦₆₄ w3) ∗
            (((c_Addr + 72#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.cap ∗
              (c_Addr + 80#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.ptr ∗
              (c_Addr + 88#64) ↦₆₄ 32#64) ∗
             (c_Addr + 96#64) ↦₃₂ old_ck.index ∗
             memRegion (c_Addr + 100#64) 4 ∗
             (⌜32 ≤ (Gc.chains[ci]'hgi).ck.cap.toNat ∧
               (Gc.chains[ci]'hgi).ck.cap.toNat < 2 ^ 63 ∧
               (Gc.chains[ci]'hgi).ck.ptr ≠ 0⌝ ∗
              if (Gc.chains[ci]'hgi).ck.cap = 0 then emp
              else A.live (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat 1 ∗
                memRegion (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat))) =
          (⌜32 ≤ (Gc.chains[ci]'hgi).ck.cap.toNat ∧
            (Gc.chains[ci]'hgi).ck.cap.toNat < 2 ^ 63 ∧
            (Gc.chains[ci]'hgi).ck.ptr ≠ 0⌝ ∗
           (A.pool ∗
            stackAt sf.sp allocHookStack ∗
            A.live (sf_1.readReg64 Reg.x0) 32 1 ∗
            (sf_1.readReg64 Reg.x0 ↦₆₄ w0) ∗
            ((sf_1.readReg64 Reg.x0 + 8#64) ↦₆₄ w1) ∗
            ((sf_1.readReg64 Reg.x0 + 16#64) ↦₆₄ w2) ∗
            ((sf_1.readReg64 Reg.x0 + 24#64) ↦₆₄ w3) ∗
            ((c_Addr + 72#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.cap) ∗
            ((c_Addr + 80#64) ↦₆₄ (Gc.chains[ci]'hgi).ck.ptr) ∗
            ((c_Addr + 88#64) ↦₆₄ 32#64) ∗
            ((c_Addr + 96#64) ↦₃₂ old_ck.index) ∗
            memRegion (c_Addr + 100#64) 4 ∗
            (if (Gc.chains[ci]'hgi).ck.cap = 0 then emp
             else A.live (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat 1 ∗
               memRegion (Gc.chains[ci]'hgi).ck.ptr (Gc.chains[ci]'hgi).ck.cap.toNat))) := by ac_rfl
      simp only [← sepConj_assoc] at hpull_pure ⊢
      rw [hpull_pure]
      simp only [sepConj_assoc]
      refine SepWPp.pure_elim fun ⟨hcap32, hcap_lt63, hptr_old_ne⟩ => ?_
      have hcap_ne0 : (Gc.chains[ci]'hgi).ck.cap ≠ 0 := by
        intro h0; rw [h0] at hcap32; change 32 ≤ 0 at hcap32; omega
      simp only [hcap_ne0, ↓reduceIte]
      have hslt_some : ¬BitVec.slt (Gc.chains[ci]'hgi).ck.cap 1#64 := by
        unfold BitVec.slt
        have : (Gc.chains[ci]'hgi).ck.cap.toInt = (Gc.chains[ci]'hgi).ck.cap.toNat :=
          BitVec.toInt_eq_toNat_of_lt (by omega)
        have h1 : (1#64).toInt = 1 := rfl
        simp only [this, h1, decide_eq_true_eq]
        omega
      have hlayout_old : LayoutOk (Gc.chains[ci]'hgi).ck.cap.toNat 1 :=
        ⟨by omega, hpow1, by omega⟩
      refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1400)) hloaded2 ?_
      wp_steps
      wp_call hdealloc ((Gc.chains[ci]'hgi).ck.ptr, (Gc.chains[ci]'hgi).ck.cap.toNat, 1)
      apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
      intro hloaded3
      refine SepWPp.conseq_pre ?_
        (hset_fn (sf_1.readReg64 Reg.x0) (Gc.chains[ci]'hgi).ck.cap (Gc.chains[ci]'hgi).ck.ptr 32#64 old_ck.index R s0 _
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hsp0
          (by unfold State.spAligned at *; simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hloaded3
          (by simp only [wp_norm, arm64_norm, *])
          (by simp only [c_Addr, wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
          hoom hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
          hsrk hmax hklen hagree_Gc hm1 hm2 htouched)
      refine Entails.trans ?_
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
            (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
              (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
                (sepConj_mono_left h320_mem)))))))))))))))))
      dsimp only [c_Addr]
      have hsf1_sp : sf_1.sp = s0.sp - 480#64 := by simp only [wp_norm, arm64_norm, *]
      rw [hw_ck (sf_1.readReg64 Reg.x0), stackAt_7712_split_4096 (s0.sp - 480#64), h8192, hsf1_sp]
      have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
      exact heq (by ac_rfl)

set_option maxHeartbeats 1600000 in
private theorem advanceEpilogue_entry_placed_inv [LibsignalPlacement]
    {Inv : Memory → Prop} [EpInvClass Inv]
    {F : ShaState → List (BitVec 8) → ShaState}
    {A : RustAlloc} {H : String → Option (State → State)}
    (hA : CmkAllocHooks A H)
    (hfind : FindIndexPlacedOk H A)
    (hhmac_at : ∀ {s : State}, Inv s.mem →
      subroutine_ok ((blkPC_24).rebase (blkPl_24).base H) (lsmpl.base 73) (hmacAtStateSpec F s))
    (x : ConsumeMessageKeyGhost) (Gc : RatchetGhost) (stc : RatchetState) (ckc : ChainKey)
    (ci : Nat) (chc : ReceiverChain) (R : SepProp) (s0 s : State)
    (hpc : s.pc = (blkPl_24).base + 1244#64)
    (hrun : s.status = .Running)
    (hsp_eq : s.sp = s0.sp - 480#64)
    (hsp0 : s0.spAligned = true)
    (_hsp : s.spAligned = true)
    (hx29 : s.readReg64 .x29 = s0.sp - 96#64)
    (htr : s.trace = s0.trace)
    (hloaded : Inv s.mem)
    (hvregs : calleeSavedVRegs s = calleeSavedVRegs s0)
    (hx21 : s.readReg64 .x21 = x.ckA)
    (hx23 : s.readReg64 .x23 = x.self)
    (hx26 : s.readReg64 .x26 = x.theirA)
    (hx27 : s.readReg64 .x27 = s0.sp - 224#64)
    (hx28 : s.readReg64 .x28 = ckc.index.zeroExtend 64)
    (hck_eq : ckc.index = x.counter)
    (hc_max : x.counter ≠ BitVec.allOnes 32)
    (hci_find : stc.findReceiverChainIndex x.their = some ci)
    (hchc_get : stc.receiverChains[ci]? = some chc)
    (hagree_Gc : x.G.AgreeExcept Gc (some ci))
    (hm1 : (x.model F).1 = .ok (ckc.messageKeys F))
    (hm2 : (x.model F).2 =
      { stc with
        receiverChains := stc.receiverChains.set ci
          { chc with chainKey := some (chainStepN F 1 ckc) } })
    (htouched : x.touched F = some ci) :
    SepWPp ((blkPC_24).rebase (blkPl_24).base H) (s0.readReg64 Reg.lr) s
      (cmkLoopHeap_placed A x Gc stc ckc s0)
      (advanceEpiloguePostPlaced F A x R s0) (advanceEpiloguePanicPlaced F A x R s0) := by
  have hafter_find_fn := @advanceEpilogue_after_find_index_placed_inv _ Inv _ F A H hA hhmac_at x Gc stc ckc ci chc R s0
  have ⟨hci, hchc_eq⟩ := List.getElem?_eq_some_iff.mp hchc_get
  unfold cmkLoopHeap_placed
  rw [chainKeyBytes_pointsTo x.ckA ckc, stackAt_7712_split_2048 (s0.sp - 480#64)]
  refine SepWPp.conseq_pre
    (sepConj_mono (ratchetAt_expose_for_findIndex A x.self Gc stc hci)
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_left (cmkLoopFrame_unpack s0.sp x.ret x.counter)))))))) ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hchains_len, hpad_len, hmax_jumps, hcap_le, hcap_lt, hptr_ne, _hcap_ne⟩ => ?_
  simp only [sepExists_sepConj_left, sepExists_sepConj_right]
  refine SepWPp.exists_elim fun b0 => ?_
  refine sepWPp_seq_epInv (mid := lsmpl.base 73) hloaded ?_
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded1
  have hhmac1 := hhmac_at hloaded1
  have hlen_key : (keyToBytes32 ckc.key).length = 32 := length_keyToBytes32 ckc.key
  have hlen_inp : ([2#8] : List (BitVec 8)).length = 1 := rfl
  rw [pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 2#8]
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1276)) hloaded1 ?_
  wp_call hhmac1 (s0.sp - 224#64, x.ckA, keyToBytes32 ckc.key, s0.sp - 320#64, [2#8])
  apply SepWP.done hpc_sf hrun_sf
  intro hloaded2
  rw [← keyToBytes32_chainStepN_one F ckc,
      pointsTo8_eq_pointsToBytes1 (s0.sp - 320#64) 2#8, hsp_eq]
  obtain ⟨w0, w1, w2, w3, _, hw_ck⟩ :=
    exists_unpack64_of_length_32 (length_keyToBytes32 (chainStepN F 1 ckc).key)
  have h8192 : s0.sp - 480#64 - 7712#64 = s0.sp - 8192#64 := by bv_arith
  have h320_cells :
      ((s0.sp - 320#64) ↦ₛ [2#8]) ∗ memRegion (s0.sp - 319#64) 31 ⊢
        ∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
          ((s0.sp - 320#64) ↦₆₄ d0) ∗ ((s0.sp - 312#64) ↦₆₄ d1) ∗
          ((s0.sp - 304#64) ↦₆₄ d2) ∗ ((s0.sp - 296#64) ↦₆₄ d3) := by
    have h319 : s0.sp - 320#64 + 1#64 = s0.sp - 319#64 := by bv_arith
    have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
    have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
    have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
    have h := pointsToBytes1_31_entails_cells4 (s0.sp - 320#64) 2#8
    rwa [h319, ha1, ha2, ha3] at h
  have hprep :
      (((s0.sp - 224#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((s0.sp - 320#64) ↦ₛ [2#8]) ∗
       stackAt (s0.sp - 480#64) 2048 ∗
       ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
       ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
       arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
       ratchetTail A x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       memRegion x.ret 88 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       memRegion (s0.sp - 8192#64) 5664 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       memRegion (s0.sp - 319#64) 31 ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) ⊢
      ((∃∗ d0 : BitVec 64, ∃∗ d1 : BitVec 64, ∃∗ d2 : BitVec 64, ∃∗ d3 : BitVec 64,
          ((s0.sp - 320#64) ↦₆₄ d0) ∗ ((s0.sp - 312#64) ↦₆₄ d1) ∗
          ((s0.sp - 304#64) ↦₆₄ d2) ∗ ((s0.sp - 296#64) ↦₆₄ d3)) ∗
       (((s0.sp - 224#64) ↦₆₄ w0) ∗
        ((s0.sp - 224#64 + 8#64) ↦₆₄ w1) ∗
        ((s0.sp - 224#64 + 16#64) ↦₆₄ w2) ∗
        ((s0.sp - 224#64 + 24#64) ↦₆₄ w3)) ∗
       ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
       ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
       arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
       ratchetTail A x.self Gc stc ∗
       (x.theirA ↦ₛ x.their.bytes.toList) ∗
       (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
       ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
       memRegion x.ret 88 ∗
       (lsLogFilterAddr ↦₆₄ 0#64) ∗
       stackAt (s0.sp - 480#64) 7712 ∗
       ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
       ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
       cmkLoopFrameRest s0.sp ∗
       cmkSavedRegs s0.sp s0 ∗
       A.pool) := by
    rw [hw_ck (s0.sp - 224#64), stackAt_7712_split_2048 (s0.sp - 480#64), h8192]
    refine Entails.trans ?_ (sepConj_mono_left h320_cells)
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by ac_rfl)
  refine SepWPp.conseq_pre hprep ?_
  rw [stackAt_7712_split_1024 (s0.sp - 480#64), h8192]
  simp only [sepExists_sepConj_left]
  refine SepWPp.exists_elim fun d0 => SepWPp.exists_elim fun d1 =>
    SepWPp.exists_elim fun d2 => SepWPp.exists_elim fun d3 => ?_
  have hadd1_ne0 : x.counter + 1#32 ≠ 0#32 := by
    have hc_ne : x.counter ≠ 0xffffffff#32 := hc_max
    bv_omega
  have hadd1_beq0 : (x.counter + 1#32 == 0#32) = false :=
    beq_false_of_ne hadd1_ne0
  have hadd1_not_beq0 : ¬((x.counter + 1#32 == 0#32) = true) := by
    rw [hadd1_beq0]; decide
  refine sepWPp_seq_epInv (mid := lsmpl.base 26) hloaded2 ?_
  wp_steps
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded3
  have hfind1 := findIndex_placed_ok_at_state_ls hfind (EpInvClass.to_lscl hloaded3)
  have hzip_len : (Gc.chains.zip stc.receiverChains).length = stc.receiverChains.length := by
    simp [hchains_len]
  have hlen_bv_toNat : (BitVec.ofNat 64 stc.receiverChains.length).toNat =
      (Gc.chains.zip stc.receiverChains).length := by
    rw [hzip_len, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hzip_cap_lt : (Gc.chains.zip stc.receiverChains).length * 104 < 2 ^ 63 := by
    rw [hzip_len]; omega
  refine sepWPp_seq_epInv (mid := (blkPl_24).base + bv% (1312)) hloaded3 ?_
  wp_call hfind1 (Gc.chainsPtr, Gc.chains.zip stc.receiverChains, x.theirA, x.their)
  apply SepWP.done (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
  intro hloaded4
  have hmap_find :
      ((Gc.chains.zip stc.receiverChains).map (·.2)).findIdx? (fun c => c.senderRatchetKey == x.their) =
        some ci := by
    rw [map_snd_zip_chains hchains_len]
    exact hci_find
  rw [hmap_find] at hpost_1
  rcases hpost_1 with ⟨hx0_sf1, hx1_toNat_sf1⟩
  have hx1_sf1 : sf_1.readReg64 Reg.x1 = BitVec.ofNat 64 ci := by
    rw [← hx1_toNat_sf1, BitVec.ofNat_toNat]; rfl
  have hgi : ci < Gc.chains.length := hchains_len ▸ hci
  have hfocus := focus_optChainKeyAt A x.self Gc stc ci chc hci hgi hchc_eq
  have hpull_focus :
      (arrayAt (chainAt A) 104 Gc.chainsPtr (Gc.chains.zip stc.receiverChains) ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt sf.sp 1024 ∗
        ((s0.sp - 320#64) ↦₆₄ w0) ∗
        ((s0.sp - 312#64) ↦₆₄ w1) ∗
        ((s0.sp - 304#64) ↦₆₄ w2) ∗
        ((s0.sp - 296#64) ↦₆₄ w3) ∗
        ((s0.sp - 224#64) ↦₆₄ w0) ∗
        ((s0.sp - 216#64) ↦₆₄ w1) ∗
        ((s0.sp - 208#64) ↦₆₄ w2) ∗
        ((s0.sp - 200#64) ↦₆₄ w3) ∗
        ((x.self + 8#64) ↦₆₄ Gc.chainsPtr) ∗
        ((x.self + 16#64) ↦₆₄ BitVec.ofNat 64 stc.receiverChains.length) ∗
        ratchetTail A x.self Gc stc ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        memRegion x.ret 88 ∗
        memRegion (s0.sp - 8192#64) 6688 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        cmkLoopFrameRest s0.sp ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool) ⊢
      ((⌜PublicKey.deserialize (Gc.chains[ci]'hgi).srk.bytes = .ok chc.senderRatchetKey ∧
          chc.messageKeys.length ≤ maxMessageKeys ∧
          (Gc.chains[ci]'hgi).keys.length = chc.messageKeys.length⌝ ∗
        optChainKeyAt A (Gc.chains[ci]'hgi).ck chc.chainKey
          (Gc.chainsPtr + BitVec.ofNat 64 (ci * 104) + 72#64) ∗
        ratchetRestAtChain A x.self Gc stc ci chc hgi) ∗
        memRegion x.ret 88 ∗
        (x.theirA ↦ₛ x.their.bytes.toList) ∗
        (x.ckA ↦ₛ keyToBytes32 ckc.key) ∗
        ((x.ckA + 32#64) ↦₃₂ ckc.index) ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt (s0.sp - 480#64) 7712 ∗
        ((s0.sp - 368#64) ↦₆₄ x.ret) ∗
        ((s0.sp - 356#64) ↦₃₂ x.counter) ∗
        ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) ∗
        memRegion (s0.sp - 224#64) 32 ∗
        cmkLoopFrameRest s0.sp ∗
        cmkSavedRegs s0.sp s0 ∗
        A.pool) := by
    have h224_mem :
        ((s0.sp - 224#64) ↦₆₄ w0) ∗ ((s0.sp - 216#64) ↦₆₄ w1) ∗
          ((s0.sp - 208#64) ↦₆₄ w2) ∗ ((s0.sp - 200#64) ↦₆₄ w3) ⊢
          memRegion (s0.sp - 224#64) 32 := by
      have := cells4_entails_memRegion32 (s0.sp - 224#64) w0 w1 w2 w3
      have hb1 : s0.sp - 224#64 + 8#64 = s0.sp - 216#64 := by bv_arith
      have hb2 : s0.sp - 224#64 + 16#64 = s0.sp - 208#64 := by bv_arith
      have hb3 : s0.sp - 224#64 + 24#64 = s0.sp - 200#64 := by bv_arith
      rwa [hb1, hb2, hb3] at this
    have h320_ck :
        ((s0.sp - 320#64) ↦₆₄ w0) ∗ ((s0.sp - 312#64) ↦₆₄ w1) ∗
          ((s0.sp - 304#64) ↦₆₄ w2) ∗ ((s0.sp - 296#64) ↦₆₄ w3) =
          ((s0.sp - 320#64) ↦ₛ keyToBytes32 (chainStepN F 1 ckc).key) := by
      have ha1 : s0.sp - 320#64 + 8#64 = s0.sp - 312#64 := by bv_arith
      have ha2 : s0.sp - 320#64 + 16#64 = s0.sp - 304#64 := by bv_arith
      have ha3 : s0.sp - 320#64 + 24#64 = s0.sp - 296#64 := by bv_arith
      rw [hw_ck (s0.sp - 320#64), ha1, ha2, ha3]
    refine Entails.trans ?_ (sepConj_mono_left hfocus)
    refine Entails.trans ?_
      (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right (sepConj_mono_right
          (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left h224_mem)))))))))))
    rw [hsp_sf, hsp_eq, stackAt_7712_split_1024 (s0.sp - 480#64), h8192, ← h320_ck]
    have heq : ∀ {P Q : SepProp}, P = Q → (P ⊢ Q) := fun h => h ▸ Entails.refl _
    exact heq (by ac_rfl)
  refine SepWPp.conseq_pre hpull_focus ?_
  simp only [sepConj_assoc]
  refine SepWPp.pure_elim fun ⟨hsrk, hmax, hklen⟩ => ?_
  exact hafter_find_fn sf_1
    hpc_sf_1 hrun_sf_1 (by simp only [wp_norm, arm64_norm, *]) hsp0
    (by simpa [State.spAligned, hsp_sf_1, hsp_sf, hsp_eq] using _hsp)
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) hloaded4
    (by simp only [wp_norm, arm64_norm, *])
    hx0_sf1 hx1_sf1 (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *]) (by simp only [wp_norm, arm64_norm, *])
    hci hgi hchains_len hpad_len hmax_jumps hcap_le hcap_lt hptr_ne
    hsrk hmax hklen hagree_Gc hm1 hm2 htouched

theorem advanceEpilogue_placed_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (H : String → Option (State → State)) :
    AdvanceEpiloguePlacedSpec F A H := by
  intro hA hfind hhmac x Gc stc ckc ci chc R s0 s
    hck_eq hc_max hci_find hchc_get hagree_Gc hm1 hm2 htouched hstate
  rcases hstate with ⟨hpc, ⟨hrun, hsp_eq, hsp0, hsp, hx29, htr, hloaded, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _hx19, hmem⟩
  change s.pc = (blkPl_24).base + 1244#64 at hpc
  refine reaches_outcome_of_sepWPp (spec := cmkPlacedSpec F A) hmem ?_
  exact advanceEpilogue_entry_placed_inv (Inv := LibsignalCodeLoaded lsmpl) hA hfind
    (hmac_placed_ok_at_state hhmac) x Gc stc ckc ci chc R s0 s
    hpc hrun hsp_eq hsp0 hsp hx29 htr hloaded hvregs
    hx21 hx23 hx26 hx27 hx28 hck_eq hc_max hci_find hchc_get
    hagree_Gc hm1 hm2 htouched

theorem advanceEpilogue_placed_ro_ok [LibsignalPlacement] (F : ShaState → List (BitVec 8) → ShaState)
    (A : RustAlloc) (H : String → Option (State → State)) :
    AdvanceEpiloguePlacedRoSpec F A H := by
  intro hA hfind hhmac x Gc stc ckc ci chc R s0 s
    hck_eq hc_max hci_find hchc_get hagree_Gc hm1 hm2 htouched hstate hro
  rcases hstate with ⟨hpc, ⟨hrun, hsp_eq, hsp0, hsp, hx29, htr, hloaded, hvregs⟩,
    ⟨hx21, hx23, hx26, hx27, hx28⟩, _hx19, hmem⟩
  change s.pc = (blkPl_24).base + 1244#64 at hpc
  refine reaches_outcome_of_sepWPp (spec := cmkPlacedSpec F A) hmem ?_
  exact advanceEpilogue_entry_placed_inv
    (Inv := fun m => LibsignalCodeLoaded lsmpl m ∧ LibsignalRoLoaded lsmpl m) hA hfind
    (hmac_placed_ro_ok_at_state hhmac) x Gc stc ckc ci chc R s0 s
    hpc hrun hsp_eq hsp0 hsp hx29 htr ⟨hloaded, hro⟩ hvregs
    hx21 hx23 hx26 hx27 hx28 hck_eq hc_max hci_find hchc_get
    hagree_Gc hm1 hm2 htouched

end CryptoVerification.LibsignalSession.AdvanceEpilogue

namespace CryptoVerification.LibsignalSession

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr

/-- Correctness of the `consume_message_key` epilogue (`AdvanceEpilogueSpec`). -/
theorem advanceEpilogue_ok (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (alloc : String → Option (State → State)) (img : Obj.Image) :
    AdvanceEpilogueSpec F A alloc img :=
  AdvanceEpilogue.advanceEpilogue_ok F A alloc img

/-- Relocatable correctness of the `consume_message_key` epilogue (`[LibsignalPlacement]`). -/
theorem advanceEpilogue_placed_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    AdvanceEpiloguePlacedSpec F A H :=
  AdvanceEpilogue.advanceEpilogue_placed_ok F A H

/-- Relocatable correctness of the `consume_message_key` epilogue backed by `.rodata`. -/
theorem advanceEpilogue_placed_ro_ok [LibsignalPlacement]
    (F : ShaState → List (BitVec 8) → ShaState) (A : RustAlloc)
    (H : String → Option (State → State)) :
    AdvanceEpiloguePlacedRoSpec F A H :=
  AdvanceEpilogue.advanceEpilogue_placed_ro_ok F A H

end CryptoVerification.LibsignalSession
