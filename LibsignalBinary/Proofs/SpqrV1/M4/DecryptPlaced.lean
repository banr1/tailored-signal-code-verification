/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.PqRecv
public import LibsignalBinary.Proofs.SpqrV1.GF.Mul2U16
public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
import LibsignalBinary.Proofs.SpqrV1.Prost.MessageEncode.Base
import LibsignalBinary.Proofs.SpqrV1.Top.Recv.RecvPlacedCodeSym
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DeriveKeys
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Model
import LibsignalBinary.Proofs.TripleRatchet.Decrypt.Root
import ProofLib.SepLogic.WPp

/-!
# Relocatable `try_decrypt_with_state` over SPQR V1

Relocatable `[LibsignalPlacement]` widened `spqr::recv` contract (`spqrRecvPlacedSpecWT`), framed
Segment S5 seams, and root compositions for Blocks `130` (`HookRng`) and `433` (`CoinsRng`).
-/

@[expose] public section

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 400000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace CryptoVerification.LibsignalSpqrV1.M4

open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Decrypt
open CryptoVerification.LibsignalTripleRatchet.Decrypt.Model
open CryptoVerification.LibsignalTripleRatchet.Decrypt.KeyDerive
open CryptoVerification.SpqrV1.GF.Mul2U16
open CryptoVerification.SpqrV1.Top.Recv

variable [LibsignalPlacement]

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero BitVec.add_assoc
attribute [local wp_norm] BitVec.add_assoc
attribute [local simp, local wp_norm, local arm64_norm] extractLsb0_8_append56

/-! ## Relocatable Widened Recv Contract (`spqrRecvPlacedSpecWT`) & Bridge from `spqrRecvPlacedSpecXT` -/

private abbrev optKeyAtW (A : RustAlloc) (a : BitVec 64) (k : Salt) : SepProp :=
  spqrRecvKeyAt A a k

private abbrev recvResultAtW (A : RustAlloc) (r : BitVec 64)
    (res : Except Bool (List (BitVec 8) × Salt)) : SepProp :=
  spqrRecvResultAt A r res

private theorem optKeyAtW_eq_optKeyRecvAt_pub (A : RustAlloc) (a : BitVec 64) (k : Salt) :
    optKeyAtW A a k = spqrRecvKeyAt A a k := rfl

private theorem recvResultAtW_eq_recvResultAt (A : RustAlloc) (r : BitVec 64)
    (res : Except Bool (List (BitVec 8) × Salt)) :
    recvResultAtW A r res = spqrRecvResultAt A r res := rfl

section
set_option quotPrecheck false
local notation "recvResultAtW_pub" =>
  fun (A : RustAlloc) (r : BitVec 64) (res : Except Bool (List (BitVec 8) × Salt)) =>
    spqrRecvResultAt A r res

/-- Relocatable `spqr::recv` specification with the widened key layout (`recvResultAtW`). -/
def spqrRecvPlacedSpecW (A : RustAlloc) (S : SpqrModel) : Spec (VecArg × VecArg × BitVec 64) where
  pre := fun (st, msg, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
      st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ logOff tryDecryptPlacedImg ∗ A.pool ∗
      stackAt s.sp spqrRecvStack
  post := fun (st, msg, ret) s0 sf =>
    ⌜sf.trace = s0.trace ∧ ¬ S.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
      recvResultAtW_pub A ret (S.recv st.bytes msg.bytes) ∗
      logOff tryDecryptPlacedImg ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
  onPanic := fun (st, msg, _) s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap
end

/-- Relocatable `spqrRecvPlacedSpecW` with `tokenInitPlacedAt` framed and the bounds of
    `spqrRecvPlacedSpecXT` (`st < 2^32`, `msg < 2^40`, `spqrRecvStack ≤ sp`). -/
def spqrRecvPlacedSpecWT (A : RustAlloc) (S : SpqrModel) : Spec (VecArg × VecArg × BitVec 64) :=
  { spqrRecvPlacedSpecW A S with
    pre := fun x s =>
      ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧ spqrRecvStack ≤ s.sp.toNat⌝ ∗
        tokenInitPlacedAt ∗ (spqrRecvPlacedSpecW A S).pre x s
    post := fun x s0 sf => tokenInitPlacedAt ∗ (spqrRecvPlacedSpecW A S).post x s0 sf }

private theorem recvResultAtX_entails_recvResultAtW_placed (F : ShaCompress) (K : MlKem)
    (A : RustAlloc) (ret : BitVec 64) (st msg : List (BitVec 8)) :
    recvResultExactKeyAt A ret ((spqrV1Recv F K).recv st msg) ⊢
      recvResultAtW A ret ((spqrV1 F K).recv st msg) := by
  rw [recvResultAtW_eq_recvResultAt]
  exact recvResultAtX_entails_recvResultAt A ret F K st msg

/-- Raw relocatable `spqr::recv` specification over `SpqrRecvModel` (`recvResultExactKeyAt`). -/
def spqrRecvPlacedRawSpecX (A : RustAlloc) (S : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) where
  pre := fun (st, msg, ret) s =>
    ⌜s.readReg64 .x0 = st.v ∧ s.readReg64 .x1 = msg.v ∧ s.readReg64 .x8 = ret⌝ ∗
      st.at A ∗ msg.at A ∗ memRegion ret 48 ∗ (lsmpl.ρ lsLogFilterSym ↦₆₄ 0#64) ∗ A.pool ∗
      stackAt s.sp spqrRecvStack
  post := fun (st, msg, ret) s0 sf =>
    ⌜sf.trace = s0.trace ∧ ¬ S.recvPanics st.bytes msg.bytes⌝ ∗ st.at A ∗ msg.at A ∗
      recvResultExactKeyAt A ret (S.recv st.bytes msg.bytes) ∗
      (lsmpl.ρ lsLogFilterSym ↦₆₄ 0#64) ∗ A.pool ∗ stackAt s0.sp spqrRecvStack
  onPanic := fun (st, msg, _) s0 sf =>
    ⌜(allocFailedIn s0 sf ∨ S.recvPanics st.bytes msg.bytes) ∧ s0.trace <+: sf.trace⌝ ∗
      anyHeap

/-- Relocatable `spqr::recv` specification with `tokenInitPlacedAt` framed and input/stack bounds. -/
def spqrRecvPlacedSpecXT (A : RustAlloc) (S : SpqrRecvModel) :
    Spec (VecArg × VecArg × BitVec 64) :=
  withLsCodeRoLoaded lsmpl
    { spqrRecvPlacedRawSpecX A S with
      pre := fun x s =>
        ⌜x.1.bytes.length < 2 ^ 32 ∧ x.2.1.bytes.length < 2 ^ 40 ∧
          spqrRecvStack ≤ s.sp.toNat⌝ ∗
          tokenInitPlacedAt ∗ (spqrRecvPlacedRawSpecX A S).pre x s
      post := fun x s0 sf =>
        tokenInitPlacedAt ∗ (spqrRecvPlacedRawSpecX A S).post x s0 sf }

/-- Bridge from `spqrRecvPlacedSpecXT A (spqrV1Recv F K)` to
    `withLsCodeRoLoaded lsmpl (spqrRecvPlacedSpecWT A (spqrV1 F K))` on any `prog : Program`
    and `entry_pc : BitVec 64`. -/
theorem spqrRecvPlacedOkWT_of_v1 {prog : Program} {entry_pc : BitVec 64}
    (A : RustAlloc) (F : ShaCompress) (K : MlKem)
    (hRecvV1 : subroutine_ok prog entry_pc (spqrRecvPlacedSpecXT A (spqrV1Recv F K))) :
    subroutine_ok prog entry_pc (withLsCodeRoLoaded lsmpl (spqrRecvPlacedSpecWT A (spqrV1 F K))) := by
  refine subroutine_ok_mono hRecvV1
    (fun (st, msg, ret) R s0 hpre => by
      dsimp only [withLsCodeRoLoaded, spqrRecvPlacedSpecWT, spqrRecvPlacedSpecW,
        spqrRecvPlacedSpecXT, spqrRecvPlacedRawSpecX] at hpre ⊢
      rw [logOff_tryDecryptPlacedImg] at hpre
      exact hpre)
    (fun (st, msg, ret) R s0 sf hpost => by
      dsimp only [withLsCodeRoLoaded, spqrRecvPlacedSpecWT, spqrRecvPlacedSpecW,
        spqrRecvPlacedSpecXT, spqrRecvPlacedRawSpecX] at hpost ⊢
      rw [logOff_tryDecryptPlacedImg]
      exact Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_right
        (sepConj_mono_right (sepConj_mono_right (sepConj_mono_left
          (recvResultAtX_entails_recvResultAtW_placed F K A ret st.bytes msg.bytes))))))) hpost)
    (fun (st, msg, ret) R s0 sf hpan => by
      dsimp only [withLsCodeRoLoaded, spqrRecvPlacedSpecWT, spqrRecvPlacedSpecW,
        spqrRecvPlacedSpecXT, spqrRecvPlacedRawSpecX] at hpan ⊢
      rw [sepConj_assoc, satisfies_pure_sepConj] at hpan ⊢
      rcases hpan with ⟨⟨hp, htr⟩, hany⟩
      refine ⟨⟨?_, htr⟩, hany⟩
      rcases hp with ha | hr
      · exact Or.inl ha
      · exact Or.inr (toSpqrModel_recvPanics_of_toSpqrRecvModel (spqrDeps F K)
          (spqrHkdfWith F) st.bytes msg.bytes hr))
    (fun _ _ _ _ _ he => he)

/-! ## Relocatable Framed Segment S5 Seam (`S5SeamPlacedWT`, `pqRecv_159_placed_okWT`, `pqRecv_549_placed_okWT`) -/

/-- Relocatable Segment S5 seam with `tokenInitPlacedAt` framed and `x.st.pqRatchetState.length < 2^32`
    + `rootStack ≤ s0.sp.toNat`. -/
def S5SeamPlacedWT (prog : Program) (entry : BitVec 64)
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (parse : UuidParser) (S : SpqrModel) : Prop :=
  ∀ (x : TryDecryptGhost) (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8)))
    (st1 : SessionState (List (BitVec 8))) (mkg : MessageKeyGenerator) (draws : Nat)
    (R : SepProp) (s0 s : State),
    x.st.pqRatchetState.length < 2 ^ 32 →
    rootStack ≤ s0.sp.toNat →
    tr.pqrState = x.st.pqRatchetState →
    PqRecvStatePlaced entry A ctl x trG tr st1 mkg draws (tokenInitPlacedAt ∗ R) s0 s →
    prog.CodeLoaded s.mem →
    match S.recv tr.pqrState x.msg.pqRatchet with
    | .ok (newPqrState, pqrKey) =>
      ∃ s', Steps prog s s' ∧
        ((DeriveKeysStatePlaced entry A ctl x trG tr st1 mkg newPqrState pqrKey draws
            (tokenInitPlacedAt ∗ R) s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))
    | .error sd =>
      let e : SignalProtocolError :=
        if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
      ∃ s', Steps prog s s' ∧
        ((ErrTailStatePlaced entry A ctl x trG tr st1 e draws (tokenInitPlacedAt ∗ R) s0 s' ∧
           S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
         (s'.status = .Panicked ∧
           (s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)))

private theorem pqr_len_lt_of_restAt {A : RustAlloc} {g : SignalMessageGhost} {a : BitVec 64}
    {m : SignalMessage} {Q : SepProp} {mem : Memory}
    (h : mem ⊨ signalMessageRestAt A g a m ∗ Q) :
    m.pqRatchet.length < 2 ^ 40 := by
  unfold signalMessageRestAt at h
  rw [sepConj_assoc, satisfies_pure_sepConj] at h
  exact h.1.2.2.2.1

private theorem spqrRecvStack_le_of_rootStack {sp0 sp : BitVec 64}
    (hstack : rootStack ≤ sp0.toNat) (hsp : sp0 - 1504#64 = sp) :
    spqrRecvStack ≤ sp.toNat := by
  subst hsp
  have h1 : rootStack = 262144 := rfl
  have h2 : spqrRecvStack = 131072 := rfl
  rw [BitVec.toNat_sub_of_le]
  · simp only [BitVec.toNat_ofNat]; omega
  · rw [BitVec.le_def]; simp only [BitVec.toNat_ofNat]; omega

private theorem onPanic_absorb_tokenInit {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {x : TryDecryptGhost} {R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ (tokenInitPlacedAt ∗ R)) :
    s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R :=
  Decrypt.onPanic_drop_frame (img := tryDecryptPlacedImg) h

private theorem s5_err_out_absorb {prog : Program} {s s0 : State} {P : State → Prop}
    {Q : Prop} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {x : TryDecryptGhost} {R : SepProp}
    (hQ : Q)
    (h : ∃ s', Steps prog s s' ∧
      (P s' ∨ (s'.status = .Panicked ∧
        s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ (tokenInitPlacedAt ∗ R)))) :
    ∃ s', Steps prog s s' ∧
      ((P s' ∧ Q) ∨ (s'.status = .Panicked ∧
        s'.mem ⊨ (tryDecryptSpecPlaced C A ctl parse S).onPanic x s0 s' ∗ R)) := by
  rcases h with ⟨s', hst, hp | ⟨hpan, hmem⟩⟩
  · exact ⟨s', hst, Or.inl ⟨hp, hQ⟩⟩
  · exact ⟨s', hst, Or.inr ⟨hpan, onPanic_absorb_tokenInit hmem⟩⟩

private abbrev pqRecvCallFrame (A : RustAlloc) (ctl : BitVec 64) (x : TryDecryptGhost)
    (trG : TrGhost) (tr : TripleRatchet (List (BitVec 8))) (st1 : SessionState (List (BitVec 8)))
    (mkg : MessageKeyGenerator) (draws : Nat) (seedCap seedPtr sp : BitVec 64)
    (msgW : BitVec 32) (s0 : State) : SepProp :=
  trRestAt A sp trG tr ∗ signalMessageRestAt A x.msgG x.msgA x.msg ∗
    sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
    (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
      (seedPtr ↦ₛ mkg.seed) ∗
      memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
    memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
    memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
    ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
    memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
    ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
    memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A x.rem x.remA ∗
    protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest draws ∗
    memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
    tryDecryptSavedRegs s0.sp s0

private theorem pqRecv_pre_callWT {A : RustAlloc} {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {trG : TrGhost} {tr : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {mkg : MessageKeyGenerator} {draws : Nat}
    {seedCap seedPtr sp : BitVec 64} {msgW : BitVec 32} {R : SepProp} {s0 sm : State}
    (hpqr_lt : x.st.pqRatchetState.length < 2 ^ 32)
    (hstack : rootStack ≤ s0.sp.toNat)
    (hpqr_eq : tr.pqrState = x.st.pqRatchetState)
    (hsp_def : s0.sp - 1504#64 = sp)
    (hx0m : sm.readReg64 .x0 = sp + 232#64)
    (hx1m : sm.readReg64 .x1 = x.msgA)
    (hx8m : sm.readReg64 .x8 = sp + 1280#64)
    (hspm : sm.sp = sp)
    (hmm : sm.mem ⊨
      (sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
       (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
         (seedPtr ↦ₛ mkg.seed) ∗
         memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
       memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
       memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
       ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
       memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
       ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
       memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80 ∗
       protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
       signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
       logOff tryDecryptPlacedImg ∗ stackAt sp tryDecryptSubStack ∗
       tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ (tokenInitPlacedAt ∗ R)) :
    sm.mem ⊨ (spqrRecvPlacedSpecWT A S).pre
        (⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩,
         ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩,
         sp + 1280#64) sm ∗
      (pqRecvCallFrame A ctl x trG tr st1 mkg draws seedCap seedPtr sp msgW s0 ∗ R) := by
  let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
  let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
  have hpre_raw : sm.mem ⊨ (spqrRecvPlacedSpecW A S).pre (stArg, msgArg, sp + 1280#64) sm ∗
      (pqRecvCallFrame A ctl x trG tr st1 mkg draws seedCap seedPtr sp msgW s0 ∗ (tokenInitPlacedAt ∗ R)) := by
    dsimp only [spqrRecvPlacedSpecW, VecArg.at, stArg, msgArg, pqRecvCallFrame]
    rw [hspm]
    rw [trAt_split_pq, signalMessageAt_split_pq,
      stackAt_sub sp tryDecryptSubStack spqrRecvStack] at hmm
    rw [sepConj_assoc, satisfies_pure_sepConj]
    refine ⟨⟨hx0m, hx1m, hx8m⟩, ?_⟩
    simp only [sepConj_assoc] at hmm ⊢
    arm64_sep_close
  clear hmm
  have hpqr_msg_lt : x.msg.pqRatchet.length < 2 ^ 40 := by
    have hsub : sm.mem ⊨ signalMessageRestAt A x.msgG x.msgA x.msg ∗
        ((spqrRecvPlacedSpecW A S).pre (stArg, msgArg, sp + 1280#64) sm ∗
         trRestAt A sp trG tr ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
         (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
           (seedPtr ↦ₛ mkg.seed) ∗
           memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
         memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
         memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
         ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
         memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
         ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
         memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A x.rem x.remA ∗
         protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest draws ∗
         memRegion (sp - BitVec.ofNat 64 tryDecryptSubStack) (tryDecryptSubStack - spqrRecvStack) ∗
         tryDecryptSavedRegs s0.sp s0 ∗ tokenInitPlacedAt ∗ R) := by
      dsimp only [pqRecvCallFrame] at hpre_raw
      simp only [sepConj_assoc] at hpre_raw ⊢
      arm64_sep_close
    exact pqr_len_lt_of_restAt hsub
  have hst_len : stArg.bytes.length < 2 ^ 32 := by
    dsimp only [stArg]; rw [hpqr_eq]; exact hpqr_lt
  have hsp_recv : spqrRecvStack ≤ sm.sp.toNat := by
    rw [hspm]; exact spqrRecvStack_le_of_rootStack hstack hsp_def
  dsimp only [spqrRecvPlacedSpecWT, pqRecvCallFrame] at hpre_raw ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj]
  refine ⟨⟨hst_len, hpqr_msg_lt, hsp_recv⟩, ?_⟩
  simp only [sepConj_assoc] at hpre_raw ⊢
  arm64_sep_close

theorem pqRecv_159_placed_okWT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvPlacedSpecWT A S)))
    (hfmt_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S5SeamPlacedWT ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mkg draws R s0 s hpqr_lt hstack hpqr_eq h5 hL
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segPqRecvPC_at at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  rw [sepConj_assoc] at hmem
  suffices ∃ s', Steps ((blkPC_131).rebase (blkPl_131).base H) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysStatePlaced (blkPl_131).base A ctl x trG tr st1 mkg newPqrState pqrKey draws
            (tokenInitPlacedAt ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (ErrTailStatePlaced (blkPl_131).base A ctl x trG tr st1 e draws (tokenInitPlacedAt ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R) by
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP_placed (R := tokenInitPlacedAt ∗ R) hmem hL hcl
    (mid := lsmpl.base 329)
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_131).base + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗ stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗ A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hclm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call := pqRecv_pre_callWT (S := S) hpqr_lt hstack hpqr_eq hsp_def hx0m hx1m hx8m hspm hmm
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvPlacedSpecWT, spqrRecvPlacedSpecW, VecArg.at, stArg, msgArg, pqRecvCallFrame] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A (sp + 1304#64) pqrKey ∗ trAt A (sp + 56#64) trG tr ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗ stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ (tokenInitPlacedAt ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      refine s5_out_add_np hnpF ?_
      unfold DeriveKeysStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ (tokenInitPlacedAt ∗ R)))
        hpost1' hLf1 hclf1 ?_
      unfold segDeriveKeysPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvPlacedSpecWT, spqrRecvPlacedSpecW, VecArg.at, stArg, msgArg, pqRecvCallFrame] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗ memRegion (sp + 1289#64) 7 ∗
           ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sp + 1296#64) 32 ∗
           trAt A (sp + 56#64) trG tr ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗ stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ (tokenInitPlacedAt ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        exact s5_err_out_absorb hnpF (KeyDeriveCallees.pqRecv_recv_err_true_159_placed C A ctl S H x trG tr st1 mkg draws (tokenInitPlacedAt ∗ R) s0
          hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        exact s5_err_out_absorb hnpF (KeyDeriveCallees.pqRecv_recv_err_false_159_placed C A ctl S H x trG tr st1 mkg draws (tokenInitPlacedAt ∗ R) s0
          hmsgW hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def hd_ne
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')

theorem pqRecv_549_placed_okWT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (H : String → Option (State → State))
    (hrecv_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvPlacedSpecWT A S)))
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A)) :
    S5SeamPlacedWT ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S := by
  intro x trG tr st1 mkg draws R s0 s hpqr_lt hstack hpqr_eq h5 hL
  rcases h5 with ⟨hpc, hmeta, hx19, hx20, hx21, hx22, hx23, hw24, hx25,
    seedCap, seedPtr, msgW, hmsgW, hseed1, hseed2, hseed3, hmem⟩
  rcases hmeta with ⟨hrun, hsp, hsp0_al, hsp_al, hx29, htrace, hcl, hvregs⟩
  have hsp0_al' : (s0.sp &&& 15#64 == 0#64) = true := hsp0_al
  have hseed : mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 :=
    ⟨hseed1, hseed2, hseed3⟩
  unfold segPqRecvPC_at at hpc
  rw [show (0x5b8#64 : BitVec 64) = 1464#64 by rfl] at hpc
  have hsp29_eq : s0.sp - 96#64 = (s0.sp - 1504#64) + 1408#64 := sp_fp_eq rfl
  change s.readReg64 .fp = s0.sp - 96#64 at hx29
  rw [hsp29_eq] at hx29
  clear hsp29_eq
  unfold tryDecryptCommonHeap at hmem
  generalize hsp_def : s0.sp - 1504#64 = sp at hsp hx20 hx23 hx25 hx29 hmem
  have hsp_al' : (sp &&& 15#64 == 0#64) = true := by rw [← hsp]; exact hsp_al
  simp only [← sepConj_assoc] at hmem
  rw [sepConj_assoc] at hmem
  suffices ∃ s', Steps ((blkPC_434).rebase (blkPl_434).base H) s s' ∧
      match S.recv tr.pqrState x.msg.pqRatchet with
      | .ok (newPqrState, pqrKey) =>
        (DeriveKeysStatePlaced (blkPl_434).base A ctl x trG tr st1 mkg newPqrState pqrKey draws
            (tokenInitPlacedAt ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R)
      | .error sd =>
        let e := if sd = true then .invalidState else .invalidMessage x.msgType .pqRatchet
        (ErrTailStatePlaced (blkPl_434).base A ctl x trG tr st1 e draws (tokenInitPlacedAt ∗ R) s0 s' ∧
          S.recvPanics tr.pqrState x.msg.pqRatchet = false) ∨
          (s'.status = .Panicked ∧ s'.mem ⊨ (tryDecryptSpecPlaced C A ctl uuidTryParse S).onPanic x s0 s' ∗ R) by
    cases hrecv_eq : S.recv tr.pqrState x.msg.pqRatchet with
    | error sd =>
      rw [hrecv_eq] at this
      exact this
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      rw [hrecv_eq] at this
      exact this
  refine steps_of_sepWP_placed (R := tokenInitPlacedAt ∗ R) hmem hL hcl
    (mid := lsmpl.base 329)
    (RegMid := fun sm =>
      sm.readReg64 .x0 = sp + 232#64 ∧
      sm.readReg64 .x1 = x.msgA ∧
      sm.readReg64 .x8 = sp + 1280#64 ∧
      sm.readReg64 .lr = (blkPl_434).base + 1488#64 ∧
      sm.readReg64 .x19 = x.ret ∧
      sm.readReg64 .x20 = sp + 320#64 ∧
      sm.readReg64 .x21 = x.ss ∧
      sm.readReg64 .x22 = x.msgA ∧
      sm.readReg64 .x23 = sp + 1280#64 ∧
      (sm.readReg64 .x24).setWidth 32 = 1#32 ∧
      sm.readReg64 .x25 = sp + 400#64 ∧
      sm.readReg64 .x27 = sp + 56#64 ∧
      sm.readReg64 .x28 = sp + 1280#64 ∧
      sm.readReg64 .fp = sp + 1408#64 ∧
      sm.sp = sp ∧ sm.spAligned = true ∧ sm.trace = s0.trace ∧
      calleeSavedVRegs sm = calleeSavedVRegs s0)
    (P_mid :=
      sessionStateAt A x.ss x.G.afterTrFrom st1 ∗ trAt A (sp + 56#64) trG tr ∗
      (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
        (seedPtr ↦ₛ mkg.seed) ∗
        memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
      memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
      memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
      ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
      memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
      ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
      memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80 ∗
      protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      signalMessageAt A x.msgG x.msgA x.msg ∗ tapeAfter ctl x.cur x.rest draws ∗
      logOff tryDecryptPlacedImg ∗ stackAt sp tryDecryptSubStack ∗
      tryDecryptSavedRegs s0.sp s0 ∗ A.pool)
    ?_ ?_
  · wp_steps
    have hm1116 : memRegion (sp + 1116#64) 292 =
        memRegion (sp + 1116#64) 164 ∗ (memRegion (sp + 1280#64) 48 ∗ memRegion (sp + 1328#64) 80) := by
      rw [mr_cut_add sp 1116 164 128 (by decide), mr_cut_add sp 1280 48 80 (by decide)]
    rw [hm1116]
    wp_done
  · intro sm hpcm hrunm hclm hLm hReg hmm
    rcases hReg with ⟨hx0m, hx1m, hx8m, hlrm, hx19m, hx20m, hx21m, hx22m, hx23m, hw24m,
      hx25m, hx27m, hx28m, hfpm, hspm, hsp_alm, htracem, hvregsm⟩
    let stArg : VecArg := ⟨sp + 232#64, trG.pq.cap, trG.pq.ptr, tr.pqrState⟩
    let msgArg : VecArg := ⟨x.msgA, x.msgG.pqCap, x.msgG.pqPtr, x.msg.pqRatchet⟩
    have hpre_call := pqRecv_pre_callWT (S := S) hpqr_lt hstack hpqr_eq hsp_def hx0m hx1m hx8m hspm hmm
    cases hrecv : S.recv tr.pqrState x.msg.pqRatchet with
    | ok pair =>
      rcases pair with ⟨newPqrState, pqrKey⟩
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvPlacedSpecWT, spqrRecvPlacedSpecW, VecArg.at, stArg, msgArg, pqRecvCallFrame] at hpost1
      rw [hspm] at hspf1 hpost1
      have hsp_al1' : (sf1.sp &&& 15#64 == 0#64) = true := hsp_alf1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt] at hpost1
      unfold vecU8 at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨newPqrCap, newPqrPtr, hpost1⟩
      have hpost1' : sf1.mem ⊨
          vecU8At A (sp + 1280#64) newPqrCap newPqrPtr newPqrState ∗
          (spqrRecvKeyAt A (sp + 1304#64) pqrKey ∗ trAt A (sp + 56#64) trG tr ∗
           signalMessageAt A x.msgG x.msgA x.msg ∗ sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗ stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ (tokenInitPlacedAt ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 24#64 = sp + 1304#64 by rw [BitVec.add_assoc]; rfl] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      unfold vecU8At vecHeader at hpost1'
      simp only [sepConj_assoc] at hpost1'
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        satisfies_pure_sepConj] at hpost1'
      rcases hpost1' with ⟨⟨hnp1, hnp2, hnp3⟩, hpost1'⟩
      have hcap_not_m1 : (newPqrCap + 1#64 == 0#64) = false := cap_add_one_ne_zero hnp2
      simp only [← sepConj_assoc] at hpost1'
      refine s5_out_add_np hnpF ?_
      unfold DeriveKeysStatePlaced
      refine steps_done_of_sepWP_midMeta_placed (s0 := s0)
        (Rest := fun sf =>
          sf.readReg64 .x19 = x.ret ∧
          sf.readReg64 .x20 = (s0.sp - 1504#64) + 0x140#64 ∧
          sf.readReg64 .x21 = x.ss ∧
          sf.readReg64 .x22 = x.msgA ∧
          sf.readReg64 .x23 = (s0.sp - 1504#64) + 0x500#64 ∧
          (sf.readReg64 .x24).setWidth 32 = 1#32 ∧
          sf.readReg64 .x25 = (s0.sp - 1504#64) + 0x190#64 ∧
          sf.readReg64 .x27 = (s0.sp - 1504#64) + 0x38#64 ∧
          sf.readReg64 .x28 = (s0.sp - 1504#64) + 0x500#64 ∧
          ∃ (seedCap seedPtr newPqrCap newPqrPtr : BitVec 64) (msgW : BitVec 32),
            sf.readReg64 .x8 = newPqrCap ∧
            msgW.setWidth 8 = msgTypeByte x.msgType ∧
            mkg.seed.length ≤ seedCap.toNat ∧ seedCap.toNat < 2 ^ 63 ∧ seedPtr ≠ 0 ∧
            (sf.mem ⊨
              sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
              trAt A ((s0.sp - 1504#64) + 0x38#64) trG tr ∗
              (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
                (seedPtr ↦ₛ mkg.seed) ∗
                memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
              vecU8At A ((s0.sp - 1504#64) + 0x500#64) newPqrCap newPqrPtr newPqrState ∗
              spqrRecvKeyAt A ((s0.sp - 1504#64) + 0x518#64) pqrKey ∗
              memRegion x.ret 48 ∗
              memRegion (s0.sp - 1504#64) 0x10 ∗
              (((s0.sp - 1504#64) + 0x10#64) ↦₆₄ seedPtr) ∗
              memRegion ((s0.sp - 1504#64) + 0x18#64) 4 ∗
              (((s0.sp - 1504#64) + 0x1c#64) ↦₃₂ msgW) ∗
              (((s0.sp - 1504#64) + 0x20#64) ↦₆₄ x.locA) ∗
              (((s0.sp - 1504#64) + 0x28#64) ↦₆₄ seedCap) ∗
              (((s0.sp - 1504#64) + 0x30#64) ↦₆₄ x.remA) ∗
              memRegion ((s0.sp - 1504#64) + 0x140#64) 0x310 ∗
              (((s0.sp - 1504#64) + 0x450#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
              (((s0.sp - 1504#64) + 0x458#64) ↦₃₂ mkg.counter) ∗
              memRegion ((s0.sp - 1504#64) + 0x45c#64) 0xa4 ∗
              memRegion ((s0.sp - 1504#64) + 0x530#64) 0x50 ∗
              tryDecryptCommonHeap A ctl tryDecryptPlacedImg x draws s0 ∗ (tokenInitPlacedAt ∗ R)))
        hpost1' hLf1 hclf1 ?_
      unfold segDeriveKeysPC_at tryDecryptMidMetaCore tryDecryptCommonHeap
      rw [show (0x5dc#64 : BitVec 64) = 1500#64 by rfl]
      have hsp29_eq : s0.sp - 96#64 = sp + 1408#64 := sp_fp_eq hsp_def
      rw [hsp29_eq]
      clear hsp29_eq
      rw [hsp_def]
      dsimp only [vecU8At, vecHeader]
      wp_conv_pre => simp only [sepConj_assoc]
      wp_steps
      wp_done
    | error sd =>
      refine steps_call_placed_cro (stArg, msgArg, sp + 1280#64) hrecv_call
        hpcm hrunm hsp_alm hlrm hclm hLm hpre_call
        (fun sf hpan hpost => ⟨hpan, onPanic_of_spqrRecv_placed (st := stArg) (msg := msgArg)
          (ret := sp + 1280#64) htracem hpqr_eq rfl hpost⟩) ?_
      intro sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hcsf1 hclf1 hLf1 hpost1
      dsimp only [spqrRecvPlacedSpecWT, spqrRecvPlacedSpecW, VecArg.at, stArg, msgArg, pqRecvCallFrame] at hpost1
      rw [hspm] at hspf1 hpost1
      have hcs := hcsf1
      rcases hcs with ⟨hx19_1, hx20_1, hx21_1, hx22_1, hx23_1, hx24_1, hx25_1,
        hx26_1, hx27_1, hx28_1, hfp_1, hvregs_1⟩
      rw [hx19m] at hx19_1; rw [hx20m] at hx20_1; rw [hx21m] at hx21_1
      rw [hx22m] at hx22_1; rw [hx23m] at hx23_1; rw [hx25m] at hx25_1
      rw [hx27m] at hx27_1; rw [hx28m] at hx28_1; rw [hfpm] at hfp_1; rw [hvregsm] at hvregs_1
      have hw24_1 : (sf1.readReg64 .x24).setWidth 32 = 1#32 := by rw [hx24_1]; exact hw24m
      rw [sepConj_assoc, sepConj_pure_left_comm, sepConj_assoc, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨⟨htrace1, hnoP⟩, hpost1⟩
      have hnpF : S.recvPanics tr.pqrState x.msg.pqRatchet = false := by simpa using hnoP
      rw [htracem] at htrace1
      rw [hrecv] at hpost1
      dsimp only [spqrRecvResultAt, errTag] at hpost1
      simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost1
      rcases hpost1 with ⟨d, hpost1⟩
      simp only [sepConj_assoc] at hpost1
      rw [sepConj_pure_left_comm, sepConj_pure_left_comm, sepConj_pure_left_comm,
        sepConj_pure_left_comm, satisfies_pure_sepConj] at hpost1
      rcases hpost1 with ⟨hd_iff, hpost1⟩
      have hpost1' : sf1.mem ⊨
          (((sp + 1288#64) ↦₈ d) ∗ memRegion (sp + 1289#64) 7 ∗
           ((sp + 1280#64) ↦₆₄ 0xFFFFFFFFFFFFFFFF#64) ∗ memRegion (sp + 1296#64) 32 ∗
           trAt A (sp + 56#64) trG tr ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
           sessionStateAt A x.ss x.G.afterTrFrom st1 ∗
           (if seedCap = 0 then emp else A.live seedPtr seedCap.toNat 1 ∗
             (seedPtr ↦ₛ mkg.seed) ∗
             memRegion (seedPtr + BitVec.ofNat 64 mkg.seed.length) (seedCap.toNat - mkg.seed.length)) ∗
           memRegion x.ret 48 ∗ memRegion sp 16 ∗ ((sp + 16#64) ↦₆₄ seedPtr) ∗
           memRegion (sp + 24#64) 4 ∗ ((sp + 28#64) ↦₃₂ msgW) ∗ ((sp + 32#64) ↦₆₄ x.locA) ∗
           ((sp + 40#64) ↦₆₄ seedCap) ∗ ((sp + 48#64) ↦₆₄ x.remA) ∗
           memRegion (sp + 320#64) 784 ∗ ((sp + 1104#64) ↦₆₄ BitVec.ofNat 64 mkg.seed.length) ∗
           ((sp + 1112#64) ↦₃₂ mkg.counter) ∗ memRegion (sp + 1116#64) 164 ∗
           memRegion (sp + 1328#64) 80 ∗ protocolAddressAt A x.rem x.remA ∗
           protocolAddressAt A x.loc x.locA ∗ tapeAfter ctl x.cur x.rest draws ∗
           logOff tryDecryptPlacedImg ∗ stackAt sp tryDecryptSubStack ∗
           tryDecryptSavedRegs s0.sp s0 ∗ A.pool) ∗ (tokenInitPlacedAt ∗ R) := by
        rw [trAt_split_pq, signalMessageAt_split_pq,
          stackAt_sub sp tryDecryptSubStack spqrRecvStack]
        rw [show (sp + 1280#64) + 8#64 = sp + 1288#64 by rw [BitVec.add_assoc]; rfl,
          show (sp + 1280#64) + 9#64 = sp + 1289#64 by rw [BitVec.add_assoc]; rfl,
          mr_cut sp 1289 7 32 39 1296#64] at hpost1
        simp only [sepConj_assoc] at hpost1 ⊢
        arm64_sep_close
      rw [show sp + 1289#64 = (sp + 1288#64) + 1#64 by rw [BitVec.add_assoc]; rfl] at hpost1'
      cases sd with
      | true =>
        have hd0 : d = 0#8 := hd_iff.mpr rfl
        subst hd0
        exact s5_err_out_absorb hnpF (KeyDeriveCallees.pqRecv_recv_err_true_549_placed C A ctl S H x trG tr st1 mkg draws (tokenInitPlacedAt ∗ R) s0
          hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')
      | false =>
        have hd_ne : d ≠ 0#8 := fun h => Bool.noConfusion (hd_iff.mp h)
        exact s5_err_out_absorb hnpF (KeyDeriveCallees.pqRecv_recv_err_false_549_placed C A ctl S H x trG tr st1 mkg draws (tokenInitPlacedAt ∗ R) s0
          hmsgW hsp0_al' hseed1 hseed2 hfmt_call hdealloc_call hsp_def hd_ne
          sf1 hpcf1 hrunf1 hspf1 hsp_alf1 hx19_1 hx20_1 hx23_1 hw24_1 hx25_1 hx28_1 hfp_1
          htrace1 hvregs_1 hclf1 hLf1 hpost1')

/-! ## Relocatable Root Composition (`tryDecryptPlacedSpecT`, `try_decrypt_placed_ok_of_seamW`) -/

/-- Relocatable `try_decrypt_with_state` specification with `tokenInitPlacedAt` framed and
    `x.st.pqRatchetState.length < 2 ^ 32`. -/
def tryDecryptPlacedSpecT (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel) : Spec TryDecryptGhost :=
  { tryDecryptSpecPlaced C A ctl parse S with
    pre := fun x s =>
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        tokenInitPlacedAt ∗ (tryDecryptSpecPlaced C A ctl parse S).pre x s
    post := fun x s0 sf =>
      tokenInitPlacedAt ∗ (tryDecryptSpecPlaced C A ctl parse S).post x s0 sf }

private theorem reaches_outcome_placed_specT {prog : Program} {C : Crypto} {A : RustAlloc}
    {ctl : BitVec 64} {S : SpqrModel}
    {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome prog (tryDecryptSpecPlaced C A ctl uuidTryParse S) x (tokenInitPlacedAt ∗ R) s0 s) :
    reaches_outcome prog (tryDecryptPlacedSpecT C A ctl uuidTryParse S) x R s0 s := by
  refine h.mono_outcome (fun sf hout => ?_)
  rcases hout with ⟨hret, hcc, hpost⟩ | ⟨hpan, hq⟩ | ⟨code, hexit, hq⟩ | ⟨hoom, hq⟩
  · refine Or.inl ⟨hret, hcc, ?_⟩
    dsimp only [tryDecryptPlacedSpecT]
    have heq : (tokenInitPlacedAt ∗ (tryDecryptSpecPlaced C A ctl uuidTryParse S).post x s0 sf) ∗ R =
        (tryDecryptSpecPlaced C A ctl uuidTryParse S).post x s0 sf ∗ (tokenInitPlacedAt ∗ R) := by ac_rfl
    exact heq ▸ hpost
  · refine Or.inr (Or.inl ⟨hpan, ?_⟩)
    dsimp only [tryDecryptPlacedSpecT]
    exact onPanic_absorb_tokenInit hq
  · exact (not_satisfies_false_sepConj hq).elim
  · exact (not_satisfies_false_sepConj hq).elim

theorem reaches_outcome_of_s4_placedWT
    {prog : Program} {entry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    (hs4 : S4SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs5 : S5SeamPlacedWT prog entry C A ctl uuidTryParse S)
    (hs6 : S6SeamPlaced prog entry C A ctl)
    (hs7 : S7SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs8 : S8SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs9 : S9SeamPlaced prog entry C A ctl uuidTryParse S)
    (herr : ErrTailSeamPlaced prog entry C A ctl uuidTryParse S)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : x.st.pqRatchetState.length < 2 ^ 32)
    (hstk : rootStack ≤ s0.sp.toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : ConsumeMsgKeyStatePlaced entry A ctl x trG { tr0 with ratchet := r1 } st1 ck draws
      (tokenInitPlacedAt ∗ R) s0 s4)
    (hL4 : prog.CodeLoaded s4.mem) :
    reaches_outcome prog (tryDecryptPlacedSpecT C A ctl uuidTryParse S) x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := fromSessionState_ok_inv htr
  have hs4_step := hs4 x trG { tr0 with ratchet := r1 } st1 ck draws (tokenInitPlacedAt ∗ R) s0 s4 hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      apply reaches_outcome_placed_specT
      have hmodel := model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact Decrypt.reaches_outcome_steps hsteps4
          (herr x trG' { tr0 with ratchet := r2 } st1 e (tokenInitPlacedAt ∗ R) s0 s4' hne hm1 hm2 herr_st)
      · exact reaches_outcome_of_panic_placed hsteps4 hpan (onPanic_of_cmk_panic_placed hm1 hp hmem)
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine Decrypt.reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hs5_step := hs5 x trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
          hQ hstk hpqr0 hs5_state hL5
        dsimp only at hs5_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs5_step
          let e : SignalProtocolError :=
            if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
          have hne : e ≠ .panic := by subst e; cases sd <;> nofun
          rcases hs5_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · apply reaches_outcome_placed_specT
            have hmodel := model_of_spqr_error htr herc hcmk hspqr hnp5
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            subst hdraws
            exact Decrypt.reaches_outcome_steps hsteps5'
              (herr x trG5 { tr0 with ratchet := r2 } st1 e (tokenInitPlacedAt ∗ R) s0 s5' hne hm1 hm2 herr_st)
          · exact Decrypt.reaches_outcome_steps hsteps5'
              (reaches_outcome_refl_panic (spec := tryDecryptPlacedSpecT C A ctl uuidTryParse S) hpan hq)
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · apply reaches_outcome_placed_specT
            refine Decrypt.reaches_outcome_steps hsteps6 ?_
            have hL6 := hsteps6.codeLoaded hL5
            have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
            rcases hs6 x trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws (tokenInitPlacedAt ∗ R) s0 s6 hseed32 hs6_state hL6 with
              ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hfalse⟩⟩
            swap; · exact hfalse.elim
            refine Decrypt.reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            let mks := mkg.generateKeys C.F pqrKey
            have hs7_step := hs7 x trG5 { tr0 with ratchet := r2 }
              st1 mks newPqrState draws (tokenInitPlacedAt ∗ R) s0 s7 hs7_state hL7
            dsimp only at hs7_step
            cases hmac : x.msg.verifyMacWithAddresses C.F (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 = .error (.invalidMessage x.msgType .macFailed) := by
                rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
              · subst hdraws
                exact Decrypt.reaches_outcome_steps hsteps7'
                  (herr x trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) (tokenInitPlacedAt ∗ R) s0 s7' hne hm1 hm2 herr_st)
              · exact reaches_outcome_of_panic_placed hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                have hs8_step := hs8 x trG5 { tr0 with ratchet := r2 }
                  st1 mks newPqrState draws (tokenInitPlacedAt ∗ R) s0 s8 hs8_state hL8
                cases haes : aesCbcDecrypt C.D mks.cipherKey mks.iv x.msg.ciphertext with
                | none =>
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_none htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 =
                      .error (.invalidMessage x.msgType .badCiphertext) := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
                  have hne : SignalProtocolError.invalidMessage x.msgType .badCiphertext ≠ .panic :=
                    nofun
                  rcases hs8_step with ⟨s8', hsteps8', herr_st | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps8'
                      (herr x trG5 { tr0 with ratchet := r2 } st1
                        (.invalidMessage x.msgType .badCiphertext) (tokenInitPlacedAt ∗ R) s0 s8' hne hm1 hm2 herr_st)
                  · exact reaches_outcome_of_panic_placed hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 } with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact Decrypt.reaches_outcome_steps hsteps9
                      (hs9 x trG5 { tr0 with ratchet := r2 } st1 newPqrState pt (tokenInitPlacedAt ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact reaches_outcome_of_panic_placed hsteps9 hpan hq
              · exact reaches_outcome_of_panic_placed hsteps8 hpan hq
          · exact Decrypt.reaches_outcome_steps hsteps6
              (reaches_outcome_refl_panic (spec := tryDecryptPlacedSpecT C A ctl uuidTryParse S) hpan hq)
      · exact reaches_outcome_placed_specT (reaches_outcome_of_panic_placed hsteps5 hpan hq)

/-- Relocatable Root Composition (`try_decrypt_placed_ok_of_seamW`) on any `prog : Program`
    and `entry : BitVec 64` (instantiates to Block `130`, Block `433`, or `lsProg H`). -/
theorem try_decrypt_placed_ok_of_seamW
    {prog : Program} {entry : BitVec 64} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel}
    (hs0 : S0SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs1 : S1SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs2 : S2SeamPlaced prog entry A ctl)
    (hs3 : S3SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs4 : S4SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs5 : S5SeamPlacedWT prog entry C A ctl uuidTryParse S)
    (hs6 : S6SeamPlaced prog entry C A ctl)
    (hs7 : S7SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs8 : S8SeamPlaced prog entry C A ctl uuidTryParse S)
    (hs9 : S9SeamPlaced prog entry C A ctl uuidTryParse S)
    (herr : ErrTailSeamPlaced prog entry C A ctl uuidTryParse S) :
    subroutine_ok prog entry (tryDecryptPlacedSpecT C A ctl uuidTryParse S) := by
  apply subroutine_ok_outcome_intro
  intro x R s0 hpc hrun hpre hsp
  dsimp only [tryDecryptPlacedSpecT] at hpre
  have hpre_eq : (⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗ tokenInitPlacedAt ∗
      (tryDecryptSpecPlaced C A ctl uuidTryParse S).pre x s0) ∗ R =
      ⌜x.st.pqRatchetState.length < 2 ^ 32⌝ ∗
        ((tryDecryptSpecPlaced C A ctl uuidTryParse S).pre x s0 ∗ (tokenInitPlacedAt ∗ R)) := by ac_rfl
  rw [hpre_eq, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  refine reaches_outcome.of_codeLoaded fun hL => ?_
  obtain ⟨hseeds, hchains, hstk⟩ := seedsLen32_of_pre_placed hpre
  have hrest : x.rest.length < 2 ^ 63 := restLen_of_pre_placed hpre
  rcases hs0 x (tokenInitPlacedAt ∗ R) s0 hpc hrun hsp hpre hL with
    ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hfalse⟩⟩
  swap; · exact hfalse.elim
  refine Decrypt.reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 x (tokenInitPlacedAt ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact reaches_outcome_placed_specT hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine Decrypt.reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step := hs2 x trG2 tr0 st1 (tokenInitPlacedAt ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        rcases hs2_step hL2 with ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hfalse⟩⟩
        swap; · exact hfalse.elim
        have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
            (coinsOf x.rest)) tr0.ratchet = (.error e, tr0.ratchet) :=
          ensureReceiverChain_of_find_error hf
        have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
        have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
        have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
        have hne : e ≠ .panic := by
          have he := findReceiverChainKey_error_eq hf
          subst he
          decide
        have hdraws : decryptDraws C x.st x.msg.senderRatchetKey x.rest = 0 :=
          decryptDraws_of_find_error x.rest htr hf
        rw [← hdraws] at herr_st
        apply reaches_outcome_placed_specT
        exact Decrypt.reaches_outcome_steps hsteps2'
          (herr x trG2 tr0 st1 e (tokenInitPlacedAt ∗ R) s0 s2' hne hm1 hm2 herr_st)
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          exact reaches_outcome_of_s4_placedWT hs4 hs5 hs6 hs7 hs8 hs9 herr
            hseeds hQ hstk htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          rcases hs2_step hL2 with ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hfalse⟩⟩
          swap; · exact hfalse.elim
          refine Decrypt.reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := hs3 x trG2 tr0 st1 (tokenInitPlacedAt ∗ R) s0 s3 htr hf htr_chains hstk hrest hs3_state hL3
          dsimp only at hs3_step
          cases hdh : Mut.exec (RatchetState.dhRatchetStep C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet with
          | mk dhRes r1 =>
            rw [hdh] at hs3_step
            cases dhRes with
            | error e =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.error e, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              have hmodel := model_of_ensureReceiverChain_error (S := S) htr herc
              have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : e ≠ .panic := dhRatchetStep_error_ne_panic hdh
              rcases hs3_step with ⟨s3', hsteps3', ⟨trG3, r1', herr_st⟩ | ⟨hpan, hq⟩⟩
              · apply reaches_outcome_placed_specT
                exact Decrypt.reaches_outcome_steps hsteps3'
                  (herr x trG3 { tr0 with ratchet := r1' } st1 e (tokenInitPlacedAt ∗ R) s0 s3' hne hm1 hm2 herr_st)
              · exact reaches_outcome_placed_specT (reaches_outcome_of_panic_placed hsteps3' hpan hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine Decrypt.reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact reaches_outcome_of_s4_placedWT hs4 hs5 hs6 hs7 hs8 hs9 herr
                  hseeds hQ hstk htr herc rfl hs4_state hL4
              · exact reaches_outcome_placed_specT (reaches_outcome_of_panic_placed hsteps4 hpan hq)

/-- Block `130` (`try_decrypt_with_state::<HookRng>`) specialization of `try_decrypt_placed_ok_of_seamW`,
    with `S5` instantiated via `pqRecv_159_placed_okWT` and `S6` via `deriveKeys_159_placed_ok`. -/
theorem tryDecryptT_159_placed_ok_of_seamW
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hs0 : S0SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S)
    (hs1 : S1SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S)
    (hs2 : S2SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base A ctl)
    (hs3 : S3SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S)
    (hs4 : S4SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S)
    (hrecv_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvPlacedSpecWT A S)))
    (hfmt_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hgk_call : subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hs7 : S7SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S)
    (hs8 : S8SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S)
    (hs9 : S9SeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S)
    (herr : ErrTailSeamPlaced ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base C A ctl uuidTryParse S) :
    subroutine_ok ((blkPC_131).rebase (blkPl_131).base H) (blkPl_131).base
      (tryDecryptPlacedSpecT C A ctl uuidTryParse S) :=
  try_decrypt_placed_ok_of_seamW hs0 hs1 hs2 hs3 hs4
    (pqRecv_159_placed_okWT C A ctl S H hrecv_call hfmt_call hdealloc_call)
    (deriveKeys_159_placed_ok C A ctl H hgk_call)
    hs7 hs8 hs9 herr

/-- Block `433` (`try_decrypt_with_state::<CoinsRng>`) specialization of `try_decrypt_placed_ok_of_seamW`,
    with `S5` instantiated via `pqRecv_549_placed_okWT` and `S6` via `deriveKeys_549_placed_ok`. -/
theorem tryDecryptT_549_placed_ok_of_seamW
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64) (S : SpqrModel)
    (H : String → Option (State → State))
    (hs0 : S0SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S)
    (hs1 : S1SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S)
    (hs2 : S2SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base A ctl)
    (hs3 : S3SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S)
    (hs4 : S4SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S)
    (hrecv_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 329)
      (withLsCodeRoLoaded lsmpl (spqrRecvPlacedSpecWT A S)))
    (hfmt_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ KeyDeriveCallees.lsFormatInnerSym) (formatInnerSpec A))
    (hdealloc_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H)
      (lsρ lsRustDeallocSym) (rustDeallocSpec A))
    (hgk_call : subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (lsmpl.base 69)
      (withLsCodeRoLoaded lsmpl (generateKeysSpec C.F A)))
    (hs7 : S7SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S)
    (hs8 : S8SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S)
    (hs9 : S9SeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S)
    (herr : ErrTailSeamPlaced ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base C A ctl uuidTryParse S) :
    subroutine_ok ((blkPC_434).rebase (blkPl_434).base H) (blkPl_434).base
      (tryDecryptPlacedSpecT C A ctl uuidTryParse S) :=
  try_decrypt_placed_ok_of_seamW hs0 hs1 hs2 hs3 hs4
    (pqRecv_549_placed_okWT C A ctl S H hrecv_call hfmt_call hdealloc_call)
    (deriveKeys_549_placed_ok C A ctl H hgk_call)
    hs7 hs8 hs9 herr

end CryptoVerification.LibsignalSpqrV1.M4
