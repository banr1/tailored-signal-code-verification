/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefs
public import LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget
import ProofLib.SepLogic.WPp

/-!
# Budget-Threaded Back-Segment `SepWPp` & `onPanic` Helpers for `try_decrypt_with_state`

Re-exports allocator-independent `[LibsignalPlacement]` `SepWPp` and log-filter helpers from
`AuthDecryptDefs`, provides budget-form `onPanic` bridges (with `allocFailedIn` eliminated), and
equates `tryDecryptFnSpecPlaced.onPanic` with `tryDecryptSpecPlaced.onPanic` over
`RustCliAllocBudget M`.
-/

@[expose] public section

set_option autoImplicit false

namespace LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget

open Arm64 ProofLib
open CryptoGames.CBC (blockToBytesLE)
open CryptoGames.HMAC (keyToBytes32)
open CryptoGames.LibsignalSession (
  Crypto MessageKeyGenerator MessageType Mut RatchetState SessionState SignalMessage
  SignalProtocolError Spqr TripleRatchet aesCbcDecrypt liftE
)
open CryptoVerification (
  LibsignalPlacement lsmpl lsLogFilterSym lsρ
)
open CryptoVerification.LibsignalTripleRatchetRepr (
  UuidParser coinsOf serviceIdParse serializeAddresses
)
open CryptoVerification.LibsignalTripleRatchet (
  LibsignalCodeRoLoaded SpqrModel TryDecryptGhost logOff withLsCodeRoLoaded
)
open LibsignalBinary.Heap (
  AllocEvent AllocCostModel BudgetLimits RustCliAllocBudget
)
open LibsignalBinary.Proofs.TripleRatchet.Record.DefsBudget (TryDecryptEnvArgs)
open LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget (
  tryDecryptOnPanic tryDecryptFnOnPanic
  tryDecryptSpecPlaced tryDecryptFnSpecPlaced
)

/-! ## 1. Allocator-Independent `[LibsignalPlacement]` `SepWPp` & Log-Filter Re-Exports -/

theorem SepWPp.of_sepWP_placed [LibsignalPlacement] {prog : Program} {ret mid : BitVec 64}
    {s : State} {P : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (h : SepWP prog mid s P (fun sm Pm =>
      LibsignalCodeRoLoaded lsmpl sm.mem →
      SepWPp prog ret sm Pm Q Qp)) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.SepWPp.of_sepWP_placed hcl h

theorem SepWPp.call_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry spec)
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.SepWPp.call_frame_placed
    hcl hcall hpc hrun hsp hlr hspec hφ hP hexit hpanic hnext hoom

theorem SepWPp.call_cro_frame_placed [LibsignalPlacement] {α : Type} {prog : Program}
    {ret entry ret_pc : BitVec 64} {spec : Spec α} {x : α} {s : State} {φ : Prop}
    {P T F : SepProp} {Q Qp : State → SepProp → Prop}
    (hcl : LibsignalCodeRoLoaded lsmpl s.mem)
    (hcall : subroutine_ok prog entry (withLsCodeRoLoaded lsmpl spec))
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hspec : spec.pre x s = (⌜φ⌝ ∗ T)) (hφ : φ) (hP : P = T ∗ F)
    (hexit : ∀ sf code R', sf.status = .Exited code →
      (sf.mem ⊨ spec.onExit x code s sf ∗ R') → False)
    (hpanic : ∀ sf, sf.status = .Panicked → Qp sf (spec.onPanic x s sf ∗ F))
    (hnext : ∀ sf : State, sf.pc = ret_pc → sf.status = .Running →
      sf.sp = s.sp → sf.spAligned = true → CalleeSavedPreserved s sf →
      LibsignalCodeRoLoaded lsmpl sf.mem →
      SepWPp prog ret sf (spec.post x s sf ∗ F) Q Qp)
    (hoom : ∀ sf R', sf.status = .OutOfMemory →
      (sf.mem ⊨ spec.onOom x s sf ∗ (F ∗ R')) →
      (sf.mem ⊨ (⌜False⌝ : SepProp) ∗ R') := by wp_close_oom_default) :
    SepWPp prog ret s P Q Qp :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.SepWPp.call_cro_frame_placed
    hcl hcall hpc hrun hsp hlr hspec hφ hP hexit hpanic hnext hoom

theorem logFilterAddr_eq_placed [LibsignalPlacement] :
    CryptoVerification.LibsignalSession.logFilterAddr
      CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptPlacedImg =
      lsρ lsLogFilterSym :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.logFilterAddr_eq_placed

theorem logOff_eq_placed [LibsignalPlacement] :
    logOff CryptoVerification.LibsignalTripleRatchet.Decrypt.tryDecryptPlacedImg =
      (lsρ lsLogFilterSym ↦₆₄ 0#64) :=
  CryptoVerification.LibsignalTripleRatchet.Decrypt.AuthDecrypt.logOff_eq_placed

/-! ## 2. Budget-Form `onPanic` Bridges (`allocFailedIn` Eliminated) -/

/-- Under `FitsEnv`, non-panicking budget callees (`onPanic = ⌜False⌝`) discharge any
    `tryDecryptSpecPlaced.onPanic` obligation vacuously. -/
theorem tryDecrypt_onPanic_of_false_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : TryDecryptGhost) (st_init : M.σ) (s0 sf : State) (F R : SepProp)
    (hm : sf.mem ⊨ (⌜False⌝ ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R := by
  rw [sepConj_assoc] at hm
  exact (not_satisfies_false_sepConj hm).elim

/-- Under `FitsEnv`, non-panicking budget callees (`onPanic = ⌜False⌝`) discharge any
    `tryDecryptFnSpecPlaced.onPanic` obligation vacuously. -/
theorem tryDecryptFn_onPanic_of_false_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : TryDecryptGhost) (st_init : M.σ) (s0 sf : State) (F R : SepProp)
    (hm : sf.mem ⊨ (⌜False⌝ ∗ F) ∗ R) :
    sf.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R := by
  rw [sepConj_assoc] at hm
  exact (not_satisfies_false_sepConj hm).elim

/-- Bridges a legitimate callee model / SPQR panic at intermediate state `sm` (`s0.trace <+: sm.trace`)
    into `(tryDecryptSpecPlaced ...).onPanic (x, st_init) s0 sf ∗ R`. -/
theorem tryDecrypt_onPanic_of_callee_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto) (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : TryDecryptGhost) (st_init : M.σ) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨
      ((⌜((x.model C S parse).1 = .error .panic ∨
            S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∧
          sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨ (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R := by
  dsimp only [tryDecryptSpecPlaced, withLsCodeRoLoaded,
    LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget.tryDecryptRawSpecPlaced,
    tryDecryptOnPanic]
  exact allowPanic_frame (fun ⟨hpan, hmf⟩ => ⟨hpan, h0m.trans hmf⟩) hm

/-- Bridges a legitimate callee model / SPQR panic at intermediate state `sm` (`s0.trace <+: sm.trace`)
    into `(tryDecryptFnSpecPlaced ...).onPanic (x, st_init) s0 sf ∗ R`. -/
theorem tryDecryptFn_onPanic_of_callee_placed [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop)
    (x : TryDecryptGhost) (st_init : M.σ) (s0 sm sf : State) (F R : SepProp)
    (h0m : s0.trace <+: sm.trace)
    (hm : sf.mem ⊨
      ((⌜((x.modelFn C decFn S parse).1 = .error .panic ∨
            S.recvPanics x.st.pqRatchetState x.msg.pqRatchet) ∧
          sm.trace <+: sf.trace⌝ ∗ anyHeap) ∗ F) ∗ R) :
    sf.mem ⊨
      (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).onPanic (x, st_init) s0 sf ∗ R := by
  dsimp only [tryDecryptFnSpecPlaced, withLsCodeRoLoaded,
    LibsignalBinary.Proofs.TripleRatchet.Decrypt.DefsBudget.tryDecryptFnRawSpecPlaced,
    tryDecryptFnOnPanic]
  exact allowPanic_frame (fun ⟨hpan, hmf⟩ => ⟨hpan, h0m.trans hmf⟩) hm

/-! ## 3. Equality of `tryDecryptFnSpecPlaced.onPanic` and `tryDecryptSpecPlaced.onPanic` -/

private theorem exec_bind_panic_eq_auth {σ α β : Type} (m : Mut σ α)
    (f₁ f₂ : α → Mut σ β) (s : σ)
    (h : ∀ a s', ((Mut.exec (f₁ a) s').1 = .error .panic) =
      ((Mut.exec (f₂ a) s').1 = .error .panic)) :
    ((Mut.exec (m >>= f₁) s).1 = .error .panic) =
      ((Mut.exec (m >>= f₂) s).1 = .error .panic) := by
  dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run,
    ExceptT.mk, ExceptT.bindCont]
  cases m s with
  | mk res s' =>
    cases res with
    | error e => rfl
    | ok a => exact h a s'

private theorem decryptFn_error_panic_eq_auth {PQ PQC : Type} (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : TripleRatchet PQ) :
    ((Mut.exec (TripleRatchet.decryptFn C decFn spqr expected ciphertext msgType coins) s).1 =
        .error .panic) =
      ((Mut.exec (TripleRatchet.decrypt C spqr expected ciphertext msgType coins) s).1 =
        .error .panic) := by
  unfold TripleRatchet.decryptFn TripleRatchet.decrypt
  refine exec_bind_panic_eq_auth _ _ _ s fun chainKey s1 => ?_
  refine exec_bind_panic_eq_auth _ _ _ s1 fun messageKeyGen s2 => ?_
  refine exec_bind_panic_eq_auth _ _ _ s2 fun t s3 => ?_
  dsimp only
  cases spqr.recvPanics t.pqrState ciphertext.pqRatchet with
  | true => rfl
  | false =>
    cases spqr.recv t.pqrState ciphertext.pqRatchet with
    | error sd => cases sd <;> rfl
    | ok r =>
      rcases r with ⟨newPqrState, pqrKey⟩
      simp only [Bool.false_eq_true, ↓reduceIte]
      dsimp only [Bind.bind, ExceptT.bind, StateT.bind, Mut.exec, ExceptT.run, StateT.run,
        pure, ExceptT.pure, StateT.pure, ExceptT.mk, ExceptT.bindCont]
      cases SignalMessage.verifyMacWithAddresses C.F ciphertext expected
          t.remoteIdentityKey t.localIdentityKey
          (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).macKey with
      | false => rfl
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases decFn ciphertext.ciphertext
            (keyToBytes32 (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey)
            (blockToBytesLE (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv) <;>
          cases aesCbcDecrypt C.D
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).cipherKey
            (MessageKeyGenerator.generateKeys C.F messageKeyGen pqrKey).iv
            ciphertext.ciphertext <;>
          exact propext ⟨nofun, nofun⟩

private theorem exec_liftE_tail_panic_eq_auth {PQ : Type} [Inhabited PQ]
    (r : Except SignalProtocolError (List (BitVec 8))) (session : TripleRatchet PQ)
    (s : SessionState PQ) :
    ((Mut.exec (do
      let ptext ← liftE r
      modify fun st => (session.applyToSessionState st).clearUnacknowledgedPreKeyMessage
      return ptext) s).1 = .error .panic) = (r = .error .panic) := by
  cases r with
  | error e => rfl
  | ok ptext => rfl

private theorem tryDecryptWithStateFn_error_panic_eq_auth {PQ PQC : Type} [Inhabited PQ]
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (spqr : Spqr PQ PQC)
    (expected : Option (List (BitVec 8))) (ciphertext : SignalMessage) (msgType : MessageType)
    (coins : BitVec 256) (s : SessionState PQ) :
    ((Mut.exec (SessionState.tryDecryptWithStateFn C decFn spqr expected ciphertext msgType coins)
        s).1 = .error .panic) =
      ((Mut.exec (SessionState.tryDecryptWithState C spqr expected ciphertext msgType coins)
        s).1 = .error .panic) := by
  unfold SessionState.tryDecryptWithStateFn SessionState.tryDecryptWithState
  refine exec_bind_panic_eq_auth _ _ _ s fun session s1 => ?_
  dsimp only
  rw [exec_liftE_tail_panic_eq_auth, exec_liftE_tail_panic_eq_auth]
  exact decryptFn_error_panic_eq_auth C decFn spqr expected ciphertext msgType coins session

theorem tryDecryptFnOnPanic_eq_auth (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (parse : UuidParser) (S : SpqrModel) :
    tryDecryptFnOnPanic C decFn parse S = tryDecryptOnPanic C parse S := by
  funext x s0 sf
  simp only [tryDecryptFnOnPanic, tryDecryptOnPanic, TryDecryptGhost.modelFn,
    TryDecryptGhost.model]
  rw [tryDecryptWithStateFn_error_panic_eq_auth]

theorem tryDecryptFnSpecPlaced_onPanic_eq_auth [LibsignalPlacement] {M : AllocCostModel}
    (C : Crypto)
    (decFn : List (BitVec 8) → List (BitVec 8) → List (BitVec 8) → Option (List (BitVec 8)))
    (A : RustCliAllocBudget M) (lim : BudgetLimits) (ctl : BitVec 64)
    (parse : UuidParser) (S : SpqrModel)
    (tdEnv : TryDecryptEnvArgs → List AllocEvent → Prop) :
    (tryDecryptFnSpecPlaced C decFn A lim ctl parse S tdEnv).onPanic =
      (tryDecryptSpecPlaced C A lim ctl parse S tdEnv).onPanic := by
  funext ⟨x, _⟩ s0 sf
  change tryDecryptFnOnPanic C decFn parse S x s0 sf = tryDecryptOnPanic C parse S x s0 sf
  rw [tryDecryptFnOnPanic_eq_auth]

end LibsignalBinary.Proofs.TripleRatchet.Decrypt.AuthDecryptDefsBudget
