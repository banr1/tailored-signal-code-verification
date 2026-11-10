/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.PlacedDefs
public import LibsignalBinary.Proofs.Cli.PublicApi.MessageEncrypt.TailsPlaced
public import LibsignalBinary.Proofs.PublicApi.MessageEncrypt.Seg.SegFrom
public import LibsignalBinary.Proofs.Common.SharedHelpers
public import ProofLib.RegChain
import all Arm64.Trusted.Spec.Hoare
import Arm64.Trusted.Spec.SepLogic
import LibsignalBinary.Proofs.TripleRatchet.Encrypt.Core.Defs

/-!
# Relocatable CLI `SegFrom` Proof (`segFrom_placed_okV`)

Verifies `SegFromSpecVPlaced` (`CurStateVPlaced` at `+0x20c` → `OtrStateVPlaced` at `+0x2c8` or
error tail at `+0x49c`) on `lsProg_464 Hk` (`blkPl_464`) under `[LibsignalPlacement]`.
-/

@[expose] public section

set_option autoImplicit false

namespace CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom

open CryptoVerification.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
open CryptoVerification.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt
open CryptoVerification.CliRatchet.EncPlaced CryptoVerification.CliRatchet.Placed CryptoVerification.Cli.CoinsTape
open Arm64 ProofLib ProofLib.ProgramReflection
open CryptoGames CryptoGames.HKDF CryptoGames.HMAC CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Encrypt
open CryptoVerification.LibsignalPublicApiRepr CryptoVerification.LibsignalProtoCodec
open CryptoVerification.LibsignalPublicApi
open CryptoVerification.LibsignalPublicApi.StoreKit
open CryptoVerification.LibsignalPublicApi.MessageEncrypt CryptoVerification.LibsignalPublicApi.MessageEncrypt.Tails CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Tails

set_option maxRecDepth 200000
set_option maxHeartbeats 400000

attribute [local irreducible] Program.fetch Program.externAt?
attribute [local arm64_norm] bv_sub_add_lit BitVec.toNat_zero

private theorem model_of_fromSessionState_error_placed
    {C : Crypto} {S : SpqrModel} {x : WithStoresEncGhost}
    {r : SessionRecord (List (BitVec 8))} {sess : Session (List (BitVec 8))}
    {e : SignalProtocolError}
    (hcur : r.currentSession = some sess)
    (herr : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error e) :
    x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (.protocol e), [.loadSession x.rem.val]) ∧
    x.draws S (okAnswers r .newOrUnchanged) = 0 := by
  have hex : execOk OutgoingTripleRatchet.fromSessionState sess.state = .error e :=
    execOk_fromSessionState_of_error_shared_lb herr
  have hprot : (ApiError.ofProtocol e : ApiError AddrVal Unit) = .protocol e := by
    cases e <;> first | rfl | exact absurd rfl (fromSessionState_error_ne_invalidState_shared_lb herr).2
  have hmod : x.model C S uuidTryParse (okAnswers r .newOrUnchanged) =
      (.error (ApiError.ofProtocol e), [.loadSession x.rem.val]) := by
    unfold EncryptGhost.model messageEncrypt Api.run storeCall liftProtocol okAnswers
    simp [hcur, hex, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet,
      ExceptT.run, StateT.run, bind, ExceptT.mk, ExceptT.bind, ExceptT.bindCont, ExceptT.lift,
      StateT.bind, StateT.map, Functor.map, monadLift, MonadLift.monadLift,
      MonadLiftT.monadLift, pure, ExceptT.pure, StateT.pure, throw, throwThe,
      MonadExceptOf.throw]
  refine ⟨by rw [hmod, hprot], ?_⟩
  unfold EncryptGhost.draws EncryptGhost.sendState loadedSession okAnswers
  simp only [hcur, hex]

/-! ## 1. `SegExitPlaced` Combinators -/

theorem SegExitPlaced.next [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop} (h : next s) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s next :=
  fun _ => ⟨s, Steps.refl s, Or.inl h⟩

theorem SegExitPlaced.of_false [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R : SepProp}
    {s0 s : State} {next : State → Prop}
    (h : SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s (fun _ => False)) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R s0 s next := by
  intro hL
  obtain ⟨sf, hsteps, hfalse | hout⟩ := h hL
  · exact False.elim hfalse
  · exact ⟨sf, hsteps, Or.inr hout⟩

theorem SegExitPlaced.of_sepWP [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {mid : BitVec 64} {P F : SepProp}
    {post : State → SepProp → Prop}
    (hm : s.mem ⊨ P ∗ (F ∗ R))
    (hwp : SepWP (lsProg_464 Hk) mid s P post)
    (hcont : ∀ sm Pm, (lsProg_464 Hk).CodeLoaded s.mem →
      Steps (lsProg_464 Hk) s sm →
      sm.pc = mid → sm.status = .Running → (sm.mem ⊨ Pm ∗ (F ∗ R)) →
      post sm Pm → SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, ⟨hpc, hrun, Pm, hmm, hpost⟩ | ⟨_, _hoom⟩⟩ := hwp.elim hm hL
  rotate_left
  · exact (not_satisfies_false_sepConj _hoom).elim
  obtain ⟨sf, hsteps', hout⟩ := hcont sm Pm hL hsteps hpc hrun hmm hpost (hsteps.codeLoaded hL)
  exact ⟨sf, hsteps.trans hsteps', hout⟩

theorem SegExitPlaced.call {α : Type} [LibsignalPlacement] {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState} {ctl : BitVec 64}
    {S : SpqrModel}
    {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} {x : WithStoresEncGhost} {R R0 : SepProp}
    {s0 s : State} {next : State → Prop} {entry ret_pc : BitVec 64} {spec : Spec α}
    (hcall : subroutine_ok (lsProg_464 Hk) entry spec)
    (xc : α) {F : SepProp}
    (hpc : s.pc = entry) (hrun : s.status = .Running) (hsp : s.spAligned = true)
    (hlr : s.readReg64 Reg.lr = ret_pc)
    (hm : s.mem ⊨ spec.pre xc s ∗ (F ∗ R))
    (hexit : ∀ sf code R', sf.status = .Exited code → (sf.mem ⊨ spec.onExit xc code s sf ∗ R') → False)
    (hpanic : ∀ sf, Steps (lsProg_464 Hk) s sf → sf.status = .Panicked →
      (sf.mem ⊨ (spec.onPanic xc s sf ∗ F) ∗ R) →
      (sf.mem ⊨ (withStoresEncPlacedSpecV kit st0 ikit ist0 C ctl uuidTryParse S encRecord).onPanic x s0 sf ∗ R0))
    (hnext : ∀ sm : State, (lsProg_464 Hk).CodeLoaded s.mem →
      Steps (lsProg_464 Hk) s sm →
      sm.pc = ret_pc → sm.status = .Running →
      sm.sp = s.sp → CalleeSavedPreserved s sm →
      (sm.mem ⊨ (spec.post xc s sm ∗ F) ∗ R) →
      SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 sm next)
    (hoom : ∀ sf R', sf.status = .OutOfMemory → (sf.mem ⊨ spec.onOom xc s sf ∗ R') → False := by
      intro _ _ _ h; exact not_satisfies_false_sepConj h) :
    SegExitPlaced kit st0 ikit ist0 C ctl uuidTryParse S encRecord Hk x R0 s0 s next := by
  intro hL
  obtain ⟨sm, hsteps, hout⟩ :=
    subroutine_ok_apply_outcome hcall xc (F ∗ R) hpc hrun hm hsp hL
  rcases hout with ⟨⟨hpcm, _, hrunm⟩, ⟨hspm, hcsm⟩, hpost⟩ | ⟨hpan, hpost⟩ | ⟨code, hex, hpost⟩ | ⟨_hoom_st, _hoom_post⟩
  · rw [← sepConj_assoc] at hpost
    rw [hlr] at hpcm
    obtain ⟨sf, hsteps', hout'⟩ :=
      hnext sm hL hsteps hpcm hrunm hspm hcsm hpost (hsteps.codeLoaded hL)
    exact ⟨sf, hsteps.trans hsteps', hout'⟩
  · rw [← sepConj_assoc] at hpost
    exact ⟨sm, hsteps, Or.inr (Or.inr (Or.inl ⟨hpan, hpanic sm hsteps hpan hpost⟩))⟩
  · exact (hexit sm code _ hex hpost).elim
  · exact (hoom sm _ _hoom_st _hoom_post).elim

/-! ## 2. Relocatable Steppers (`lsProg_464 Hk`) -/

theorem segFrom_placed_step_pre [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp u280 : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x20c#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx21 : s.readReg64 .x21 = sp + 0x128#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64) :
    SepWP (lsProg_464 Hk) (lsmpl.base 19) s ((sp + 0x280#64) ↦₆₄ u280)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x21 = sp + 0x580#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        sm.readReg64 Reg.lr = encEntryPlaced + 0x228#64 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))) := by
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true]
  wp_steps
  wp_done

theorem segFrom_placed_step_err [LibsignalPlacement] {Hk : LibsignalHooks}
    {sp : BitVec 64} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x49c#64) s ((sp + 0x580#64) ↦₆₄ errTag)
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x21 = s.readReg64 .x21 ∧
        sm.readReg64 .x25 = s.readReg64 .x25 ∧
        sm.readReg64 .x26 = s.readReg64 .x26 ∧
        sm.readReg64 .x28 = s.readReg64 .x28 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ (sp + 0x580#64) ↦₆₄ errTag)) := by
  unfold encEntryPlaced at hs_pc ⊢
  unfold errTag
  dsimp only [lsProg_464, ite_true]
  wp_steps
  wp_done

set_option maxHeartbeats 1600000 in
theorem segFrom_placed_step_ok [LibsignalPlacement] {Hk : LibsignalHooks} {sp : BitVec 64}
    {pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64}
    {d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
      BitVec 64}
    {u850 u858 u860 u950 u958 u960 : BitVec 64} {u469 : BitVec 8} {s : State}
    (hs_pc : s.pc = encEntryPlaced + 0x228#64)
    (hrun : s.status = .Running)
    (hsp : s.sp = sp)
    (hal : s.spAligned = true)
    (hx20 : s.readReg64 .x20 = sp + 0x58#64)
    (hx24 : s.readReg64 .x24 = sp + 0x58#64)
    (hx25 : s.readReg64 .x25 = sp + 0x580#64)
    (hx26 : s.readReg64 .x26 = sp + 0x9d0#64)
    (hx27 : s.readReg64 .x27 = sp + 0xc0#64)
    (hx28 : s.readReg64 .x28 = sp + 0x4a0#64)
    (hpq : pqCap + 1#64 ≠ 0#64) :
    SepWP (lsProg_464 Hk) (encEntryPlaced + 0x2c8#64) s
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        ((sp + 0x469#64) ↦₈ u469) ∗
        otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860) ∗
        ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960))
      (fun sm Pm =>
        sm.sp = sp ∧ sm.trace = s.trace ∧
        sm.readReg64 .x0 = sp + 0x128#64 ∧
        sm.readReg64 .x8 = sp + 0x580#64 ∧
        sm.readReg64 .x19 = s.readReg64 .x19 ∧
        sm.readReg64 .x20 = sp + 0x58#64 ∧
        sm.readReg64 .x22 = sp + 0x8b8#64 ∧
        sm.readReg64 .x23 = sp + 0x58#64 ∧
        sm.readReg64 .x24 = sp + 0x58#64 ∧
        sm.readReg64 .x25 = sp + 0x580#64 ∧
        sm.readReg64 .x26 = sp + 0x9d0#64 ∧
        sm.readReg64 .x27 = sp + 0xc0#64 ∧
        sm.readReg64 .x28 = sp + 0x4a0#64 ∧
        sm.readReg64 .x29 = s.readReg64 .x29 ∧
        calleeSavedVRegs sm = calleeSavedVRegs s ∧
        (Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          otrWords25 (sp + 0x288#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x469#64) ↦₈ 1#8) ∗
          otrWords25 (sp + 0x580#64) pqCap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ∗
          ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))) := by
  have hpq_beq : (pqCap + 1#64 == 0#64) = false := beq_eq_false_iff_ne.mpr hpq
  unfold encEntryPlaced at hs_pc ⊢
  dsimp only [lsProg_464, ite_true, otrWords25]
  simp only [BitVec.add_assoc, BitVec.reduceAdd, sepConj_assoc]
  wp_steps
  wp_done

/-! ## 3. Frame Split/Merge Helpers -/

def fromRestFramePlaced [LibsignalPlacement] (ss_vt id_vt : BitVec 64) (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (sp : BitVec 64) (s0 : State) : SepProp :=
  vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
  memRegion (sp + 0x288#64) 0x1e0 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
  memRegion x.ret 248 ∗
  (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
  nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗
  memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - smallRootStack) ∗
  encSavedRegs s0.sp s0

theorem curState_placed_mem_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (r : SessionRecord (List (BitVec 8))) (g : RecordGhost)
    (sess : Session (List (BitVec 8))) (sp : BitVec 64) (R : SepProp) (s0 : State) {m : Memory}
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hcur : r.currentSession = some sess)
    (hm : m ⊨ (sessionRecordAt A (sp + 0x110#64) g r ∗
      memRegion (sp + 0x280#64) 0x1e8 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ G u280,
      g.cur = some G ∧ sessionPure G sess ∧
      (m ⊨ ((sp + 0x280#64) ↦₆₄ u280) ∗
        ((sessionStateAt A (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x580#64) 200 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt sp smallRootStack ∗
          A.pool ∗
          fromRestFramePlaced ss_vt id_vt A ctl x g sp s0) ∗ R)) := by
  simp only [sepConj_assoc] at hm
  obtain ⟨G, hgcur, hpure, hm⟩ := sessionRecordAt_cur_some A sp g r sess hcur hm
  have h280 : memRegion (sp + 0x280#64) 0x1e8 =
      memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x288#64) 0x1e0 := by
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using mr_cut_add sp 0x280 8 0x1e0 (by decide)
  have h46a : memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 200 ∗
      memRegion (sp + 0x648#64) 0x538 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 200 0x538 (by decide)]
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  rw [h280, ProofLib.memRegion_eight (sp + 0x280#64), h46a] at hm
  unfold encCommonPlaced at hm
  rw [hsp0, hlog, stackAt_sub sp encSubStack smallRootStack] at hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm
  obtain ⟨u280, hm⟩ := hm
  refine ⟨G, u280, hgcur, hpure, ?_⟩
  unfold fromRestFramePlaced
  exact Eq.mp (congrArg (m ⊨ ·) (by sep_ac_rfl)) hm

theorem otrFrom_placed_pre_frame [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (sp : BitVec 64) (R Pm : SepProp) (s0 s1 : State)
    (hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem)
    (hsp1 : s1.sp = sp)
    (hx0 : s1.readReg64 .x0 = sp + 0x128#64)
    (hx8 : s1.readReg64 .x8 = sp + 0x580#64)
    (hPm : Pm ⊢ (sp + 0x280#64) ↦₆₄ (sp + 0x128#64))
    (hm : s1.mem ⊨ Pm ∗
      ((sessionStateAt A (sp + 0x128#64) G sess.state ∗
        memRegion (sp + 0x580#64) 200 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt sp smallRootStack ∗
        A.pool ∗
        fromRestFramePlaced ss_vt id_vt A ctl x g sp s0) ∗ R)) :
    s1.mem ⊨ (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A)).pre
        ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ s1 ∗
      ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ fromRestFramePlaced ss_vt id_vt A ctl x g sp s0) ∗ R) := by
  have hm' := Satisfies.mono (sepConj_mono_left hPm) hm
  dsimp only [StoreKit.withLsRoCl, OutgoingRatchet.otrFromRawPlacedSpec]
  rw [hsp1]
  have hpure : (⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝ : SepProp) ∗
      ⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sessionStateAt A (sp + 0x128#64) G sess.state ∗
          memRegion (sp + 0x580#64) 200 ∗
          (lsLogFilterAddr ↦₆₄ 0#64) ∗
          stackAt sp smallRootStack ∗
          A.pool ∗
          fromRestFramePlaced ss_vt id_vt A ctl x g sp s0) ∗ R)) =
      (((⌜s1.readReg64 .x0 = sp + 0x128#64 ∧ s1.readReg64 .x8 = sp + 0x580#64⌝ ∗
        sessionStateAt A (sp + 0x128#64) G sess.state ∗
        memRegion (sp + 0x580#64) 200 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗
        stackAt sp smallRootStack ∗
        A.pool) ∗ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem⌝) ∗
        ((((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ fromRestFramePlaced ss_vt id_vt A ctl x g sp s0) ∗ R)) := by
    sep_ac_rfl
  rw [← hpure, satisfies_pure_sepConj, satisfies_pure_sepConj]
  exact ⟨hcrl1, ⟨hx0, hx8⟩, hm'⟩

theorem otrFrom_placed_post_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g : RecordGhost) (G : SessionGhost)
    (sess : Session (List (BitVec 8))) (xc : OtrFromGhost) (sp : BitVec 64)
    (R : SepProp) (s0 s1 s2 : State)
    (hxc : xc = ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩)
    (hsp0 : s0.sp - 0xbe0#64 = sp)
    (hsp1 : s1.sp = sp)
    (hpure : sessionPure G sess)
    (hpost : s2.mem ⊨ ((StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A)).post xc s1 s2 ∗
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        fromRestFramePlaced ss_vt id_vt A ctl x g sp s0)) ∗ R) :
    StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem ∧
    ∃ G' : SessionGhost,
      xc.model.1 ≠ .error .panic ∧ s2.trace = s1.trace ∧
      (s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq xc.model.1 ∗
        sessionRecordAt A (sp + 0x110#64) { g with cur := some G' } (takenRecord sess xc.model.2) ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
        curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
        memRegion x.ret 248 ∗
        encCommonPlaced A ctl x 0 s0 ∗ R) := by
  subst hxc
  let xc : OtrFromGhost := ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
  dsimp only [StoreKit.withLsRoCl, OutgoingRatchet.otrFromRawPlacedSpec] at hpost
  rw [hsp1] at hpost
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hpost
  obtain ⟨G', hpost⟩ := hpost
  have h1 : s2.mem ⊨ ⌜StoreKit.LibsignalCodeRoLoaded lsmpl s2.mem⌝ ∗
      ⌜xc.model.1 ≠ .error .panic ∧ s2.trace = s1.trace⌝ ∗
      ⌜G.AgreeExceptPq G'⌝ ∗
      ((sessionStateAt A (sp + 0x128#64) G' xc.model.2 ∗
        otrResultAt A (sp + 0x580#64) G.pq xc.model.1 ∗
        (lsLogFilterAddr ↦₆₄ 0#64) ∗ stackAt sp smallRootStack ∗ A.pool ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        fromRestFramePlaced ss_vt id_vt A ctl x g sp s0) ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hpost
  rw [satisfies_pure_sepConj, satisfies_pure_sepConj, satisfies_pure_sepConj] at h1
  rcases h1 with ⟨hcrl2, ⟨hne, htr⟩, hagr, hmem⟩
  refine ⟨hcrl2, G', hne, htr, ?_⟩
  unfold fromRestFramePlaced at hmem
  have hrec := sessionRecordAt_taken_fold A sp g sess G G' xc.model.2 hpure hagr
  have hlog : FromRecordCallees.lsLogOff = (lsLogFilterAddr ↦₆₄ 0#64) := rfl
  have hmem_rearr : s2.mem ⊨
      (vecAt A 24 8 (fun (_ : Unit) _ => emp) (sp + 0x110#64) g.prevCap g.prevPtr [] ∗
        sessionStateAt A (sp + 0x128#64) G' xc.model.2) ∗
      (memRegion (sp - BitVec.ofNat 64 encSubStack) (encSubStack - smallRootStack) ∗
        stackAt sp smallRootStack) ∗
      otrResultAt A (sp + 0x580#64) G.pq xc.model.1 ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 0x1e0 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
      memRegion x.ret 248 ∗
      (x.ptA ↦ₛ x.ptext) ∗ protocolAddressAt A x.rem x.remA ∗ protocolAddressAt A x.loc x.locA ∗
      nowAt s0.sp x.now ∗ cliTapeAfter ctl x.cur x.rest 0 ∗ (lsLogFilterAddr ↦₆₄ 0#64) ∗
      encSavedRegs s0.sp s0 ∗ A.pool ∗ R :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem
  rw [← stackAt_sub sp encSubStack smallRootStack] at hmem_rearr
  have hmem_fold := Satisfies.mono (sepConj_mono_left hrec) hmem_rearr
  unfold encCommonPlaced
  rw [hsp0, hlog]
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hmem_fold

theorem otrFrom_placed_err_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost) (pq : VecPin)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (p : SignalProtocolError) (sp : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 = .error p)
    (hm : s2.mem ⊨ otrResultAt A (sp + 0x580#64) pq (.error p) ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 0x1e0 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x648#64) 0x538 ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ w0 w1 w2 w3 w4 w5 H,
      SpeStaged A x.ret (.protocol p) [w0, w1, w2, w3, w4, w5] H ∧
      (s2.mem ⊨ ((sp + 0x580#64) ↦₆₄ errTag) ∗
        ((words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
          memRegion (sp + 0x5b8#64) 144 ∗ H ∗
          sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          memRegion (sp + 0x288#64) 0x1e0 ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
          memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
          memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0) ∗ R)) := by
  have hp_inv : p ≠ .invalidState := (fromSessionState_error_ne_invalidState_shared_lb hres).1
  have hp_pan : (ApiError.protocol p : ApiError AddrVal Unit) ≠ .panic := by
    intro h
    cases h
  unfold otrResultAt errResultAt at hm
  dsimp only at hm
  have h588 : (sp + 0x580#64) + 8#64 = sp + 0x588#64 := by bv_omega
  have h5b8 : (sp + 0x580#64) + 56#64 = sp + 0x5b8#64 := by bv_omega
  rw [h588, h5b8, speAt_fnName_eq A [] (utf8 "encrypt") (sp + 0x588#64) p hp_inv] at hm
  change s2.mem ⊨ (((sp + 0x580#64) ↦₆₄ errTag) ∗
      encErrAt A (sp + 0x588#64) (.protocol p) ∗
      memRegion (sp + 0x5b8#64) 144) ∗
    sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
    ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
    memRegion (sp + 0x288#64) 0x1e0 ∗
    ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
    curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
    memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
    memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R at hm
  have hstage := speStaged_of_encErrAt A (sp + 0x588#64) x.ret (.protocol p) hp_pan
  have hm_st := Satisfies.mono (sepConj_mono_left (sepConj_mono_right (sepConj_mono_left hstage))) hm
  simp only [sepExists_sepConj_left, sepExists_sepConj_right, satisfies_sepExists] at hm_st
  obtain ⟨ws, H, hm_st⟩ := hm_st
  have hm_pure : s2.mem ⊨ ⌜SpeStaged A x.ret (.protocol p) ws H⌝ ∗
      (((sp + 0x580#64) ↦₆₄ errTag) ∗
        ((words64At (sp + 0x588#64) ws ∗
          memRegion (sp + 0x5b8#64) 144 ∗ H ∗
          sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
          ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          memRegion (sp + 0x288#64) 0x1e0 ∗
          ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
          curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
          memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x648#64) 0x538 ∗
          memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0) ∗ R)) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_st
  rw [satisfies_pure_sepConj] at hm_pure
  rcases hm_pure with ⟨hst, hm_out⟩
  obtain ⟨w0, w1, w2, w3, w4, w5, rfl⟩ := list_len6_shared_lb ws hst.2.1
  exact ⟨w0, w1, w2, w3, w4, w5, H, hst, hm_out⟩

theorem otrFrom_placed_err_tail_mem [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (w0 w1 w2 w3 w4 w5 : BitVec 64) (sp : BitVec 64) (H R Pm : SepProp) (s0 s3 : State)
    (hPm : Pm ⊢ (sp + 0x580#64) ↦₆₄ errTag)
    (hm : s3.mem ⊨ Pm ∗
      ((words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        memRegion (sp + 0x5b8#64) 144 ∗ H ∗
        sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
        curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
        memRegion (sp + 0x46a#64) 0x116 ∗
        memRegion (sp + 0x648#64) 0x538 ∗
        memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0) ∗ R)) :
    s3.mem ⊨ (curScratch sp ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      memRegion (sp + 0x280#64) 0x1ea ∗
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] ∗ H) ∗
      encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left (Entails.trans hPm (pointsTo64_entails_memRegion _ _))) hm
  have h280_1ea :
      memRegion (sp + 0x280#64) 0x1ea =
      memRegion (sp + 0x280#64) 8 ∗ memRegion (sp + 0x288#64) 0x1e0 ∗
        memRegion (sp + 0x468#64) 1 ∗ memRegion (sp + 0x469#64) 1 := by
    rw [show sp + 0x280#64 = sp + BitVec.ofNat 64 0x280 from rfl,
        mr_cut_add sp 0x280 8 0x1e2 (by decide),
        mr_cut_add sp (0x280 + 8) 0x1e0 2 (by decide),
        mr_cut_add sp (0x280 + 8 + 0x1e0) 1 1 (by decide)]
  have h280_ent :
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ⊢
      memRegion (sp + 0x280#64) 0x1ea := by
    rw [h280_1ea]
    exact sepConj_mono (pointsTo64_entails_memRegion _ _)
      (sepConj_mono (Entails.refl _)
        (sepConj_mono (pointsTo8_entails_memRegion _ _) (pointsTo8_entails_memRegion _ _)))
  have hpoll_eq :
      pollWith sp 0x588 [w0, w1, w2, w3, w4, w5] =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
        words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        memRegion (sp + 0x5b8#64) 144 ∗ memRegion (sp + 0x648#64) 0x538 := by
    have h1 : memRegion (sp + 0x46a#64) (0x588 - 0x46a) =
        memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 :=
      mr_cut_add sp 0x46a 0x116 8 (by decide)
    have h2 : memRegion (sp + BitVec.ofNat 64 (0x588 + 8 * 6)) (0xb80 - (0x588 + 8 * 6)) =
        memRegion (sp + 0x5b8#64) 144 ∗ memRegion (sp + 0x648#64) 0x538 :=
      mr_cut_add sp (0x588 + 8 * 6) 144 0x538 (by decide)
    unfold pollWith
    dsimp only [List.length_cons, List.length_nil]
    rw [h1, h2]
    sep_ac_rfl
  have hm_rearr : s3.mem ⊨
      (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗ memRegion (sp + 0x288#64) 0x1e0 ∗
        ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8)) ∗
      curScratch sp ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 8 ∗
        words64At (sp + 0x588#64) [w0, w1, w2, w3, w4, w5] ∗
        memRegion (sp + 0x5b8#64) 144 ∗ memRegion (sp + 0x648#64) 0x538) ∗
      H ∗ encSpillsAtV ss_vt id_vt sp x ∗ memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm1
  rw [← hpoll_eq] at hm_rearr
  have hm_out := Satisfies.mono (sepConj_mono_left h280_ent) hm_rearr
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm_out

def okStepFramePlaced [LibsignalPlacement] (ss_vt id_vt : BitVec 64)
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost) (sess : Session (List (BitVec 8)))
    (st' : SessionState (List (BitVec 8))) (sp : BitVec 64) (H : SepProp) (s0 : State) : SepProp :=
  H ∗
  sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
  memRegion (sp + 0x350#64) 0x118 ∗
  ((sp + 0x468#64) ↦₈ 0#8) ∗
  curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
  memRegion (sp + 0x46a#64) 0x116 ∗
  memRegion (sp + 0x648#64) 0x208 ∗
  memRegion (sp + 0x868#64) 0xe8 ∗
  memRegion (sp + 0x968#64) 0x218 ∗
  memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0

theorem otrFrom_placed_ok_unpack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost) (pq : VecPin)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8))) (sp : BitVec 64) (R : SepProp) (s0 s2 : State)
    (hm : s2.mem ⊨ otrResultAt A (sp + 0x580#64) pq (.ok otr) ∗
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      memRegion (sp + 0x288#64) 0x1e0 ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 0#8) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x648#64) 0x538 ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R) :
    ∃ (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
        BitVec 64)
      (d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17 d18 d19 d20 d21 d22 d23 d24 :
        BitVec 64)
      (u850 u858 u860 u950 u958 u960 : BitVec 64) (H : SepProp),
      pq.cap + 1#64 ≠ 0#64 ∧
      (∀ dst : BitVec 64,
        otrWords25 dst pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
          w19 w20 w21 w22 w23 w24 ∗ H ⊢ otrAt A dst pq.cap pq.ptr otr) ∧
      (s2.mem ⊨ (((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
          otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
            d18 d19 d20 d21 d22 d23 d24 ∗
          ((sp + 0x469#64) ↦₈ 0#8) ∗
          otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
            w17 w18 w19 w20 w21 w22 w23 w24 ∗
          ((sp + 0x850#64) ↦₆₄ u850) ∗ ((sp + 0x858#64) ↦₆₄ u858) ∗ ((sp + 0x860#64) ↦₆₄ u860) ∗
          ((sp + 0x950#64) ↦₆₄ u950) ∗ ((sp + 0x958#64) ↦₆₄ u958) ∗ ((sp + 0x960#64) ↦₆₄ u960)) ∗
        (okStepFramePlaced ss_vt id_vt A ctl x g' sess st' sp H s0 ∗ R)) := by
  unfold otrResultAt at hm
  dsimp only at hm
  obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
    w19, w20, w21, w22, w23, w24, H, hpq, hm, hpack⟩ :=
    otrAt_relocate A (sp + 0x580#64) pq.cap pq.ptr otr hm
  have h288 : memRegion (sp + 0x288#64) 0x1e0 =
      memRegion (sp + 0x288#64) 200 ∗ memRegion (sp + 0x350#64) 0x118 := by
    rw [show sp + 0x288#64 = sp + BitVec.ofNat 64 0x288 from rfl,
        mr_cut_add sp 0x288 200 0x118 (by decide)]
  have h648 : memRegion (sp + 0x648#64) 0x538 =
      memRegion (sp + 0x648#64) 0x208 ∗ memRegion (sp + 0x850#64) 24 ∗
      memRegion (sp + 0x868#64) 0xe8 ∗ memRegion (sp + 0x950#64) 24 ∗
      memRegion (sp + 0x968#64) 0x218 := by
    rw [show sp + 0x648#64 = sp + BitVec.ofNat 64 0x648 from rfl,
        mr_cut_add sp 0x648 0x208 0x330 (by decide),
        mr_cut_add sp (0x648 + 0x208) 24 0x318 (by decide),
        mr_cut_add sp (0x648 + 0x208 + 24) 0xe8 0x230 (by decide),
        mr_cut_add sp (0x648 + 0x208 + 24 + 0xe8) 24 0x218 (by decide)]
  rw [h288, h648] at hm
  have hm_d : s2.mem ⊨ memRegion (sp + 0x288#64) 200 ∗
      (memRegion (sp + 0x850#64) 24 ∗ memRegion (sp + 0x950#64) 24 ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x469#64) ↦₈ 0#8) ∗
        okStepFramePlaced ss_vt id_vt A ctl x g' sess st' sp H s0 ∗ R) := by
    unfold okStepFramePlaced
    exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
    d19, d20, d21, d22, d23, d24, hm_d⟩ := memRegion_200_exists_otrWords25_shared_lb (sp + 0x288#64) hm_d
  have hm_850 : s2.mem ⊨ memRegion (sp + 0x850#64) 24 ∗
      (memRegion (sp + 0x950#64) 24 ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x469#64) ↦₈ 0#8) ∗
        okStepFramePlaced ss_vt id_vt A ctl x g' sess st' sp H s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_d
  obtain ⟨u850, u858, u860, hm_850⟩ := memRegion_24_exists_words_shared_lb (sp + 0x850#64) hm_850
  have hm_950 : s2.mem ⊨ memRegion (sp + 0x950#64) 24 ∗
      (((sp + 0x850#64) ↦₆₄ u850) ∗ (((sp + 0x850#64) + 8#64) ↦₆₄ u858) ∗
        (((sp + 0x850#64) + 16#64) ↦₆₄ u860) ∗
        otrWords25 (sp + 0x288#64) d0 d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 d12 d13 d14 d15 d16 d17
          d18 d19 d20 d21 d22 d23 d24 ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
        ((sp + 0x469#64) ↦₈ 0#8) ∗
        okStepFramePlaced ss_vt id_vt A ctl x g' sess st' sp H s0 ∗ R) :=
    Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_850
  obtain ⟨u950, u958, u960, hm_950⟩ := memRegion_24_exists_words_shared_lb (sp + 0x950#64) hm_950
  simp only [BitVec.add_assoc, BitVec.reduceAdd] at hm_950
  refine ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
    w19, w20, w21, w22, w23, w24,
    d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
    d19, d20, d21, d22, d23, d24,
    u850, u858, u860, u950, u958, u960, H, hpq, hpack, ?_⟩
  exact Eq.mp (congrArg (s2.mem ⊨ ·) (by sep_ac_rfl)) hm_950

theorem otrFrom_placed_ok_pack [LibsignalPlacement] {ss_vt id_vt : BitVec 64}
    (A : RustAlloc) (ctl : BitVec 64)
    (x : WithStoresEncGhost) (g' : RecordGhost) (pq : VecPin)
    (sess : Session (List (BitVec 8))) (st' : SessionState (List (BitVec 8)))
    (otr : OutgoingTripleRatchet (List (BitVec 8)))
    (w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24 :
      BitVec 64)
    (sp : BitVec 64) (H R Pm : SepProp) (s0 s3 : State)
    (hpack : ∀ dst : BitVec 64,
      otrWords25 dst pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18
        w19 w20 w21 w22 w23 w24 ∗ H ⊢ otrAt A dst pq.cap pq.ptr otr)
    (hPm : Pm ⊢ ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      otrWords25 (sp + 0x288#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ∗
      ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ∗
      ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ∗
      ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))
    (hm : s3.mem ⊨ Pm ∗ (okStepFramePlaced ss_vt id_vt A ctl x g' sess st' sp H s0 ∗ R)) :
    s3.mem ⊨ (takenSlots A sp sess st' ∗ otrAt A (sp + 0x288#64) pq.cap pq.ptr otr ∗
      memRegion (sp + 0x350#64) 0x118) ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x716 ∗ memRegion x.ret 248 ∗
      encCommonPlaced A ctl x 0 s0 ∗ R := by
  have hm1 := Satisfies.mono (sepConj_mono_left hPm) hm
  unfold okStepFramePlaced at hm1
  have hotr_src :
      otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
        w17 w18 w19 w20 w21 w22 w23 w24 ⊢ memRegion (sp + 0x580#64) 200 :=
    otrWords25_entails_memRegion (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12
      w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
  have h850 :
      ((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6) ⊢
      memRegion (sp + 0x850#64) 24 := by
    have h := words_entails_memRegion_24_shared_lb (sp + 0x850#64) w4 w5 w6
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have h950 :
      ((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6) ⊢
      memRegion (sp + 0x950#64) 24 := by
    have h := words_entails_memRegion_24_shared_lb (sp + 0x950#64) w4 w5 w6
    simpa only [BitVec.add_assoc, BitVec.reduceAdd] using h
  have h46a_eq :
      memRegion (sp + 0x46a#64) 0x716 =
      memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 200 ∗
        memRegion (sp + 0x648#64) 0x208 ∗ memRegion (sp + 0x850#64) 24 ∗
        memRegion (sp + 0x868#64) 0xe8 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x968#64) 0x218 := by
    rw [show sp + 0x46a#64 = sp + BitVec.ofNat 64 0x46a from rfl,
        mr_cut_add sp 0x46a 0x116 0x600 (by decide),
        mr_cut_add sp (0x46a + 0x116) 200 0x538 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200) 0x208 0x330 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200 + 0x208) 24 0x318 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200 + 0x208 + 24) 0xe8 0x230 (by decide),
        mr_cut_add sp (0x46a + 0x116 + 200 + 0x208 + 24 + 0xe8) 24 0x218 (by decide)]
  have hrec_ex :
      sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ⊢
      ∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st') :=
    Entails.sepExists_right g' (Entails.refl _)
  have hm_rearr : s3.mem ⊨
      ((otrWords25 (sp + 0x288#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗ H) ∗
        sessionRecordAt A (sp + 0x110#64) g' (takenRecord sess st') ∗
        otrWords25 (sp + 0x580#64) pq.cap w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16
          w17 w18 w19 w20 w21 w22 w23 w24 ∗
        (((sp + 0x850#64) ↦₆₄ w4) ∗ ((sp + 0x858#64) ↦₆₄ w5) ∗ ((sp + 0x860#64) ↦₆₄ w6)) ∗
        (((sp + 0x950#64) ↦₆₄ w4) ∗ ((sp + 0x958#64) ↦₆₄ w5) ∗ ((sp + 0x960#64) ↦₆₄ w6))) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion (sp + 0x46a#64) 0x116 ∗
      memRegion (sp + 0x648#64) 0x208 ∗
      memRegion (sp + 0x868#64) 0xe8 ∗
      memRegion (sp + 0x968#64) 0x218 ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm1
  have hm_mono := Satisfies.mono
    (sepConj_mono_left
      (sepConj_mono (hpack (sp + 0x288#64))
        (sepConj_mono hrec_ex
          (sepConj_mono hotr_src (sepConj_mono h850 h950))))) hm_rearr
  have hm_poll : s3.mem ⊨
      (memRegion (sp + 0x46a#64) 0x116 ∗ memRegion (sp + 0x580#64) 200 ∗
        memRegion (sp + 0x648#64) 0x208 ∗ memRegion (sp + 0x850#64) 24 ∗
        memRegion (sp + 0x868#64) 0xe8 ∗ memRegion (sp + 0x950#64) 24 ∗
        memRegion (sp + 0x968#64) 0x218) ∗
      (∃∗ g : RecordGhost, sessionRecordAt A (sp + 0x110#64) g (takenRecord sess st')) ∗
      ((sp + 0x280#64) ↦₆₄ (sp + 0x128#64)) ∗
      ((sp + 0x468#64) ↦₈ 0#8) ∗ ((sp + 0x469#64) ↦₈ 1#8) ∗
      otrAt A (sp + 0x288#64) pq.cap pq.ptr otr ∗
      memRegion (sp + 0x350#64) 0x118 ∗
      curScratch sp ∗ encSpillsAtV ss_vt id_vt sp x ∗
      memRegion x.ret 248 ∗ encCommonPlaced A ctl x 0 s0 ∗ R :=
    Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm_mono
  rw [← h46a_eq] at hm_poll
  unfold takenSlots
  exact Eq.mp (congrArg (s3.mem ⊨ ·) (by sep_ac_rfl)) hm_poll

/-! ## 4. Main Segment Proof (`segFrom_placed_okV`) -/

theorem segFrom_placed_okV [LibsignalPlacement]
    {Scope : SessionRecord (List (BitVec 8)) → Prop}
    {Q : List (BitVec 8) → Prop}
    {C : Crypto} {A : RustAlloc}
    {kit : SessionStoreSpec A 0#64} {st0 : kit.StoreState}
    {ikit : IdentityStoreSpec A 0#64} {ist0 : ikit.IdState}
    {ctl : BitVec 64}
    {S : SpqrModel} {encRecord : SessionRecord (List (BitVec 8)) → List (BitVec 8)}
    {Hk : LibsignalHooks} :
    SegFromSpecVPlaced kit st0 ikit ist0 Scope Q C ctl uuidTryParse S encRecord Hk := by
  intro env x r g sess R0 s0 s hcurState
  let R := encStoreExtraPlaced kit st0 ikit ist0 x s0 ∗ R0
  rcases hcurState with ⟨hcur, hsc, hs_pc,
    ⟨hrun, hsp, hal0, hal, hx29, hx19, hcrl, hvregs⟩,
    htr, ⟨hx20, hx21, hx25, hx26, hx28⟩,
    hpt, hrest, hloc, hnow, hstk, hm⟩
  set sp := s0.sp - 0xbe0#64
  have hsp0 : s0.sp - 0xbe0#64 = sp := rfl
  have hs_pc' : s.pc = encEntryPlaced + 0x20c#64 := hs_pc
  obtain ⟨G, u280, _, hpure, hm_unp⟩ :=
    curState_placed_mem_unpack A ctl x r g sess sp R s0 hsp0 hcur hm
  refine SegExitPlaced.of_sepWP hm_unp
    (segFrom_placed_step_pre hs_pc' hrun hsp hal hx20 hx21 hx25 hx26 hx28) ?_
  intro s1 Pm1 _hL0 hsteps01 hs1_pc hs1_run hm1
    ⟨hs1_sp, hs1_tr, hs1_x0, hs1_x8, hs1_x19, hs1_x20, hs1_x21, hs1_x24, hs1_x25, hs1_x26,
      hs1_x27, hs1_x28, hs1_x29, hs1_lr, hs1_vregs, hPm1⟩
  have hcrl1 : StoreKit.LibsignalCodeRoLoaded lsmpl s1.mem := hcrl.of_keepsFrozen hsteps01.keepsFrozen
  have hs1_al : s1.spAligned = true := spAligned_of_sp_eq hal (hs1_sp.trans hsp.symm)
  have hm1_pre := otrFrom_placed_pre_frame A ctl x g G sess sp R Pm1 s0 s1
    hcrl1 hs1_sp hs1_x0 hs1_x8 hPm1 hm1
  refine SegExitPlaced.call env.callees.otrFrom ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
    hs1_pc hs1_run hs1_al hs1_lr hm1_pre
    (fun _ code _ _ hex => by
      rw [show (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A)).onExit
          ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ code s1 _ = ⌜False⌝ from rfl,
          satisfies_pure_sepConj] at hex
      exact hex.1)
    (fun sf _ _ hpan_post => by
      rw [show (StoreKit.withLsRoCl lsmpl (OutgoingRatchet.otrFromRawPlacedSpec A)).onPanic
          ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩ s1 sf = ⌜False⌝ from rfl,
          sepConj_assoc, satisfies_pure_sepConj] at hpan_post
      exact hpan_post.1.elim)
    ?_
  intro s2 _hL1 _hsteps12 hs2_pc hs2_run hs2_sp hcs12 hpost2
  have hs2_sp' : s2.sp = sp := hs2_sp.trans hs1_sp
  have hs2_al : s2.spAligned = true := spAligned_of_sp_eq hs1_al hs2_sp
  have hs2_x20 : s2.readReg64 .x20 = sp + 0x58#64 := by reg_chain
  have hs2_x24 : s2.readReg64 .x24 = sp + 0x58#64 := by reg_chain
  have hs2_x25 : s2.readReg64 .x25 = sp + 0x580#64 := by reg_chain
  have hs2_x26 : s2.readReg64 .x26 = sp + 0x9d0#64 := by reg_chain
  have hs2_x27 : s2.readReg64 .x27 = sp + 0xc0#64 := by reg_chain
  have hs2_x28 : s2.readReg64 .x28 = sp + 0x4a0#64 := by reg_chain
  obtain ⟨hcrl2, G', _, hs2_tr, hm2⟩ :=
    otrFrom_placed_post_unpack A ctl x g G sess ⟨sp + 0x128#64, G, sess.state, sp + 0x580#64⟩
      sp R s0 s1 s2 rfl hsp0 hs1_sp hpure hpost2
  have hs2_tr' : s2.trace = s0.trace ++ kit.loadEvs encRecord x.rem.val (.ok (some r)) :=
    hs2_tr.trans (hs1_tr.trans htr)
  rcases hres : (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 with p | otr
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w0, w1, w2, w3, w4, w5, H, hst, hm2_err⟩ :=
      otrFrom_placed_err_unpack A ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 p sp R s0 s2 hres hm2
    refine SegExitPlaced.of_sepWP hm2_err (segFrom_placed_step_err hs2_pc hs2_run hs2_sp' hs2_al) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x19, hs3_x21, hs3_x25, hs3_x26, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have ⟨hmod_res, hdraws0⟩ := model_of_fromSessionState_error_placed (C := C) (S := S)
      (x := x) hcur hres
    have hm3_tail := otrFrom_placed_err_tail_mem A ctl x { g with cur := some G' } sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 w0 w1 w2 w3 w4 w5 sp H R Pm3
      s0 s3 hPm3 hm3
    refine SegExitPlaced.of_false (tailFromSessionStateErr_placed_ok env x R0 s0 s3
      (okAnswers r .newOrUnchanged)
      (.protocol p) w0 w1 w2 w3 w4 w5 H { g with cur := some G' }
      (takenRecord sess (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2)
      ?_ hst ?_)
    · refine ⟨⟨by rw [hmod_res], by rw [hmod_res]; exact ⟨hsc.2, trivial⟩, by rw [hmod_res]; trivial⟩, ?_⟩
      rw [hs3_tr, hs2_tr', hmod_res]
      dsimp only [okAnswers]
      rw [ikit.traceOfWith_load]
    · refine ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
        by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
        ⟨by reg_chain, by reg_chain, by reg_chain, by reg_chain⟩, hstk, ?_⟩
      rw [hdraws0, hmod_res]
      exact hm3_tail
  · change s2.mem ⊨ otrResultAt A (sp + 0x580#64) G.pq
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).1 ∗ _ at hm2
    rw [hres] at hm2
    obtain ⟨w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18,
      w19, w20, w21, w22, w23, w24,
      d0, d1, d2, d3, d4, d5, d6, d7, d8, d9, d10, d11, d12, d13, d14, d15, d16, d17, d18,
      d19, d20, d21, d22, d23, d24,
      u850, u858, u860, u950, u958, u960, H, hpq, hpack, hm2_ok⟩ :=
      otrFrom_placed_ok_unpack A ctl x { g with cur := some G' } G.pq sess
        (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr sp R s0 s2 hm2
    refine SegExitPlaced.of_sepWP hm2_ok
      (segFrom_placed_step_ok hs2_pc hs2_run hs2_sp' hs2_al hs2_x20 hs2_x24 hs2_x25 hs2_x26 hs2_x27
        hs2_x28 hpq) ?_
    intro s3 Pm3 _hL2 hsteps23 hs3_pc hs3_run hm3
      ⟨hs3_sp, hs3_tr, hs3_x0, hs3_x8, hs3_x19, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25,
        hs3_x26, hs3_x27, hs3_x28, hs3_x29, hs3_vregs, hPm3⟩
    have hcrl3 : StoreKit.LibsignalCodeRoLoaded lsmpl s3.mem := hcrl2.of_keepsFrozen hsteps23.keepsFrozen
    have hs3_al : s3.spAligned = true := spAligned_of_sp_eq hs2_al (hs3_sp.trans hs2_sp'.symm)
    have hm3_ok := otrFrom_placed_ok_pack A ctl x { g with cur := some G' } G.pq sess
      (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2 otr
      w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w24
      sp H R Pm3 s0 s3 hpack hPm3 hm3
    refine SegExitPlaced.next ⟨otr, (Mut.exec OutgoingTripleRatchet.fromSessionState sess.state).2,
      G.pq.cap, G.pq.ptr, hcur, hsc, execOk_fromSessionState_of_ok_shared_lb hres, ?_⟩
    exact ⟨hs3_pc, ⟨hs3_run, hs3_sp, hal0, hs3_al, by reg_chain, by reg_chain, hcrl3,
      by rw [hs3_vregs, hcs12.2.2.2.2.2.2.2.2.2.2.2, hs1_vregs, hvregs]⟩,
      hs3_tr.trans hs2_tr',
      ⟨hs3_x0, hs3_x8, hs3_x20, hs3_x22, hs3_x23, hs3_x24, hs3_x25, hs3_x26, hs3_x27, hs3_x28⟩,
      hpt, hrest, hloc, hnow, hstk, hm3_ok⟩

end CryptoVerification.Cli.LibsignalPublicApi.MessageEncrypt.Pf.SegFrom
