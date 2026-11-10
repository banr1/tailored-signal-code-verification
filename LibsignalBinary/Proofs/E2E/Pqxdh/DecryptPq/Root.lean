/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import LibsignalBinary.Specifications.LibsignalSpqrV1.Statements
public import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Defs
import LibsignalBinary.Proofs.E2E.Pqxdh.DecryptPq.Model

/-!
# Root Composition for `try_decrypt_with_state::<HookRng>`

Composes the segment contracts `S0Spec` .. `S9Spec` and `ErrTailSpec` (`Defs`) with the pure model
lemmas (`Model`) to prove `decrypt_mkg_seed`, `reaches_outcome_of_s4`, `try_decrypt_ok_of_seams`
(`TryDecryptOk`), and the top-level run theorems `tryDecrypt_run_of_seams`,
`tryDecryptEmpty_run_of_seams`, and `tryDecryptV1_run_of_seams`.
-/

@[expose] public section

namespace CryptoVerification.LibsignalTripleRatchet.DecryptPq

open Arm64 ProofLib CryptoGames CryptoGames.HMAC CryptoGames.HKDF CryptoGames.LibsignalSession
open CryptoVerification.RustHeap CryptoVerification.LibsignalSessionRepr
open CryptoVerification.LibsignalTripleRatchetRepr
open CryptoVerification.LibsignalTripleRatchet
open CryptoVerification.LibsignalTripleRatchet.Getters
open CryptoVerification.LibsignalTripleRatchet.OutgoingRatchet
open CryptoVerification.LibsignalSession
open CryptoVerification.LibsignalTripleRatchet.DecryptPq.Model

/-! ## 1. `SeedsLen32` Preservation to `consumeMessageKey` Output (`decrypt_mkg_seed`) -/

/-- `SeedsLen32` for a `RatchetState`: every stored message-key seed in every receiver chain has
length 32. -/
def RatchetSeedsLen32 (r : RatchetState) : Prop :=
  ∀ c ∈ r.receiverChains, ∀ k ∈ c.messageKeys, k.seed.length = 32

theorem length_flatMap_toBEBytes :
    ∀ l : List (BitVec 32), (l.flatMap (toBEBytes 4)).length = 4 * l.length
  | [] => rfl
  | _ :: xs => by
    simp [List.flatMap_cons, toBEBytes, length_flatMap_toBEBytes xs]
    omega

theorem length_sha256With (F : ShaCompress) (m : List (BitVec 8)) :
    (sha256With F m).length = 32 := by
  unfold sha256With
  rw [length_flatMap_toBEBytes]
  simp

theorem length_hmacWith (F : ShaCompress) (k m : List (BitVec 8)) :
    (hmacWith F k m).length = 32 := by
  unfold hmacWith
  exact length_sha256With F _

/-- Freshly derived message keys `ck.messageKeys F` have a 32-byte HMAC-SHA256 seed. -/
theorem messageKeys_seed_length (F : ShaCompress) (ck : ChainKey) :
    (ck.messageKeys F).seed.length = 32 := by
  unfold ChainKey.messageKeys Ratchet.chainHmac
  exact length_hmacWith F _ _

/-- `evictReceiverChains` (which drops old chains from the front) preserves `RatchetSeedsLen32`. -/
theorem evictReceiverChains_preserves {cs : List ReceiverChain}
    (h : ∀ c ∈ cs, ∀ k ∈ c.messageKeys, k.seed.length = 32) :
    ∀ c ∈ RatchetState.evictReceiverChains cs, ∀ k ∈ c.messageKeys, k.seed.length = 32 := by
  intro c hc k hk
  unfold RatchetState.evictReceiverChains at hc
  exact h c (List.mem_of_mem_drop hc) k hk

/-- `TripleRatchet.fromSessionState` transfers `x.st.receiverChains` directly to `tr.ratchet`. -/
theorem tr_fromSessionState_ratchet_seedsLen32 {st st1 : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))}
    (h : SeedsLen32 st)
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1)) :
    RatchetSeedsLen32 tr.ratchet := by
  have ⟨_, hrat, _, _, _⟩ := fromSessionState_ok_inv htr
  intro c hc k hk
  rw [hrat] at hc
  exact h c hc k hk

/-- `ensureReceiverChain` preserves `RatchetSeedsLen32` on `.ok (ck, r1)`: either `r1 = r` or
`dhRatchetStep` appended a chain with `messageKeys = []` and evicted from the front. -/
theorem ensureReceiverChain_ok_seedsLen32 {C : Crypto} {their : PublicKey} {coins : BitVec 256}
    {r r1 : RatchetState} {ck : ChainKey}
    (hr : RatchetSeedsLen32 r)
    (herc : Mut.exec (RatchetState.ensureReceiverChain C their coins) r = (.ok ck, r1)) :
    RatchetSeedsLen32 r1 := by
  cases hf : r.findReceiverChainKey their with
  | error e =>
    rw [ensureReceiverChain_of_find_error hf] at herc
    cases herc
  | ok optCk =>
    cases optCk with
    | some ck0 =>
      rw [ensureReceiverChain_of_find_some hf] at herc
      injection herc with _ hr1
      subst hr1
      exact hr
    | none =>
      rw [ensureReceiverChain_of_find_none hf] at herc
      cases hsc : r.senderChain with
      | none =>
        rw [dhRatchetStep_of_senderChain_none hsc] at herc
        cases herc
      | some sc =>
        cases hcc1 : rootCreateChain C r.rootKey their sc.ratchetKey.privateKey with
        | error e1 =>
          rw [dhRatchetStep_of_first_createChain_error hsc hcc1] at herc
          cases herc
        | ok p1 =>
          rcases p1 with ⟨newRk, recvCk⟩
          cases hcc2 : rootCreateChain C newRk their (KeyPair.generate C coins).privateKey with
          | error e2 =>
            rw [dhRatchetStep_of_second_createChain_error hsc hcc1 hcc2] at herc
            cases herc
          | ok p2 =>
            rcases p2 with ⟨finalRk, sendCk⟩
            rw [dhRatchetStep_of_both_createChain_ok hsc hcc1 hcc2] at herc
            injection herc with _ hr1
            subst hr1
            intro c hc k hk
            dsimp only at hc
            refine evictReceiverChains_preserves ?_ c hc k hk
            intro c' hc' k' hk'
            rcases List.mem_append.mp hc' with hc_old | hc_new
            · exact hr c' hc_old k' hk'
            · simp only [List.mem_singleton] at hc_new
              subst hc_new
              cases hk'

/-- If `takeSkippedKey` returns `.ok (some k)` from a `RatchetSeedsLen32` state,
`k.seed.length = 32`. -/
theorem takeSkippedKey_seed_length {their : PublicKey} {counter : BitVec 32}
    {r r' : RatchetState} {k : MessageKeyGenerator}
    (hr : RatchetSeedsLen32 r)
    (htk : Mut.exec (RatchetState.takeSkippedKey their counter) r = (.ok (some k), r')) :
    k.seed.length = 32 := by
  unfold RatchetState.takeSkippedKey at htk
  rw [exec_bind, exec_get] at htk
  dsimp only at htk
  cases hci : r.findReceiverChainIndex their with
  | none =>
    rw [hci] at htk
    cases htk
  | some chainIdx =>
    rw [hci] at htk
    dsimp only at htk
    cases hc : r.receiverChains[chainIdx]? with
    | none =>
      rw [hc] at htk
      cases htk
    | some c =>
      rw [hc] at htk
      dsimp only at htk
      cases hpos : c.messageKeys.findIdx? (fun mk => mk.counter == counter) with
      | none =>
        rw [hpos] at htk
        cases htk
      | some pos =>
        rw [hpos] at htk
        dsimp only at htk
        cases hkey : c.messageKeys[pos]? with
        | none =>
          rw [hkey] at htk
          cases htk
        | some key =>
          rw [hkey] at htk
          dsimp only [exec_bind, Mut.exec, ExceptT.run, StateT.run, set, StateT.set,
            pure, ExceptT.pure, ExceptT.mk] at htk
          injection htk with hok _
          injection hok with hsome
          injection hsome with hkey_eq
          subst hkey_eq
          exact hr c (List.mem_of_getElem? hc) key (List.mem_of_getElem? hkey)

/-- If `consumeMessageKey` returns `.ok mkg` from a `RatchetSeedsLen32` state,
`mkg.seed.length = 32` (via `takeSkippedKey` or `ChainKey.messageKeys`). -/
theorem consumeMessageKey_seed_length {F : ShaCompress} {their : PublicKey} {ck : ChainKey}
    {counter : BitVec 32} {msgType : MessageType} {r1 r2 : RatchetState}
    {mkg : MessageKeyGenerator}
    (hr1 : RatchetSeedsLen32 r1)
    (hcmk : Mut.exec (RatchetState.consumeMessageKey F their ck counter msgType) r1 =
      (.ok mkg, r2)) :
    mkg.seed.length = 32 := by
  unfold RatchetState.consumeMessageKey at hcmk
  by_cases hlt : counter < ck.index
  · simp only [hlt, ↓reduceIte] at hcmk
    rw [exec_bind] at hcmk
    cases htk : Mut.exec (RatchetState.takeSkippedKey their counter) r1 with
    | mk res r' =>
      rw [htk] at hcmk
      cases res with
      | error e => cases hcmk
      | ok optK =>
        cases optK with
        | none => cases hcmk
        | some k =>
          dsimp only [exec_pure] at hcmk
          injection hcmk with hok _
          injection hok with hk
          subst hk
          exact takeSkippedKey_seed_length hr1 htk
  · simp only [hlt, ↓reduceIte] at hcmk
    rw [exec_bind, exec_get] at hcmk
    dsimp only at hcmk
    by_cases hj : r1.maxForwardJumps < (counter - ck.index).toNat
    · simp only [hj, ↓reduceIte, exec_bind, exec_throw] at hcmk
      cases hcmk
    · simp only [hj, ↓reduceIte, exec_pure, exec_bind] at hcmk
      cases hadv : Mut.exec
          (RatchetState.advanceChain F their counter (counter - ck.index).toNat ck) r1 with
      | mk resAdv rAdv =>
        rw [hadv] at hcmk
        cases resAdv with
        | error e => cases hcmk
        | ok ck' =>
          dsimp only at hcmk
          cases hnext : ck'.nextChainKey F with
          | error e =>
            rw [hnext, exec_liftE_error] at hcmk
            cases hcmk
          | ok nextCk =>
            rw [hnext, exec_liftE_ok] at hcmk
            dsimp only at hcmk
            cases hset : Mut.exec (RatchetState.setReceiverChainKey their nextCk) rAdv with
            | mk resSet rSet =>
              rw [hset] at hcmk
              cases resSet with
              | error e => cases hcmk
              | ok u =>
                dsimp only [exec_pure] at hcmk
                injection hcmk with hok _
                injection hok with hmkg
                rw [← hmkg]
                exact messageKeys_seed_length F ck'

/-- Root-facing seed-length lemma: from `SeedsLen32 x.st`, `fromSessionState = (.ok tr, st1)`,
`ensureReceiverChain = (.ok ck, r1)`, and `consumeMessageKey = (.ok mkg, r2)`, we have
`mkg.seed.length = 32`. -/
theorem decrypt_mkg_seed {C : Crypto} {st st1 : SessionState (List (BitVec 8))}
    {tr : TripleRatchet (List (BitVec 8))} {their : PublicKey} {coins : BitVec 256}
    {ck : ChainKey} {r1 r2 : RatchetState} {counter : BitVec 32} {msgType : MessageType}
    {mkg : MessageKeyGenerator}
    (hseeds : SeedsLen32 st)
    (htr : Mut.exec TripleRatchet.fromSessionState st = (.ok tr, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C their coins) tr.ratchet = (.ok ck, r1))
    (hcmk : Mut.exec (RatchetState.consumeMessageKey C.F their ck counter msgType) r1 =
      (.ok mkg, r2)) :
    mkg.seed.length = 32 :=
  consumeMessageKey_seed_length
    (ensureReceiverChain_ok_seedsLen32 (tr_fromSessionState_ratchet_seedsLen32 hseeds htr) herc)
    hcmk

/-! ## 2. Precondition Extraction and Outcome Helpers -/

/-- Extract `SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat`
from `(tryDecryptSpec C A ctl parse S img).pre x s0 ∗ R`. -/
theorem seedsLen32_of_pre {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 : State}
    (hpre : s0.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).pre x s0 ∗ R) :
    SeedsLen32 x.st ∧ x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat := by
  simp only [tryDecryptSpec, Spec.inImage] at hpre
  have hpre' : s0.mem ⊨
      ⌜s0.readReg64 .x0 = x.ret ∧ s0.readReg64 .x1 = x.ss ∧ s0.readReg64 .x2 = x.remA ∧
        s0.readReg64 .x3 = x.locA ∧ s0.readReg64 .x4 = x.msgA ∧
        (s0.readReg64 .x5).setWidth 8 = msgTypeByte x.msgType ∧
        x.st.remoteIdentity ≠ some x.st.localIdentity ∧ SeedsLen32 x.st ∧
        x.st.receiverChains.length < 2 ^ 32 ∧ rootStack ≤ s0.sp.toNat⌝ ∗
      (⌜img.FrozenLoaded s0 ∧ s0.symtab = img.symtab⌝ ∗
       sessionStateAt A x.ss x.G x.st ∗ protocolAddressAt A x.rem x.remA ∗
       protocolAddressAt A x.loc x.locA ∗ signalMessageAt A x.msgG x.msgA x.msg ∗
       memRegion x.ret 48 ∗ tapeAt ctl x.cur x.rest ∗ logOff img ∗ stackAt s0.sp rootStack ∗
       A.pool ∗ R) :=
    Satisfies.of_eq hpre
  rw [satisfies_pure_sepConj] at hpre'
  exact hpre'.1.2.2.2.2.2.2.2

theorem reaches_outcome_of_panic {P : Program} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) :
    reaches_outcome P (tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s :=
  reaches_outcome_steps hsteps (reaches_outcome_refl_panic hpan hq)

/-- Lift `S4Spec`'s panic disjunct `((e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace)`
into `(tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R`
when `(x.model C S parse).1 = .error e`. -/
theorem onPanic_of_cmk_panic {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {e : SignalProtocolError} {R : SepProp} {s0 s' : State}
    (hm1 : (x.model C S uuidTryParse).1 = .error e)
    (hp : (e = .panic ∨ allocFailedIn s0 s') ∧ s0.trace <+: s'.trace)
    (hmem : s'.mem ⊨ anyHeap ∗ R) :
    s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R := by
  have hcond : ((x.model C S uuidTryParse).1 = .error .panic ∨
      S.recvPanics x.st.pqRatchetState x.msg.pqRatchet ∨ allocFailedIn s0 s') ∧
      s0.trace <+: s'.trace := by
    refine ⟨?_, hp.2⟩
    rcases hp.1 with rfl | halloc
    · exact Or.inl hm1
    · exact Or.inr (Or.inr halloc)
  simp only [tryDecryptSpec, Spec.inImage]
  rw [sepConj_assoc, satisfies_pure_sepConj]
  exact ⟨hcond, hmem⟩

theorem onPanic_drop_frame {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {parse : UuidParser} {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {F R : SepProp} {s0 s' : State}
    (h : s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ (F ∗ R)) :
    s'.mem ⊨ (tryDecryptSpec C A ctl parse S img).onPanic x s0 s' ∗ R := by
  dsimp only [tryDecryptSpec, Spec.inImage] at h ⊢
  rw [sepConj_assoc, satisfies_pure_sepConj] at h ⊢
  rcases h with ⟨hcond, hmem⟩
  rw [← sepConj_assoc] at hmem
  exact ⟨hcond, Satisfies.mono (sepConj_mono_left (entails_anyHeap _)) hmem⟩

theorem spqrRecvStack_le_sub_of_rootStack {sp0 : BitVec 64} (h : rootStack ≤ sp0.toNat) :
    spqrRecvStack ≤ (sp0 - 1504#64).toNat := by
  unfold rootStack spqrRecvStack at *
  bv_omega

theorem reaches_outcome_tryDecryptSpecQF {P : Program} {Q : List (BitVec 8) → Prop}
    {F : SepProp} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64} {parse : UuidParser}
    {S : SpqrModel} {img : Obj.Image} {x : TryDecryptGhost} {R : SepProp} {s0 s : State}
    (h : reaches_outcome P (tryDecryptSpec C A ctl parse S img) x (F ∗ R) s0 s) :
    reaches_outcome P (tryDecryptSpecQF Q F C A ctl parse S img) x R s0 s := by
  refine h.mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨_, _, hqe⟩ | ⟨_, hoom⟩
  · refine Or.inl ⟨hhalted, hcs, ?_⟩
    dsimp only [tryDecryptSpecQF]
    rw [sepConj_assoc, sepConj_left_comm]
    exact hpost
  · exact Or.inr (Or.inl ⟨hpan, onPanic_drop_frame hqp⟩)
  · exact (not_satisfies_false_sepConj hqe).elim
  · exact (not_satisfies_false_sepConj hoom).elim

theorem reaches_outcome_of_panicQF {P : Program} {Q : List (BitVec 8) → Prop}
    {F : SepProp} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {img : Obj.Image}
    {x : TryDecryptGhost} {R : SepProp} {s0 s s' : State}
    (hsteps : Steps P s s')
    (hpan : s'.status = .Panicked)
    (hq : s'.mem ⊨ (tryDecryptSpec C A ctl uuidTryParse S img).onPanic x s0 s' ∗ R) :
    reaches_outcome P (tryDecryptSpecQF Q F C A ctl uuidTryParse S img) x R s0 s :=
  reaches_outcome_steps hsteps
    (reaches_outcome_refl_panic (spec := tryDecryptSpecQF Q F C A ctl uuidTryParse S img) hpan hq)

/-! ## 3. Post-`ensureReceiverChain` Composition (`S4` .. `S9` / `ErrTail`) -/

theorem reaches_outcome_of_s4QF
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQF Q Pstk F C A ctl S abs img)
    (hcallees : TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs4 : S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : S5SpecQF Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : S6Spec img C A ctl abs)
    (hs7 : S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : S9Spec img C A ctl uuidTryParse S abs)
    (herr : ErrTailSpec img C A ctl uuidTryParse S abs)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : Q x.st.pqRatchetState)
    (hPstk : Pstk (s0.sp - 1504#64).toNat)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : S4State A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws (F ∗ R) s0 s4)
    (hL4 : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s4.mem) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (tryDecryptSpecQF Q F C A ctl uuidTryParse S img) x R s0 s4 := by
  have ⟨_, _, hpqr0, _, _⟩ := fromSessionState_ok_inv htr
  have hs4_step :=
    hs4 hloads hhooks hcallees.cmk x trG { tr0 with ratchet := r1 } st1 ck draws (F ∗ R) s0 s4
    hs4_state hL4
  dsimp only at hs4_step
  cases hcmk : Mut.exec (RatchetState.consumeMessageKey C.F x.msg.senderRatchetKey ck x.msg.counter
      x.msgType) r1 with
  | mk cmkRes r2 =>
    rw [hcmk] at hs4_step
    cases cmkRes with
    | error e =>
      have hmodel := model_of_cmk_error (S := S) htr herc hcmk
      have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
      have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
      rcases hs4_step with ⟨s4', hsteps4, ⟨hne, trG', herr_st⟩ | ⟨hpan, hp, hmem⟩⟩
      · subst hdraws
        exact reaches_outcome_steps hsteps4
          (reaches_outcome_tryDecryptSpecQF
            (herr hloads hhooks hcallees.dropChain x trG' { tr0 with ratchet := r2 } st1 e
              (F ∗ R) s0 s4' hne hm1 hm2 herr_st))
      · exact reaches_outcome_of_panicQF hsteps4 hpan
          (onPanic_drop_frame (onPanic_of_cmk_panic hm1 hp hmem))
    | ok mkg =>
      rcases hs4_step with ⟨s5, hsteps5, ⟨trG5, hs5_state⟩ | ⟨hpan, hq⟩⟩
      · refine reaches_outcome_steps hsteps5 ?_
        have hL5 := hsteps5.codeLoaded hL4
        have hs5_step :=
          hs5 hloads hhooks hrecv x trG5 { tr0 with ratchet := r2 } st1 mkg draws R s0 s5
          hQ hpqr0 hPstk hs5_state hL5
        dsimp only at hs5_step
        cases hspqr : S.recv tr0.pqrState x.msg.pqRatchet with
        | error sd =>
          rw [hspqr] at hs5_step
          let e : SignalProtocolError :=
            if sd then .invalidState else .invalidMessage x.msgType .pqRatchet
          have hne : e ≠ .panic := by subst e; cases sd <;> nofun
          rcases hs5_step with ⟨s5', hsteps5', ⟨herr_st, hnp5⟩ | ⟨hpan, hq⟩⟩
          · have hmodel := model_of_spqr_error htr herc hcmk hspqr hnp5
            have hm1 : (x.model C S uuidTryParse).1 = .error e := by rw [hmodel]
            have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
            subst hdraws
            exact reaches_outcome_steps hsteps5'
              (reaches_outcome_tryDecryptSpecQF
                (herr hloads hhooks hcallees.dropChain x trG5
                  { tr0 with ratchet := r2 } st1 e (F ∗ R) s0 s5'
                  hne hm1 hm2 herr_st))
          · exact reaches_outcome_of_panicQF hsteps5' hpan hq
        | ok pqrRes =>
          rcases pqrRes with ⟨newPqrState, pqrKey⟩
          rw [hspqr] at hs5_step
          rcases hs5_step with ⟨s6, hsteps6, ⟨hs6_state, hnp5⟩ | ⟨hpan, hq⟩⟩
          · refine reaches_outcome_steps hsteps6 (reaches_outcome_tryDecryptSpecQF ?_)
            have hL6 := hsteps6.codeLoaded hL5
            have hseed32 : mkg.seed.length = 32 := decrypt_mkg_seed hseeds htr herc hcmk
            obtain ⟨s7, hsteps7, ⟨_, _, hs7_state⟩ | ⟨_, hoom⟩⟩ :=
              hs6 hloads hcallees.genKeys x trG5 { tr0 with ratchet := r2 } st1 mkg
                newPqrState pqrKey draws (F ∗ R) s0 s6 hseed32 hs6_state hL6
            rotate_left; · exact False.elim hoom
            refine reaches_outcome_steps hsteps7 ?_
            have hL7 := hsteps7.codeLoaded hL6
            let mks := mkg.generateKeys C.F pqrKey
            have hs7_step := hs7 hloads hhooks hcallees.verifyMac x trG5 { tr0 with ratchet := r2 }
              st1 mks newPqrState draws (F ∗ R) s0 s7 hs7_state hL7
            dsimp only at hs7_step
            cases hmac : x.msg.verifyMacWithAddresses C.F
                (serializeAddresses (serviceIdParse uuidTryParse) x.rem x.loc)
                tr0.remoteIdentityKey tr0.localIdentityKey mks.macKey with
            | false =>
              rw [hmac] at hs7_step
              simp only [Bool.false_eq_true, ↓reduceIte] at hs7_step
              have hmodel := model_of_verifyMac_false htr herc hcmk hspqr hmac hnp5
              have hm1 : (x.model C S uuidTryParse).1 =
                  .error (.invalidMessage x.msgType .macFailed) := by
                rw [hmodel]
              have hm2 : (x.model C S uuidTryParse).2 = st1 := by rw [hmodel]
              have hne : SignalProtocolError.invalidMessage x.msgType .macFailed ≠ .panic := nofun
              rcases hs7_step with ⟨s7', hsteps7', herr_st | ⟨hpan, hq⟩⟩
              · subst hdraws
                exact reaches_outcome_steps hsteps7'
                  (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                    (.invalidMessage x.msgType .macFailed) (F ∗ R) s0 s7' hne hm1 hm2 herr_st)
              · exact reaches_outcome_of_panic hsteps7' hpan hq
            | true =>
              rw [hmac] at hs7_step
              simp only [↓reduceIte] at hs7_step
              rcases hs7_step with ⟨s8, hsteps8, hs8_state | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps8 ?_
                have hL8 := hsteps8.codeLoaded hL7
                have hs8_step := hs8 hloads hhooks x trG5 { tr0 with ratchet := r2 }
                  st1 mks newPqrState draws (F ∗ R) s0 s8 hs8_state hL8
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
                    exact reaches_outcome_steps hsteps8'
                      (herr hloads hhooks hcallees.dropChain x trG5 { tr0 with ratchet := r2 } st1
                        (.invalidMessage x.msgType .badCiphertext) (F ∗ R) s0 s8' hne hm1 hm2 herr_st)
                  · exact reaches_outcome_of_panic hsteps8' hpan hq
                | some pt =>
                  rw [haes] at hs8_step
                  have hmodel := model_of_aesDec_some htr herc hcmk hspqr hmac haes hnp5
                  have hm1 : (x.model C S uuidTryParse).1 = .ok pt := by rw [hmodel]
                  have hm2 : (x.model C S uuidTryParse).2 =
                      (({ { tr0 with ratchet := r2 }
                          with pqrState := newPqrState }).applyToSessionState
                        st1).clearUnacknowledgedPreKeyMessage := by rw [hmodel]
                  rcases hs8_step with ⟨s9, hsteps9, hs9_state | ⟨hpan, hq⟩⟩
                  · subst hdraws
                    exact reaches_outcome_steps hsteps9
                      (hs9 hloads hhooks hcallees.trApply hcallees.clearUpk x trG5
                        { tr0 with ratchet := r2 } st1 newPqrState pt (F ∗ R) s0 s9 hm1 hm2 hs9_state)
                  · exact reaches_outcome_of_panic hsteps9 hpan hq
              · exact reaches_outcome_of_panic hsteps8 hpan hq
          · exact reaches_outcome_of_panicQF hsteps6 hpan hq
      · exact reaches_outcome_of_panicQF hsteps5 hpan (onPanic_drop_frame hq)

/-- From `S4State` at the join point of `ensureReceiverChain = (.ok ck, r1)`, chaining `S4Spec`,
`S5Spec`, `S6Spec`, `S7Spec`, `S8Spec`, `S9Spec`, and `ErrTailSpec` reaches a valid outcome of
`tryDecryptSpec`. -/
theorem reaches_outcome_of_s4
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img)
    (hcallees : TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs4 : S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : S5Spec Q img C A ctl uuidTryParse S abs)
    (hs6 : S6Spec img C A ctl abs)
    (hs7 : S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : S9Spec img C A ctl uuidTryParse S abs)
    (herr : ErrTailSpec img C A ctl uuidTryParse S abs)
    {x : TryDecryptGhost} {trG : TrGhost} {tr0 : TripleRatchet (List (BitVec 8))}
    {st1 : SessionState (List (BitVec 8))} {ck : ChainKey} {r1 : RatchetState}
    {draws : Nat} {R : SepProp} {s0 s4 : State}
    (hseeds : SeedsLen32 x.st)
    (hQ : Q x.st.pqRatchetState)
    (htr : Mut.exec TripleRatchet.fromSessionState x.st = (.ok tr0, st1))
    (herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey (coinsOf x.rest))
      tr0.ratchet = (.ok ck, r1))
    (hdraws : draws = decryptDraws C x.st x.msg.senderRatchetKey x.rest)
    (hs4_state : S4State A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws R s0 s4)
    (hL4 : (tripleRatchetProgAt img.base C ctl abs).CodeLoaded s4.mem) :
    reaches_outcome (tripleRatchetProgAt img.base C ctl abs)
      (tryDecryptSpec C A ctl uuidTryParse S img) x R s0 s4 := by
  have hs4' : S4State A ctl img x trG { tr0 with ratchet := r1 } st1 ck draws
      (emp ∗ R) s0 s4 := by rwa [emp_sepConj]
  have hs5' : S5SpecQF Q (fun _ => True) emp img C A ctl uuidTryParse S abs := by
    intro hloads' hhooks' _ x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' _ h5' hL'
    rw [emp_sepConj] at h5'
    have h := hs5 hloads' hhooks' hrecv x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' h5' hL'
    simpa only [emp_sepConj] using h
  refine (reaches_outcome_of_s4QF hloads hhooks (spqrRecvOkQF_of_okQ hrecv) hcallees
    hs4 hs5' hs6 hs7 hs8 hs9 herr hseeds hQ trivial htr herc hdraws hs4' hL4).mono_outcome (fun s' hout => ?_)
  rcases hout with ⟨hhalted, hcs, hpost⟩ | ⟨hpan, hqp⟩ | ⟨code, hex, hqe⟩ | ⟨_, hoom⟩
  · dsimp only [tryDecryptSpecQF] at hpost
    rw [emp_sepConj] at hpost
    exact Or.inl ⟨hhalted, hcs, hpost⟩
  · exact Or.inr (Or.inl ⟨hpan, hqp⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨code, hex, hqe⟩))
  · exact (not_satisfies_false_sepConj hoom).elim

/-! ## 4. Full Root Composition (`S0` .. `S9` + `ErrTail` → `TryDecryptOk` / `TryDecryptRunStmt`) -/

theorem try_decrypt_ok_of_seamsQF
    {Q : List (BitVec 8) → Prop} {Pstk : Nat → Prop} {F : SepProp}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hPstk : ∀ sp0 : BitVec 64, rootStack ≤ sp0.toNat → Pstk (sp0 - 1504#64).toNat)
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQF Q Pstk F C A ctl S abs img)
    (hcallees : TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : S2Spec img C A ctl abs)
    (hs3 : S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : S5SpecQF Q Pstk F img C A ctl uuidTryParse S abs)
    (hs6 : S6Spec img C A ctl abs)
    (hs7 : S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : S9Spec img C A ctl uuidTryParse S abs)
    (herr : ErrTailSpec img C A ctl uuidTryParse S abs) :
    TryDecryptOkQF Q F img C A ctl uuidTryParse S abs := by
  refine subroutine_ok.of_codeLoaded fun x R s0 hpc hrun hpre hsp hL => ?_
  dsimp only [tryDecryptSpecQF] at hpre
  rw [sepConj_assoc, satisfies_pure_sepConj] at hpre
  rcases hpre with ⟨hQ, hpre⟩
  rw [sepConj_assoc, sepConj_left_comm] at hpre
  obtain ⟨hseeds, hchains, hstk⟩ := seedsLen32_of_pre hpre
  have hPstk0 : Pstk (s0.sp - 1504#64).toNat := hPstk s0.sp hstk
  obtain ⟨s1, hsteps1, ⟨_, _, hs1_state⟩ | ⟨_, hoom⟩⟩ :=
    hs0 hloads hcallees.localIk hcallees.remoteIk hcallees.sameAcc x (F ∗ R) s0 hpc hrun hsp hpre hL
  rotate_left; · exact False.elim hoom
  refine reaches_outcome_steps hsteps1 ?_
  have hL1 := hsteps1.codeLoaded hL
  have hs1_step := hs1 hloads hcallees.trFrom x (F ∗ R) s0 s1 hs1_state hL1
  cases htr : Mut.exec TripleRatchet.fromSessionState x.st with
  | mk trRes st1 =>
    rw [htr] at hs1_step
    cases trRes with
    | error e =>
      exact reaches_outcome_tryDecryptSpecQF hs1_step
    | ok tr0 =>
      rcases hs1_step with ⟨s2, hsteps2, trG2, hs2_state⟩
      refine reaches_outcome_steps hsteps2 ?_
      have hL2 := hsteps2.codeLoaded hL1
      have hs2_step :=
        hs2 hloads hcallees.findReceiverChainKey x trG2 tr0 st1 (F ∗ R) s0 s2 hs2_state hL2
      cases hf : tr0.ratchet.findReceiverChainKey x.msg.senderRatchetKey with
      | error e =>
        rw [hf] at hs2_step
        obtain ⟨s2', hsteps2', ⟨_, _, herr_st⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
        rotate_left; · exact False.elim hoom
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
        exact reaches_outcome_steps hsteps2'
          (reaches_outcome_tryDecryptSpecQF
            (herr hloads hhooks hcallees.dropChain x trG2 tr0 st1 e (F ∗ R) s0 s2'
              hne hm1 hm2 herr_st))
      | ok optCk =>
        cases optCk with
        | some ck =>
          rw [hf] at hs2_step
          obtain ⟨s4, hsteps4, ⟨_, _, hs4_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine reaches_outcome_steps hsteps4 ?_
          have hL4 := hsteps4.codeLoaded hL2
          have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
              (coinsOf x.rest)) tr0.ratchet = (.ok ck, tr0.ratchet) :=
            ensureReceiverChain_of_find_some hf
          have hdraws : 0 = decryptDraws C x.st x.msg.senderRatchetKey x.rest :=
            (decryptDraws_of_find_some x.rest htr hf).symm
          exact reaches_outcome_of_s4QF hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
            hseeds hQ hPstk0 htr herc hdraws hs4_state hL4
        | none =>
          rw [hf] at hs2_step
          obtain ⟨s3, hsteps3, ⟨_, _, hs3_state⟩ | ⟨_, hoom⟩⟩ := hs2_step hL2
          rotate_left; · exact False.elim hoom
          refine reaches_outcome_steps hsteps3 ?_
          have hL3 := hsteps3.codeLoaded hL2
          have htr_chains : tr0.ratchet.receiverChains.length < 2 ^ 32 := by
            rw [(fromSessionState_ok_inv htr).2.1]
            exact hchains
          have hs3_step := hs3 hloads hhooks hcallees.createChain hcallees.derivePk
            hcallees.pkSer hcallees.chainKeyToPb hcallees.growOne hcallees.dropChain
            x trG2 tr0 st1 (F ∗ R) s0 s3 htr hf htr_chains hstk hs3_state hL3
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
              · exact reaches_outcome_steps hsteps3'
                  (reaches_outcome_tryDecryptSpecQF
                    (herr hloads hhooks hcallees.dropChain x trG3 { tr0 with ratchet := r1' } st1 e
                      (F ∗ R) s0 s3' hne hm1 hm2 herr_st))
              · exact reaches_outcome_of_panicQF hsteps3' hpan (onPanic_drop_frame hq)
            | ok ck =>
              have herc : Mut.exec (RatchetState.ensureReceiverChain C x.msg.senderRatchetKey
                  (coinsOf x.rest)) tr0.ratchet = (.ok ck, r1) := by
                rw [ensureReceiverChain_of_find_none hf, hdh]
              rcases hs3_step with ⟨s4, hsteps4, ⟨trG4, hs4_state⟩ | ⟨hpan, hq⟩⟩
              · refine reaches_outcome_steps hsteps4 ?_
                have hL4 := hsteps4.codeLoaded hL3
                exact reaches_outcome_of_s4QF
                  hloads hhooks hrecv hcallees hs4 hs5 hs6 hs7 hs8 hs9 herr
                  hseeds hQ hPstk0 htr herc rfl hs4_state hL4
              · exact reaches_outcome_of_panicQF hsteps4 hpan (onPanic_drop_frame hq)

/-- Composes `S0Spec` .. `S9Spec`, `ErrTailSpec`, `SpqrRecvOkQ Q`, and `TryDecryptCallees` into
`TryDecryptOk Q` on session states whose PQ ratchet state satisfies `Q`. -/
theorem try_decrypt_ok_of_seams
    {Q : List (BitVec 8) → Prop}
    {img : Obj.Image} {C : Crypto} {A : RustAlloc} {ctl : BitVec 64}
    {S : SpqrModel} {abs : String → Option (State → State)}
    (hloads : Obj.Loads libsignalSessionImage img)
    (hhooks : TripleRatchetHooks C A S abs)
    (hrecv : SpqrRecvOkQ Q C A ctl S abs img)
    (hcallees : TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : S2Spec img C A ctl abs)
    (hs3 : S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : S5Spec Q img C A ctl uuidTryParse S abs)
    (hs6 : S6Spec img C A ctl abs)
    (hs7 : S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : S9Spec img C A ctl uuidTryParse S abs)
    (herr : ErrTailSpec img C A ctl uuidTryParse S abs) :
    TryDecryptOk Q img C A ctl uuidTryParse S abs := by
  have hs5' : S5SpecQF Q (fun _ => True) emp img C A ctl uuidTryParse S abs := by
    intro hloads' hhooks' _ x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' _ h5' hL'
    rw [emp_sepConj] at h5'
    have h := hs5 hloads' hhooks' hrecv x' trG' tr' st1' mkg' draws' R' s0' s' hQ' hpqr' h5' hL'
    simpa only [emp_sepConj] using h
  exact tryDecryptOk_of_okQF
    (try_decrypt_ok_of_seamsQF (fun _ _ => trivial) hloads hhooks (spqrRecvOkQF_of_okQ hrecv)
      hcallees hs0 hs1 hs2 hs3 hs4 hs5' hs6 hs7 hs8 hs9 herr)

/-- **Decrypt (`<PqxdhRng>`).** For an image of `libsignalSessionImage` and abstract hooks meeting
`TripleRatchetHooks`, `try_decrypt_with_state::<PqxdhRng>` (`0x6eff8`) meets `tryDecryptSpec`. -/
def TryDecryptPqRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → SpqrRecvOk C A ctl S abs img →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryDecryptName)
      (tryDecryptSpec C A ctl uuidTryParse S img)

/-- **Decrypt (`<PqxdhRng>`) on an empty pq state.** -/
def TryDecryptPqEmptyRunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A S abs → S.RecvEmptyOk → Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryDecryptName)
      ((tryDecryptSpec C A ctl uuidTryParse S img).restrictPre (·.st.pqRatchetState = []))

/-- Instantiates `try_decrypt_ok_of_seams` at `Q := fun _ => True` to establish
`TryDecryptRunStmt`. -/
theorem tryDecrypt_run_of_seams
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : S2Spec img C A ctl abs)
    (hs3 : S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : S5Spec (fun _ => True) img C A ctl uuidTryParse S abs)
    (hs6 : S6Spec img C A ctl abs)
    (hs7 : S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : S9Spec img C A ctl uuidTryParse S abs)
    (herr : ErrTailSpec img C A ctl uuidTryParse S abs) :
    TryDecryptPqRunStmt C A ctl S abs img := by
  intro hhooks hrecv hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  have h := try_decrypt_ok_of_seams (Q := fun _ => True) hloads hhooks
    (spqrRecvOkQ_of_recvOk hrecv) (hcallees hhooks hloads)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 herr
  unfold TryDecryptOk at h
  rwa [Spec.restrictPre_true] at h

/-- Instantiates `try_decrypt_ok_of_seams` at `Q := (· = [])` using `SpqrRecvEmptyRunStmt` to
establish `TryDecryptEmptyRunStmt`. -/
theorem tryDecryptEmpty_run_of_seams
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (S : SpqrModel) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvEmpty : SpqrRecvEmptyRunStmt C A ctl S abs img)
    (hcallees : TripleRatchetHooks C A S abs → Obj.Loads libsignalSessionImage img →
      TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : S0Spec img C A ctl uuidTryParse S abs)
    (hs1 : S1Spec img C A ctl uuidTryParse S abs)
    (hs2 : S2Spec img C A ctl abs)
    (hs3 : S3Spec img C A ctl uuidTryParse S abs)
    (hs4 : S4Spec img C A ctl uuidTryParse S abs)
    (hs5 : S5Spec (· = []) img C A ctl uuidTryParse S abs)
    (hs6 : S6Spec img C A ctl abs)
    (hs7 : S7Spec img C A ctl uuidTryParse S abs)
    (hs8 : S8Spec img C A ctl uuidTryParse S abs)
    (hs9 : S9Spec img C A ctl uuidTryParse S abs)
    (herr : ErrTailSpec img C A ctl uuidTryParse S abs) :
    TryDecryptPqEmptyRunStmt C A ctl S abs img := by
  intro hhooks hempty hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  exact try_decrypt_ok_of_seams (Q := (· = [])) hloads hhooks
    (spqrRecvOkQ_empty hrecvEmpty hhooks hempty hloads) (hcallees hhooks hloads)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 herr

/-- Decrypt (`<PqxdhRng>`) statement specialized to SPQR v1 states (`pqRatchetState.length < 2 ^ 32`). -/
def TryDecryptPqV1RunStmt (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State)) (img : Obj.Image) : Prop :=
  TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
    LibsignalSpqrV1.SpqrHooks C A K abs →
    Obj.Loads libsignalSessionImage img →
    subroutine_ok (tripleRatchetProg img C ctl abs) (entryOf img tryDecryptName)
      (LibsignalSpqrV1.tryDecryptSpecT C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) img)

/-- Instantiates `try_decrypt_ok_of_seams` at `Q := (·.length < 2 ^ 32)`,
`Pstk := (spqrRecvStack ≤ ·)`, and `F := TokenInit img` using `SpqrRecvV1Stmt` to establish
`TryDecryptV1RunStmt`. -/
theorem tryDecryptV1_run_of_seams
    (C : Crypto) (A : RustAlloc) (ctl : BitVec 64)
    (K : LibsignalSpqrV1.MlKem) (abs : String → Option (State → State))
    (img : Obj.Image)
    (hrecvV1 : LibsignalSpqrV1.SpqrRecvV1Stmt C A ctl K abs img)
    (hcallees : TripleRatchetHooks C A (LibsignalSpqrV1.spqrV1 C.F K) abs →
      Obj.Loads libsignalSessionImage img →
      TryDecryptCallees img C A ctl uuidTryParse abs)
    (hs0 : S0Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs1 : S1Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs2 : S2Spec img C A ctl abs)
    (hs3 : S3Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs4 : S4Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs5 : S5SpecQF (·.length < 2 ^ 32) (spqrRecvStack ≤ ·) (LibsignalSpqrV1.TokenInit img)
      img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs6 : S6Spec img C A ctl abs)
    (hs7 : S7Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs8 : S8Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (hs9 : S9Spec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs)
    (herr : ErrTailSpec img C A ctl uuidTryParse (LibsignalSpqrV1.spqrV1 C.F K) abs) :
    TryDecryptPqV1RunStmt C A ctl K abs img := by
  intro hhooks hspqr hloads
  rw [tripleRatchetProg_eq_tripleRatchetProgAt hloads]
  have hrecv : SpqrRecvOkQF (·.length < 2 ^ 32) (spqrRecvStack ≤ ·) (LibsignalSpqrV1.TokenInit img)
      C A ctl (LibsignalSpqrV1.spqrV1 C.F K) abs img :=
    LibsignalSpqrV1.spqrRecvSpecXT_imp_spqrRecvSpec _ _ A C.F K img (hrecvV1 hhooks hspqr hloads)
  exact try_decrypt_ok_of_seamsQF (fun _ h => spqrRecvStack_le_sub_of_rootStack h)
    hloads hhooks hrecv (hcallees hhooks hloads)
    hs0 hs1 hs2 hs3 hs4 hs5 hs6 hs7 hs8 hs9 herr

alias try_decrypt_ok := try_decrypt_ok_of_seams
alias tryDecrypt_ok := tryDecrypt_run_of_seams

end CryptoVerification.LibsignalTripleRatchet.DecryptPq
