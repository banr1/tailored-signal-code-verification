/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Cli.RetiredTraceExplanation
import Mathlib.Data.List.Basic

/-!
# Receiver-Trial Algebra and `MacTagForgeryOrCollision` Lemmas

Introduction, membership, inversion, monotonicity, and `gamma`-congruence lemmas for `TrialCtx`,
`trialTerms`, `MacTagForgeryOrCollision`, `whisperTrials`, `bobTrials`, `MemoCollisionOn`, and
`RecvCollision`.
-/

@[expose] public section

set_option autoImplicit false

namespace Symbolic.Swarm.Stage1Trials

open DY
open CryptoProofLib.Refinement (ExternInterpretation)
open DY.Libsignal
open DY.Libsignal.Composed
open DY.Libsignal.Composed.Refinement
open DY.Libsignal.PQXDH (HandshakeKeys pqxdhKdf pqxdhIkm agree errToOption serializedIk)
open DY.Libsignal.TripleRatchet (messageVersion recvChainFor findRecvChain consumeMessageKey
  skippedSeeds computeMac RecvChain createChain TRState DRState TRSignalMsg parseTrSignalMsg
  trMsgKeys TREvent SessionInfo)

/-! ## `trialTerms` Membership -/

theorem trialTerms_seed_some (salts : List DY.Bytes) (msg : TRSignalMsg) (ctx : TrialCtx)
    (seed : DY.Bytes) (h : ctx.seed? = some seed) :
    trialTerms salts msg ctx =
      ctx.extra ++ salts.flatMap fun salt =>
        let mk := trMsgKeys salt seed
        [mk.cipherKey, mk.macKey, mk.iv, computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire] ++
        (DY.SymEnc.symDec mk.cipherKey mk.iv msg.ciphertext).toList := by
  simp [trialTerms, h]

theorem mem_trialTerms_of_mem_extra {salts : List DY.Bytes} {msg : TRSignalMsg} {ctx : TrialCtx}
    {t : DY.Bytes} (ht : t ∈ ctx.extra) : t ∈ trialTerms salts msg ctx :=
  List.mem_append_left _ ht

theorem computeMac_mem_trialTerms {salts : List DY.Bytes} {msg : TRSignalMsg} {ctx : TrialCtx}
    {seed salt : DY.Bytes} (hseed : ctx.seed? = some seed) (hsalt : salt ∈ salts) :
    computeMac (trMsgKeys salt seed).macKey ctx.peerIk ctx.myIk msg.wire ∈
      trialTerms salts msg ctx := by
  rw [trialTerms_seed_some salts msg ctx seed hseed]
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨salt, hsalt, by simp⟩)

theorem mem_flatMap_trialTerms_of_mem_extra {salts : List DY.Bytes} {msg : TRSignalMsg}
    {ctxs : List TrialCtx} {ctx : TrialCtx} {t : DY.Bytes}
    (hctx : ctx ∈ ctxs) (ht : t ∈ ctx.extra) : t ∈ ctxs.flatMap (trialTerms salts msg) :=
  List.mem_flatMap.mpr ⟨ctx, hctx, mem_trialTerms_of_mem_extra ht⟩

/-! ## `MacTagForgeryOrCollision` Rules and Congruence -/

/-- Own-salt MAC-guess introduction for `MacTagForgeryOrCollision`. -/
theorem MacTagForgeryOrCollision.of_ownSaltGuess
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop}
    {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx} {ctx : TrialCtx}
    {seed k : DY.Bytes} (hctx : ctx ∈ ctxs) (hseed : ctx.seed? = some seed) (hk : k ∈ ctx.ownSalts)
    (hmac : gamma interpretation S g
        (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
      gamma interpretation S g msg.mac) (hunk : ¬ known seed)
    (hne : ∀ salt ∈ honest,
      let hmk := trMsgKeys salt seed; let mk := trMsgKeys k seed
      (gamma interpretation S g hmk.cipherKey, gamma interpretation S g hmk.macKey,
       gamma interpretation S g hmk.iv) ≠
      (gamma interpretation S g mk.cipherKey, gamma interpretation S g mk.macKey,
       gamma interpretation S g mk.iv)) :
    MacTagForgeryOrCollision interpretation S g known honest msg ctxs :=
  Or.inl ⟨ctx, hctx, seed, hseed, k, hk, hmac, hunk, hne⟩

/-- Cross-seed byte-level MAC-collision introduction for `MacTagForgeryOrCollision`. -/
theorem MacTagForgeryOrCollision.of_crossSeedBytes
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop}
    {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx} {ctx ctx₀ : TrialCtx}
    {seed k seed₀ salt₀ : DY.Bytes} (hctx : ctx ∈ ctxs) (hseed : ctx.seed? = some seed)
    (hk : k ∈ ctx.ownSalts)
    (hmac : gamma interpretation S g
        (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
      gamma interpretation S g msg.mac)
    (hctx₀ : ctx₀ ∈ ctxs) (hseed₀ : ctx₀.seed? = some seed₀)
    (hseed_ne : gamma interpretation S g seed ≠ gamma interpretation S g seed₀)
    (hsalt₀ : salt₀ ∈ ctx₀.ownSalts ++ honest)
    (hmac₀ : gamma interpretation S g
        (computeMac (trMsgKeys salt₀ seed₀).macKey ctx₀.peerIk ctx₀.myIk msg.wire) =
      gamma interpretation S g msg.mac) :
    MacTagForgeryOrCollision interpretation S g known honest msg ctxs :=
  Or.inr ⟨ctx, hctx, seed, hseed, k, hk, hmac,
    ctx₀, hctx₀, seed₀, hseed₀, hseed_ne, Or.inl ⟨salt₀, hsalt₀, hmac₀⟩⟩

/-- Cross-seed `computeMac`-term MAC-collision introduction for `MacTagForgeryOrCollision`. -/
theorem MacTagForgeryOrCollision.of_crossSeedTerm
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop}
    {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx} {ctx ctx₀ : TrialCtx}
    {seed k seed₀ peerIk₀ myIk₀ salt₀ w : DY.Bytes}
    (hctx : ctx ∈ ctxs) (hseed : ctx.seed? = some seed) (hk : k ∈ ctx.ownSalts)
    (hmac : gamma interpretation S g
        (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
      gamma interpretation S g msg.mac)
    (hctx₀ : ctx₀ ∈ ctxs) (hseed₀ : ctx₀.seed? = some seed₀)
    (hseed_ne : gamma interpretation S g seed ≠ gamma interpretation S g seed₀)
    (hmac_term : msg.mac = computeMac (trMsgKeys salt₀ seed₀).macKey peerIk₀ myIk₀ w)
    (hwire : gamma interpretation S g w = gamma interpretation S g msg.wire) :
    MacTagForgeryOrCollision interpretation S g known honest msg ctxs :=
  Or.inr ⟨ctx, hctx, seed, hseed, k, hk, hmac,
    ctx₀, hctx₀, seed₀, hseed₀, hseed_ne, Or.inr ⟨peerIk₀, myIk₀, salt₀, w, hmac_term, hwire⟩⟩

/-- Specialization of `MacTagForgeryOrCollision.of_crossSeedTerm` when `w = msg.wire`. -/
theorem MacTagForgeryOrCollision.of_crossSeedTerm_exact
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop}
    {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx} {ctx ctx₀ : TrialCtx}
    {seed k seed₀ peerIk₀ myIk₀ salt₀ : DY.Bytes}
    (hctx : ctx ∈ ctxs) (hseed : ctx.seed? = some seed) (hk : k ∈ ctx.ownSalts)
    (hmac : gamma interpretation S g
        (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
      gamma interpretation S g msg.mac)
    (hctx₀ : ctx₀ ∈ ctxs) (hseed₀ : ctx₀.seed? = some seed₀)
    (hseed_ne : gamma interpretation S g seed ≠ gamma interpretation S g seed₀)
    (hmac_term : msg.mac = computeMac (trMsgKeys salt₀ seed₀).macKey peerIk₀ myIk₀ msg.wire) :
    MacTagForgeryOrCollision interpretation S g known honest msg ctxs :=
  MacTagForgeryOrCollision.of_crossSeedTerm hctx hseed hk hmac hctx₀ hseed₀ hseed_ne hmac_term rfl

/-- Under `¬ MacTagForgeryOrCollision`, a matching MAC on an unknown seed `seed` with own salt `k`
yields an honest salt `salt ∈ honest` producing identical message keys under `gamma`. -/
theorem exists_honestSalt_of_not_ownSaltMacCollision
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost} {known : DY.Bytes → Prop}
    {honest : List DY.Bytes} {msg : TRSignalMsg} {ctxs : List TrialCtx} {ctx : TrialCtx}
    {seed k : DY.Bytes} (hctx : ctx ∈ ctxs) (hseed : ctx.seed? = some seed) (hk : k ∈ ctx.ownSalts)
    (hunk : ¬ known seed)
    (hmac : gamma interpretation S g
        (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
      gamma interpretation S g msg.mac)
    (hnot : ¬ MacTagForgeryOrCollision interpretation S g known honest msg ctxs) :
    ∃ salt ∈ honest,
      gamma interpretation S g (trMsgKeys salt seed).cipherKey =
        gamma interpretation S g (trMsgKeys k seed).cipherKey ∧
      gamma interpretation S g (trMsgKeys salt seed).macKey =
        gamma interpretation S g (trMsgKeys k seed).macKey ∧
      gamma interpretation S g (trMsgKeys salt seed).iv =
        gamma interpretation S g (trMsgKeys k seed).iv := by
  by_contra hall; apply hnot
  refine MacTagForgeryOrCollision.of_ownSaltGuess hctx hseed hk hmac hunk fun salt hsalt => ?_
  dsimp only; intro heq
  injection heq with hc hrest; injection hrest with hm hi
  exact hall ⟨salt, hsalt, hc, hm, hi⟩

/-- Monotonicity of `MacTagForgeryOrCollision` under `ctxs₁ ⊆ ctxs₂` and antitone `known`. -/
theorem MacTagForgeryOrCollision.mono_ctxs
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {known₁ known₂ : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg}
    {ctxs₁ ctxs₂ : List TrialCtx}
    (hctxs : ctxs₁ ⊆ ctxs₂) (hknown : ∀ u, known₂ u → known₁ u)
    (h : MacTagForgeryOrCollision interpretation S g known₁ honest msg ctxs₁) :
    MacTagForgeryOrCollision interpretation S g known₂ honest msg ctxs₂ := by
  rcases h with ⟨ctx, hctx, seed, hseed, k, hk, hmac, hunk, hne⟩ |
                ⟨ctx, hctx, seed, hseed, k, hk, hmac, ctx₀, hctx₀, seed₀, hseed₀, hγne, hbr₀⟩
  · exact MacTagForgeryOrCollision.of_ownSaltGuess (hctxs hctx) hseed hk hmac
      (fun hk₂ => hunk (hknown seed hk₂)) hne
  · rcases hbr₀ with ⟨salt₀, hsalt₀, hmac₀⟩ | ⟨peerIk₀, myIk₀, salt₀, w, hterm, hwire⟩
    · exact MacTagForgeryOrCollision.of_crossSeedBytes (hctxs hctx) hseed hk hmac
        (hctxs hctx₀) hseed₀ hγne hsalt₀ hmac₀
    · exact MacTagForgeryOrCollision.of_crossSeedTerm (hctxs hctx) hseed hk hmac
        (hctxs hctx₀) hseed₀ hγne hterm hwire

/-- Ghost-congruence (`gamma` transfer) for `MacTagForgeryOrCollision`. -/
theorem MacTagForgeryOrCollision.congr_gamma
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {known : DY.Bytes → Prop} {honest : List DY.Bytes} {msg : TRSignalMsg}
    {ctxs : List TrialCtx}
    (hmac_msg : gamma interpretation S g₁ msg.mac = gamma interpretation S g₂ msg.mac)
    (hwire_msg : gamma interpretation S g₁ msg.wire = gamma interpretation S g₂ msg.wire)
    (hseed_eq : ∀ ctx ∈ ctxs, ∀ seed, ctx.seed? = some seed →
      gamma interpretation S g₁ seed = gamma interpretation S g₂ seed)
    (hkeys_eq : ∀ ctx ∈ ctxs, ∀ seed, ctx.seed? = some seed →
      ∀ s ∈ ctx.ownSalts ++ honest,
        let mk := trMsgKeys s seed
        gamma interpretation S g₁ mk.cipherKey = gamma interpretation S g₂ mk.cipherKey ∧
        gamma interpretation S g₁ mk.macKey = gamma interpretation S g₂ mk.macKey ∧
        gamma interpretation S g₁ mk.iv = gamma interpretation S g₂ mk.iv ∧
        gamma interpretation S g₁ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire) =
          gamma interpretation S g₂ (computeMac mk.macKey ctx.peerIk ctx.myIk msg.wire))
    (hterm_wire : ∀ peerIk₀ myIk₀ salt₀ seed₀ w,
      msg.mac = computeMac (trMsgKeys salt₀ seed₀).macKey peerIk₀ myIk₀ w →
      gamma interpretation S g₁ w = gamma interpretation S g₂ w)
    (h : MacTagForgeryOrCollision interpretation S g₁ known honest msg ctxs) :
    MacTagForgeryOrCollision interpretation S g₂ known honest msg ctxs := by
  rcases h with ⟨ctx, hctx, seed, hseed, k, hk, hmac, hunk, hne⟩ |
                ⟨ctx, hctx, seed, hseed, k, hk, hmac, ctx₀, hctx₀, seed₀, hseed₀, hγne, hbr₀⟩
  · have hk_mem : k ∈ ctx.ownSalts ++ honest := List.mem_append_left _ hk
    obtain ⟨hk_c, hk_m, hk_i, hk_cmac⟩ := hkeys_eq ctx hctx seed hseed k hk_mem
    have hmac₂ : gamma interpretation S g₂
        (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
        gamma interpretation S g₂ msg.mac := by rw [← hk_cmac, hmac, hmac_msg]
    refine MacTagForgeryOrCollision.of_ownSaltGuess hctx hseed hk hmac₂ hunk ?_
    intro salt hsalt; dsimp only; intro heq₂
    obtain ⟨hs_c, hs_m, hs_i, _⟩ := hkeys_eq ctx hctx seed hseed salt (List.mem_append_right _ hsalt)
    apply hne salt hsalt; rw [hs_c, hs_m, hs_i, hk_c, hk_m, hk_i]; exact heq₂
  · have hk_mem : k ∈ ctx.ownSalts ++ honest := List.mem_append_left _ hk
    obtain ⟨_, _, _, hk_cmac⟩ := hkeys_eq ctx hctx seed hseed k hk_mem
    have hmac₂ : gamma interpretation S g₂
        (computeMac (trMsgKeys k seed).macKey ctx.peerIk ctx.myIk msg.wire) =
        gamma interpretation S g₂ msg.mac := by rw [← hk_cmac, hmac, hmac_msg]
    have hγne₂ : gamma interpretation S g₂ seed ≠ gamma interpretation S g₂ seed₀ := by
      rwa [← hseed_eq ctx hctx seed hseed, ← hseed_eq ctx₀ hctx₀ seed₀ hseed₀]
    rcases hbr₀ with ⟨salt₀, hsalt₀, hmac₀⟩ | ⟨peerIk₀, myIk₀, salt₀, w, hterm, hwire⟩
    · obtain ⟨_, _, _, hs₀_cmac⟩ := hkeys_eq ctx₀ hctx₀ seed₀ hseed₀ salt₀ hsalt₀
      have hmac₀₂ : gamma interpretation S g₂
          (computeMac (trMsgKeys salt₀ seed₀).macKey ctx₀.peerIk ctx₀.myIk msg.wire) =
          gamma interpretation S g₂ msg.mac := by rw [← hs₀_cmac, hmac₀, hmac_msg]
      exact MacTagForgeryOrCollision.of_crossSeedBytes hctx hseed hk hmac₂
        hctx₀ hseed₀ hγne₂ hsalt₀ hmac₀₂
    · have hwire₂ : gamma interpretation S g₂ w = gamma interpretation S g₂ msg.wire := by
        rw [← hterm_wire peerIk₀ myIk₀ salt₀ seed₀ w hterm, hwire, hwire_msg]
      exact MacTagForgeryOrCollision.of_crossSeedTerm hctx hseed hk hmac₂
        hctx₀ hseed₀ hγne₂ hterm hwire₂

/-! ## `whisperTrials` Membership and Congruence -/

theorem sinfo_exists_iff (st : DRState) (s : SessionInfo) :
    (∃ p, st.sessionInfo p = s) ↔ st.sessionInfo s.me = s :=
  ⟨fun ⟨_, h⟩ => h ▸ rfl, fun h => ⟨s.me, h⟩⟩

private def whisperChains (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    (st : TRState) (msg : TRSignalMsg) : List RecvChain :=
  (st.toDRState.recv.filter fun c =>
      decide (gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey)) ++
    match recvChainFor st.toDRState msg.ratchetKey with
    | some (c, true) => [c]
    | _ => []

private theorem mem_whisperChains_of_byteChain
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {msg : TRSignalMsg} {c : RecvChain}
    (hc : c ∈ st.toDRState.recv)
    (hγ : gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey) :
    c ∈ whisperChains interpretation S g st msg :=
  List.mem_append_left _ (List.mem_filter.mpr ⟨hc, decide_eq_true hγ⟩)

private theorem mem_whisperChains_of_freshChain
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {msg : TRSignalMsg} {c : RecvChain}
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, true)) :
    c ∈ whisperChains interpretation S g st msg := by
  unfold whisperChains
  rw [hrc]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

private theorem mem_whisperChains_of_recvChainFor
    {interpretation : ExternInterpretation} {S : OpaqueSymbolSemantics} {g : Ghost}
    {st : TRState} {msg : TRSignalMsg} {c : RecvChain} {fresh : Bool}
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, fresh)) :
    c ∈ whisperChains interpretation S g st msg := by
  cases fresh with
  | true => exact mem_whisperChains_of_freshChain hrc
  | false =>
    have hrc' := hrc
    unfold recvChainFor at hrc'
    cases hfind : findRecvChain st.toDRState.recv msg.ratchetKey with
    | some c₀ =>
      rw [hfind] at hrc'
      cases hrc'
      unfold findRecvChain at hfind
      have hc_mem : c ∈ st.toDRState.recv := List.mem_of_find?_eq_some hfind
      have hbeq := List.find?_some hfind
      exact mem_whisperChains_of_byteChain hc_mem
        (congrArg (gamma interpretation S g) (eq_of_beq hbeq))
    | none =>
      rw [hfind] at hrc'
      dsimp only at hrc'
      by_cases hlo : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey <;> simp [hlo] at hrc'

private theorem whisperTrials_mem_of_chain_none
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState} {c : RecvChain}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hc : c ∈ whisperChains interpretation S g st msg)
    (hcmk : consumeMessageKey c msg.counter = none) :
    ({ peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
       ownSalts := [], seed? := none } : TrialCtx) ∈
      whisperTrials interpretation r S g tr msg := by
  unfold whisperTrials; simp only [hver, ↓reduceIte]
  have hc' : c ∈ (st.toDRState.recv.filter fun c =>
      decide (gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey)) ++
      (match findRecvChain st.recv msg.ratchetKey,
             DY.Libsignal.TripleRatchet.recvHalfStep st.toDRState msg.ratchetKey with
       | none, some (_, c) => [c]
       | _, _ => []) := by
    unfold whisperChains recvChainFor at hc
    unfold DY.Libsignal.TripleRatchet.recvHalfStep
    cases h1 : findRecvChain st.recv msg.ratchetKey <;>
      cases h2 : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey <;>
      simpa [TRState.toDRState, h1, h2] using hc
  exact List.mem_flatMap.mpr ⟨st, hst, List.mem_append_left _ (List.mem_map.mpr ⟨c, hc', by simp [hcmk]⟩)⟩

private theorem whisperTrials_mem_of_chain_some
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState} {c c' : RecvChain} {seed : DY.Bytes}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hc : c ∈ whisperChains interpretation S g st msg)
    (hcmk : consumeMessageKey c msg.counter = some (seed, c')) :
    ({ peerIk := st.peerIk, myIk := st.myIk,
       extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
       ownSalts := ownKeys r tr st msg, seed? := some seed } : TrialCtx) ∈
      whisperTrials interpretation r S g tr msg := by
  unfold whisperTrials; simp only [hver, ↓reduceIte]
  have hc' : c ∈ (st.toDRState.recv.filter fun c =>
      decide (gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey)) ++
      (match findRecvChain st.recv msg.ratchetKey,
             DY.Libsignal.TripleRatchet.recvHalfStep st.toDRState msg.ratchetKey with
       | none, some (_, c) => [c]
       | _, _ => []) := by
    unfold whisperChains recvChainFor at hc
    unfold DY.Libsignal.TripleRatchet.recvHalfStep
    cases h1 : findRecvChain st.recv msg.ratchetKey <;>
      cases h2 : DY.Libsignal.TripleRatchet.x25519LowOrder msg.ratchetKey <;>
      simpa [TRState.toDRState, h1, h2] using hc
  exact List.mem_flatMap.mpr ⟨st, hst, List.mem_append_left _ (List.mem_map.mpr ⟨c, hc', by simp [hcmk]⟩)⟩

/-- Stored receive-chain trial (`consumeMessageKey = some (seed, c')`) matched by ratchet-key bytes. -/
theorem whisperTrials_mem_of_byteChain_some
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState} {c c' : RecvChain} {seed : DY.Bytes}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hc : c ∈ st.toDRState.recv)
    (hγ : gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey)
    (hcmk : consumeMessageKey c msg.counter = some (seed, c')) :
    ({ peerIk := st.peerIk, myIk := st.myIk,
       extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
       ownSalts := ownKeys r tr st msg, seed? := some seed } : TrialCtx) ∈
      whisperTrials interpretation r S g tr msg :=
  whisperTrials_mem_of_chain_some hver hst (mem_whisperChains_of_byteChain hc hγ) hcmk

/-- `recvChainFor` trial when `consumeMessageKey c msg.counter = none`. -/
theorem whisperTrials_mem_of_recvChainFor_none
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState} {c : RecvChain} {fresh : Bool}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, fresh))
    (hcmk : consumeMessageKey c msg.counter = none) :
    ({ peerIk := st.peerIk, myIk := st.myIk, extra := [c.chainKey],
       ownSalts := [], seed? := none } : TrialCtx) ∈
      whisperTrials interpretation r S g tr msg :=
  whisperTrials_mem_of_chain_none hver hst (mem_whisperChains_of_recvChainFor hrc) hcmk

/-- `recvChainFor` trial when `consumeMessageKey c msg.counter = some (seed, c')`. -/
theorem whisperTrials_mem_of_recvChainFor_some
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState} {c c' : RecvChain}
    {seed : DY.Bytes} {fresh : Bool}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, fresh))
    (hcmk : consumeMessageKey c msg.counter = some (seed, c')) :
    ({ peerIk := st.peerIk, myIk := st.myIk,
       extra := [c.chainKey, c'.chainKey] ++ skippedSeeds c msg.counter,
       ownSalts := ownKeys r tr st msg, seed? := some seed } : TrialCtx) ∈
      whisperTrials interpretation r S g tr msg :=
  whisperTrials_mem_of_chain_some hver hst (mem_whisperChains_of_recvChainFor hrc) hcmk

/-- Cached `SkippedKeyStored` trial in `whisperTrials`, matched by ratchet-key bytes and counter. -/
theorem whisperTrials_mem_of_skippedKeyStored
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState}
    {s : SessionInfo} {pk seed : DY.Bytes} {rIdx src idx : Nat}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hfind : (findRecvChain st.toDRState.recv pk).isSome = true)
    (hev : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk msg.counter seed rIdx src) idx)
    (hγ : gamma interpretation S g pk = gamma interpretation S g msg.ratchetKey) :
    ({ peerIk := st.peerIk, myIk := st.myIk, extra := [],
       ownSalts := if st.sessionInfo s.me = s then ownKeys r tr st msg else [],
       seed? := some seed } : TrialCtx) ∈
      whisperTrials interpretation r S g tr msg := by
  have hlt : idx < tr.length := DY.Trace.EventLoggedAt_implies_i_le_length _ idx tr hev
  have hget : tr.getEventAt TREvent idx =
      some (TREvent.SkippedKeyStored s pk msg.counter seed rIdx src) := by
    rwa [← DY.Trace.EventLoggedAt_eq_getEventAt]
  unfold whisperTrials; simp only [hver, ↓reduceIte]
  refine List.mem_flatMap.mpr ⟨st, hst, List.mem_append_right _ ?_⟩
  exact List.mem_filterMap.mpr ⟨idx, List.mem_range.mpr hlt, by simp [hget, hfind, hγ]⟩

/-- Owner-specialized `SkippedKeyStored` trial carrying `ownSalts = ownKeys r tr st msg`. -/
theorem whisperTrials_mem_of_skippedKeyStored_owner
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg} {st : TRState}
    {s : SessionInfo} {pk seed : DY.Bytes} {rIdx src idx : Nat}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hfind : (findRecvChain st.toDRState.recv pk).isSome = true)
    (howner : ∃ p, st.sessionInfo p = s)
    (hev : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk msg.counter seed rIdx src) idx)
    (hγ : gamma interpretation S g pk = gamma interpretation S g msg.ratchetKey) :
    ({ peerIk := st.peerIk, myIk := st.myIk, extra := [],
       ownSalts := ownKeys r tr st msg, seed? := some seed } : TrialCtx) ∈
      whisperTrials interpretation r S g tr msg := by
  have hsinfo : st.sessionInfo s.me = s := (sinfo_exists_iff st.toDRState s).mp howner
  have hmem := whisperTrials_mem_of_skippedKeyStored hver hst hfind hev hγ
  simpa only [hsinfo, ↓reduceIte] using hmem

/-- `c.chainKey` belongs to `(whisperTrials ...).flatMap (trialTerms salts msg)` whenever
`recvChainFor st.toDRState msg.ratchetKey = some (c, fresh)`. -/
theorem chainKey_mem_whisperTrialTerms_of_recvChainFor
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {salts : List DY.Bytes} {msg : TRSignalMsg}
    {st : TRState} {c : RecvChain} {fresh : Bool}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, fresh)) :
    c.chainKey ∈ (whisperTrials interpretation r S g tr msg).flatMap (trialTerms salts msg) := by
  cases hcmk : consumeMessageKey c msg.counter with
  | none =>
    exact mem_flatMap_trialTerms_of_mem_extra
      (whisperTrials_mem_of_recvChainFor_none hver hst hrc hcmk) (List.mem_singleton.mpr rfl)
  | some sc =>
    exact mem_flatMap_trialTerms_of_mem_extra
      (whisperTrials_mem_of_recvChainFor_some hver hst hrc hcmk) (by simp)

private theorem computeMac_mem_flatMap_trialTerms_eq {salts : List DY.Bytes} {msg : TRSignalMsg}
    {ctxs : List TrialCtx} {ctx : TrialCtx} {peerIk myIk seed salt : DY.Bytes}
    (hctx : ctx ∈ ctxs) (hp : ctx.peerIk = peerIk) (hm : ctx.myIk = myIk)
    (hseed : ctx.seed? = some seed) (hsalt : salt ∈ salts) :
    computeMac (trMsgKeys salt seed).macKey peerIk myIk msg.wire ∈
      ctxs.flatMap (trialTerms salts msg) := by
  rw [← hp, ← hm]
  exact List.mem_flatMap.mpr ⟨ctx, hctx, computeMac_mem_trialTerms hseed hsalt⟩

/-- Candidate MAC from `recvChainFor` and `salt ∈ salts` belongs to expanded `whisperTrials`. -/
theorem computeMac_mem_whisperTrialTerms_of_recvChainFor
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {salts : List DY.Bytes} {msg : TRSignalMsg}
    {st : TRState} {c c' : RecvChain} {seed salt : DY.Bytes} {fresh : Bool}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hrc : recvChainFor st.toDRState msg.ratchetKey = some (c, fresh))
    (hcmk : consumeMessageKey c msg.counter = some (seed, c')) (hsalt : salt ∈ salts) :
    computeMac (trMsgKeys salt seed).macKey st.peerIk st.myIk msg.wire ∈
      (whisperTrials interpretation r S g tr msg).flatMap (trialTerms salts msg) :=
  computeMac_mem_flatMap_trialTerms_eq
    (whisperTrials_mem_of_recvChainFor_some hver hst hrc hcmk) rfl rfl rfl hsalt

/-- Candidate MAC on a stored receive chain matched by ratchet-key bytes belongs to expanded `whisperTrials`. -/
theorem computeMac_mem_whisperTrialTerms_of_byteChain
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {salts : List DY.Bytes} {msg : TRSignalMsg}
    {st : TRState} {c c' : RecvChain} {seed salt : DY.Bytes}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hc : c ∈ st.toDRState.recv)
    (hγ : gamma interpretation S g c.ratchetKey = gamma interpretation S g msg.ratchetKey)
    (hcmk : consumeMessageKey c msg.counter = some (seed, c')) (hsalt : salt ∈ salts) :
    computeMac (trMsgKeys salt seed).macKey st.peerIk st.myIk msg.wire ∈
      (whisperTrials interpretation r S g tr msg).flatMap (trialTerms salts msg) :=
  computeMac_mem_flatMap_trialTerms_eq
    (whisperTrials_mem_of_byteChain_some hver hst hc hγ hcmk) rfl rfl rfl hsalt

/-- Candidate MAC on a cached `SkippedKeyStored` seed belongs to expanded `whisperTrials`. -/
theorem computeMac_mem_whisperTrialTerms_of_skippedKeyStored
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {tr : ExecTrace} {salts : List DY.Bytes} {msg : TRSignalMsg} {st : TRState}
    {s : SessionInfo} {pk seed salt : DY.Bytes} {rIdx src idx : Nat}
    (hver : msg.version = messageVersion) (hst : st ∈ availableStates r tr)
    (hfind : (findRecvChain st.toDRState.recv pk).isSome = true)
    (hev : tr.EventLoggedAt (TREvent.SkippedKeyStored s pk msg.counter seed rIdx src) idx)
    (hγ : gamma interpretation S g pk = gamma interpretation S g msg.ratchetKey)
    (hsalt : salt ∈ salts) :
    computeMac (trMsgKeys salt seed).macKey st.peerIk st.myIk msg.wire ∈
      (whisperTrials interpretation r S g tr msg).flatMap (trialTerms salts msg) :=
  computeMac_mem_flatMap_trialTerms_eq
    (whisperTrials_mem_of_skippedKeyStored hver hst hfind hev hγ) rfl rfl rfl hsalt

/-- Ghost-congruence of `whisperTrials` when `g₁` and `g₂` agree under `gamma` on `msg.ratchetKey`,
stored receive-chain ratchet keys, and logged `SkippedKeyStored` ratchet keys. -/
theorem whisperTrials_congr_gamma
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g₁ g₂ : Ghost}
    {tr : ExecTrace} {msg : TRSignalMsg}
    (hrk_msg : gamma interpretation S g₁ msg.ratchetKey = gamma interpretation S g₂ msg.ratchetKey)
    (hrk_recv : ∀ st ∈ availableStates r tr, ∀ c ∈ st.toDRState.recv,
      gamma interpretation S g₁ c.ratchetKey = gamma interpretation S g₂ c.ratchetKey)
    (hrk_skip : ∀ idx < tr.length, ∀ s pk n seed rIdx src,
      tr.getEventAt TREvent idx = some (TREvent.SkippedKeyStored s pk n seed rIdx src) →
      gamma interpretation S g₁ pk = gamma interpretation S g₂ pk) :
    whisperTrials interpretation r S g₁ tr msg =
      whisperTrials interpretation r S g₂ tr msg := by
  unfold whisperTrials
  split
  · refine List.flatMap_congr fun st hst => ?_
    dsimp only
    congr 1
    · congr 1
      congr 1
      refine List.filter_congr fun c hc => ?_
      rw [hrk_recv st hst c hc, hrk_msg]
    · refine List.filterMap_congr fun idx hidx => ?_
      have hlt : idx < tr.length := List.mem_range.mp hidx
      cases hget : tr.getEventAt TREvent idx with
      | none => rfl
      | some ev =>
        cases ev with
        | SkippedKeyStored s pk n seed rIdx src =>
          dsimp only
          rw [hrk_skip idx hlt s pk n seed rIdx src hget, hrk_msg]
        | _ => rfl
  · rfl

/-! ## `bobTrials`, `MemoCollisionOn`, and `RecvCollision` -/

/-- Bob's one-time prekey selection in `bobTrials`: `some none` when `p.preKeyId = none`,
`some (some (setupSecret r 6))` when `p.preKeyId` matches `r.opkId` with `r.withOpk = true`, and
`none` when `p.preKeyId` names an unknown one-time prekey id. -/
def bobOpk? (r : ProtocolSetup) (p : PreKeyFields) : Option (Option DY.Bytes) :=
  match p.preKeyId with
  | none => some none
  | some id => if r.withOpk && id == r.opkId then some (some (setupSecret r 6)) else none

/-- Bob's PQXDH handshake keys for selected `opk` and representation `x`. -/
def bobHandshakeKeys (r : ProtocolSetup) (opk : Option DY.Bytes) (x : PreKeyRep) : HandshakeKeys :=
  let ikA := setupPublic r 0
  let spk := setupSecret r 2
  let pqsk := setupSecret r 4
  let ss := (errToOption (DY.PQKem.kemDecap pqsk x.ct)).getD
    (DY.PQKem.kemRejKey pqsk x.ct)
  pqxdhKdf (pqxdhIkm (agree ikA spk) (agree x.ek (setupSecret r 1))
    (agree x.ek spk) (opk.map (agree x.ek ·)) ss)

/-- Bob's initial receiving chain for handshake `keys` and inner message `msg`. -/
def bobInitChain (r : ProtocolSetup) (keys : HandshakeKeys) (msg : TRSignalMsg) : RecvChain :=
  { ratchetKey := msg.ratchetKey,
    chainKey := (createChain keys.rk msg.ratchetKey (setupSecret r 2)).2, index := 0, rIdx := 2 }

/-- Pre-MAC handshake guard Boolean in `bobTrials`. -/
def bobTrialGuard (r : ProtocolSetup) (tr : ExecTrace) (p : PreKeyFields) (x : PreKeyRep)
    (msg : TRSignalMsg) (opk : Option DY.Bytes) : Bool :=
  let ekBytes := ((p.baseKey.take 33).drop 1).map BitVec.toNat
  let rkBytes := p.inner.senderRatchetKey.bytes.toList.map BitVec.toNat
  decide (DY.X25519.leValue ekBytes < DY.X25519.p25519) &&
    !DY.X25519.isLowOrderKey ekBytes &&
    !PQXDH.x25519LowOrder x.ek &&
    decide (msg.version = messageVersion) &&
    !DY.X25519.isLowOrderKey rkBytes &&
    !TripleRatchet.x25519LowOrder msg.ratchetKey &&
    opk.all fun s => !PQXDH.opkUsedB tr r.bob (DY.DiffieHellman.dhPk s)

theorem bobTrials_some_some {r : ProtocolSetup} {tr : ExecTrace} {p : PreKeyFields}
    {x : PreKeyRep} {msg : TRSignalMsg}
    {opk : Option DY.Bytes} {seed : DY.Bytes} {c' : RecvChain} (hopk : bobOpk? r p = some opk)
    (hguard : bobTrialGuard r tr p x msg opk = true)
    (hcmk : consumeMessageKey (bobInitChain r (bobHandshakeKeys r opk x) msg) msg.counter =
      some (seed, c')) :
    let keys := bobHandshakeKeys r opk x
    let c := bobInitChain r keys msg
    let own := ((DY.Spqr.spqrRecv (DY.Spqr.spqrInit keys.pqr DY.Libsignal.TripleRatchet.spqrB2A)
      msg.pqRatchet (preKeySpqrIndex p)).map (·.2)).toList
    bobTrials r tr p x msg =
      [{ peerIk := serializedIk (setupPublic r 0), myIk := serializedIk (setupPublic r 2),
         extra := [keys.rk, keys.ck, keys.pqr, c.chainKey, c'.chainKey] ++
           skippedSeeds c msg.counter, ownSalts := own, seed? := some seed }] := by
  unfold bobTrials ProtocolSetup.ikAPubTerm ProtocolSetup.ikBPubTerm
    ProtocolSetup.spkSecTerm ProtocolSetup.ikBSecTerm ProtocolSetup.pqskSecTerm
    ProtocolSetup.opkSecTerm
  change (match bobOpk? r p with
    | none => []
    | some opk => if !(bobTrialGuard r tr p x msg opk) then [] else _) = _
  rw [hopk]
  dsimp only
  rw [hguard]
  unfold bobInitChain bobHandshakeKeys at hcmk
  dsimp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hcmk ⊢
  rw [hcmk]; rfl

/-- Bob's candidate MAC under any `salt ∈ salts` belongs to `(bobTrials r tr p x msg).flatMap (trialTerms salts msg)`. -/
theorem computeMac_mem_bobTrialTerms
    {r : ProtocolSetup} {tr : ExecTrace} {salts : List DY.Bytes} {p : PreKeyFields}
    {x : PreKeyRep} {msg : TRSignalMsg}
    {opk : Option DY.Bytes} {seed salt : DY.Bytes} {c' : RecvChain}
    (hopk : bobOpk? r p = some opk)
    (hguard : bobTrialGuard r tr p x msg opk = true)
    (hcmk : consumeMessageKey (bobInitChain r (bobHandshakeKeys r opk x) msg) msg.counter =
      some (seed, c')) (hsalt : salt ∈ salts) :
    computeMac (trMsgKeys salt seed).macKey
        (serializedIk (setupPublic r 0)) (serializedIk (setupPublic r 2)) msg.wire ∈
      (bobTrials r tr p x msg).flatMap (trialTerms salts msg) := by
  rw [bobTrials_some_some hopk hguard hcmk]
  exact computeMac_mem_flatMap_trialTerms_eq (List.mem_singleton.mpr rfl) rfl rfl rfl hsalt

/-- Monotonicity of `MemoCollisionOn` under `newTerms` and `prefixTerms` inclusion when
`plaintextTerms` is unchanged and `known` is antitone. -/
theorem MemoCollisionOn.mono_quiet
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {known₁ known₂ : DY.Bytes → Prop} {tr₁ tr₂ : ExecTrace} {vis₁ vis₂ : List VisEntry}
    {newTerms₁ newTerms₂ newPts : List DY.Bytes}
    (hnew : newTerms₁ ⊆ newTerms₂) (hpref : prefixTerms r tr₁ vis₁ ⊆ prefixTerms r tr₂ vis₂)
    (hpts : plaintextTerms vis₁ = plaintextTerms vis₂) (hknown : ∀ u, known₂ u → known₁ u)
    (h : MemoCollisionOn interpretation r S g known₁ tr₁ vis₁ newTerms₁ newPts) :
    MemoCollisionOn interpretation r S g known₂ tr₂ vis₂ newTerms₂ newPts := by
  obtain ⟨x₁, hx₁, x₂, hx₂, hsh, hinj, hpt₁, hpt₂, hbytes⟩ := h
  have hx₁' : x₁ ∈ newTerms₂.flatMap (fun t => (gamma' interpretation S g t).memo) := by
    obtain ⟨t, ht, hx₁_t⟩ := List.mem_flatMap.mp hx₁
    exact List.mem_flatMap.mpr ⟨t, hnew ht, hx₁_t⟩
  have hx₂' : x₂ ∈ ((prefixTerms r tr₂ vis₂).flatMap fun t => (gamma' interpretation S g t).memo) ++
      newTerms₂.flatMap (fun t => (gamma' interpretation S g t).memo) := by
    rcases List.mem_append.mp hx₂ with hp | hn
    · obtain ⟨t, ht, hx₂_t⟩ := List.mem_flatMap.mp hp
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨t, hpref ht, hx₂_t⟩)
    · obtain ⟨t, ht, hx₂_t⟩ := List.mem_flatMap.mp hn
      exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨t, hnew ht, hx₂_t⟩)
  refine ⟨x₁, hx₁', x₂, hx₂', hsh, hinj, ?_, ?_, hbytes⟩
  · rw [← hpts]; intro hmem
    obtain ⟨hnmem, hai, hunk⟩ := hpt₁ hmem
    exact ⟨hnmem, hai, fun hk₂ => hunk (hknown x₂.1 hk₂)⟩
  · rw [← hpts]; intro hmem
    obtain ⟨hnmem, hai, hunk⟩ := hpt₂ hmem
    exact ⟨hnmem, hai, fun hk₂ => hunk (hknown x₁.1 hk₂)⟩

/-- Introduction of `RecvCollision` via `MacTagForgeryOrCollision` on a parsed `SignalMessage`. -/
theorem RecvCollision.of_ownSaltMacCollision
    {interpretation : ExternInterpretation} {r : ProtocolSetup} {S : OpaqueSymbolSemantics} {g : Ghost}
    {ms : List Move} {t : DY.Bytes} {msg : TRSignalMsg}
    (hparse : parseTrSignalMsg t = some msg)
    (hown : MacTagForgeryOrCollision interpretation S g
      (fun u => u.AttackerKnows (runTraceMoves r ms)) (honestSalts r ms) msg
      (whisperTrials interpretation r S g (runTraceMoves r ms) msg)) :
    RecvCollision interpretation r S g ms t := by
  unfold RecvCollision; simp [hparse, hown]

end Symbolic.Swarm.Stage1Trials
