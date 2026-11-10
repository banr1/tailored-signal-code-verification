/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.Stage1Kyber -- shake: keep
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import DY.Actions.ProtocolEvent
public import Symbolic.Proofs.Swarm.COMPOSED.CompInvDefs
public import Symbolic.Proofs.Swarm.CREF.TR.G1.WireShapeInj
import Symbolic.Proofs.Swarm.COMPOSED.CompHsClass
import Symbolic.Proofs.Swarm.COMPOSED.CompInv
import Symbolic.Proofs.Swarm.COMPOSED.CompPubInv
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonLocal
import Symbolic.Proofs.Swarm.CREF.TR.G1.HonestSpineRk
import Symbolic.Proofs.Swarm.CREF.TR.G1.OneSidedPeelDefs
import Symbolic.Proofs.Swarm.CREF.TROpen
import Symbolic.Proofs.Swarm.CREF.Cli.PureCRel -- shake: keep
import Symbolic.Proofs.Swarm.TRREF.B3DefsPure -- shake: keep
import Symbolic.Proofs.SR.RecvSpecWPure -- shake: keep
import Symbolic.Proofs.Refinement.RngFree.SendSpecPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.Cli.Rpk.RecvDecStepCommonPure -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.FreshSigma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.Leaks -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQGamma -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.PQModelRunNil -- shake: keep
import Symbolic.Proofs.Swarm.CREF.TR.RecvDec -- shake: keep
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.DYBridge.DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Actions.ProtocolEvent

/-!
# Honest Seed Shape Injectivity for Composed Sessions

Proves `honestSkelUniq_of_reachable_compat`, establishing that equal term shapes under `gamma'`
between an honest sender seed `(kdfCk st_s.cks).2` and a receiver seed `mkSeed` force term equality
on reachable composed traces.
-/

@[expose] public section

cref_hide_foreign_instances
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
open Symbolic.Swarm.CREF.TR hiding PureBinCanonSession PureRecordRepr SpqrSem at?_append_of_lt gamma_concat gamma_dhPk getLocalState_fst leValue_leBytes length_leBytes newRandoms_append_rnd p25519_lt p25519_pos runMoves_append runTrace_append runTrace_snoc runVis_append runVis_snoc run_bind_fst run_bind_snd uOf_leBytes uOf_lt

cref_open
cref_open_tr

open DY DY.Comparse DY.Literal DY.Libsignal
open DY.Libsignal.TripleRatchet (kdfCk)
open DY.Libsignal.TripleRatchet
open DY.Libsignal.HwEvents DY.Libsignal.Rust
open CryptoGames CryptoGames.HMAC CryptoGames.HKDF
open CryptoGames.LibsignalSession CryptoGames.LibsignalSessionApi
open CryptoVerification
open CryptoVerification.LibsignalTripleRatchet CryptoVerification.LibsignalProtoCodec
open CryptoVerification.E2E CryptoVerification.E2E.InMem CryptoVerification.E2E.Record
open CryptoVerification.E2E.Bin hiding RecordCanonical recordDeserializeOpenSpec encodeRecord
open CryptoVerification.E2E.Pqxdh.WireEntries
open CryptoVerification.E2E.Pqxdh.WireEntries.SymP3 hiding encodeRecord
open CryptoProofLib.Refinement (ExternInterpretation)
open Proofs.libsignal.Refinement Proofs.libsignal.RngG

open Proofs.libsignal.RngG.R3 Proofs.libsignal.RngG.CliPure.R3 Symbolic.Swarm.CREF Symbolic.Swarm.CREF.CliPure Symbolic.Swarm.CREF.CliPure.TR
open Symbolic.Swarm.CREF.TR.RecvDec (at?_append_of_lt)
open Symbolic.Swarm.CREF.TR.Pure
open Symbolic.Swarm.CREF.TR.FreshSigma hiding TREntry StEntry
open Symbolic.Swarm.CREF.CliPure.TR.RecvDecStep hiding at?_append_of_lt

unseal DY.Bytes in
private instance (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeRandom g) (concretizeAll interpretation S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

theorem gamma_randTerm32_at (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (idx : Nat) :
    gamma interpretation S g (randTerm idx 32) = g.σ idx 32 := by
  unfold gamma gamma' randTerm
  show ((({ timestamp := idx, size := 32 } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll interpretation S g)).bytes = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]; rfl

unseal DY.Bytes in
private theorem shape_randTerm32_at (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost) (idx : Nat) :
    (gamma' interpretation S g (randTerm idx 32)).shape = randTerm idx 32 := by
  unfold gamma' randTerm
  show ((({ timestamp := idx, size := 32 } : DY.Random.Random DY.Bytes).pack).rec (concretizeAll interpretation S g)).shape = _
  rw [DY.Bytes.rec_eq (concretizeRandom g) (concretizeAll interpretation S g)]; rfl

private theorem kemEncap_snd_eq_of_alice_bob
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t → (g.σ (t + 1) 32).length = 32)
    {pA pB pB' pA' : Participant}
    {ikA ikB spk pqpk ek ct ikB' ikA' spk' pqpk' ek' ct' pk₁ e₁ pk₂ e₂ : DY.Bytes}
    {opk opk' : Option DY.Bytes}
    {keys keys' : DY.Libsignal.PQXDH.HandshakeKeys} {jA jB : Nat}
    (hevA : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone pA pB ikA ikB spk pqpk opk ek ct keys) jA)
    (hevB : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone pB' pA' ikB' ikA' spk' pqpk' opk' ek' ct' keys') jB)
    (hct₁ : ct = (DY.PQKem.kemEncap pk₁ e₁).1)
    (hct₂ : ct' = (DY.PQKem.kemEncap pk₂ e₂).1)
    (hsh : (gamma' interpretation S g (DY.PQKem.kemEncap pk₁ e₁).2).shape =
      (gamma' interpretation S g (DY.PQKem.kemEncap pk₂ e₂).2).shape) :
    (DY.PQKem.kemEncap pk₁ e₁).2 = (DY.PQKem.kemEncap pk₂ e₂).2 := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable T hreach
  obtain ⟨t, sA, rfl, hSlot, _, _, _, hAgree, _⟩ :=
    hinv.aliceDone pA pB ikA ikB spk pqpk opk ek ct keys jA hevA
  have hct_alice : ct = (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).1 :=
    congrArg Prod.fst hAgree
  obtain ⟨rfl, rfl⟩ := Stage1Kyber.kemEncap_fst_inj (hct₁.symm.trans hct_alice)
  have h32 : (gamma interpretation S g (randTerm (t + 1) 32)).length = 32 := by
    rw [gamma_randTerm32_at]; exact hσ32 t hSlot
  obtain ⟨pk₂', e₂', heq₂, _, _, hsh_e₂⟩ :=
    Stage1Kyber.eq_kemSS_of_shape_eq_kemSS_len32 interpretation S g h32 hsh.symm
  obtain ⟨rfl, rfl⟩ := Stage1Kyber.kemEncap_snd_inj heq₂
  rw [shape_randTerm32_at] at hsh_e₂
  have he₂_eq : e₂ = randTerm (t + 1) 32 :=
    (Stage1Kyber.shape_eq_randTerm_iff interpretation S g e₂ (by decide)).mp hsh_e₂
  subst he₂_eq
  have hctB_ak : (DY.PQKem.kemEncap pk₂ (randTerm (t + 1) 32)).1.AttackerKnows T := by
    rw [← hct₂]
    exact (Symbolic.Swarm.CREF.TR.G1.Spine.bobDone_ct_pqpk_attackerKnows_of_reachable hreach hevB).1
  rcases Symbolic.Swarm.CREF.TR.G1.Spine.kemEncap_fst_attackerKnows_inv hreach hctB_ak with
    hcoins_ak | ⟨t', a', b', ikA'', ikB'', spk'', pqpk'', opk'', ek'', ct'', keys'', hevA', rfl, hrnd_eq⟩
  · exact False.elim (Symbolic.Swarm.COMPOSED.CompInv.not_pub_coins_of_spqrInv hinv hSlot
      (Symbolic.Swarm.COMPOSED.CompInv.pub_of_knows hinv hcoins_ak))
  · have ht_eq : t + 1 = t' + 1 := (Stage1Kyber.randTerm_inj hrnd_eq).1
    have ht_eq' : t' + 5 = t + 5 := by omega
    rw [ht_eq'] at hevA'
    have hev_eq := Symbolic.Swarm.COMPOSED.CompInv.BundleVerifyHelpers.evAt_unique hevA hevA'
    injection hev_eq with _ _ _ _ _ hpqpk_eq
    subst hpqpk_eq; rfl

private theorem alice_bob_kemLeaf_eq
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t → (g.σ (t + 1) 32).length = 32)
    {pA pB pB' pA' : Participant}
    {ikA ikB spk pqpk ek ct ikB' ikA' spk' pqpk' ek' ct' ss₁ ss₂ : DY.Bytes}
    {opk opk' : Option DY.Bytes}
    {keys keys' : DY.Libsignal.PQXDH.HandshakeKeys} {jA jB : Nat}
    (hevA : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.AliceDone pA pB ikA ikB spk pqpk opk ek ct keys) jA)
    (hevB : T.EventLoggedAt (DY.Libsignal.PQXDH.PQXDHEvent.BobDone pB' pA' ikB' ikA' spk' pqpk' opk' ek' ct' keys') jB)
    (hkem₁ : (∃ pk₁ e₁ : DY.Bytes, ct = (DY.PQKem.kemEncap pk₁ e₁).1 ∧ ss₁ = (DY.PQKem.kemEncap pk₁ e₁).2) ∨
      (∃ sk₁ : DY.Bytes, ss₁ = DY.PQKem.kemRejKey sk₁ ct))
    (hkeys₁ : ∃ a₁ b₁ c₁ d₁, keys = DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ ss₁))
    (hkem₂ : (∃ pk₂ e₂ : DY.Bytes, ct' = (DY.PQKem.kemEncap pk₂ e₂).1 ∧ ss₂ = (DY.PQKem.kemEncap pk₂ e₂).2) ∨
      (∃ sk₂ : DY.Bytes, ss₂ = DY.PQKem.kemRejKey sk₂ ct'))
    (hsh : (gamma' interpretation S g ss₁).shape = (gamma' interpretation S g ss₂).shape) :
    ss₁ = ss₂ := by
  rcases hkem₁ with ⟨pk₁, e₁, hct₁, rfl⟩ | ⟨sk₁, rfl⟩
  · rcases hkem₂ with ⟨pk₂, e₂, hct₂, rfl⟩ | ⟨sk₂, rfl⟩
    · exact kemEncap_snd_eq_of_alice_bob interpretation S g hreach hσ32 hevA hevB hct₁ hct₂ hsh
    · have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable T hreach
      obtain ⟨t, _, rfl, hSlot, _, _, _, hAgree, _⟩ :=
        hinv.aliceDone pA pB ikA ikB spk pqpk opk ek ct keys jA hevA
      obtain ⟨rfl, rfl⟩ := Stage1Kyber.kemEncap_fst_inj (hct₁.symm.trans (congrArg Prod.fst hAgree))
      have h32 : (gamma interpretation S g (randTerm (t + 1) 32)).length = 32 := by
        rw [gamma_randTerm32_at]; exact hσ32 t hSlot
      change (gamma' interpretation S g (DY.PQKem.kemEncap pk₁ (randTerm (t + 1) 32)).2).shape =
        (gamma' interpretation S g (DY.PQKem.kemRejKey sk₂ ct')).shape at hsh
      rw [Stage1Kyber.gamma'_kemSS_of_len32 interpretation S g h32,
          Stage1Kyber.gamma'_kemRejKey_eq interpretation S g sk₂ ct'] at hsh
      dsimp only [node, Stage1Kyber.kemRejKey_eq_pack] at hsh
      exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hsh)
  · have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable T hreach
    obtain ⟨t, sA, rfl, hSlot, _, _, _, hAgree, _⟩ :=
      hinv.aliceDone pA pB ikA ikB spk pqpk opk ek ct keys jA hevA
    obtain ⟨a₁, b₁, c₁, d₁, hk₁⟩ := hkeys₁
    have hk₂ : ∃ a₀ b₀ c₀ d₀,
        keys = DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm a₀ b₀ c₀ d₀
          (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2) := by
      rcases henc : DY.PQKem.kemEncap pqpk
          (Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd (t + 1) 32) with ⟨c₀, s₀⟩
      unfold DY.Libsignal.PQXDH.aliceAgreement at hAgree
      rw [henc] at hAgree
      simp only [Prod.mk.injEq] at hAgree
      have hrnd : Symbolic.Swarm.COMPOSED.CompKeyInversion.rnd (t + 1) 32 = randTerm (t + 1) 32 := rfl
      rw [hrnd] at henc
      have hs₀ : s₀ = (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2 := by rw [henc]
      exact ⟨_, _, _, _, hs₀ ▸ hAgree.2⟩
    obtain ⟨a₀, b₀, c₀, d₀, hk₂⟩ := hk₂
    have hrk : (DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ (DY.PQKem.kemRejKey sk₁ ct))).rk =
        (DY.Libsignal.PQXDH.pqxdhKdf (DY.Libsignal.PQXDH.pqxdhIkm a₀ b₀ c₀ d₀ (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2)).rk :=
      congrArg DY.Libsignal.PQXDH.HandshakeKeys.rk (hk₁.symm.trans hk₂)
    have hikm_eq : DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ (DY.PQKem.kemRejKey sk₁ ct) =
        DY.Libsignal.PQXDH.pqxdhIkm a₀ b₀ c₀ d₀ (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2 :=
      (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective (Symbolic.Swarm.CREF.TR.G1.kdfExtract_injective hrk).1).2
    have hikm_sh := congrArg (fun m => (gamma' interpretation S g m).shape) hikm_eq
    unfold DY.Libsignal.PQXDH.pqxdhIkm at hikm_sh
    obtain ⟨_, h1⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g hikm_sh
    obtain ⟨_, h2⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h1
    obtain ⟨_, h3⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h2
    obtain ⟨_, h4⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h3
    have hss_sh : (gamma' interpretation S g (DY.PQKem.kemRejKey sk₁ ct)).shape =
        (gamma' interpretation S g (DY.PQKem.kemEncap pqpk (randTerm (t + 1) 32)).2).shape := by
      cases d₁ <;> cases d₀ <;> dsimp only at h4
      · exact h4
      · exact absurd h4 (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g (.inr ⟨sk₁, ct, rfl⟩))
      · exact absurd h4.symm (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g (.inl ⟨_, _, rfl⟩))
      · exact (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h4).2
    have h32 : (gamma interpretation S g (randTerm (t + 1) 32)).length = 32 := by
      rw [gamma_randTerm32_at]; exact hσ32 t hSlot
    rw [Stage1Kyber.gamma'_kemRejKey_eq interpretation S g sk₁ ct,
        Stage1Kyber.gamma'_kemSS_of_len32 interpretation S g h32] at hss_sh
    dsimp only [node, Stage1Kyber.kemRejKey_eq_pack] at hss_sh
    exact False.elim (Symbolic.DYBridge.DY.BytesView.pack_ne_pack_of_proj_none hss_sh.symm)

private theorem ikm_eq_of_peel_at
    (interpretation : ExternInterpretation) (S : OpaqueSymbolSemantics) (g : Ghost)
    {T : ExecTrace} (hreach : T.Reachable DY.Libsignal.Composed.reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot T t → (g.σ (t + 1) 32).length = 32)
    {u₀ v₀ : DY.Bytes}
    (hhole : ∀ d₁ d₂ : DY.Bytes,
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.Peel u₀ v₀ d₁ d₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole d₁ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole d₂ →
      (gamma' interpretation S g d₁).shape = (gamma' interpretation S g d₂).shape → d₁ = d₂) :
    ∀ (c c' : Bool) (m₁ m₂ : DY.Bytes),
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.PeelKdf u₀ v₀ m₁ m₂ →
      Symbolic.Swarm.CREF.TR.G1.Spine.LoggedIkmR T c m₁ →
      Symbolic.Swarm.CREF.TR.G1.Spine.LoggedIkmR T c' m₂ →
      (c ^^ c') = true →
      (gamma' interpretation S g m₁).shape = (gamma' interpretation S g m₂).shape → m₁ = m₂ := by
  intro c c' m₁ m₂ hP hm₁ hm₂ hp h
  have hkem_leaf : ∀ {ct ss : DY.Bytes},
      ((∃ pk e : DY.Bytes, ct = (DY.PQKem.kemEncap pk e).1 ∧ ss = (DY.PQKem.kemEncap pk e).2) ∨
        (∃ sk : DY.Bytes, ss = DY.PQKem.kemRejKey sk ct)) →
      Symbolic.Swarm.CREF.TR.G1.ShapeModKem.KemLeaf ss := by
    rintro ct ss (⟨pk, e, _, rfl⟩ | ⟨sk, rfl⟩)
    · exact .inl ⟨pk, e, rfl⟩
    · exact .inr ⟨sk, ct, rfl⟩
  have hpeel : ∀ {ss₁ a₁ b₁ c₁ : DY.Bytes} {d₁ : Option DY.Bytes}
      {ss₂ a₂ b₂ c₂ : DY.Bytes} {d₂ : Option DY.Bytes},
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.PeelKdf u₀ v₀
        (DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ ss₁)
        (DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ c₂ d₂ ss₂) →
      Symbolic.Swarm.CREF.TR.G1.ShapeModKem.KemLeaf ss₁ →
      Symbolic.Swarm.CREF.TR.G1.ShapeModKem.KemLeaf ss₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole a₁ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole b₁ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole c₁ →
      (∀ x, d₁ = some x → Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole x) →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole a₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole b₂ →
      Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole c₂ →
      (∀ x, d₂ = some x → Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole x) →
      ((gamma' interpretation S g ss₁).shape =
        (gamma' interpretation S g ss₂).shape → ss₁ = ss₂) →
      (gamma' interpretation S g
        (DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ ss₁)).shape =
      (gamma' interpretation S g
        (DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ c₂ d₂ ss₂)).shape →
      DY.Libsignal.PQXDH.pqxdhIkm a₁ b₁ c₁ d₁ ss₁ =
        DY.Libsignal.PQXDH.pqxdhIkm a₂ b₂ c₂ d₂ ss₂ := by
    intro ss₁ a₁ b₁ c₁ d₁ ss₂ a₂ b₂ c₂ d₂ hP' hkl₁ hkl₂ ha₁ hb₁ hc₁ hd₁ ha₂ hb₂ hc₂ hd₂ hleaf hsh
    unfold DY.Libsignal.PQXDH.pqxdhIkm at hsh
    obtain ⟨_, h1⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g hsh
    obtain ⟨sha, h2⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h1
    obtain ⟨shb, h3⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h2
    obtain ⟨she, h4⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h3
    have ha : a₁ = a₂ := hhole _ _ (.ikmDh1 hP'.peel) ha₁ ha₂ sha
    have hb : b₁ = b₂ := hhole _ _ (.ikmDh2 hP'.peel) hb₁ hb₂ shb
    have he : c₁ = c₂ := hhole _ _ (.ikmDh3 hP'.peel) hc₁ hc₂ she
    subst ha hb he
    cases d₁ with
    | none =>
      cases d₂ with
      | none => rw [hleaf h4]
      | some v₂ =>
        exact False.elim (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g hkl₁ h4)
    | some v₁ =>
      cases d₂ with
      | none =>
        exact False.elim (Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_kemLeaf_ne_concat
          interpretation S g hkl₂ h4.symm)
      | some v₂ =>
        obtain ⟨shd, hss⟩ := Symbolic.Swarm.CREF.TR.G1.ShapeModKem.shape_concat_inj interpretation S g h4
        have hd : v₁ = v₂ := hhole _ _ (.ikmDh4 hP'.peel) (hd₁ v₁ rfl) (hd₂ v₂ rfl) shd
        subst hd
        rw [hleaf hss]
  cases c <;> cases c'
  · cases hp
  · obtain ⟨evA, ⟨jA, ⟨evA'⟩, hatA, rfl⟩, hdA⟩ := hm₁
    obtain ⟨evB, ⟨jB, ⟨evB'⟩, hatB, rfl⟩, hdB⟩ := hm₂
    cases evA' <;> try exact hdA.elim
    cases evB' <;> try exact hdB.elim
    rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hatA hatB
    obtain ⟨ss₁, a₁, b₁, c₁, d₁, hkem₁, rfl, hkeys₁, ha₁, hb₁, hc₁, hd₁⟩ := hdA
    obtain ⟨ss₂, a₂, b₂, c₂, d₂, hkem₂, rfl, _, ha₂, hb₂, hc₂, hd₂⟩ := hdB
    exact hpeel hP (hkem_leaf hkem₁) (hkem_leaf hkem₂) ha₁ hb₁ hc₁ hd₁ ha₂ hb₂ hc₂ hd₂
      (alice_bob_kemLeaf_eq interpretation S g hreach hσ32 hatA hatB hkem₁ ⟨a₁, b₁, c₁, d₁, hkeys₁⟩ hkem₂) h
  · obtain ⟨evB, ⟨jB, ⟨evB'⟩, hatB, rfl⟩, hdB⟩ := hm₁
    obtain ⟨evA, ⟨jA, ⟨evA'⟩, hatA, rfl⟩, hdA⟩ := hm₂
    cases evB' <;> try exact hdB.elim
    cases evA' <;> try exact hdA.elim
    rw [← Symbolic.DYBridge.DY.Trace.EventLoggedAt_eq_1] at hatA hatB
    obtain ⟨ss₁, a₁, b₁, c₁, d₁, hkem₁, rfl, _, ha₁, hb₁, hc₁, hd₁⟩ := hdB
    obtain ⟨ss₂, a₂, b₂, c₂, d₂, hkem₂, rfl, hkeys₂, ha₂, hb₂, hc₂, hd₂⟩ := hdA
    exact hpeel hP (hkem_leaf hkem₁) (hkem_leaf hkem₂) ha₁ hb₁ hc₁ hd₁ ha₂ hb₂ hc₂ hd₂
      (fun hss => (alice_bob_kemLeaf_eq interpretation S g hreach hσ32 hatA hatB hkem₂ ⟨a₂, b₂, c₂, d₂, hkeys₂⟩ hkem₁ hss.symm).symm) h
  · cases hp

theorem honestSkelUniq_of_reachable_compat
    (interpretation : ExternInterpretation) (r : ProtocolSetup) (S : OpaqueSymbolSemantics) (g : Ghost) (ms : List Move)
    (hreach : (runTraceMoves r ms).Reachable reachability)
    (hσ32 : ∀ t, Symbolic.Swarm.COMPOSED.CompInv.AliceSlot (runTraceMoves r ms) t → (g.σ (t + 1) 32).length = 32)
    {st_s st₀ : TRState}
    (hst_s : st_s ∈ availableStates r (runTraceMoves r ms))
    (hst₀ : st₀ ∈ availableStates r (runTraceMoves r ms))
    {msg₀ : TRSignalMsg} {mkSeed : DY.Bytes}
    (hseed : recvSeed st₀ msg₀ = some mkSeed)
    (hshape : (gamma' interpretation S g (kdfCk st_s.cks).2).shape =
      (gamma' interpretation S g mkSeed).shape) :
    (kdfCk st_s.cks).2 = mkSeed :=
  let hhole := fun d₁ d₂ hP hd₁ (_ : Symbolic.Swarm.CREF.TR.G1.SpineIkm.DhHole d₂)
      (_ : (gamma' interpretation S g d₁).shape = (gamma' interpretation S g d₂).shape) =>
    Symbolic.Swarm.CREF.TR.G1.Spine.hdh_of_spineRk interpretation S g
      (Symbolic.Swarm.CREF.TR.G1.Spine.ikAt_spkAt_false (runTraceMoves r ms))
      (Symbolic.Swarm.CREF.TR.G1.Spine.ekAt_ikAt_false (runTraceMoves r ms))
      (Symbolic.Swarm.CREF.TR.G1.Spine.ekAt_spkAt_false (runTraceMoves r ms))
      (Symbolic.Swarm.CREF.TR.G1.Spine.ekAt_opkAt_false (runTraceMoves r ms))
      (fun _ _ h => Symbolic.Swarm.CREF.TR.G1.Spine.loggedIkmRk_roleHoles h)
      rfl
      (Symbolic.Swarm.CREF.TR.G1.Spine.spineRk_send_runTrace hst_s)
      (Symbolic.Swarm.CREF.TR.G1.Spine.spineRk_recvSeed_runTrace hst₀ hseed)
      hshape d₁ d₂ hP hd₁
  Symbolic.Swarm.CREF.TR.G1.Spine.seed_eq_of_shape_eq_peel interpretation r S g ms hst_s hst₀ hseed
    hhole (ikm_eq_of_peel_at interpretation S g hreach hσ32 hhole) hshape

end Symbolic.Swarm.CREF.CliPure.TR.RecvDecStepAt
