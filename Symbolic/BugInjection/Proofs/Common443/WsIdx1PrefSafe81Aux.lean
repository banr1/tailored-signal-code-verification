/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40Aux
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts

@[expose] public section
set_option autoImplicit false
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81Aux
open ByteSpecs open CryptoProofLib.Refinement (ExternInterpretation)
open DY DY.Libsignal DY.Libsignal.HwEvents DY.Libsignal.Refinement DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompFitsNames Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix81EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40Aux Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40
export Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40 (seg0_eq setup_aliceId_untagged4 setup_bobId_untagged4 setup_spk_untagged4)
open Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
attribute [local irreducible] setupPublic setupSecret
abbrev evPtAt := WsIdx1PrefSafe40.ptAt
abbrev evRngAt := rngAt
theorem seg43_eq : seg 43 35 = .recv (wireAt 43) :: (seg 43 35).tail := rfl
theorem seg43_tail_safe : ∀ e ∈ (seg 43 35).tail, RngEventSafe e := by decide
theorem seg43_tail_ne_fillFresh64 : ∀ b : HwBytes, .rng b ∈ (seg 43 35).tail → ∀ t ∈ ([11, 16, 17] : List Nat), b ≠ fillFresh t 64 := fun b hb => (seg43_tail_safe (.rng b) hb).1
theorem seg43_tail_untagged4 : ∀ b : HwBytes, .rng b ∈ (seg 43 35).tail → Untagged4 b := fun b hb => (seg43_tail_safe (.rng b) hb).2
theorem rngAt41_ne_fillFresh64 :
    ∀ t ∈ ([11, 16, 17] : List Nat), evRngAt 41 ≠ fillFresh t 64 := by decide
theorem rngAt41_untagged4 : Untagged4 (evRngAt 41) := by decide
theorem ptAt78_len_ne_64 : (evPtAt 78).length ≠ 64 := by decide
theorem ptAt78_untagged4 : Untagged4 (evPtAt 78) := by decide
set_option maxRecDepth 200000 in
theorem rngAt79_ne_fillFresh64 :
    ∀ t ∈ ([11, 16, 17] : List Nat), evRngAt 79 ≠ fillFresh t 64 := by decide
set_option maxRecDepth 200000 in theorem rngAt79_untagged4 : Untagged4 (evRngAt 79) := by decide
theorem compKyberE2_untagged4 : Untagged4 compKyberE2 := by decide
theorem spqrRecv_fst_eq {st m : DY.Bytes} {idx : UInt32} {spqr' : DY.Bytes} (h : (DY.Spqr.spqrRecv st m idx).map Prod.fst = some spqr') : spqr' = ({ st := st, msg := m } : DY.Spqr.RecvState.SubF DY.Bytes).pack := by
  unfold DY.Spqr.spqrRecv at h; split at h; · cases h
  cases hv : st.view? DY.Spqr.InitState.SubF with
  | none => rw [hv] at h; injection h with h'; exact h'.symm
  | some x =>
    rw [hv] at h; rcases x with ⟨authKey, params⟩; dsimp only at h
    cases hd : DY.Spqr.spqrParamsDir? params with
    | none => rw [hd] at h; cases h
    | some dir => rw [hd] at h; injection h with h'; exact h'.symm
section UnsealBytes
theorem freshSafeTerm_spqrRecv_fst {i : ExternInterpretation} {S : Sem} {g : Ghost} {st m : DY.Bytes} {idx : UInt32} {spqr' : DY.Bytes} (h : (DY.Spqr.spqrRecv st m idx).map Prod.fst = some spqr') (hst : CompFreshDistinct.FreshSafeTerm i S g st) (hm : CompFreshDistinct.FreshSafeTerm i S g m) : CompFreshDistinct.FreshSafeTerm i S g spqr' := by
  rw [spqrRecv_fst_eq h]
  refine freshSafeTerm_of_opaqueNode (ts := [st, m]) ?_
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hm))
  unfold gamma'; rw [DY.Bytes.rec_eq (gSpqrRecvState S) (gAll i S g)]; rfl
theorem randUntaggedTerm_spqrRecv_fst {i : ExternInterpretation} {S : Sem} {g : Ghost} {st m : DY.Bytes} {idx : UInt32} {spqr' : DY.Bytes} (h : (DY.Spqr.spqrRecv st m idx).map Prod.fst = some spqr') (hst : RandUntaggedTerm i S g st) (hm : RandUntaggedTerm i S g m) : RandUntaggedTerm i S g spqr' := by
  rw [spqrRecv_fst_eq h]
  refine randUntaggedTerm_of_opaqueNode (ts := [st, m]) ?_
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hm))
  unfold gamma'; rw [DY.Bytes.rec_eq (gSpqrRecvState S) (gAll i S g)]; rfl
end UnsealBytes
theorem freshSafeTerm_chainKeyAt {S : Sem} {g : Ghost} :
    ∀ (steps : Nat) {ck : DY.Bytes}, CompFreshDistinct.FreshSafeTerm compI0 S g ck → CompFreshDistinct.FreshSafeTerm compI0 S g (DY.Libsignal.TripleRatchet.chainKeyAt ck steps)
  | 0, _, hck => hck
  | steps + 1, _, hck => freshSafeTerm_chainKeyAt steps (freshSafeTerm_kdfCk hck).1
theorem randUntaggedTerm_chainKeyAt {i : ExternInterpretation} {S : Sem} {g : Ghost} :
    ∀ (steps : Nat) {ck : DY.Bytes}, RandUntaggedTerm i S g ck → RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.chainKeyAt ck steps)
  | 0, _, hck => hck
  | steps + 1, _, hck => randUntaggedTerm_chainKeyAt steps (randUntaggedTerm_kdfCk hck).1
theorem freshSafeTerm_serBob_bobSt81 {r : Records} {S : Sem} {g : Ghost} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ st_spqr : DY.Libsignal.TripleRatchet.TRState} {tr_enc tr_bob : ExecTrace} {cl : Nat} {spqrMsgIdx₂ ctr₂ : UInt32} {spqr₂' : DY.Bytes} (hb_ne : r.bob.toUTF8.size ≠ 64) (ha_ne : r.alice.toUTF8.size ≠ 64) (hpub0_f : CompFreshDistinct.FreshSafeTerm compI0 S g (setupPublic r 0)) (hpub2_f : CompFreshDistinct.FreshSafeTerm compI0 S g (setupPublic r 2)) (hsec2_f : CompFreshDistinct.FreshSafeTerm compI0 S g (setupSecret r 2)) (hrk₁_f : CompFreshDistinct.FreshSafeTerm compI0 S g o₁.keys.rk) (hpqr₁_f : CompFreshDistinct.FreshSafeTerm compI0 S g o₁.keys.pqr) (hdhs₁_f : CompFreshDistinct.FreshSafeTerm compI0 S g stA₁.dhs) (hst_spqr_f : CompFreshDistinct.FreshSafeTerm compI0 S g st_spqr.spqr) (hcoins_f : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm (tr_enc.length + 1) cl)) (hγ_bob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) (hspqr₂ : (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend st_spqr.spqr (randTerm (tr_enc.length + 1) cl)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') : CompFreshDistinct.FreshSafeTerm compI0 S g (serBob r (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' ctr₂)) := by
  have hσ_bob : g.σ tr_bob.length 32 = evRngAt 41 := by
    rw [← gamma_randTerm_eq_of_ne_zero compI0 S g tr_bob.length 32 (by decide)]; exact hγ_bob
  have hdhs_bob_f := freshSafeTerm_randTerm_of_ne_fillFresh64 compI0 S g tr_bob.length 32 (hσ_bob ▸ rngAt41_ne_fillFresh64); have hrt₂_f := freshSafeTerm_dhPk hdhs₁_f
  have hrt₂_key_f : CompFreshDistinct.FreshSafeTerm compI0 S g
      (DY.X25519.x25519Key (DY.DiffieHellman.dhPk stA₁.dhs)) := by rw [x25519Key_dhPk]; exact hrt₂_f
  have hcc1 := freshSafeTerm_createChain hrk₁_f hrt₂_key_f hsec2_f; have hcc2 := freshSafeTerm_createChain hcc1.1 hrt₂_key_f hdhs_bob_f
  have hspqr₂_f := freshSafeTerm_spqrRecv_fst hspqr₂
    (freshSafeTerm_spqrInit hpqr₁_f (freshSafeTerm_lit_of_length_ne_64 compI0 S g _ (by decide)))
    (freshSafeTerm_spqrSendMsg hst_spqr_f hcoins_f)
  have hsid_f : CompFreshDistinct.FreshSafeTerm compI0 S g
      (DY.Concat.concat (DY.X25519.x25519Key (DY.DiffieHellman.dhPk stA₁.dhs)) o₁.keys.rk) := by
    rw [x25519Key_dhPk]; exact freshSafeTerm_sid hdhs₁_f hrk₁_f
  exact freshSafeTerm_serialize_local_tr_of_ck_hmac r.bob _ hb_ne ha_ne (freshSafeTerm_serializedIk compI0 S g hpub2_f) (freshSafeTerm_serializedIk compI0 S g hpub0_f) hcc2.1 hdhs_bob_f hcc2.2 hsid_f hspqr₂_f rfl hrt₂_f
    (freshSafeTerm_kdfCk (freshSafeTerm_chainKeyAt ctr₂.toNat hcc1.2)).1 ⟨_, _, rfl⟩ (by dsimp only; decide)
theorem randUntaggedTerm_serBob_bobSt81 {r : Records} {S : Sem} {g : Ghost} {o₁ : DY.Libsignal.PQXDH.AliceHandshakeOut} {stA₁ st_spqr : DY.Libsignal.TripleRatchet.TRState} {tr_enc tr_bob : ExecTrace} {cl : Nat} {spqrMsgIdx₂ ctr₂ : UInt32} {spqr₂' : DY.Bytes} (hpub0_u : RandUntaggedTerm compI0 S g (setupPublic r 0)) (hpub2_u : RandUntaggedTerm compI0 S g (setupPublic r 2)) (hsec2_u : RandUntaggedTerm compI0 S g (setupSecret r 2)) (hrk₁_u : RandUntaggedTerm compI0 S g o₁.keys.rk) (hpqr₁_u : RandUntaggedTerm compI0 S g o₁.keys.pqr) (hdhs₁_u : RandUntaggedTerm compI0 S g stA₁.dhs) (hst_spqr_u : RandUntaggedTerm compI0 S g st_spqr.spqr) (hcoins_u : RandUntaggedTerm compI0 S g (randTerm (tr_enc.length + 1) cl)) (hγ_bob : gamma compI0 S g (randTerm tr_bob.length 32) = bobRng41Bytes) (hspqr₂ : (DY.Spqr.spqrRecv (DY.Spqr.spqrInit o₁.keys.pqr DY.Libsignal.TripleRatchet.spqrB2A) (DY.Spqr.spqrSend st_spqr.spqr (randTerm (tr_enc.length + 1) cl)).2.2 spqrMsgIdx₂).map Prod.fst = some spqr₂') : RandUntaggedTerm compI0 S g (serBob r (bobSt81 r o₁ tr_bob (DY.DiffieHellman.dhPk stA₁.dhs) spqr₂' ctr₂)) := by
  have hdhs_bob_u := randUntaggedTerm_randTerm_of_gamma_eq hγ_bob rngAt41_untagged4; have hrt₂_u := randUntaggedTerm_dhPk hdhs₁_u
  have hrt₂_key_u : RandUntaggedTerm compI0 S g
      (DY.X25519.x25519Key (DY.DiffieHellman.dhPk stA₁.dhs)) := by rw [x25519Key_dhPk]; exact hrt₂_u
  have hcc1_u := randUntaggedTerm_createChain hrk₁_u hrt₂_key_u hsec2_u; have hcc2_u := randUntaggedTerm_createChain hcc1_u.1 hrt₂_key_u hdhs_bob_u; have hspqr₂_u := randUntaggedTerm_spqrRecv_fst hspqr₂ (randUntaggedTerm_spqrInit hpqr₁_u (randUntaggedTerm_lit compI0 S g _)) (randUntaggedTerm_spqrSendMsg hst_spqr_u hcoins_u)
  refine randUntaggedTerm_serialize_local_tr
    { myIk := randUntaggedTerm_serializedIk hpub2_u, peerIk := randUntaggedTerm_serializedIk hpub0_u
      rk := hcc2_u.1, dhs := hdhs_bob_u, cks := hcc2_u.2, sid := randUntaggedTerm_concat hrt₂_key_u hrk₁_u
      spqr := hspqr₂_u, recv := fun d hd => by
        simp only [bobSt81, List.mem_singleton] at hd; subst hd
        exact ⟨hrt₂_u, (randUntaggedTerm_kdfCk (randUntaggedTerm_chainKeyAt ctr₂.toNat hcc1_u.2)).1⟩ }
end Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe81Aux
