/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum
public import Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore
public import Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh
public import Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts
public import Symbolic.BugInjection.Proofs.Common443.CompFitsNames
public import Symbolic.BugInjection.Proofs.Cheval26WeakStateIdx1.TraceFacts
import Symbolic.DYBridge.DY.Bytes.Basic

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
cref_hide_foreign_instances
namespace Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40Aux
open CryptoProofLib.Refinement (ExternInterpretation) open DY.Libsignal (HwBytes) open DY.Libsignal.HwEvents (MachineEvent)
open DY DY.Libsignal.Composed DY.Libsignal.Composed.Refinement Symbolic.BugInjection Symbolic.BugInjection.Disproofs.Hyp.FrozenSSC.Interp0 Symbolic.BugInjection.Witnesses.Cheval26WeakStateIdx1 Symbolic.BugInjection.Proofs.Common443.Census443Defs Symbolic.BugInjection.Proofs.Common443.CompExcuse Symbolic.BugInjection.Proofs.Common443.CompFreshDistinct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvStruct Symbolic.BugInjection.Proofs.Common443.CompPrefixInvAlice Symbolic.BugInjection.Proofs.Common443.CompPrefixInvBundle Symbolic.BugInjection.Proofs.Common443.CompPrefixInvEnc Symbolic.BugInjection.Proofs.Common443.CompPrefixInvSwap Symbolic.BugInjection.Proofs.Common443.CompPrefixInvFresh Symbolic.BugInjection.Proofs.Common443.CompRX0NBSC38Parts Symbolic.BugInjection.Proofs.Common443.CompFitsNames Symbolic.BugInjection.Proofs.Common443.WsIdx1CensusDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1DecompCore Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40EnumDefs Symbolic.BugInjection.Proofs.Common443.WsIdx1Prefix40Enum Symbolic.Swarm.CREF Symbolic.Swarm.COMPOSED Symbolic.Swarm.COMPOSED.CompTrace
attribute [local irreducible] setupPublic setupSecret
private theorem bytesLike_length_hmac (k m : DY.Bytes) : Comparse.BytesLike.length (DY.Libsignal.TripleRatchet.hmac k m) = 32 :=
  Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.length_hmac_symbolic_bridge k m
theorem freshSafeTerm_serialize_local_tr_of_ck_hmac {S : Sem} {g : Ghost} (part : Participant) (st : DY.Libsignal.TripleRatchet.TRState) {c₀ : DY.Libsignal.TripleRatchet.RecvChain} (hpart : part.toUTF8.size ≠ 64) (hpeer : st.peer.toUTF8.size ≠ 64) (hmyIk : CompFreshDistinct.FreshSafeTerm compI0 S g st.myIk) (hpeerIk : CompFreshDistinct.FreshSafeTerm compI0 S g st.peerIk) (hrk : CompFreshDistinct.FreshSafeTerm compI0 S g st.rk) (hdhs : CompFreshDistinct.FreshSafeTerm compI0 S g st.dhs) (hcks : CompFreshDistinct.FreshSafeTerm compI0 S g st.cks) (hsid : CompFreshDistinct.FreshSafeTerm compI0 S g st.sid) (hspqr : CompFreshDistinct.FreshSafeTerm compI0 S g st.spqr) (hrecv : st.recv = [c₀]) (hcrk : CompFreshDistinct.FreshSafeTerm compI0 S g c₀.ratchetKey) (hcck : CompFreshDistinct.FreshSafeTerm compI0 S g c₀.chainKey) (hcck_eq : ∃ k m, c₀.chainKey = DY.Libsignal.TripleRatchet.hmac k m) (hrIdx : c₀.rIdx < 27) : CompFreshDistinct.FreshSafeTerm compI0 S g (Comparse.serialize (⟨part, st⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) := by
  let ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState := ⟨part, st⟩
  obtain ⟨k, m, hkm⟩ := hcck_eq; have hcck_len : (gamma compI0 S g c₀.chainKey).length = 32 := hkm ▸ gamma_hmac_length S g k m; have hcck_ne : gamma compI0 S g c₀.chainKey ≠ List.replicate 32 0#8 := hkm ▸ gamma_hmac_ne_zero32 S g k m; have hcck_bl : Comparse.BytesLike.length c₀.chainKey = 32 := hkm ▸ bytesLike_length_hmac k m
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list
        (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize
        ls.state.recv) := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls
  have h0 : ((Comparse.ExtensibleMessageFormat.list
      (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize [c₀]) =
      Comparse.concatPrefixes ((Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize c₀)
        (DY.Literal.literalToBytes .empty) := by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil]
  have hser_c : (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize c₀ = Comparse.NonExtensibleMessageFormat.slowBytes.serialize c₀.ratchetKey ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize c₀.chainKey ++ (Comparse.NonExtensibleMessageFormat.uint32.serialize c₀.index ++
            Comparse.NonExtensibleMessageFormat.slowNat.serialize c₀.rIdx)) :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq c₀
  have hsb : Comparse.NonExtensibleMessageFormat.slowBytes.serialize c₀.chainKey =
      Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length c₀.chainKey) ++ [c₀.chainKey] :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq c₀.chainKey
  rw [hser, hrecv, h0, hser_c, ← concatPrefixes_append, ← concatPrefixes_append, concatPrefixes_append]
  have hempty := freshSafeTerm_lit_of_length_ne_64 compI0 S g .empty (by decide)
  have hempty_len := gamma_literalToBytes_length compI0 S g .empty
  have hs2_len : (gamma compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize c₀.index ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize c₀.rIdx) (DY.Literal.literalToBytes .empty))).length = c₀.rIdx + 5 := by have hbe : ByteArray.empty.size = 0 := rfl; rw [gamma_concatPrefixes, List.flatMap_append, List.length_append, List.length_append, gamma_uint32_serialize_length, gamma_slowNat_serialize_length, hempty_len]; omega
  have hs2 : CompFreshDistinct.FreshSafeTerm compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize c₀.index ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize c₀.rIdx)
        (DY.Literal.literalToBytes .empty)) :=
    freshSafeTerm_concatPrefixes_of_length_lt_64 _
      (fun _ hp => (List.mem_append.mp hp).elim (freshSafeTerm_mem_uint32 compI0 S g c₀.index)
        (freshSafeTerm_mem_slowNat compI0 S g c₀.rIdx)) hempty (by omega)
  have hs3 := freshSafeTerm_concatPrefixes_slowBytes_mid32 hcck hs2 hcck_len hcck_ne (by rw [hcck_len, hs2_len]; omega)
  have hs3_gt : 64 < (gamma compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowBytes.serialize c₀.chainKey) (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.uint32.serialize c₀.index ++ Comparse.NonExtensibleMessageFormat.slowNat.serialize c₀.rIdx) (DY.Literal.literalToBytes .empty)))).length := by rw [hsb, gamma_concatPrefixes, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, List.length_append, gamma_slowNat_serialize_length, hcck_len, hs2_len, hcck_bl]; omega
  exact freshSafeTerm_concatPrefixes_of_suffix_gt_64
    (fun _ hp => (List.mem_append.mp hp).elim
      (freshSafeTerm_mem_trStatePrefixes hpart hpeer hmyIk hpeerIk hrk hdhs hcks hsid hspqr)
      (freshSafeTerm_mem_slowBytes hcrk)) hs3 hs3_gt
cref_hide_foreign_instances
theorem freshSafeTerm_serialize_local_pqxdh {S : Sem} {g : Ghost} (part : Participant) (kind : DY.Libsignal.PQXDH.KeyKind) (sk : DY.Bytes) (hpart : part.utf8ByteSize + part.toUTF8.size < 28) (hsk : CompFreshDistinct.FreshSafeTerm compI0 S g sk) (hlen : (gamma compI0 S g sk).length = 32 ∨ (gamma compI0 S g sk).length = 64) : CompFreshDistinct.FreshSafeTerm compI0 S g (Comparse.serialize (⟨part, ⟨kind, sk⟩⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState) : DY.Bytes) := by
  let ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState := ⟨part, ⟨kind, sk⟩⟩
  have hpart_ne64 : part.toUTF8.size ≠ 64 := by omega
  rw [CompRX0NBSC38Parts.serialize_local_pqxdh_eq ls]
  rcases hlen with h32 | h64
  · refine freshSafeTerm_concatPrefixes_of_length_lt_64 _ (fun p hp => ?_) hsk ?_
    · simp only [List.mem_append] at hp
      exact hp.elim (freshSafeTerm_mem_slowString compI0 S g hpart_ne64)
        (fun h => h.elim (freshSafeTerm_mem_bool compI0 S g _) (freshSafeTerm_mem_bool compI0 S g _))
    · have hstr : Comparse.NonExtensibleMessageFormat.slowString.serialize ls.participant =
          Comparse.NonExtensibleMessageFormat.slowNat.serialize part.utf8ByteSize ++
            [(DY.Literal.literalToBytes part.toUTF8 : DY.Bytes)] :=
        Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq part
      rw [gamma_concatPrefixes, hstr]; simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.length_append, gamma_slowNat_serialize_length, gamma_literalToBytes_length, gamma_bool_serialize_length]; change (part.utf8ByteSize + 1 + part.toUTF8.size + (1 + 1)) + (gamma compI0 S g sk).length < 64; omega
  · obtain ⟨ba₂, _, hp₂_eq⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton kind.toBits.2
    obtain ⟨p₂, hp₂⟩ : ∃ p₂, (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize
        kind.toBits.2 = [p₂] := ⟨_, hp₂_eq⟩
    have hp₂_mem : p₂ ∈ (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize kind.toBits.2 := by rw [hp₂]; exact List.mem_cons_self
    have hp₂_len : (gamma compI0 S g p₂).length = 1 := by have h := gamma_bool_serialize_length compI0 S g kind.toBits.2; rw [hp₂, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h; exact h
    change CompFreshDistinct.FreshSafeTerm compI0 S g (Comparse.concatPrefixes (Comparse.NonExtensibleMessageFormat.slowString.serialize part ++ (Comparse.NonExtensibleMessageFormat.bool.serialize kind.toBits.1 ++ Comparse.NonExtensibleMessageFormat.bool.serialize kind.toBits.2)) sk)
    rw [← List.append_assoc, ← concatPrefixes_append, hp₂,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons,
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    have hsuf_len : (gamma compI0 S g (DY.Concat.concat p₂ sk)).length = 65 := by rw [gamma_concat_eq, List.length_append, hp₂_len, h64]
    have hsuf := freshSafeTerm_concat (fun _ _ => ne_fillFresh64_of_length_ne (by rw [hsuf_len]; decide))
      (freshSafeTerm_mem_bool compI0 S g _ hp₂_mem) hsk
    exact freshSafeTerm_concatPrefixes_of_suffix_gt_64
      (fun _ hp => (List.mem_append.mp hp).elim
        (freshSafeTerm_mem_slowString compI0 S g hpart_ne64) (freshSafeTerm_mem_bool compI0 S g _)) hsuf (by omega)
theorem gamma_setup_randTerm_length {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (ts sz : Nat) (hcompat : Compat i r S g) (hwf : RecordsWF r) (hsz : sz ≠ 0) (hp : (ts, sz) ∈ setupRandomsAt r) : (gamma i S g (randTerm ts sz)).length = sz := by rw [gamma_randTerm_eq_of_ne_zero i S g ts sz hsz, hcompat.1 (ts, sz) hp, hwf.2.1 (ts, sz) hp]
theorem freshSafeTerm_storedSecrets_of_no_setup {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hcompat : Compat compI0 r S g) (hwf : RecordsWF r) (hopk_r : r.withOpk = false) (ha_len : r.alice.utf8ByteSize + r.alice.toUTF8.size < 28) (hb_len : r.bob.utf8ByteSize + r.bob.toUTF8.size < 28) (hsec3 : secretBytes r 3 = fillFresh 11 64) (hsec4 : secretBytes r 4 = fillFresh 16 64) (hsec5 : secretBytes r 5 = fillFresh 17 64) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), CompFreshDistinct.FreshSafeTerm compI0 S g u := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach; have hsec := freshSafeTerm_setupSecret hcompat hwf hsec3 hsec4 hsec5; intro u hu
  obtain ⟨j, _, ⟨part, kind, sk⟩, hat, rfl⟩ :=
    (CompRX0NBSC38Parts.mem_storedSecrets_iff (tr := runTraceMoves r ms) (u := u)).mp hu
  have hkind := hinv.stOK part { kind := kind, sk := sk } j hat; dsimp only [Symbolic.Swarm.COMPOSED.CompInv.KindOK] at hkind
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hwf.1 hns hkind with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    · refine freshSafeTerm_serialize_local_pqxdh r.alice .identity (setupSecret r 0) ha_len (hsec 0) (.inl ?_)
      rw [CompSetupSecrecy.setupSecret_0 hwf.1]
      exact gamma_setup_randTerm_length 0 32 hcompat hwf (by decide) (mem_setupRandomsAt_32 hwf.1 (.inl (.inl rfl)))
    · refine freshSafeTerm_serialize_local_pqxdh r.bob .identity (setupSecret r 1) hb_len (hsec 1) (.inl ?_)
      rw [CompSetupSecrecy.setupSecret_1 hwf.1]
      exact gamma_setup_randTerm_length 5 32 hcompat hwf (by decide) (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inl rfl))))
  | signedPrekey =>
    obtain ⟨rfl, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hwf.1 hns hkind
    refine freshSafeTerm_serialize_local_pqxdh r.bob .signedPrekey (setupSecret r 2) hb_len (hsec 2) (.inl ?_)
    rw [CompSetupSecrecy.setupSecret_2 hwf.1]
    exact gamma_setup_randTerm_length 10 32 hcompat hwf (by decide) (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inr rfl))))
  | pqPrekey =>
    obtain ⟨rfl, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hwf.1 hns hkind
    refine freshSafeTerm_serialize_local_pqxdh r.bob .pqPrekey (setupSecret r 4) hb_len (hsec 4) (.inr ?_)
    rw [CompSetupSecrecy.setupSecret_4 hwf.1]
    exact gamma_setup_randTerm_length 16 64 hcompat hwf (by decide) (mem_setupRandomsAt_64 r hwf.1 (by decide))
  | oneTimePrekey =>
    obtain ⟨t, _, _, hev⟩ := hkind; have h0 := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hwf.1 h0 with
      ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨hopk, _, _⟩
    rw [hopk_r] at hopk; cases hopk
theorem fresh_session {S : Sem} {g : Ghost} {tr₁ tr₂ tr₃ : ExecTrace}
    {a b : Participant} {ikA ikB spk pqpk : DY.Bytes} {cl₁ cl₃ : Nat}
    (ha_ne : a.toUTF8.size ≠ 64) (hb_ne : b.toUTF8.size ≠ 64)
    (hikA : CompFreshDistinct.FreshSafeTerm compI0 S g ikA)
    (hikB : CompFreshDistinct.FreshSafeTerm compI0 S g ikB)
    (hikB_key : CompFreshDistinct.FreshSafeTerm compI0 S g (DY.X25519.x25519Key ikB))
    (hspk : CompFreshDistinct.FreshSafeTerm compI0 S g spk)
    (hspk_key : CompFreshDistinct.FreshSafeTerm compI0 S g (DY.X25519.x25519Key spk))
    (hpqpk : CompFreshDistinct.FreshSafeTerm compI0 S g pqpk)
    (hek : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm tr₁.length 32))
    (hent : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm (tr₁.length + 1) 32))
    (hdhs : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm (tr₁.length + 2) 32))
    (hm₁ : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm tr₂.length 32))
    (hcoins₁ : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm (tr₂.length + 1) cl₁))
    (hm₁_len : (g.σ tr₂.length 32).length ≠ 64)
    (hm₃ : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm tr₃.length 32))
    (hcoins₃ : CompFreshDistinct.FreshSafeTerm compI0 S g (randTerm (tr₃.length + 1) cl₃))
    (hm₃_len : (g.σ tr₃.length 32).length ≠ 64) :
    let o := CompPrefixInvAlice.iniAliceOut tr₁ ikA ikB spk pqpk none
    let stA := CompPrefixInvAlice.iniAliceStartState tr₁ b o
    let stA' := CompPrefixInvEnc.encSt tr₂ stA cl₁
    CompFreshDistinct.FreshSafeTerm compI0 S g o.ek ∧
    CompFreshDistinct.FreshSafeTerm compI0 S g o.ct ∧
    CompFreshDistinct.FreshSafeTerm compI0 S g (CompPrefixInvEnc.encOut tr₂ stA cl₁ (tr₂.length + 2)) ∧
    CompFreshDistinct.FreshSafeTerm compI0 S g (CompPrefixInvEnc.encOut tr₃ stA' cl₃ (tr₃.length + 2)) ∧
    CompFreshDistinct.FreshSafeTerm compI0 S g (Comparse.serialize (⟨a, stA⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∧
    CompFreshDistinct.FreshSafeTerm compI0 S g (Comparse.serialize (⟨a, stA'⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∧
    CompFreshDistinct.FreshSafeTerm compI0 S g (Comparse.serialize (⟨a, CompPrefixInvEnc.encSt tr₃ stA' cl₃⟩ :
        DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) := by
  intro o stA stA'; have ho := freshSafeTerm_aliceOut (tr₁ := tr₁) hikA hikB hikB_key hspk hspk_key hpqpk hek hent; have hstA := freshSafeTerm_iniAliceStartState (tr₁ := tr₁) (b := b) hikA hikB hikB_key hspk hspk_key hpqpk hek hent hdhs; have he₁ := freshSafeTerm_encTerms (tr₂ := tr₂) (stA := stA) (cl := cl₁) rfl rfl ho.1 ho.2.1 hstA.2.2.2.1 hstA.2.2.2.2.1 hstA.2.2.2.2.2.2 hm₁ hm₁_len hcoins₁
  have he₃ := freshSafeTerm_encTerms (tr₂ := tr₃) (stA := stA') (cl := cl₃) rfl rfl ho.1 ho.2.1 hstA.2.2.2.1 he₁.2.2.2.2.1 he₁.2.2.2.2.2 hm₃ hm₃_len hcoins₃; have hcks' := (freshSafeTerm_kdfCk hstA.2.2.2.2.1).1; have hspqr' := freshSafeTerm_spqrSendState hstA.2.2.2.2.2.2 hcoins₁
  exact ⟨ho.2.2.2.2.1, ho.2.2.2.2.2.1, he₁.2.2.2.1, he₃.2.2.2.1, freshSafeTerm_serialize_local_tr_of_ck_hmac a stA ha_ne hb_ne hstA.1 hstA.2.1 hstA.2.2.1 hstA.2.2.2.1 hstA.2.2.2.2.1 hstA.2.2.2.2.2.1 hstA.2.2.2.2.2.2 rfl hspk ho.2.2.2.2.2.2.2.1
      ⟨_, _, rfl⟩ (by dsimp only; decide),
    freshSafeTerm_serialize_local_tr_of_ck_hmac a stA' ha_ne hb_ne hstA.1 hstA.2.1 hstA.2.2.1 hstA.2.2.2.1 hcks' hstA.2.2.2.2.2.1 hspqr' rfl hspk ho.2.2.2.2.2.2.2.1
      ⟨_, _, rfl⟩ (by dsimp only; decide),
    freshSafeTerm_serialize_local_tr_of_ck_hmac a (CompPrefixInvEnc.encSt tr₃ stA' cl₃) ha_ne hb_ne hstA.1 hstA.2.1 hstA.2.2.1 hstA.2.2.2.1 (freshSafeTerm_kdfCk hcks').1 hstA.2.2.2.2.2.1 (freshSafeTerm_spqrSendState hspqr' hcoins₃) rfl hspk ho.2.2.2.2.2.2.2.1
      ⟨_, _, rfl⟩ (by dsimp only; decide)⟩
def Untagged4 (bs : HwBytes) : Prop := bs.take 4 ≠ compTag4 ∧ bs.take 4 ≠ compTag4Ipad ∧ bs.take 4 ≠ compTag4Opad
instance (bs : HwBytes) : Decidable (Untagged4 bs) := by unfold Untagged4; infer_instance
section UnsealBytes
unseal DY.Bytes
theorem randUntaggedTerm_of_node {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {self : DY.Bytes} {ts : List DY.Bytes}
    (hγ : (gamma' i S g self).memo =
      (self, (gamma' i S g self).shape, (gamma' i S g self).bytes) :: (ts.map (gamma' i S g)).flatMap (·.memo))
    (hts : ∀ u ∈ ts, RandUntaggedTerm i S g u) (hview : self.view? DY.Random.Random = none := by exact Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none _ _) :
    RandUntaggedTerm i S g self := by
  intro x hx r hr; rw [hγ] at hx
  rcases List.mem_cons.mp hx with rfl | hcs
  · dsimp only at hr; rw [hr, DY.BytesView.view_pack] at hview; cases hview
  · obtain ⟨c, hc, hx_c⟩ := List.mem_flatMap.mp hcs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; exact hts u hu x hx_c r hr
theorem randUntaggedTerm_of_opaqueNode {i : ExternInterpretation} {S : Sem} {g : Ghost} {self : DY.Bytes} {ts : List DY.Bytes} (hγ : (gamma' i S g self).memo = (ts.map (gamma' i S g)).flatMap (·.memo)) (hts : ∀ u ∈ ts, RandUntaggedTerm i S g u) : RandUntaggedTerm i S g self := by intro x hx r hr; rw [hγ] at hx; obtain ⟨c, hc, hx_c⟩ := List.mem_flatMap.mp hx; obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hc; exact hts u hu x hx_c r hr
theorem randUntaggedTerm_randTerm_zero (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts : Nat) : RandUntaggedTerm i S g (randTerm ts 0) := by intro x hx _ _; unfold gamma' randTerm at hx; change x ∈ ((({ timestamp := ts, size := 0 } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)).memo at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx; simp [gRandom, concretizeRandom] at hx
theorem randUntaggedTerm_randTerm_of_untagged4 (i : ExternInterpretation) (S : Sem) (g : Ghost) (ts sz : Nat) (h : sz ≠ 0 → Untagged4 (g.σ ts sz)) : RandUntaggedTerm i S g (randTerm ts sz) := by
  intro x hx r hr; unfold gamma' randTerm at hx; change x ∈ ((({ timestamp := ts, size := sz } : DY.Random.Random DY.Bytes).pack).rec (gAll i S g)).memo at hx; rw [DY.Bytes.rec_eq (gRandom g) (gAll i S g)] at hx
  by_cases hsz : sz = 0
  · simp [gRandom, concretizeRandom, hsz] at hx
  · simp only [gRandom, concretizeRandom, hsz, ↓reduceIte, node, List.flatMap_nil, List.mem_singleton] at hx; subst hx; exact h hsz
theorem randUntaggedTerm_lit (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : ByteArray) :
    RandUntaggedTerm i S g (({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack) :=
  randUntaggedTerm_of_node (ts := []) (by unfold gamma'; rw [DY.Bytes.rec_eq gLit0 (gAll i S g)]; rfl) (by nofun)
theorem randUntaggedTerm_concat {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {a b : DY.Bytes} (ha : RandUntaggedTerm i S g a) (hb : RandUntaggedTerm i S g b) :
    RandUntaggedTerm i S g (DY.Concat.concat a b) :=
  randUntaggedTerm_of_node (ts := [a, b])
    (by unfold gamma'
        change ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).memo =
          (({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack,
           ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).shape,
           ((({ lhs := a, rhs := b } : DY.Concat.Concat.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _
        rw [DY.Bytes.rec_eq gConcat0 (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ ha) (fun h => List.mem_singleton.mp h ▸ hb))
theorem randUntaggedTerm_dhPk {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {sk : DY.Bytes} (hsk : RandUntaggedTerm i S g sk) : RandUntaggedTerm i S g (DY.DiffieHellman.dhPk sk) :=
  randUntaggedTerm_of_node (ts := [sk])
    (by unfold gamma'
        change ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll i S g)).memo =
          (({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack,
           ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll i S g)).shape,
           ((({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _
        rw [DY.Bytes.rec_eq (gDhPk i) (gAll i S g)]; rfl)
    (fun _ hu => List.mem_singleton.mp hu ▸ hsk)
theorem randUntaggedTerm_dh_pack {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {pk sk : DY.Bytes} (hpk : RandUntaggedTerm i S g pk) (hsk : RandUntaggedTerm i S g sk) :
    RandUntaggedTerm i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) :=
  randUntaggedTerm_of_node (ts := [pk, sk])
    (by unfold gamma'; rw [DY.Bytes.rec_eq (gDh i) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hpk) (fun h => List.mem_singleton.mp h ▸ hsk))
theorem randUntaggedTerm_dh {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk sk : DY.Bytes} (hpk : RandUntaggedTerm i S g pk) (hsk : RandUntaggedTerm i S g sk) : RandUntaggedTerm i S g (DY.DiffieHellman.dh pk sk) := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk; simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; split
  · rename_i sk2 heq; rw [heq] at hv; simp only at hv; subst hv
    split
    · exact randUntaggedTerm_dh_pack hpk hsk
    · refine randUntaggedTerm_dh_pack (randUntaggedTerm_dhPk hsk) (fun x hx r hr => hpk x ?_ r hr)
      unfold gamma' at hx ⊢; show x ∈ (((({ sk := sk2 } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack).rec (gAll i S g))).memo
      rw [DY.Bytes.rec_eq (gDhPk i) (gAll i S g)]; exact List.mem_cons_of_mem _ (by simpa [node] using hx)
  · exact randUntaggedTerm_dh_pack hpk hsk
theorem randUntaggedTerm_hmac {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {k m : DY.Bytes} (hk : RandUntaggedTerm i S g k) (hm : RandUntaggedTerm i S g m) :
    RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.hmac k m) :=
  randUntaggedTerm_of_node (ts := [k, m])
    (by unfold gamma' DY.Libsignal.TripleRatchet.hmac
        change ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll i S g)).memo =
          (({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack,
           ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll i S g)).shape,
           ((({ salt := k, ikm := m } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _
        rw [DY.Bytes.rec_eq (gKdf0 i) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hk) (fun h => List.mem_singleton.mp h ▸ hm))
theorem randUntaggedTerm_trunc8 {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {a : DY.Bytes} (ha : RandUntaggedTerm i S g a) : RandUntaggedTerm i S g (DY.Trunc.trunc8 a) :=
  randUntaggedTerm_of_node (ts := [a])
    (by unfold gamma'
        change ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).memo =
          (({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack,
           ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).shape,
           ((({ input := a } : DY.Trunc.Trunc8.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _
        rw [DY.Bytes.rec_eq gTrunc0 (gAll i S g)]; rfl)
    (fun _ hu => List.mem_singleton.mp hu ▸ ha)
theorem randUntaggedTerm_symEnc {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {k iv m : DY.Bytes} (hk : RandUntaggedTerm i S g k) (hiv : RandUntaggedTerm i S g iv) (hm : RandUntaggedTerm i S g m) :
    RandUntaggedTerm i S g (DY.SymEnc.symEnc k iv m) :=
  randUntaggedTerm_of_node (ts := [k, iv, m])
    (by unfold gamma'
        change ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (gAll i S g)).memo =
          (({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack,
           ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (gAll i S g)).shape,
           ((({ key := k, iv := iv, msg := m } : DY.SymEnc.Enc.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _
        rw [DY.Bytes.rec_eq (gSym0 i) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hk) (fun h => (List.mem_cons.mp h).elim (· ▸ hiv) (fun h => List.mem_singleton.mp h ▸ hm)))
theorem randUntaggedTerm_trWire {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {v : UInt8} {rk : DY.Bytes} {c pc : UInt32} {ct pq : DY.Bytes} {ev : DY.TrWire.EncodingVariation}
    (hrk : RandUntaggedTerm i S g rk) (hct : RandUntaggedTerm i S g ct) (hpq : RandUntaggedTerm i S g pq) :
    RandUntaggedTerm i S g (DY.TrWire.trWireMsg v rk c pc ct pq ev) :=
  randUntaggedTerm_of_node (ts := [rk, ct, pq])
    (by unfold gamma'; dsimp only [DY.TrWire.trWireMsg, DY.TrWire.CanTrWireMsg.trWireMsg, DY.TrWire.instCanTrWireMsgBytes]
        rw [DY.Bytes.rec_eq (gTrWire0 g) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hrk) (fun h => (List.mem_cons.mp h).elim (· ▸ hct) (fun h => List.mem_singleton.mp h ▸ hpq)))
theorem randUntaggedTerm_kemPk {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {sk : DY.Bytes} (hsk : RandUntaggedTerm i S g sk) : RandUntaggedTerm i S g (DY.PQKem.kemPk sk) :=
  randUntaggedTerm_of_opaqueNode (ts := [sk])
    (by unfold gamma'; show (((({ sk := sk } : DY.PQKem.Pk.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _
        rw [DY.Bytes.rec_eq (gKemPk S) (gAll i S g)]; rfl)
    (fun _ hu => List.mem_singleton.mp hu ▸ hsk)
theorem randUntaggedTerm_kemEncap {i : ExternInterpretation} {S : Sem} {g : Ghost} {pk e : DY.Bytes} (hpk : RandUntaggedTerm i S g pk) (he : RandUntaggedTerm i S g e) : RandUntaggedTerm i S g (DY.PQKem.kemEncap pk e).1 ∧ RandUntaggedTerm i S g (DY.PQKem.kemEncap pk e).2 := by
  have hts : ∀ u ∈ [pk, e], RandUntaggedTerm i S g u :=
    fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hpk) (fun h => List.mem_singleton.mp h ▸ he)
  by_cases helen : (gamma' i S g e).bytes.length = 32
  · exact ⟨randUntaggedTerm_of_node (ts := [pk, e]) (by
        unfold gamma' at helen ⊢
        change (((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll i S g))).memo =
          (({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack,
           ((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll i S g)).shape,
           ((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _
        rw [DY.Bytes.rec_eq (gKemEncap i) (gAll i S g)]; simp only [gKemEncap, concretizeKemEncap, gAll, helen, ↓reduceIte]; rfl) hts,
      randUntaggedTerm_of_node (ts := [pk, e]) (by
        unfold gamma' at helen ⊢
        change (((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll i S g))).memo =
          (({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack,
           ((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll i S g)).shape,
           ((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll i S g)).bytes) :: _
        rw [DY.Bytes.rec_eq (gKemSS i S) (gAll i S g)]; simp only [gKemSS, concretizeKemSS, gAll, helen, ↓reduceIte]; rfl) hts⟩
  · exact ⟨randUntaggedTerm_of_opaqueNode (ts := [pk, e]) (by
        unfold gamma' at helen ⊢; show (((({ pk := pk, entropy := e } : DY.PQKem.Encap.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _
        rw [DY.Bytes.rec_eq (gKemEncap i) (gAll i S g)]; simp only [gKemEncap, concretizeKemEncap, gAll, helen, ↓reduceIte]; rfl) hts,
      randUntaggedTerm_of_opaqueNode (ts := [pk, e]) (by
        unfold gamma' at helen ⊢; show (((({ pk := pk, entropy := e } : DY.PQKem.SharedSecret.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _
        rw [DY.Bytes.rec_eq (gKemSS i S) (gAll i S g)]; simp only [gKemSS, concretizeKemSS, gAll, helen, ↓reduceIte]; rfl) hts⟩
end UnsealBytes
theorem randUntaggedTerm_vk {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {sk : DY.Bytes} (hsk : RandUntaggedTerm i S g sk) : RandUntaggedTerm i S g (DY.Signature.vk sk) :=
  randUntaggedTerm_of_opaqueNode (ts := [sk])
    (by unfold gamma'; show (((({ sk := sk } : DY.Signature.Vk.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _
        rw [DY.Bytes.rec_eq (gVk S) (gAll i S g)]; rfl)
    (fun _ hu => List.mem_singleton.mp hu ▸ hsk)
theorem randUntaggedTerm_sign {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {sk n m : DY.Bytes} (hsk : RandUntaggedTerm i S g sk) (hn : RandUntaggedTerm i S g n) (hm : RandUntaggedTerm i S g m) :
    RandUntaggedTerm i S g (DY.Signature.sign sk n m) :=
  randUntaggedTerm_of_opaqueNode (ts := [sk, n, m])
    (by unfold gamma'; show (((({ sk := sk, nonce := n, msg := m } : DY.Signature.Sign.SubF DY.Bytes).pack).rec (gAll i S g))).memo = _
        rw [DY.Bytes.rec_eq (gSign S) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hsk) (fun h => (List.mem_cons.mp h).elim (· ▸ hn) (fun h => List.mem_singleton.mp h ▸ hm)))
theorem randUntaggedTerm_spqrInit {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {a p : DY.Bytes} (ha : RandUntaggedTerm i S g a) (hp : RandUntaggedTerm i S g p) :
    RandUntaggedTerm i S g (DY.Spqr.spqrInit a p) :=
  randUntaggedTerm_of_opaqueNode (ts := [a, p])
    (by unfold gamma' DY.Spqr.spqrInit; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ ha) (fun h => List.mem_singleton.mp h ▸ hp))
theorem randUntaggedTerm_spqrSendState {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {st coins : DY.Bytes} (hst : RandUntaggedTerm i S g st) (hc : RandUntaggedTerm i S g coins) :
    RandUntaggedTerm i S g (DY.Spqr.spqrSend st coins).1 :=
  randUntaggedTerm_of_opaqueNode (ts := [st, coins])
    (by unfold gamma' DY.Spqr.spqrSend; dsimp only; rw [DY.Bytes.rec_eq (gSpqrSendState S) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hc))
theorem randUntaggedTerm_spqrSendKey {i : ExternInterpretation} {S : Sem} {g : Ghost} {st coins : DY.Bytes} (hst : RandUntaggedTerm i S g st) (hc : RandUntaggedTerm i S g coins) : RandUntaggedTerm i S g (DY.Spqr.spqrSend st coins).2.1 := by
  have hv := DY.Bytes.pack_view? DY.Spqr.InitState.SubF st; unfold DY.Spqr.spqrSend; dsimp only; split
  · rename_i a p heq; rw [heq] at hv; simp only at hv; subst hv
    have ha : RandUntaggedTerm i S g a := fun x hx r hr => hst x (by
      unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]
      exact List.mem_append_left _ (by simpa using hx)) r hr
    have hp : RandUntaggedTerm i S g p := fun x hx r hr => hst x (by
      unfold gamma' at hx ⊢; rw [DY.Bytes.rec_eq (gSpqrInit S) (gAll i S g)]
      exact List.mem_append_right _ (by simpa using hx)) r hr
    exact randUntaggedTerm_of_opaqueNode (ts := [a, p, _])
      (by unfold gamma' DY.Spqr.spqrChainKey; rw [DY.Bytes.rec_eq (gSpqrChainKey S) (gAll i S g)]; rfl)
      (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ ha) (fun h => (List.mem_cons.mp h).elim (· ▸ hp)
        (fun h => List.mem_singleton.mp h ▸ randUntaggedTerm_lit i S g _)))
  · exact randUntaggedTerm_of_opaqueNode (ts := [st, coins])
      (by unfold gamma'; rw [DY.Bytes.rec_eq (gSpqrSendKey S) (gAll i S g)]; rfl)
      (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hc))
theorem randUntaggedTerm_spqrSendMsg {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {st coins : DY.Bytes} (hst : RandUntaggedTerm i S g st) (hc : RandUntaggedTerm i S g coins) :
    RandUntaggedTerm i S g (DY.Spqr.spqrSend st coins).2.2 :=
  randUntaggedTerm_of_opaqueNode (ts := [st, coins])
    (by unfold gamma' DY.Spqr.spqrSend; dsimp only; rw [DY.Bytes.rec_eq (gSpqrSendMsg S) (gAll i S g)]; rfl)
    (fun _ hu => (List.mem_cons.mp hu).elim (· ▸ hst) (fun h => List.mem_singleton.mp h ▸ hc))
theorem randUntaggedTerm_hkdfBlock1 {i : ExternInterpretation} {S : Sem} {g : Ghost} {prk info : DY.Bytes} (hprk : RandUntaggedTerm i S g prk) (hinfo : RandUntaggedTerm i S g info) : RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.hkdfBlock1 prk info) := randUntaggedTerm_hmac hprk (randUntaggedTerm_concat hinfo (randUntaggedTerm_lit i S g _))
theorem randUntaggedTerm_hkdfBlock2 {i : ExternInterpretation} {S : Sem} {g : Ghost} {prk info : DY.Bytes} (hprk : RandUntaggedTerm i S g prk) (hinfo : RandUntaggedTerm i S g info) : RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.hkdfBlock2 prk info) := randUntaggedTerm_hmac hprk (randUntaggedTerm_concat (randUntaggedTerm_hkdfBlock1 hprk hinfo) (randUntaggedTerm_concat hinfo (randUntaggedTerm_lit i S g _)))
theorem randUntaggedTerm_hkdfBlock3 {i : ExternInterpretation} {S : Sem} {g : Ghost} {prk info : DY.Bytes} (hprk : RandUntaggedTerm i S g prk) (hinfo : RandUntaggedTerm i S g info) : RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.hkdfBlock3 prk info) := randUntaggedTerm_hmac hprk (randUntaggedTerm_concat (randUntaggedTerm_hkdfBlock2 hprk hinfo) (randUntaggedTerm_concat hinfo (randUntaggedTerm_lit i S g _)))
theorem randUntaggedTerm_createChain {i : ExternInterpretation} {S : Sem} {g : Ghost} {rk pk sk : DY.Bytes} (hrk : RandUntaggedTerm i S g rk) (hpk : RandUntaggedTerm i S g (DY.X25519.x25519Key pk)) (hsk : RandUntaggedTerm i S g sk) : RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).1 ∧ RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.createChain rk pk sk).2 := by
  have hprk := randUntaggedTerm_hmac hrk (randUntaggedTerm_dh hpk hsk); have hinfo := randUntaggedTerm_lit i S g "WhisperRatchet".toUTF8; exact ⟨randUntaggedTerm_hkdfBlock1 hprk hinfo, randUntaggedTerm_hkdfBlock2 hprk hinfo⟩
theorem randUntaggedTerm_kdfCk {i : ExternInterpretation} {S : Sem} {g : Ghost} {ck : DY.Bytes} (hck : RandUntaggedTerm i S g ck) : RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.kdfCk ck).1 ∧ RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.kdfCk ck).2 := ⟨randUntaggedTerm_hmac hck (randUntaggedTerm_lit i S g _), randUntaggedTerm_hmac hck (randUntaggedTerm_lit i S g _)⟩
theorem randUntaggedTerm_serializedIk {i : ExternInterpretation} {S : Sem} {g : Ghost} {ik : DY.Bytes} (hik : RandUntaggedTerm i S g ik) : RandUntaggedTerm i S g (DY.Libsignal.PQXDH.serializedIk ik) := randUntaggedTerm_concat (randUntaggedTerm_lit i S g _) hik
theorem randUntaggedTerm_concatPrefixes {i : ExternInterpretation} {S : Sem} {g : Ghost} :
    ∀ (ps : List DY.Bytes) {s : DY.Bytes}, (∀ p ∈ ps, RandUntaggedTerm i S g p) → RandUntaggedTerm i S g s → RandUntaggedTerm i S g (Comparse.concatPrefixes ps s)
  | [], _, _, hs => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_nil]
    exact hs
  | p :: ps, _s, hps, hs => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.concatPrefixes_cons]
    exact randUntaggedTerm_concat (hps p (List.mem_cons_self ..))
      (randUntaggedTerm_concatPrefixes ps (fun q hq => hps q (List.mem_cons_of_mem _ hq)) hs)
theorem randUntaggedTerm_mem_bool (i : ExternInterpretation) (S : Sem) (g : Ghost) (b : Bool) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.bool.serialize b) : RandUntaggedTerm i S g p := by
  obtain ⟨ba, _, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.bool_serialize_singleton b
  rw [hser] at hp
  rcases List.mem_singleton.mp hp with rfl; exact randUntaggedTerm_lit i S g _
theorem randUntaggedTerm_mem_slowNat (i : ExternInterpretation) (S : Sem) (g : Ghost) :
    ∀ (n : Nat) {p : DY.Bytes}, p ∈ Comparse.NonExtensibleMessageFormat.slowNat.serialize n → RandUntaggedTerm i S g p
  | 0, _, hp => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_zero] at hp
    exact randUntaggedTerm_mem_bool i S g false hp
  | n + 1, _, hp => by
    have hstep : (Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize (n + 1) =
        (Comparse.NonExtensibleMessageFormat.bool (Bytes := DY.Bytes)).serialize true ++
          (Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize n :=
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowNat_serialize_succ n
    rw [hstep, List.mem_append] at hp; exact hp.elim (randUntaggedTerm_mem_bool i S g true) (randUntaggedTerm_mem_slowNat i S g n)
theorem randUntaggedTerm_mem_uint32 (i : ExternInterpretation) (S : Sem) (g : Ghost) (n : UInt32) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.uint32.serialize n) : RandUntaggedTerm i S g p := by
  obtain ⟨ba, _, hser⟩ := Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.uint32_serialize_singleton n
  rw [hser] at hp
  rcases List.mem_singleton.mp hp with rfl; exact randUntaggedTerm_lit i S g _
theorem randUntaggedTerm_mem_slowBytes {i : ExternInterpretation} {S : Sem} {g : Ghost} {b : DY.Bytes} (hb : RandUntaggedTerm i S g b) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowBytes.serialize b) : RandUntaggedTerm i S g p := by
  have hser : Comparse.NonExtensibleMessageFormat.slowBytes.serialize b =
      Comparse.NonExtensibleMessageFormat.slowNat.serialize (Comparse.BytesLike.length b) ++ [b] :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowBytes_serialize_eq b
  rw [hser, List.mem_append, List.mem_singleton] at hp
  exact hp.elim (randUntaggedTerm_mem_slowNat i S g _) (· ▸ hb)
theorem randUntaggedTerm_mem_slowString (i : ExternInterpretation) (S : Sem) (g : Ghost) (s : String) {p : DY.Bytes} (hp : p ∈ Comparse.NonExtensibleMessageFormat.slowString.serialize s) : RandUntaggedTerm i S g p := by
  have hser : (Comparse.NonExtensibleMessageFormat.slowString (Bytes := DY.Bytes)).serialize s =
      (Comparse.NonExtensibleMessageFormat.slowNat (Bytes := DY.Bytes)).serialize s.utf8ByteSize ++
        [(Comparse.BytesLike.fromByteArray s.toUTF8 : DY.Bytes)] :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.slowString_serialize_eq s
  rw [hser, List.mem_append, List.mem_singleton] at hp
  exact hp.elim (randUntaggedTerm_mem_slowNat i S g _) (· ▸ randUntaggedTerm_lit i S g _)
theorem randUntaggedTerm_serialize_recvList {i : ExternInterpretation} {S : Sem} {g : Ghost} :
    ∀ {cs : List DY.Libsignal.TripleRatchet.RecvChain}, (∀ d ∈ cs, RandUntaggedTerm i S g d.ratchetKey ∧ RandUntaggedTerm i S g d.chainKey) → RandUntaggedTerm i S g ((Comparse.ExtensibleMessageFormat.list
        (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize cs)
  | [], _ => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_nil]
    exact randUntaggedTerm_lit i S g .empty
  | d :: _, hcs => by
    rw [Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvList_serialize_cons]
    have hd := hcs d List.mem_cons_self
    refine randUntaggedTerm_concatPrefixes _ (fun _ hp => ?_)
      (randUntaggedTerm_serialize_recvList (fun d' hd' => hcs d' (List.mem_cons_of_mem d hd')))
    have hser : (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain)).serialize d = Comparse.NonExtensibleMessageFormat.slowBytes.serialize d.ratchetKey ++ (Comparse.NonExtensibleMessageFormat.slowBytes.serialize d.chainKey ++ (Comparse.NonExtensibleMessageFormat.uint32.serialize d.index ++
              Comparse.NonExtensibleMessageFormat.slowNat.serialize d.rIdx)) :=
      Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.recvChain_serialize_eq d
    rw [hser] at hp; simp only [List.mem_append] at hp
    rcases hp with h1 | h2 | h3 | h4
    · exact randUntaggedTerm_mem_slowBytes hd.1 h1
    · exact randUntaggedTerm_mem_slowBytes hd.2 h2
    · exact randUntaggedTerm_mem_uint32 i S g d.index h3
    · exact randUntaggedTerm_mem_slowNat i S g d.rIdx h4
structure TRStateRandUntagged (i : ExternInterpretation) (S : Sem) (g : Ghost)
    (st : DY.Libsignal.TripleRatchet.TRState) : Prop where
  myIk : RandUntaggedTerm i S g st.myIk
  peerIk : RandUntaggedTerm i S g st.peerIk
  rk : RandUntaggedTerm i S g st.rk
  dhs : RandUntaggedTerm i S g st.dhs
  cks : RandUntaggedTerm i S g st.cks
  sid : RandUntaggedTerm i S g st.sid
  spqr : RandUntaggedTerm i S g st.spqr
  recv : ∀ d ∈ st.recv, RandUntaggedTerm i S g d.ratchetKey ∧ RandUntaggedTerm i S g d.chainKey
theorem randUntaggedTerm_serialize_local_tr {i : ExternInterpretation} {S : Sem} {g : Ghost} {ls : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState} (hst : TRStateRandUntagged i S g ls.state) : RandUntaggedTerm i S g (Comparse.serialize ls : DY.Bytes) := by
  have hser : (Comparse.serialize ls : DY.Bytes) = Comparse.concatPrefixes (trStatePrefixes ls) ((Comparse.ExtensibleMessageFormat.list
          (Comparse.ParseableSerializeableNE.mf (a := DY.Libsignal.TripleRatchet.RecvChain))).serialize
          ls.state.recv) :=
    Symbolic.Proofs.Tests.CliNonvacuity.HandshakeCollisionsFalse.serialize_local_tr_eq_bridge ls
  rw [hser]
  refine randUntaggedTerm_concatPrefixes _ (fun _ hp => ?_) (randUntaggedTerm_serialize_recvList hst.recv)
  unfold trStatePrefixes at hp; simp only [List.mem_append] at hp
  rcases hp with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13
  · exact randUntaggedTerm_mem_slowString i S g _ h1
  · exact randUntaggedTerm_mem_slowString i S g _ h2
  · exact randUntaggedTerm_mem_slowBytes hst.myIk h3
  · exact randUntaggedTerm_mem_slowBytes hst.peerIk h4
  · exact randUntaggedTerm_mem_slowBytes hst.rk h5
  · exact randUntaggedTerm_mem_slowBytes hst.dhs h6
  · exact randUntaggedTerm_mem_slowBytes hst.cks h7
  · exact randUntaggedTerm_mem_uint32 i S g _ h8
  · exact randUntaggedTerm_mem_uint32 i S g _ h9
  · exact randUntaggedTerm_mem_slowBytes hst.sid h10
  · exact randUntaggedTerm_mem_bool i S g _ h11
  · exact randUntaggedTerm_mem_slowNat i S g _ h12
  · exact randUntaggedTerm_mem_slowBytes hst.spqr h13
theorem randUntaggedTerm_aliceOut {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {tr₁ : ExecTrace} {ikA ikB spk pqpk : DY.Bytes}
    (hikA : RandUntaggedTerm i S g ikA) (hikB : RandUntaggedTerm i S g ikB)
    (hikB_key : RandUntaggedTerm i S g (DY.X25519.x25519Key ikB))
    (hspk : RandUntaggedTerm i S g spk) (hspk_key : RandUntaggedTerm i S g (DY.X25519.x25519Key spk))
    (hpqpk : RandUntaggedTerm i S g pqpk)
    (hek : RandUntaggedTerm i S g (randTerm tr₁.length 32))
    (hent : RandUntaggedTerm i S g (randTerm (tr₁.length + 1) 32)) :
    let o := CompPrefixInvAlice.iniAliceOut tr₁ ikA ikB spk pqpk none
    RandUntaggedTerm i S g o.ikA ∧ RandUntaggedTerm i S g o.ikB ∧
    RandUntaggedTerm i S g o.spk ∧ RandUntaggedTerm i S g o.pqpk ∧
    RandUntaggedTerm i S g o.ek ∧ RandUntaggedTerm i S g o.ct ∧
    RandUntaggedTerm i S g o.keys.rk ∧ RandUntaggedTerm i S g o.keys.ck ∧
    RandUntaggedTerm i S g o.keys.pqr := by
  have hkem := randUntaggedTerm_kemEncap hpqpk hent
  have hprk : RandUntaggedTerm i S g (DY.Libsignal.TripleRatchet.hmac DY.Libsignal.TripleRatchet.zeroSalt (DY.Libsignal.PQXDH.pqxdhIkm (DY.DiffieHellman.dh (DY.X25519.x25519Key spk) ikA) (DY.DiffieHellman.dh (DY.X25519.x25519Key ikB) (randTerm tr₁.length 32)) (DY.DiffieHellman.dh (DY.X25519.x25519Key spk) (randTerm tr₁.length 32)) none
          (DY.PQKem.kemEncap pqpk (randTerm (tr₁.length + 1) 32)).2)) :=
    randUntaggedTerm_hmac (randUntaggedTerm_lit i S g _) (randUntaggedTerm_concat (randUntaggedTerm_lit i S g _) (randUntaggedTerm_concat (randUntaggedTerm_dh hspk_key hikA) (randUntaggedTerm_concat (randUntaggedTerm_dh hikB_key hek) (randUntaggedTerm_concat (randUntaggedTerm_dh hspk_key hek) hkem.2))))
  have hinfo : RandUntaggedTerm i S g DY.Libsignal.PQXDH.pqxdhLabel := randUntaggedTerm_lit i S g _; exact ⟨randUntaggedTerm_dhPk hikA, hikB, hspk, hpqpk, randUntaggedTerm_dhPk hek, hkem.1, randUntaggedTerm_hkdfBlock1 hprk hinfo, randUntaggedTerm_hkdfBlock2 hprk hinfo, randUntaggedTerm_hkdfBlock3 hprk hinfo⟩
theorem trStateRandUntagged_iniAliceStartState {i : ExternInterpretation} {S : Sem} {g : Ghost} (tr : ExecTrace) (b : DY.Participant) (o : DY.Libsignal.PQXDH.AliceHandshakeOut) (hikA : RandUntaggedTerm i S g o.ikA) (hikB : RandUntaggedTerm i S g o.ikB) (hspk : RandUntaggedTerm i S g o.spk) (hspk_key : RandUntaggedTerm i S g (DY.X25519.x25519Key o.spk)) (hrk : RandUntaggedTerm i S g o.keys.rk) (hck : RandUntaggedTerm i S g o.keys.ck) (hpqr : RandUntaggedTerm i S g o.keys.pqr) (hdhsA : RandUntaggedTerm i S g (randTerm (tr.length + 2) 32)) : TRStateRandUntagged i S g (CompPrefixInvAlice.iniAliceStartState tr b o) := by
  have hcc := randUntaggedTerm_createChain hrk hspk_key hdhsA
  refine { myIk := randUntaggedTerm_serializedIk hikA, peerIk := randUntaggedTerm_serializedIk hikB
           rk := hcc.1, dhs := hdhsA, cks := hcc.2
           sid := randUntaggedTerm_concat (randUntaggedTerm_dhPk hdhsA) hrk
           spqr := randUntaggedTerm_spqrInit hpqr (randUntaggedTerm_lit i S g _)
           recv := fun d hd => by
             simp only [CompPrefixInvAlice.iniAliceStartState, List.mem_singleton] at hd; subst hd; exact ⟨hspk, hck⟩ }
theorem trStateRandUntagged_encSt {i : ExternInterpretation} {S : Sem} {g : Ghost}
    (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat)
    (hst : TRStateRandUntagged i S g stA)
    (hcoins : RandUntaggedTerm i S g (randTerm (tr₂.length + 1) cl)) :
    TRStateRandUntagged i S g (CompPrefixInvEnc.encSt tr₂ stA cl) :=
  { hst with cks := (randUntaggedTerm_kdfCk hst.cks).1
             spqr := randUntaggedTerm_spqrSendState hst.spqr hcoins }
theorem randUntaggedTerm_encOut {i : ExternInterpretation} {S : Sem} {g : Ghost} (tr₂ : ExecTrace) {stA : DY.Libsignal.TripleRatchet.TRState} (cl : Nat) (hst : TRStateRandUntagged i S g stA) (hm : RandUntaggedTerm i S g (randTerm tr₂.length 32)) (hcoins : RandUntaggedTerm i S g (randTerm (tr₂.length + 1) cl)) : RandUntaggedTerm i S g (CompPrefixInvEnc.encOut tr₂ stA cl (tr₂.length + 2)) := by
  dsimp only [CompPrefixInvEnc.encOut, CompPrefixInvEnc.encWire, CompPrefixInvEnc.encMac, DY.Libsignal.TripleRatchet.trHonestWireMsg]
  have hsalt : RandUntaggedTerm i S g (CompPrefixInvEnc.encSalt tr₂ stA cl (tr₂.length + 2)) := by rw [CompPrefixInvEnc.encSalt_self]; exact randUntaggedTerm_spqrSendKey hst.spqr hcoins
  have hprk := randUntaggedTerm_hmac hsalt (randUntaggedTerm_kdfCk hst.cks).2; have hinfo := randUntaggedTerm_lit i S g "WhisperMessageKeys".toUTF8; have hct := randUntaggedTerm_symEnc (randUntaggedTerm_hkdfBlock1 hprk hinfo) (randUntaggedTerm_hkdfBlock3 hprk hinfo) hm; have hdhsPk := randUntaggedTerm_dhPk hst.dhs; have hpqMsg := randUntaggedTerm_spqrSendMsg hst.spqr hcoins
  exact randUntaggedTerm_concat (randUntaggedTerm_trWire hdhsPk hct hpqMsg) (randUntaggedTerm_trunc8 (randUntaggedTerm_hmac (randUntaggedTerm_hkdfBlock2 hprk hinfo) (randUntaggedTerm_concat hst.myIk (randUntaggedTerm_concat hst.peerIk (randUntaggedTerm_trWire hdhsPk hct hpqMsg)))))
theorem randUntagged_session {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {tr₁ tr₂ tr₃ : ExecTrace} {a b : Participant} {ikA ikB spk pqpk : DY.Bytes} {cl₁ cl₃ : Nat}
    (hikA : RandUntaggedTerm i S g ikA) (hikB : RandUntaggedTerm i S g ikB)
    (hikB_key : RandUntaggedTerm i S g (DY.X25519.x25519Key ikB))
    (hspk : RandUntaggedTerm i S g spk) (hspk_key : RandUntaggedTerm i S g (DY.X25519.x25519Key spk))
    (hpqpk : RandUntaggedTerm i S g pqpk)
    (hek : RandUntaggedTerm i S g (randTerm tr₁.length 32))
    (hent : RandUntaggedTerm i S g (randTerm (tr₁.length + 1) 32))
    (hdhs : RandUntaggedTerm i S g (randTerm (tr₁.length + 2) 32))
    (hm₁ : RandUntaggedTerm i S g (randTerm tr₂.length 32))
    (hcoins₁ : RandUntaggedTerm i S g (randTerm (tr₂.length + 1) cl₁))
    (hm₃ : RandUntaggedTerm i S g (randTerm tr₃.length 32))
    (hcoins₃ : RandUntaggedTerm i S g (randTerm (tr₃.length + 1) cl₃)) :
    let o := CompPrefixInvAlice.iniAliceOut tr₁ ikA ikB spk pqpk none
    let stA := CompPrefixInvAlice.iniAliceStartState tr₁ b o
    let stA' := CompPrefixInvEnc.encSt tr₂ stA cl₁
    RandUntaggedTerm i S g o.ek ∧ RandUntaggedTerm i S g o.ct ∧
    RandUntaggedTerm i S g (CompPrefixInvEnc.encOut tr₂ stA cl₁ (tr₂.length + 2)) ∧
    RandUntaggedTerm i S g (CompPrefixInvEnc.encOut tr₃ stA' cl₃ (tr₃.length + 2)) ∧
    RandUntaggedTerm i S g (Comparse.serialize (⟨a, stA⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∧
    RandUntaggedTerm i S g (Comparse.serialize (⟨a, stA'⟩ : DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) ∧
    RandUntaggedTerm i S g (Comparse.serialize (⟨a, CompPrefixInvEnc.encSt tr₃ stA' cl₃⟩ :
        DY.PersistentLocalState.LocalState DY.Libsignal.TripleRatchet.TRState) : DY.Bytes) := by
  intro o stA stA'; have ho := randUntaggedTerm_aliceOut hikA hikB hikB_key hspk hspk_key hpqpk hek hent; have hstA := trStateRandUntagged_iniAliceStartState tr₁ b o ho.1 ho.2.1 ho.2.2.1 hspk_key ho.2.2.2.2.2.2.1 ho.2.2.2.2.2.2.2.1 ho.2.2.2.2.2.2.2.2 hdhs; have hstA' := trStateRandUntagged_encSt tr₂ cl₁ hstA hcoins₁
  exact ⟨ho.2.2.2.2.1, ho.2.2.2.2.2.1, randUntaggedTerm_encOut tr₂ cl₁ hstA hm₁ hcoins₁, randUntaggedTerm_encOut tr₃ cl₃ hstA' hm₃ hcoins₃, randUntaggedTerm_serialize_local_tr hstA, randUntaggedTerm_serialize_local_tr hstA', randUntaggedTerm_serialize_local_tr (trStateRandUntagged_encSt tr₃ cl₃ hstA' hcoins₃)⟩
theorem randUntaggedTerm_randTerm_of_gamma_eq {i : ExternInterpretation} {S : Sem} {g : Ghost}
    {ts sz : Nat} {b : HwBytes} (hγ : gamma i S g (randTerm ts sz) = b) (hb : Untagged4 b) :
    RandUntaggedTerm i S g (randTerm ts sz) :=
  randUntaggedTerm_randTerm_of_untagged4 i S g ts sz fun hsz => by
    rw [gamma_randTerm_eq_of_ne_zero i S g ts sz hsz] at hγ; rw [hγ]; exact hb
theorem randUntaggedTerm_randTerm_of_single_rng {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {b : HwBytes} {ts sz : Nat} {anc : Option Nat} (hem : EventMatchesEntry i r S g (.rng b) { kind := .rng, terms := [randTerm ts sz], layout := .single, anchor := anc }) (hb : Untagged4 b) : RandUntaggedTerm i S g (randTerm ts sz) := by
  obtain ⟨_, hmap⟩ := hem; dsimp only [List.map, DY.Libsignal.Composed.Refinement.eventBytes] at hmap
  injection hmap with hγ; exact randUntaggedTerm_randTerm_of_gamma_eq hγ hb
theorem randUntaggedTerm_randTerm_of_single_pt {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {b : HwBytes} {ts sz : Nat} {anc : Option Nat} (hem : EventMatchesEntry i r S g (.pt b) { kind := .pt, terms := [randTerm ts sz], layout := .single, anchor := anc }) (hb : Untagged4 b) : RandUntaggedTerm i S g (randTerm ts sz) := by
  obtain ⟨_, hmap⟩ := hem; dsimp only [List.map, DY.Libsignal.Composed.Refinement.eventBytes] at hmap
  injection hmap with hγ; exact randUntaggedTerm_randTerm_of_gamma_eq hγ hb
theorem randUntaggedTerm_draws_of_aliceVis {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₁ : ExecTrace} {a b : Participant} {o : DY.Libsignal.PQXDH.AliceHandshakeOut} {hb : DY.Libsignal.PQXDH.BundleHandles} {bun : HwBytes} {rs : List MachineEvent} (hm₀ : List.Forall₂ (EventMatchesEntry i r S g) (.recv bun :: rs) (aliceVis tr₁ (CompPrefixInvAlice.iniAliceStartTr tr₁ a b o) hb)) (hrs : ∀ b : HwBytes, .rng b ∈ rs → Untagged4 b) (hent : RandUntaggedTerm i S g (randTerm (tr₁.length + 1) 32)) : RandUntaggedTerm i S g (randTerm tr₁.length 32) ∧ RandUntaggedTerm i S g (randTerm (tr₁.length + 1) 32) ∧ RandUntaggedTerm i S g (randTerm (tr₁.length + 2) 32) := by
  rw [CompPrefixInvAlice.aliceVis_iniAliceStartTr] at hm₀
  obtain ⟨ev_ek, hev_ek_mem, hem_ek⟩ := forall2_exists_left hm₀ (by simp) (b := rngEntry (randTerm tr₁.length 32))
  obtain ⟨b_ek, rfl⟩ := event_eq_rng_of_matches_rng hem_ek
  have hek := randUntaggedTerm_randTerm_of_single_rng hem_ek
    (hrs b_ek ((List.mem_cons.mp hev_ek_mem).resolve_left (by nofun)))
  obtain ⟨ev_dhs, hev_dhs_mem, hem_dhs⟩ := forall2_exists_left hm₀ (by simp)
    (b := ({ rngEntry (randTerm (tr₁.length + 2) 32) with anchor := some (tr₁.length + 5) } : VisEntry))
  obtain ⟨b_dhs, rfl⟩ := event_eq_rng_of_matches_rng hem_dhs
  exact ⟨hek, hent, randUntaggedTerm_randTerm_of_single_rng hem_dhs
    (hrs b_dhs ((List.mem_cons.mp hev_dhs_mem).resolve_left (by nofun)))⟩
theorem randUntaggedTerm_draws_of_encVis {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {tr₂ : ExecTrace} {me : Participant} {sIdx : Nat} {stA : DY.Libsignal.TripleRatchet.TRState} {cl pq : Nat} {wr : Nat × Nat} {pt c w : HwBytes} (hm₁ : List.Forall₂ (EventMatchesEntry i r S g) [.pt pt, .rng c, .send w] (encVis tr₂ (CompPrefixInvEnc.encNextTr tr₂ me sIdx stA cl pq) (some wr) true)) (hpt : Untagged4 pt) (hc : Untagged4 c) : RandUntaggedTerm i S g (randTerm tr₂.length 32) ∧ RandUntaggedTerm i S g (randTerm (tr₂.length + 1) cl) := by obtain ⟨_, hem_pt, hem_rng, _⟩ := encVis_encNextTr_of_forall2_three hm₁; exact ⟨randUntaggedTerm_randTerm_of_single_pt hem_pt hpt, randUntaggedTerm_randTerm_of_single_rng hem_rng hc⟩
theorem randUntaggedTerm_setupSecret {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hopk_r : r.withOpk = false) (hsec0 : Untagged4 (secretBytes r 0)) (hsec1 : Untagged4 (secretBytes r 1)) (hsec2 : Untagged4 (secretBytes r 2)) (hsec3 : secretBytes r 3 = fillFresh 11 64) (hsec4 : secretBytes r 4 = fillFresh 16 64) (hsec5 : secretBytes r 5 = fillFresh 17 64) (k : Nat) : RandUntaggedTerm i S g (setupSecret r k) := by
  unfold setupSecret; rw [Symbolic.Swarm.CREF.TR.setupRandoms_eq r hwf.1, hopk_r]
  rcases k with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | k⟩⟩⟩⟩⟩
  · refine randUntaggedTerm_randTerm_of_untagged4 i S g 0 32 fun _ => ?_
    have h0 : r.fresh 0 32 = secretBytes r 0 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> rfl
    rw [hcompat.1 (0, 32) (mem_setupRandomsAt_32 hwf.1 (.inl (.inl rfl))), h0]; exact hsec0
  · refine randUntaggedTerm_randTerm_of_untagged4 i S g 5 32 fun _ => ?_
    have h1 : r.fresh 5 32 = secretBytes r 1 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> rfl
    rw [hcompat.1 (5, 32) (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inl rfl)))), h1]; exact hsec1
  · refine randUntaggedTerm_randTerm_of_untagged4 i S g 10 32 fun _ => ?_
    have h2 : r.fresh 10 32 = secretBytes r 2 := by unfold secretBytes; rw [Symbolic.Swarm.CREF.b1_setupRandomsAt_eq r hwf.1]; cases r.withOpk <;> rfl
    rw [hcompat.1 (10, 32) (mem_setupRandomsAt_32 hwf.1 (.inl (.inr (.inr rfl)))), h2]; exact hsec2
  · refine randUntaggedTerm_randTerm_of_untagged4 i S g 11 64 fun _ => ?_
    rw [(freshSafeTerm_setup_64 hcompat hwf.1 hsec3 hsec4 hsec5 (ts := 11) (by decide)).1]; decide
  · refine randUntaggedTerm_randTerm_of_untagged4 i S g 16 64 fun _ => ?_
    rw [(freshSafeTerm_setup_64 hcompat hwf.1 hsec3 hsec4 hsec5 (ts := 16) (by decide)).1]; decide
  · refine randUntaggedTerm_randTerm_of_untagged4 i S g 17 64 fun _ => ?_
    rw [(freshSafeTerm_setup_64 hcompat hwf.1 hsec3 hsec4 hsec5 (ts := 17) (by decide)).1]; decide
  · exact randUntaggedTerm_randTerm_zero i S g 0
theorem randUntaggedTerm_setupPublic {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hopk_r : r.withOpk = false) (hsec0 : Untagged4 (secretBytes r 0)) (hsec1 : Untagged4 (secretBytes r 1)) (hsec2 : Untagged4 (secretBytes r 2)) (hsec3 : secretBytes r 3 = fillFresh 11 64) (hsec4 : secretBytes r 4 = fillFresh 16 64) (hsec5 : secretBytes r 5 = fillFresh 17 64) (k : Nat) : RandUntaggedTerm i S g (setupPublic r k) := by
  have hsec := randUntaggedTerm_setupSecret hcompat hwf hopk_r hsec0 hsec1 hsec2 hsec3 hsec4 hsec5
  have h0 : RandUntaggedTerm i S g (randTerm 0 32) := by rw [← setupSecret_0 hwf.1]; exact hsec 0
  have h1 : RandUntaggedTerm i S g (randTerm 5 32) := by rw [← setupSecret_1 hwf.1]; exact hsec 1
  have h2 : RandUntaggedTerm i S g (randTerm 10 32) := by rw [← setupSecret_2 hwf.1]; exact hsec 2
  have h3 : RandUntaggedTerm i S g (randTerm 11 64) := by rw [← setupSecret_3 hwf.1]; exact hsec 3
  have h4 : RandUntaggedTerm i S g (randTerm 16 64) := by rw [← setupSecret_4 hwf.1]; exact hsec 4
  have h5 : RandUntaggedTerm i S g (randTerm 17 64) := by rw [← setupSecret_5 hwf.1]; exact hsec 5
  rcases k with _ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | ⟨_ | k⟩⟩⟩⟩⟩⟩⟩
  · rw [setupPublic_0 hwf.1]; exact randUntaggedTerm_dhPk h0
  · rw [setupPublic_1 hwf.1]; exact randUntaggedTerm_vk h0
  · rw [setupPublic_2 hwf.1]; exact randUntaggedTerm_dhPk h1
  · rw [setupPublic_3 hwf.1]; exact randUntaggedTerm_vk h1
  · rw [setupPublic_4 hwf.1]; exact randUntaggedTerm_dhPk h2
  · rw [setupPublic_5 hwf.1]
    exact randUntaggedTerm_sign h1 h3 (randUntaggedTerm_concat (randUntaggedTerm_lit i S g _) (randUntaggedTerm_dhPk h2))
  · rw [setupPublic_6 hwf.1]; exact randUntaggedTerm_kemPk h4
  · rw [setupPublic_7 hwf.1]
    exact randUntaggedTerm_sign h1 h5 (randUntaggedTerm_concat (randUntaggedTerm_lit i S g _) (randUntaggedTerm_kemPk h4))
  · unfold setupPublic; rw [setupSent, Symbolic.Swarm.CREF.TR.setupTrace_eq r hwf.1, hopk_r]
    simp only [Bool.false_eq_true, ↓reduceIte, Symbolic.Swarm.CREF.TR.setupTr4, Symbolic.Swarm.CREF.TR.setupTr3, Symbolic.Swarm.CREF.TR.setupTr2, Symbolic.Swarm.CREF.TR.setupTr1]
    repeat first | rw [setupSent_append_net] | rw [setupSent_append_nonNet _ _ rfl]
    rw [setupSent_nil]; exact randUntaggedTerm_randTerm_zero i S g 0
theorem randUntaggedTerm_storedSecrets_of_no_setup {i : ExternInterpretation} {r : Records} {S : Sem} {g : Ghost} {ms : List Move} (hcompat : Compat i r S g) (hwf : RecordsWF r) (hopk_r : r.withOpk = false) (hsec0 : Untagged4 (secretBytes r 0)) (hsec1 : Untagged4 (secretBytes r 1)) (hsec2 : Untagged4 (secretBytes r 2)) (hsec3 : secretBytes r 3 = fillFresh 11 64) (hsec4 : secretBytes r 4 = fillFresh 16 64) (hsec5 : secretBytes r 5 = fillFresh 17 64) (hns : ∀ m ∈ ms, m.isSetup = false) (hreach : (runTraceMoves r ms).Reachable DY.Libsignal.Composed.reachability) : ∀ u ∈ storedSecrets (runTraceMoves r ms), RandUntaggedTerm i S g u := by
  have hinv := Symbolic.Swarm.COMPOSED.CompInv.spqrInv_of_reachable (runTraceMoves r ms) hreach; have hsec := randUntaggedTerm_setupSecret hcompat hwf hopk_r hsec0 hsec1 hsec2 hsec3 hsec4 hsec5
  have hser : ∀ {ls : DY.PersistentLocalState.LocalState DY.Libsignal.PQXDH.PQXDHState},
      RandUntaggedTerm i S g ls.state.sk → RandUntaggedTerm i S g (Comparse.serialize ls : DY.Bytes) := fun hsk => by
    rw [CompRX0NBSC38Parts.serialize_local_pqxdh_eq]
    refine randUntaggedTerm_concatPrefixes _ (fun p hp => ?_) hsk
    simp only [List.mem_append] at hp
    exact hp.elim (randUntaggedTerm_mem_slowString i S g _)
      (fun h => h.elim (randUntaggedTerm_mem_bool i S g _) (randUntaggedTerm_mem_bool i S g _))
  intro u hu
  obtain ⟨j, _, ⟨part, kind, sk⟩, hat, rfl⟩ :=
    (CompRX0NBSC38Parts.mem_storedSecrets_iff (tr := runTraceMoves r ms) (u := u)).mp hu
  have hkind := hinv.stOK part { kind := kind, sk := sk } j hat; dsimp only [Symbolic.Swarm.COMPOSED.CompInv.KindOK] at hkind
  cases kind with
  | identity =>
    rcases CompSetupSecrecy.ikAt_cases_of_no_setup hwf.1 hns hkind with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    · exact hser (hsec 0)
    · exact hser (hsec 1)
  | signedPrekey =>
    obtain ⟨rfl, rfl, _⟩ := CompSetupSecrecy.spkAt_eq_of_no_setup hwf.1 hns hkind; exact hser (hsec 2)
  | pqPrekey =>
    obtain ⟨rfl, rfl, _⟩ := CompSetupSecrecy.pqAt_eq_of_no_setup hwf.1 hns hkind; exact hser (hsec 4)
  | oneTimePrekey =>
    obtain ⟨t, _, _, hev⟩ := hkind; have h0 := CompSetupSecrecy.noNewNonMovePQEv_runTrace r ms hns _ (t + 1) rfl hev
    rcases CompSetupSecrecy.setupTrace_eventLoggedAt_cases hwf.1 h0 with
      ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨_, ⟨⟩⟩ | ⟨hopk, _, _⟩
    rw [hopk_r] at hopk; cases hopk
end Symbolic.BugInjection.Proofs.Common443.WsIdx1PrefSafe40Aux
