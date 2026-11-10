/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Symbolic.Proofs.Swarm.CREF.TR.G1.CanonRep
import DY.Bytes.Basic
import DY.ALaCarte.Basic
import Symbolic.DYBridge.DY.Bytes.Basic
import Symbolic.Proofs.Refinement.X25519Covered
import Symbolic.Proofs.Swarm.CREF.Prelude
import Symbolic.Proofs.Swarm.CREF.Stage1Wire

/-!
# Skipped-Key Fresh-Chain Distinct-Base Disjointness

Proves that a non-colliding wire representation cannot match the bytes of an installed non-low-order
receiver-chain ratchet key when their normalized X25519 base keys differ.
-/

@[expose] public section

set_option autoImplicit false

cref_hide_foreign_instances

namespace Symbolic.Swarm.CREF.TR

cref_open

open DY DY.Comparse DY.Literal DY.Libsignal DY.DiffieHellman
open DY.Libsignal.TripleRatchet (RecvChain findRecvChain messageVersion x25519LowOrder createChain
  kdfRk hkdfBlock1 hkdfBlock2 hmac)
open DY.Libsignal.Refinement (ExternCryptoLawsHold)
open DY.Libsignal.TripleRatchet
open CryptoProofLib.Refinement (ExternInterpretation)
open Symbolic.Swarm.CREF.TR Symbolic.Swarm.CREF.TR.G1
open CryptoGames.LibsignalSession (SignalMessage)
open CryptoVerification.LibsignalProtoCodec (protoSignalCodec)

local notation "SpqrSem" => OpaqueSymbolSemantics

unseal DY.Bytes in
private instance subLit0SVL (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction concretizeLit (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, litFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhPkSVL (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDhPk i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subDhSVL (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeDh i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, dhFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subKdf0SVL (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeKdf i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, kdfFuns, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩
unseal DY.Bytes in
private instance subVariant0SVL (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) :
    DY.Bytes.SubFunction (concretizeVariant i) (concretizeAll i S g) :=
  @DY.Bytes.SubFunction.mk _ _ _ _ _ _ _ ⟨fun _ _ => by
    simp only [concretizeAll, allFuns, x25519Funs, Symbolic.DYBridge.DY.Bytes.PartialFunction.combine_eq]; rfl⟩

namespace RecvDecStep.SkippedVarLit

/-! ## Concretization, Shape, and Memo Helpers -/

private theorem gamma_dhPk_raw_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (sk : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dhPk sk) =
      (i DY.Libsignal.Refinement.x25519PublicKeySymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk)]).getD [] := by
  unfold gamma gamma'
  rw [show DY.DiffieHellman.dhPk sk = ({ sk := sk } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeDhPk i) (concretizeAll i S g)]
  rfl

private theorem gamma_dh_raw_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (pk sk : DY.Bytes) :
    gamma i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) =
      (i DY.Libsignal.Refinement.x25519AgreementSymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk), gamma i S g pk]).getD [] := by
  unfold gamma gamma'; rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl

private theorem gamma_dh_eq_svl (i : ExternInterpretation) (hEq : ExternCryptoLawsHold i)
    (S : SpqrSem) (g : Ghost) (pk sk : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dh pk sk) =
      (i DY.Libsignal.Refinement.x25519AgreementSymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk), gamma i S g pk]).getD [] := by
  have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF pk
  simp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  split
  · rename_i sk2 heq
    rw [heq] at hv; simp only at hv; subst hv
    split
    · rw [gamma_dh_raw_svl]
    · rw [gamma_dh_raw_svl]
      show (i DY.Libsignal.Refinement.x25519AgreementSymbol
          [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk2),
           gamma i S g (DY.DiffieHellman.dhPk sk)]).getD [] =
        (i DY.Libsignal.Refinement.x25519AgreementSymbol
          [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk),
           gamma i S g (DY.DiffieHellman.dhPk sk2)]).getD []
      rw [gamma_dhPk_raw_svl, gamma_dhPk_raw_svl,
        hEq.x25519_agreement_commutes
          (DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk2))
          (DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk))]
  · rw [gamma_dh_raw_svl]

private theorem gamma_x25519Variant_raw_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (k : DY.Bytes) (v : Fin 4) (t : Fin 8) :
    gamma i S g (({key := k, variation := v, torsion := t} : DY.X25519.Variant.SubF DY.Bytes).pack) =
      DY.Libsignal.Refinement.variantBytes
        (DY.Libsignal.Refinement.torsionShift i (gamma i S g k) t) v := by
  unfold gamma gamma'; rw [DY.Bytes.rec_eq (concretizeVariant i) (concretizeAll i S g)]; rfl

private theorem torsionShift_length_svl (i : ExternInterpretation) (p : HwBytes) (t : Fin 8) :
    (DY.Libsignal.Refinement.torsionShift i p t).length = p.length := by
  unfold DY.Libsignal.Refinement.torsionShift
  split
  · rfl
  · rename_i h
    have hlen : p.length = 32 := by revert h; simp
    split
    · split
      · rename_i q _ hq
        omega
      · rfl
    · rfl

private theorem torsionShift_of_len_ne_svl (i : ExternInterpretation) (p : HwBytes) (t : Fin 8)
    (hl : ¬p.length = 32) :
    DY.Libsignal.Refinement.torsionShift i p t = p := by
  unfold DY.Libsignal.Refinement.torsionShift; simp [hl]

private theorem isLowOrderKey_torsionShift_svl (i : ExternInterpretation)
    (hEq : ExternCryptoLawsHold i) (p : HwBytes) (t : Fin 8) (hl : p.length = 32) :
    DY.X25519.isLowOrderKey
        ((DY.Libsignal.Refinement.torsionShift i p t).map BitVec.toNat) =
      DY.X25519.isLowOrderKey (p.map BitVec.toNat) := by
  have hs : (List.replicate 32 (0 : BitVec 8)).length = 32 := by simp
  have h1 := hEq.x25519_agreement_zero_iff_low_order (List.replicate 32 0)
    (DY.Libsignal.Refinement.torsionShift i p t) hs
    ((torsionShift_length_svl i p t).trans hl)
  have h2 := hEq.x25519_agreement_zero_iff_low_order (List.replicate 32 0) p hs hl
  rw [hEq.x25519_agreement_torsion_invariant] at h1
  exact Bool.eq_iff_iff.mpr (h1.symm.trans h2)

private theorem agreement_gamma_x25519Key_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (hEq : ExternCryptoLawsHold i) (a : HwBytes) (pk : DY.Bytes) :
    i DY.Libsignal.Refinement.x25519AgreementSymbol
        [a, gamma i S g (DY.X25519.normalizeX25519Key pk)] =
      i DY.Libsignal.Refinement.x25519AgreementSymbol [a, gamma i S g pk] := by
  unfold DY.X25519.normalizeX25519Key
  split
  · rename_i x h; have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
    simp only [h] at hv; rw [← hv, gamma_x25519Variant_raw_svl i S g x.key x.variation x.torsion]
    by_cases hl : (gamma i S g x.key).length = 32
    · have hl' := (torsionShift_length_svl i (gamma i S g x.key) x.torsion).trans hl
      have hs := DY.Libsignal.Refinement.variantBytes_spec _ hl' x.variation
      rw [← hEq.x25519_agreement_torsion_invariant a (gamma i S g x.key) x.torsion]
      exact hEq.x25519_agreement_reads_u_coordinate a _ _ hl' hs.1 hs.2.symm
    · rw [torsionShift_of_len_ne_svl i _ _ hl]
      unfold DY.Libsignal.Refinement.variantBytes; simp only [hl, ↓reduceIte]
  · rfl

private theorem gamma_dh_x25519Key_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (hEq : ExternCryptoLawsHold i) (pk sk : DY.Bytes) :
    gamma i S g (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key pk) sk) =
      (i DY.Libsignal.Refinement.x25519AgreementSymbol
        [DY.Libsignal.TripleRatchet.Refinement.clamp (gamma i S g sk), gamma i S g pk]).getD [] := by
  rw [gamma_dh_eq_svl i hEq, agreement_gamma_x25519Key_svl i S g hEq]

private theorem dh_pack_exists_svl (pk sk : DY.Bytes) :
    ∃ p s, DY.DiffieHellman.dh pk sk =
      ({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]
  rcases pk.view? DY.DiffieHellman.DhPk.SubF with _ | p
  · exact ⟨pk, sk, rfl⟩
  · dsimp only; split <;> exact ⟨_, _, rfl⟩

private theorem dh_pack_of_view_dhPk_none_svl {pk : DY.Bytes} (sk : DY.Bytes)
    (hnone : pk.view? DY.DiffieHellman.DhPk.SubF = none) :
    DY.DiffieHellman.dh pk sk = ({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh]; rw [hnone]

private theorem shape_dh_pack_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (pk sk : DY.Bytes) :
    (gamma' i S g (({ pk := pk, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)).shape =
      ({ pk := (gamma' i S g pk).shape, sk := (gamma' i S g sk).shape } :
        DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  unfold gamma'; rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; rfl

private theorem mem_memo_dh_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (pk sk : DY.Bytes) :
    let d := DY.DiffieHellman.dh pk sk
    (d, (gamma' i S g d).shape, gamma i S g d) ∈ (gamma' i S g d).memo := by
  intro d; dsimp only [d]; obtain ⟨p, s, heq⟩ := dh_pack_exists_svl pk sk; rw [heq]
  change (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack,
    ((({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).shape,
    ((({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes) ∈
    ((({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack).rec (concretizeAll i S g)).memo
  rw [DY.Bytes.rec_eq (concretizeDh i) (concretizeAll i S g)]; exact List.Mem.head _

private theorem assumedInjective_dh_svl (pk sk : DY.Bytes) :
    assumedInjective (DY.DiffieHellman.dh pk sk) = true := by
  obtain ⟨p, s, heq⟩ := dh_pack_exists_svl pk sk; rw [heq]
  unfold assumedInjective; rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF)]; simp

unseal DY.Bytes in
private theorem dh_not_mem_ptAtoms_svl (r₀ : ProtocolSetup) (ms : List Move) (pk sk : DY.Bytes) :
    DY.DiffieHellman.dh pk sk ∉ plaintextTerms (runVis r₀ ms) ++ [] := by
  obtain ⟨p, s, heq⟩ := dh_pack_exists_svl pk sk; rw [heq]
  intro h
  rw [List.append_nil] at h
  exact Symbolic.Swarm.CREF.TR.G1.not_mem_ptAtoms_of_view_random_isNone r₀ ms [] (by intro _ h; cases h)
    (({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack)
    (by rw [Symbolic.DYBridge.DY.BytesView.view?_pack_eq_none DY.Random.Random]; rfl)
    (by rwa [List.append_nil])

private theorem mem_memo_kdfExtract_left_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (salt ikm : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (hs : e ∈ (gamma' i S g salt).memo) :
    e ∈ (gamma' i S g (DY.KdfExtract.kdfExtract salt ikm)).memo := by
  unfold gamma' at hs ⊢
  rw [show DY.KdfExtract.kdfExtract salt ikm =
      ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  simp only [concretizeKdf, node, List.mem_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append]
  exact Or.inr (Or.inl hs)

private theorem mem_memo_kdfExtract_right_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (salt ikm : DY.Bytes) {e : DY.Bytes × DY.Bytes × HwBytes}
    (hi : e ∈ (gamma' i S g ikm).memo) :
    e ∈ (gamma' i S g (DY.KdfExtract.kdfExtract salt ikm)).memo := by
  unfold gamma' at hi ⊢
  rw [show DY.KdfExtract.kdfExtract salt ikm =
      ({ salt := salt, ikm := ikm } : DY.KdfExtract.KdfExtract.SubF DY.Bytes).pack from rfl,
      DY.Bytes.rec_eq (concretizeKdf i) (concretizeAll i S g)]
  simp only [concretizeKdf, node, List.mem_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.mem_append]
  exact Or.inr (Or.inr hi)

/-! ## Memo-Collision Core -/

/-- A receiver chain `c ∈ st.recv` and a non-colliding representation `t` whose ratchet key
`msg.ratchetKey ≠ c.ratchetKey` has the same bytes cannot coexist when
`dh (normalizeX25519Key msg.ratchetKey) sk` and `dh (normalizeX25519Key c.ratchetKey) sk` have
distinct shapes for every `sk` and `x25519LowOrder msg.ratchetKey = false`. -/
theorem false_of_noncolliding_install_of_shape_ne
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem) (g : Ghost) (ms : List Move)
    (hHist : RecvHistInvTR interpretation S g r₀ ms)
    (hIW : Symbolic.Swarm.CREF.TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms))
    {st : TRState} {c : RecvChain} {t : DY.Bytes} {msg : TRSignalMsg}
    (hst : st ∈ availableStates r₀ (runTraceMoves r₀ ms)) (hc : c ∈ st.recv)
    (hparse : parseTrSignalMsg t = some msg) (hver : msg.version = messageVersion)
    (hne : msg.ratchetKey ≠ c.ratchetKey)
    (hsh_ne : ∀ sk : DY.Bytes,
      (gamma' interpretation S g (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key msg.ratchetKey) sk)).shape ≠
        (gamma' interpretation S g (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key c.ratchetKey) sk)).shape)
    (hlow : x25519LowOrder msg.ratchetKey = false)
    (hγ : gamma interpretation S g msg.ratchetKey = gamma interpretation S g c.ratchetKey)
    (hNotCol : ¬RecvCollision interpretation r₀ S g ms t) :
    False := by
  obtain ⟨H, hH, rk1, hHrk, c₁, h₁, hc₁⟩ := hIW st hst c hc
  have hfind : findRecvChain H.recv msg.ratchetKey = none :=
    Symbolic.Swarm.CREF.TR.G1.findRecvChain_none_of_hist_tr hHist hH h₁ hc₁ hne hγ
  let d1 := DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key msg.ratchetKey) H.dhs
  let d2 := DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key c.ratchetKey) H.dhs
  let x₁ : DY.Bytes × DY.Bytes × HwBytes :=
    (d1, (gamma' interpretation S g d1).shape, gamma interpretation S g d1)
  let x₂ : DY.Bytes × DY.Bytes × HwBytes :=
    (d2, (gamma' interpretation S g d2).shape, gamma interpretation S g d2)
  let ckr := (createChain H.rk msg.ratchetKey H.dhs).2
  have hckr_wt : ckr ∈ (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg).flatMap
      (trialTerms (honestSalts r₀ ms) msg) :=
    Symbolic.Swarm.CREF.Stage1Wire.createChain_snd_mem_whisperTrials_terms
      interpretation r₀ S g (runTraceMoves r₀ ms) (honestSalts r₀ ms) H msg hver hH hfind hlow
  have hsub : ∀ u ∈ ([t, ckr] : List DY.Bytes),
      u ∈ t :: (whisperTrials interpretation r₀ S g (runTraceMoves r₀ ms) msg).flatMap
        (trialTerms (honestSalts r₀ ms) msg) := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem t hckr_wt
  have hx1_memo : x₁ ∈ (gamma' interpretation S g ckr).memo := by
    dsimp only [ckr, createChain, DY.X25519.agree, kdfRk, hkdfBlock2, hmac]
    exact mem_memo_kdfExtract_left_svl interpretation S g _ _
      (mem_memo_kdfExtract_right_svl interpretation S g _ _
        (mem_memo_dh_svl interpretation S g (DY.X25519.normalizeX25519Key msg.ratchetKey) H.dhs))
  have hx2_memo : x₂ ∈ (gamma' interpretation S g ckr).memo := by
    dsimp only [ckr, createChain, DY.X25519.agree, kdfRk, hkdfBlock2, hmac]
    refine mem_memo_kdfExtract_left_svl interpretation S g _ _
      (mem_memo_kdfExtract_left_svl interpretation S g _ _ ?_)
    rw [hHrk]
    dsimp only [createChain, DY.X25519.agree, kdfRk, hkdfBlock1, hmac]
    exact mem_memo_kdfExtract_left_svl interpretation S g _ _
      (mem_memo_kdfExtract_right_svl interpretation S g _ _
        (mem_memo_dh_svl interpretation S g (DY.X25519.normalizeX25519Key c.ratchetKey) H.dhs))
  have hckr_ns : ckr ∈ ([t, ckr] : List DY.Bytes) := by simp
  have hx1_new : x₁ ∈ ([t, ckr] : List DY.Bytes).flatMap
      (fun u => (gamma' interpretation S g u).memo) :=
    List.mem_flatMap.mpr ⟨ckr, hckr_ns, hx1_memo⟩
  have hx2_terms : x₂ ∈
      ((prefixTerms r₀ (runTraceMoves r₀ ms) (runVis r₀ ms)).flatMap
        (fun u => (gamma' interpretation S g u).memo)) ++
      ([t, ckr] : List DY.Bytes).flatMap
        (fun u => (gamma' interpretation S g u).memo) :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨ckr, hckr_ns, hx2_memo⟩)
  have hsh_ne' : x₁.2.1 ≠ x₂.2.1 := by
    dsimp only [x₁, x₂, d1, d2]
    exact hsh_ne H.dhs
  have hγeq : x₁.2.2 = x₂.2.2 := by
    dsimp only [x₁, x₂, d1, d2]
    rw [gamma_dh_x25519Key_svl interpretation S g hEq msg.ratchetKey H.dhs,
        gamma_dh_x25519Key_svl interpretation S g hEq c.ratchetKey H.dhs, hγ]
  apply hNotCol
  exact Symbolic.Swarm.CREF.Stage1Wire.recvCollision_of_memoCollisionOn_sub (ns := [t, ckr]) hparse hsub
    ⟨x₁, hx1_new, x₂, hx2_terms, hsh_ne', Or.inl (assumedInjective_dh_svl _ _),
      fun hpt => False.elim (dh_not_mem_ptAtoms_svl r₀ ms _ _ hpt),
      fun hpt => False.elim (dh_not_mem_ptAtoms_svl r₀ ms _ _ hpt),
      hγeq⟩

/-! ## Low-Order Key Exclusion -/

private theorem gamma_literalToBytes_svl (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    (b : ByteArray) :
    gamma i S g (DY.Literal.literalToBytes b) = ofByteArray b := by
  unfold gamma gamma'
  show ((({ lit := b } : DY.Literal.Literal.SubF DY.Bytes).pack).rec (concretizeAll i S g)).bytes = _
  rw [DY.Bytes.rec_eq concretizeLit (concretizeAll i S g)]; rfl

private theorem map_toNat_ofByteArray_svl (ba : ByteArray) :
    (ofByteArray ba).map BitVec.toNat = ba.data.toList.map UInt8.toNat := by
  unfold ofByteArray; rw [List.map_map]; rfl

private theorem isLowOrderKey_variantBytes_svl (p : HwBytes) (v : Fin 4) (hlp : p.length = 32) :
    DY.X25519.isLowOrderKey
        ((DY.Libsignal.Refinement.variantBytes p v).map BitVec.toNat) =
      DY.X25519.isLowOrderKey (p.map BitVec.toNat) := by
  have hs := DY.Libsignal.Refinement.variantBytes_spec _ hlp v
  have hu : DY.X25519.uCoord (p.map BitVec.toNat) =
      DY.X25519.uCoord ((DY.Libsignal.Refinement.variantBytes
        p v).map BitVec.toNat) := hs.2.symm
  have hl' : ((DY.Libsignal.Refinement.variantBytes
      p v).map BitVec.toNat).length = 32 := by
    rw [List.length_map]; exact hs.1
  have hl'' : (p.map BitVec.toNat).length = 32 := by
    rw [List.length_map]; exact hlp
  unfold DY.X25519.isLowOrderKey
  rw [hl', hl'', hu]

private theorem isLowOrderKey_gamma_x25519Key_svl (i : ExternInterpretation) (S : SpqrSem)
    (g : Ghost) (hEq : ExternCryptoLawsHold i) (pk : DY.Bytes) :
    DY.X25519.isLowOrderKey ((gamma i S g (DY.X25519.normalizeX25519Key pk)).map BitVec.toNat) =
      DY.X25519.isLowOrderKey ((gamma i S g pk).map BitVec.toNat) := by
  unfold DY.X25519.normalizeX25519Key
  split
  · rename_i x h; have hv := DY.Bytes.pack_view? DY.X25519.Variant.SubF pk
    simp only [h] at hv; rw [← hv, gamma_x25519Variant_raw_svl i S g x.key x.variation x.torsion]
    by_cases hl : (gamma i S g x.key).length = 32
    · have hlp := (torsionShift_length_svl i (gamma i S g x.key) x.torsion).trans hl
      rw [isLowOrderKey_variantBytes_svl _ _ hlp,
        isLowOrderKey_torsionShift_svl i hEq (gamma i S g x.key) x.torsion hl]
    · rw [torsionShift_of_len_ne_svl i _ _ hl]
      unfold DY.Libsignal.Refinement.variantBytes; simp only [hl, ↓reduceIte]
  · rfl

/-- If `gamma i S g L = gamma i S g pk` and `gamma i S g pk` is not a low-order point, then
`x25519LowOrder L = false`. -/
theorem x25519LowOrder_false_of_gamma_eq_notLow
    (i : ExternInterpretation) (S : SpqrSem) (g : Ghost) (hEq : ExternCryptoLawsHold i)
    {L pk : DY.Bytes}
    (hγ : gamma i S g L = gamma i S g pk)
    (hNotLow : DY.X25519.isLowOrderKey ((gamma i S g pk).map BitVec.toNat) = false) :
    x25519LowOrder L = false := by
  have hpk : DY.X25519.isLowOrderKey ((gamma i S g L).map BitVec.toNat) = false := by
    rw [hγ]; exact hNotLow
  unfold x25519LowOrder
  rcases hb : DY.Literal.bytesToLiteral (DY.X25519.normalizeX25519Key L) with _ | b
  · rfl
  · dsimp only
    have hlit : DY.X25519.normalizeX25519Key L = DY.Literal.literalToBytes b := by
      have := DY.Literal.literalToBytes_bytesToLiteral (DY.X25519.normalizeX25519Key L); rwa [hb] at this
    have h1 := isLowOrderKey_gamma_x25519Key_svl i S g hEq L
    rw [hlit, gamma_literalToBytes_svl, map_toNat_ofByteArray_svl, hpk] at h1
    exact h1

/-! ## Distinct-Base Disjointness -/

private theorem dh_dhPk_pack_cases_svl (a sk : DY.Bytes) :
    DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) sk =
        ({ pk := DY.DiffieHellman.dhPk a, sk := sk } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack ∨
      DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) sk =
        ({ pk := DY.DiffieHellman.dhPk sk, sk := a } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack := by
  dsimp only [DY.DiffieHellman.dh, DY.DiffieHellman.CanDH.dh, DY.DiffieHellman.dhPk,
    DY.DiffieHellman.CanDH.dhPk]
  rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF)]
  dsimp only; split
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem dh_pack_inj_svl {p s p' s' : DY.Bytes}
    (h : ({ pk := p, sk := s } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack =
      ({ pk := p', sk := s' } : DY.DiffieHellman.Dh.SubF DY.Bytes).pack) :
    p = p' ∧ s = s' := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.DiffieHellman.Dh.SubF) h
  rw [DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF),
      DY.BytesView.view_pack (SubF := DY.DiffieHellman.Dh.SubF)] at hv
  injection hv with hmk; injection hmk with h1 h2
  exact ⟨h1, h2⟩

private theorem dhPk_inj_svl {x y : DY.Bytes}
    (h : DY.DiffieHellman.dhPk x = DY.DiffieHellman.dhPk y) : x = y := by
  have hv := congrArg (fun b : DY.Bytes => b.view? DY.DiffieHellman.DhPk.SubF) h
  rw [show DY.DiffieHellman.dhPk x =
      ({ sk := x } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
    show DY.DiffieHellman.dhPk y =
      ({ sk := y } : DY.DiffieHellman.DhPk.SubF DY.Bytes).pack from rfl,
    DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF),
    DY.BytesView.view_pack (SubF := DY.DiffieHellman.DhPk.SubF)] at hv
  injection hv with hmk; injection hmk

/-- Equal `dh` shapes against a `dhPk a` partner force equal shapes of the public keys. -/
theorem shape_eq_of_shape_dh_eq (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {K a sk : DY.Bytes}
    (hsh : (gamma' i S g (DY.DiffieHellman.dh K sk)).shape =
      (gamma' i S g (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) sk)).shape) :
    (gamma' i S g K).shape = (gamma' i S g (DY.DiffieHellman.dhPk a)).shape := by
  rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr]
  cases hK : K.view? DY.DiffieHellman.DhPk.SubF with
  | none =>
    rw [dh_pack_of_view_dhPk_none_svl sk hK, shape_dh_pack_svl] at hsh
    rcases dh_dhPk_pack_cases_svl a sk with h2 | h2 <;>
      rw [h2, shape_dh_pack_svl, Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr] at hsh <;>
      obtain ⟨e1, e2⟩ := dh_pack_inj_svl hsh
    · exact e1
    · rw [e1, e2]
  | some p =>
    have hKp : K = DY.DiffieHellman.dhPk p.sk := by
      have hv := DY.Bytes.pack_view? DY.DiffieHellman.DhPk.SubF K
      simp only [hK] at hv; exact hv.symm
    subst hKp
    rw [Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr]
    congr 1
    rcases dh_dhPk_pack_cases_svl p.sk sk with h1 | h1 <;>
      rcases dh_dhPk_pack_cases_svl a sk with h2 | h2 <;>
      simp only [h1, h2, shape_dh_pack_svl, Symbolic.Swarm.CREF.TR.G1.shape_dhPk_tr] at hsh <;>
      obtain ⟨e1, e2⟩ := dh_pack_inj_svl hsh
    · exact dhPk_inj_svl e1
    · exact (dhPk_inj_svl e1).trans e2
    · exact e2.trans (dhPk_inj_svl e1)
    · exact e2

/-- Against a `ShapeRigid` partner `dhPk a`, equal `dh` shapes force `K = dhPk a`. -/
theorem eq_dhPk_of_shape_dh_eq (i : ExternInterpretation) (S : SpqrSem) (g : Ghost)
    {K a sk : DY.Bytes}
    (hrigid : Symbolic.Swarm.CREF.TR.G1.ShapeRigid (DY.DiffieHellman.dhPk a))
    (hsh : (gamma' i S g (DY.DiffieHellman.dh K sk)).shape =
      (gamma' i S g (DY.DiffieHellman.dh (DY.DiffieHellman.dhPk a) sk)).shape) :
    K = DY.DiffieHellman.dhPk a :=
  Symbolic.Swarm.CREF.TR.G1.eq_of_shape_eq_shapeRigid i S g hrigid
    ((shape_eq_of_shape_dh_eq i S g hsh).trans (hrigid.1 i S g))

/-- Rules out a non-colliding wire representation whose ratchet key matches the bytes of an
installed `CaseA'` non-low-order ratchet key `pk` while differing in normalized X25519 base. -/
theorem false_of_skippedVar_diffBase
    (interpretation : ExternInterpretation) (hEq : ExternCryptoLawsHold interpretation)
    (r₀ : ProtocolSetup) (S : SpqrSem)
    (g' : Ghost) (ms₁ : List Move) (body : HwBytes) (m : SignalMessage)
    (st₁_post : TRState) (c₁ : RecvChain) (t₀ pk : DY.Bytes) (msg₀ : TRSignalMsg)
    (ht₀ : t₀ ∈ recvRepresentations interpretation r₀ S g' ms₁ body)
    (hparse₀ : parseTrSignalMsg t₀ = some msg₀)
    (hver₀ : msg₀.version = messageVersion)
    (htry : SignalMessage.tryFrom protoSignalCodec body = .ok m)
    (hNotCol : ¬RecvCollision interpretation r₀ S g' ms₁ t₀)
    (hst₁_post : st₁_post ∈ availableStates r₀ (runTraceMoves r₀ ms₁))
    (hc₁ : c₁ ∈ st₁_post.recv) (hcpk : c₁.ratchetKey = pk)
    (hCaseA' : Symbolic.Swarm.CREF.TR.G1.CaseA' pk)
    (hrk_ne : msg₀.ratchetKey ≠ pk)
    (hHist : RecvHistInvTR interpretation S g' r₀ ms₁)
    (hIW : Symbolic.Swarm.CREF.TR.G1.InstallWitnessTR r₀ (runTraceMoves r₀ ms₁))
    (hγ_pk : gamma interpretation S g' pk = m.senderRatchetKey.bytes.toList)
    (hbase : ¬DY.X25519.normalizeX25519Key msg₀.ratchetKey = DY.X25519.normalizeX25519Key pk)
    (hNotLow : DY.X25519.isLowOrderKey ((gamma interpretation S g' pk).map BitVec.toNat) = false) :
    False := by
  obtain ⟨a, ha⟩ := hCaseA'.2
  have hrig : Symbolic.Swarm.CREF.TR.G1.ShapeRigid (DY.DiffieHellman.dhPk a) := ha ▸ hCaseA'.1
  have hγ0 : gamma interpretation S g' msg₀.ratchetKey = m.senderRatchetKey.bytes.toList :=
    ((ht₀.2.2.2 msg₀ hparse₀).2.2.2 m htry).2.1
  have hγ : gamma interpretation S g' msg₀.ratchetKey = gamma interpretation S g' c₁.ratchetKey := by
    rw [hγ0, hcpk, hγ_pk]
  have hlow : x25519LowOrder msg₀.ratchetKey = false :=
    x25519LowOrder_false_of_gamma_eq_notLow interpretation S g' hEq (by rw [hγ0, hγ_pk]) hNotLow
  have hsh_ne : ∀ sk : DY.Bytes,
      (gamma' interpretation S g'
        (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key msg₀.ratchetKey) sk)).shape ≠
      (gamma' interpretation S g'
        (DY.DiffieHellman.dh (DY.X25519.normalizeX25519Key c₁.ratchetKey) sk)).shape := by
    intro sk hsh
    rw [hcpk, ha] at hsh
    exact hbase ((eq_dhPk_of_shape_dh_eq interpretation S g' hrig hsh).trans ha.symm)
  exact false_of_noncolliding_install_of_shape_ne interpretation hEq r₀ S g' ms₁ hHist hIW
    hst₁_post hc₁ hparse₀ hver₀ (hcpk ▸ hrk_ne) hsh_ne hlow hγ hNotCol

end RecvDecStep.SkippedVarLit

end Symbolic.Swarm.CREF.TR
