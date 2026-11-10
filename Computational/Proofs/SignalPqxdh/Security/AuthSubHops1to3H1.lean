/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3F
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3B
public import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3C
import Computational.Proofs.SignalPqxdh.Security.AuthSubHops1to3D
import Computational.Proofs.SignalPqxdh.Security.RoKemHop
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.EvalDist.Measure

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 400000
open scoped ENNReal BigOperators
open OracleComp OracleSpec MeasureTheory
open SignalPqxdh SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security
open _root_.Proofs.SignalPqxdh.Security.FgGapDh
namespace SignalPqxdh.Security.AuthSubHops1to3
def finishAuthSendMk {S : Setup} (P : Primitives) (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    AuthResponse × AuthHybridStateFixed S :=
  let st := hst.toAuthHybridState.base
  let isFreshPeer : Bool :=
    match peerPrincipal? with
    | some (_, pEntry) => !pEntry.corrupted
    | none             => false
  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
  let (resp, hst') := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain st.roCache st.rootRoCache
    hst.toAuthHybridState
  (resp, { toAuthHybridState := hst', recvCount := hst.recvCount, mkSaltCache := hst.mkSaltCache })
theorem primBounded_finishAuthSendMkPrim (S : Setup) (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    PrimBounded
      (finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys)
      (S.N_dh * 8 + 4) := by
  unfold finishAuthSendMkPrim
  refine primBounded_bind_le (S.N_dh * 8 + 3) (primBounded_primQ _) (fun _ => ?_) (by omega)
  exact primBounded_bind_le 0
    (primBounded_finishAuthHybridSendPrim S sid uEntry peerPrincipal? _ bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
      spqrSalt? pqRatchetMsg deriveMessageKeys _ _ msgPlain _ _ hst.toAuthHybridState)
    (fun _ => primBounded_pure') (by omega)
def finishAuthSendMkSlots {S : Setup} (P : Primitives) (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) :
    AuthResponse × AuthHybridStateFixed S :=
  let (resp, hst0) := finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
    spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys
  (resp, { hst0 with slots := hst.slots })
theorem simulateQ_finishAuthSendMkPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys)
    (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthSendMkPrim S sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys) =
      pure (finishAuthSendMkSlots P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys) := by
  unfold finishAuthSendMkPrim finishAuthSendMkSlots finishAuthSendMk
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind,
      simulateQ_bind,
      simulateQ_finishAuthHybridSendPrim S P sid uEntry peerPrincipal? _ bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
        spqrSalt? pqRatchetMsg deriveMessageKeys _ _ msgPlain _ _ hst.toAuthHybridState hPrin hSpk hOpk,
      pure_bind]
  rfl
theorem authSlotFired_finishAuthSendMk_mono {S : Setup} (P : Primitives) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys)
    (hFired : authSlotFired S idx hst = true) :
    authSlotFired S idx
      (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys).2 = true := by
  unfold finishAuthSendMk
  exact authSlotFired_finishAuthHybridSend_mono P idx sid uEntry peerPrincipal? _ bundle m0 m1
    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] mkSeed ck1_1
    spqrSalt? pqRatchetMsg deriveMessageKeys _ _ msgPlain _ _ hst hFired
theorem authSlotFired_finishAuthSendMk_self {S : Setup} (P : Primitives) (idx : Nat)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 mkSeed ck1_1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (deriveMessageKeys : MessageKeys) (hSlot : sendSlotIndex? sid = some idx) :
    authSlotFired S idx
      (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys).2 = true := by
  have hlt : idx < S.N_send_tot := sendSlotIndex?_lt hSlot
  unfold authSlotFired finishAuthSendMk finishAuthHybridSend
  simp [hlt, hSlot]
def prepareAuthSendMk (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (PreparedAuthSend S) := do
  let st := hst.toAuthHybridState.base
  if st.hasWonAuth then
    pure (.done .noneResp hst)
  else if m0.length != m1.length then
    pure (.done .noneResp hst)
  else if st.usedSendSessions.contains sid then
    pure (.done .noneResp hst)
  else
    match st.principals.find? (fun (idx, _) => idx == u.val) with
    | none => pure (.done .noneResp hst)
    | some (_, uEntry) =>
      let peerPrincipal? := findHonestPrincipal P st.principals bundle.ikB
      let isFreshPeer : Bool :=
        match peerPrincipal? with
        | some (_, pEntry) => !pEntry.corrupted
        | none             => false
      if !isFreshPeer && m0 != m1 then
        pure (.done .noneResp hst)
      else
        let msgPlain := if isFreshPeer then (if st.secb then m1 else m0) else m0
        if !koskBundleOk P st.principals st.spkBundles st.opkEntries st.advKeys bundle then
          pure (.done .noneResp hst)
        else
          let ekASk ← sampleScalar32
          let kemCoins ← sampleCoins32
          let ephASk ← sampleScalar32
          let spqrCoins ← sampleCoins32
          let sigPkB := resolveSigPk P st.principals bundle.ikB
          if !(P.sigVerify sigPkB (encodeEC bundle.spkB) bundle.spkSig &&
               P.sigVerify sigPkB (encodeKEM bundle.pqspkB) bundle.pqspkSig) then
            pure (.done .noneResp hst)
          else
            match P.kemEncaps bundle.pqspkB kemCoins with
            | none => pure (.done .noneResp hst)
            | some (ss, kemCt) =>
              let ekAPk := P.x25519Base ekASk
              let ephAPk := P.x25519Base ephASk
              let prov := checkBundleProvenanceExact P st.principals st.spkBundles st.opkEntries
                bundle
              let spkHonIdeal := checkBundleSpkHonIdeal P st.principals st.spkBundles bundle
              let isIdealSend : Bool := isFreshPeer || (peerPrincipal?.isSome && spkHonIdeal &&
                prov.2.2)
              if isIdealSend then
                let drKey ← sampleDRKey96
                let rk1 ← sampleBytes32
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.done .noneResp hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  pure (.idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
                    drKey rk1 spqrSalt? pqRatchetMsg msgPlain)
              else
                let dh1 := P.x25519 uEntry.secIKA0 bundle.spkB
                let dh2 := P.x25519 ekASk bundle.ikB
                let dh3 := P.x25519 ekASk bundle.spkB
                let dh4? := bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)
                let secrets := buildSecrets dh1 dh2 dh3 dh4? ss
                let (drKey, roCache') ← evalHkdfOrRo true P st.roCache secrets
                let dhRatchet := P.x25519 ephASk bundle.spkB
                let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache
                  drKey.rootKey dhRatchet
                let mkSeed := P.chainKdfSeed ck1_0
                let ck1_1 := P.chainKdfNext ck1_0
                match P.spqrInitSend drKey.pqrKey spqrCoins with
                | none => pure (.done .noneResp hst)
                | some (_pqrStA, spqrSalt?, pqRatchetMsg) =>
                  let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
                  let ad := firstMsgAD uEntry.ikAPk bundle.ikB ephAPk pqRatchetMsg
                  let aeadCt := P.aeadEnc deriveMessageKeys ad msgPlain
                  let (resp, hst') := finishAuthHybridSend P sid uEntry peerPrincipal? isFreshPeer
                    bundle m0 m1
                    ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 ck1_0 mkSeed ck1_1
                    spqrSalt? pqRatchetMsg deriveMessageKeys ad aeadCt msgPlain roCache' rootRoCache'
                    hst.toAuthHybridState
                  pure (.done resp { toAuthHybridState := hst', recvCount := hst.recvCount,
                                     mkSaltCache := hst.mkSaltCache })
private theorem primBounded_ite {α : Type} (c : Bool) (t e : OracleComp PrimBaseSpec α) (n : Nat)
    (ht : PrimBounded t n) (he : PrimBounded e n) : PrimBounded (if c then t else e) n := by
  cases c <;> [exact he; exact ht]
theorem primBounded_prepareAuthSendMkPrim (S : Setup)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    PrimBounded (prepareAuthSendMkPrim S sid u bundle m0 m1 hst) (S.N_dh * 22 + 21) := by
  unfold prepareAuthSendMkPrim
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte]
  swap; · exact primBounded_pure'
  split
  · exact primBounded_pure'
  · split
    · exact primBounded_pure'
    · split
      · exact primBounded_pure'
      · refine primBounded_bind_le (S.N_dh * 20 + 21)
          (primBounded_findHonestPrincipalPrim S hst.toAuthHybridState.base.principals bundle.ikB)
          (fun peerPrincipal? => ?_) (by omega)
        refine primBounded_ite _ _ _ _ primBounded_pure' ?_
        · refine primBounded_bind_le (S.N_dh * 14 + 18)
            (primBounded_koskBundleOkPrim S _ _ _ _ bundle)
            (fun koskOk => ?_) (by omega)
          by_cases hKosk : (!koskOk) = true
          · simp only [hKosk, ↓reduceIte]; exact primBounded_pure'
          · simp only [hKosk, Bool.false_eq_true, ↓reduceIte]
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleScalar32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleCoins32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleScalar32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 14 + 18) (primBounded_embedUnif sampleCoins32 0)
              (fun _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 12 + 18) (primBounded_resolveSigPkPrim S _ _) (fun
              _ => ?_) (by omega)
            refine primBounded_bind_le (S.N_dh * 12 + 17) (primBounded_primQ _) (fun v1 => ?_) (by
              omega)
            refine primBounded_bind_le (S.N_dh * 12 + 16) (primBounded_primQ _) (fun v2 => ?_) (by
              omega)
            by_cases hSig : (!(v1 && v2)) = true
            · simp only [hSig, ↓reduceIte]; exact primBounded_pure'
            · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
              refine primBounded_bind_le (S.N_dh * 12 + 15) (primBounded_primQ _) (fun kem? => ?_)
                (by omega)
              cases kem? with
              | none => exact primBounded_pure'
              | some pair =>
                rcases pair with ⟨ss, kemCt⟩
                dsimp only
                refine primBounded_bind_le (S.N_dh * 12 + 14) (primBounded_primQ _) (fun _ => ?_)
                  (by omega)
                refine primBounded_bind_le (S.N_dh * 12 + 13) (primBounded_primQ _) (fun _ => ?_)
                  (by omega)
                refine primBounded_bind_le (S.N_dh * 8 + 13)
                  (primBounded_checkBundleSpkHonIdealPrim S _ _ bundle) (fun _ => ?_) (by omega)
                refine primBounded_ite _ _ _ _ ?_ ?_
                · refine primBounded_bind_le (S.N_dh * 8 + 13) (primBounded_embedUnif sampleDRKey96
                    0) (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 13) (primBounded_embedUnif sampleBytes32
                    0) (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 12) (primBounded_primQ _) (fun spqr? =>
                    ?_) (by omega)
                  cases spqr? with
                  | none => exact primBounded_pure'
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                    exact primBounded_pure'
                · refine primBounded_bind_le (S.N_dh * 8 + 12) (primBounded_primQ _) (fun _ => ?_)
                    (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 11) (primBounded_primQ _) (fun _ => ?_)
                    (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 10) (primBounded_primQ _) (fun _ => ?_)
                    (by omega)
                  have hDh4 : ∀ ekASk, PrimBounded
                      (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                        let d4 ← primQ (.x25519 ekASk opkPk)
                        pure (some d4))) 1 := by
                    intro ekASk
                    cases bundle.opkB? with
                    | none => exact primBounded_pure'
                    | some p =>
                      exact primBounded_bind_le 0 (primBounded_primQ _) (fun _ => primBounded_pure')
                        (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 9) (hDh4 _) (fun _ => ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 9) (primBounded_embedUnif _ 0) (fun _ =>
                    ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 8) (primBounded_primQ _) (fun _ => ?_)
                    (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 8) (primBounded_embedUnif _ 0) (fun _ =>
                    ?_) (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 7) (primBounded_primQ _) (fun _ => ?_)
                    (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 6) (primBounded_primQ _) (fun _ => ?_)
                    (by omega)
                  refine primBounded_bind_le (S.N_dh * 8 + 5) (primBounded_primQ _) (fun spqr? =>
                    ?_) (by omega)
                  cases spqr? with
                  | none => exact primBounded_pure'
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                    dsimp only
                    refine primBounded_bind_le (S.N_dh * 8 + 4) (primBounded_primQ _) (fun _ => ?_)
                      (by omega)
                    refine primBounded_bind_le (S.N_dh * 8 + 3) (primBounded_primQ _) (fun _ => ?_)
                      (by omega)
                    exact primBounded_bind_le 0
                      (primBounded_finishAuthHybridSendPrim S sid _ _ _ bundle m0 m1
                        _ _ ss kemCt _ _ _ _ _ _ _ spqrSalt? pqRatchetMsg _ _ _ _ _ _
                          hst.toAuthHybridState)
                      (fun _ => primBounded_pure') (by omega)
def prepareAuthSendMkSlots (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (PreparedAuthSend S) :=
  PreparedAuthSend.mapState (fun hst0 => { hst0 with slots := hst.slots }) <$>
    prepareAuthSendMk S P sid u bundle m0 m1 hst
theorem simulateQ_prepareAuthSendMkPrim (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hPrin : hst.toAuthHybridState.base.principals.length ≤ S.N_dh)
    (hSpk : hst.toAuthHybridState.base.spkBundles.length ≤ S.N_dh)
    (hOpk : hst.toAuthHybridState.base.opkEntries.length ≤ S.N_dh)
    (hAdv : ValidAdvKeysPow8 P hst.toAuthHybridState.base.advKeys) :
    simulateQ (primBaseImpl P) (prepareAuthSendMkPrim S sid u bundle m0 m1 hst) =
      prepareAuthSendMkSlots S P sid u bundle m0 m1 hst := by
  unfold prepareAuthSendMkPrim prepareAuthSendMkSlots prepareAuthSendMk
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte]
  swap; · simp [PreparedAuthSend.mapState]
  by_cases hLen : (m0.length != m1.length) = true
  · simp [hLen, PreparedAuthSend.mapState]
  · simp only [hLen, Bool.false_eq_true, ↓reduceIte]
    by_cases hUsed : (hst.toAuthHybridState.base.usedSendSessions.contains sid) = true
    · simp only [hUsed, ↓reduceIte]; simp [PreparedAuthSend.mapState]
    · simp only [hUsed, Bool.false_eq_true, ↓reduceIte]
      cases hst.toAuthHybridState.base.principals.find? (fun (idx, _) => idx == u.val) with
      | none => simp [PreparedAuthSend.mapState]
      | some uPair =>
        rcases uPair with ⟨_, uEntry⟩
        dsimp only
        rw [simulateQ_bind,
            simulateQ_findHonestPrincipalPrim S P hst.toAuthHybridState.base.principals bundle.ikB
              hPrin,
            pure_bind]
        have hProv2 := (checkBundleProvenanceExact_spk_pqspk P hst.toAuthHybridState.base.principals
          hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries bundle).2
        cases hpeer : findHonestPrincipal P hst.toAuthHybridState.base.principals bundle.ikB with
        | none =>
          dsimp only
          by_cases hCh : (m0 != m1) = true
          · simp [hCh, PreparedAuthSend.mapState]
          · simp only [Bool.not_false, Bool.true_and, hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind, simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv,
              pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp [hKosk, PreparedAuthSend.mapState]
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
                map_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins; congr 1; funext ephASk; congr 1;
                funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals
                bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp [hSig, PreparedAuthSend.mapState]
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => simp [PreparedAuthSend.mapState]
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind]
                  simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true,
                    ↓reduceIte]
                  rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                  have hDh4 : simulateQ (primBaseImpl P)
                      (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                        let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                      pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                    cases bundle.opkB? with
                    | none => rfl
                    | some opkPair => rcases opkPair with ⟨_, opkPk⟩; simp only [simulateQ_bind,
                      simulateQ_pure]; rfl
                  rw [simulateQ_bind, hDh4, pure_bind]
                  simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure,
                    map_bind]
                  congr 1; funext ⟨drKey, roCache'⟩
                  rw [simulateQ_primQ_x25519, pure_bind]
                  simp only [evalRootKdfOrRo_true_eq_pure]
                  congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                  rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                      simulateQ_primQ_chainKdfNext, pure_bind, simulateQ_primQ_spqrInitSend,
                        pure_bind]
                  cases P.spqrInitSend drKey.pqrKey spqrCoins with
                  | none => simp [PreparedAuthSend.mapState]
                  | some spqrVal =>
                    rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                    rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                        simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                        simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1 ekASk _ ss
                          kemCt
                          ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg _ _ _ _ roCache'
                            rootRoCache'
                          hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                    simp [PreparedAuthSend.mapState]
        | some pPair =>
          rcases pPair with ⟨pIdx, pEntry⟩; dsimp only
          rw [hpeer] at hProv2
          by_cases hCh : (!!pEntry.corrupted && (m0 != m1)) = true
          · simp only [hCh, ↓reduceIte]; simp [PreparedAuthSend.mapState]
          · simp only [hCh, Bool.false_eq_true, ↓reduceIte]
            rw [simulateQ_bind, simulateQ_koskBundleOkPrim S P _ _ _ _ bundle hPrin hSpk hOpk hAdv,
              pure_bind]
            by_cases hKosk : (!koskBundleOk P hst.toAuthHybridState.base.principals
                hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                hst.toAuthHybridState.base.advKeys bundle) = true
            · simp [hKosk, PreparedAuthSend.mapState]
            · simp only [hKosk, Bool.false_eq_true, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif,
                map_bind]
              congr 1; funext ekASk; congr 1; funext kemCoins; congr 1; funext ephASk; congr 1;
                funext spqrCoins
              rw [simulateQ_resolveSigPkPrim S P _ bundle.ikB hPrin, pure_bind,
                  simulateQ_primQ_sigVerify, pure_bind, simulateQ_primQ_sigVerify, pure_bind]
              by_cases hSig : (!(P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals
                bundle.ikB)
                    (encodeEC bundle.spkB) bundle.spkSig &&
                  P.sigVerify (resolveSigPk P hst.toAuthHybridState.base.principals bundle.ikB)
                    (encodeKEM bundle.pqspkB) bundle.pqspkSig)) = true
              · simp [hSig, PreparedAuthSend.mapState]
              · simp only [hSig, Bool.false_eq_true, ↓reduceIte]
                rw [simulateQ_bind, simulateQ_primQ_kemEncaps, pure_bind]
                cases P.kemEncaps bundle.pqspkB kemCoins with
                | none => simp [PreparedAuthSend.mapState]
                | some pair =>
                  rcases pair with ⟨ss, kemCt⟩; dsimp only
                  rw [simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind, simulateQ_primQ_x25519Base, pure_bind,
                      simulateQ_bind,
                      simulateQ_checkBundleSpkHonIdealPrim S P hst.toAuthHybridState.base.principals
                        hst.toAuthHybridState.base.spkBundles bundle hPrin hSpk,
                      pure_bind, ← hProv2]
                  by_cases hIdeal : (!pEntry.corrupted ||
                      ((some (pIdx, pEntry)).isSome &&
                       checkBundleSpkHonIdeal P hst.toAuthHybridState.base.principals
                         hst.toAuthHybridState.base.spkBundles bundle &&
                       (checkBundleProvenanceExact P hst.toAuthHybridState.base.principals
                         hst.toAuthHybridState.base.spkBundles hst.toAuthHybridState.base.opkEntries
                           bundle).2.2)) = true
                  · simp only [hIdeal, ↓reduceIte, simulateQ_bind, simulateQ_embedUnif, map_bind]
                    congr 1; funext drKey; congr 1; funext rk1
                    rw [simulateQ_primQ_spqrInitSend, pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => simp [PreparedAuthSend.mapState]
                    | some spqrVal => rcases spqrVal with ⟨_, _, _⟩; simp [PreparedAuthSend.mapState]
                  · simp only [hIdeal, Bool.false_eq_true, ↓reduceIte]
                    rw [simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind,
                        simulateQ_bind, simulateQ_primQ_x25519, pure_bind]
                    have hDh4 : simulateQ (primBaseImpl P)
                        (Option.casesOn bundle.opkB? (pure none) (fun (_, opkPk) => do
                          let d4 ← primQ (.x25519 ekASk opkPk); pure (some d4))) =
                        pure (bundle.opkB?.map (fun (_, opkPk) => P.x25519 ekASk opkPk)) := by
                      cases bundle.opkB? with
                      | none => rfl
                      | some opkPair => rcases opkPair with ⟨_, opkPk⟩; simp only [simulateQ_bind,
                        simulateQ_pure]; rfl
                    rw [simulateQ_bind, hDh4, pure_bind]
                    simp only [simulateQ_bind, simulateQ_embedUnif, evalHkdfOrRo_true_eq_pure,
                      map_bind]
                    congr 1; funext ⟨drKey, roCache'⟩
                    rw [simulateQ_primQ_x25519, pure_bind]
                    simp only [evalRootKdfOrRo_true_eq_pure]
                    congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
                    rw [simulateQ_primQ_chainKdfSeed, pure_bind,
                        simulateQ_primQ_chainKdfNext, pure_bind, simulateQ_primQ_spqrInitSend,
                          pure_bind]
                    cases P.spqrInitSend drKey.pqrKey spqrCoins with
                    | none => simp [PreparedAuthSend.mapState]
                    | some spqrVal =>
                      rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩; dsimp only
                      rw [simulateQ_bind, simulateQ_primQ_deriveMsgKeys, pure_bind,
                          simulateQ_bind, simulateQ_primQ_aeadEnc, pure_bind, simulateQ_bind,
                          simulateQ_finishAuthHybridSendPrim S P sid _ _ _ bundle m0 m1 ekASk _ ss
                            kemCt
                            ephASk _ drKey rk1 ck1_0 _ _ spqrSalt? pqRatchetMsg _ _ _ _ roCache'
                              rootRoCache'
                            hst.toAuthHybridState hPrin hSpk hOpk, pure_bind]
                      simp [PreparedAuthSend.mapState]
theorem prepareAuthSendMk_cacheAuthAdvKeysFixed (S : Setup) (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    prepareAuthSendMk S P sid u bundle m0 m1 (cacheAuthAdvKeysFixed P hst) =
      PreparedAuthSend.mapState (cacheAuthAdvKeysFixed P) <$>
        prepareAuthSendMk S P sid u bundle m0 m1 hst := by
  have hWon : (cacheAuthAdvKeysFixed P hst).toAuthHybridState.base.hasWonAuth =
      hst.toAuthHybridState.base.hasWonAuth := rfl
  unfold prepareAuthSendMk
  dsimp only
  rw [hWon]
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte]
  swap; · simp [PreparedAuthSend.mapState]
  unfold cacheAuthAdvKeysFixed cacheAuthAdvKeys
  dsimp only
  rw [koskBundleOk_cacheAuthAdvKeys]
  split; · simp [PreparedAuthSend.mapState]
  split; · simp [PreparedAuthSend.mapState]
  split
  · simp [PreparedAuthSend.mapState]
  · split
    · simp [PreparedAuthSend.mapState]
    · split
      · simp [PreparedAuthSend.mapState]
      · simp only [map_bind]
        congr 1; funext ekASk; congr 1; funext kemCoins; congr 1; funext ephASk; congr 1; funext
          spqrCoins
        split
        · simp [PreparedAuthSend.mapState]
        · cases P.kemEncaps bundle.pqspkB kemCoins with
          | none => simp [PreparedAuthSend.mapState]
          | some pair =>
            rcases pair with ⟨ss, kemCt⟩
            dsimp only
            split
            · simp only [map_bind]
              congr 1; funext drKey
              congr 1; funext rk1
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [PreparedAuthSend.mapState]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                simp [PreparedAuthSend.mapState]
            · simp only [map_bind]
              congr 1; funext ⟨drKey, roCache'⟩
              congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
              cases P.spqrInitSend drKey.pqrKey spqrCoins with
              | none => simp [PreparedAuthSend.mapState]
              | some spqrVal =>
                rcases spqrVal with ⟨_, spqrSalt?, pqRatchetMsg⟩
                dsimp only
                simp [PreparedAuthSend.mapState, finishAuthHybridSend]
def finishAuthRecvMk {S : Setup} (P : Primitives) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) :
    AuthResponse × AuthHybridStateFixed S :=
  let st := prep.hstDec.base
  let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
  let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
    (drKey, rk1, ck1_1, pt, st.roCache, st.rootRoCache))
  let (resp, hst') := prep.finish res?
  (resp, { toAuthHybridState := hst', recvCount := recvCount', mkSaltCache := mkSaltCache' })
theorem primBounded_finishAuthRecvMkSlotsPrim (S : Setup)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (recvCount' : Nat) (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState)
    (deriveMessageKeys : MessageKeys) :
    PrimBounded
      (finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' slots'
        deriveMessageKeys)
      (S.N_dh * 12 + 1) := by
  unfold finishAuthRecvMkSlotsPrim
  refine primBounded_bind_le (S.N_dh * 12) (primBounded_primQ _) (fun _ => ?_) (by omega)
  exact primBounded_bind_le 0
    (primBounded_recvFinishTag_runPrim S true prep.finishTag _)
    (fun _ => primBounded_pure') (by omega)

theorem primBounded_finishAuthRecvMkPrim (S : Setup)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (recvCount' : Nat) (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) :
    PrimBounded
      (finishAuthRecvMkPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' deriveMessageKeys)
      (S.N_dh * 12 + 1) :=
  primBounded_finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' {}
    deriveMessageKeys

theorem authSlotFired_finishAuthRecvMk_self {S : Setup} (P : Primitives) (idx : Nat)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) (hSlot : S.N_send_tot + hst.recvCount = idx) :
    authSlotFired S idx
      (finishAuthRecvMk P msg prep drKey rk1 ck1_1 (hst.recvCount + 1) mkSaltCache' deriveMessageKeys).2 =
        true := by
  have hge : ¬ (idx < S.N_send_tot) := by omega
  unfold authSlotFired finishAuthRecvMk
  simp only [hge, ↓reduceIte, decide_eq_true_eq]
  omega
theorem simulateQ_finishAuthRecvMkPrim (S : Setup) (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (recvCount' : Nat) (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) (hPrin : prep.finishTag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthRecvMkPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' deriveMessageKeys) =
      pure (finishAuthRecvMk P msg (prep.toPure true P) drKey rk1 ck1_1 recvCount' mkSaltCache'
        deriveMessageKeys) := by
  unfold finishAuthRecvMkPrim finishAuthRecvMkSlotsPrim finishAuthRecvMk PreparedAuthRecvPrim.toPure
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind,
      simulateQ_bind,
      simulateQ_recvFinishTag_runPrim S true P prep.finishTag _ hPrin hSentOPK hSentNoOPK,
      pure_bind]
  rfl
def finishAuthRecvMkSlots {S : Setup} (P : Primitives) (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 ck1_1 : Bytes) (recvCount' : Nat)
    (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState)
    (deriveMessageKeys : MessageKeys) :
    AuthResponse × AuthHybridStateFixed S :=
  let (resp, hst0) := finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache'
    deriveMessageKeys
  (resp, { hst0 with slots := slots' })
theorem simulateQ_finishAuthRecvMkSlotsPrim (S : Setup) (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (recvCount' : Nat) (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (slots' : AuthSlotState)
    (deriveMessageKeys : MessageKeys) (hPrin : prep.finishTag.hstDec.base.principals.length ≤ S.N_dh)
    (hSentOPK : prep.finishTag.hstDec.base.sentOPKEvents.length ≤ S.N_dh)
    (hSentNoOPK : prep.finishTag.hstDec.base.sentNoOPKEvents.length ≤ S.N_dh) :
    simulateQ (primBaseImpl P)
      (finishAuthRecvMkSlotsPrim S msg prep drKey rk1 ck1_1 recvCount' mkSaltCache' slots'
        deriveMessageKeys) =
      pure (finishAuthRecvMkSlots P msg (prep.toPure true P) drKey rk1 ck1_1 recvCount'
        mkSaltCache' slots' deriveMessageKeys) := by
  unfold finishAuthRecvMkSlotsPrim finishAuthRecvMkSlots finishAuthRecvMk PreparedAuthRecvPrim.toPure
  dsimp only
  rw [simulateQ_bind, simulateQ_primQ_aeadDec, pure_bind,
      simulateQ_bind,
      simulateQ_recvFinishTag_runPrim S true P prep.finishTag _ hPrin hSentOPK hSentNoOPK,
      pure_bind]
  rfl
theorem finishAuthRecvMk_mapState_cacheAuthAdvKeys {S : Setup} (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecvPrim S) (drKey : DRKey) (rk1 ck1_1 : Bytes)
    (recvCount' : Nat) (mkSaltCache' : List ((SessionId S × Option Bytes) × (Nat × MessageKeys)))
    (deriveMessageKeys : MessageKeys) :
    finishAuthRecvMk P msg ((prep.mapState (cacheAuthAdvKeys P)).toPure true P)
      drKey rk1 ck1_1 recvCount' mkSaltCache' deriveMessageKeys =
    let (resp, hst') := finishAuthRecvMk P msg (prep.toPure true P) drKey rk1 ck1_1 recvCount'
      mkSaltCache' deriveMessageKeys
    (resp, cacheAuthAdvKeysFixed P hst') := by
  unfold finishAuthRecvMk PreparedAuthRecvPrim.mapState PreparedAuthRecvPrim.toPure
    cacheAuthAdvKeysFixed
  simp only [cacheAuthAdvKeys_roCache, cacheAuthAdvKeys_rootRoCache,
    recvFinishTag_mapState_toPure_fst, recvFinishTag_mapState_toPure_snd]
def finishAuthSendAfterMk {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) :
    ProbComp (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt (sessionSlotIndex sid) then do
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys ← sampleMessageKeys80
    pure (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys)
  else do
    let mkSeed ← sampMkAt (sessionSlotIndex sid)
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    pure (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
      spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys)
def finishAuthSendAfterMkSlot {S : Setup} (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM Bytes (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt (sessionSlotIndex sid) then
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys ← sampleMessageKeys80
      pure (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 [] ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys))
  else do
    let mkSeed ← getRkAtSlot idx (sessionSlotIndex sid)
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      pure (finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1
        spqrSalt? pqRatchetMsg msgPlain hst deriveMessageKeys))
def authMkSendWith (S : Setup) (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  match ← prepareAuthSendMk S P sid u bundle m0 m1 hst with
  | .done resp hst' => pure (resp, hst')
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    finishAuthSendAfterMk P sampMkAt useIdealMkAt sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst
def authMkSendSlot (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) : SlotM Bytes (AuthResponse × AuthHybridStateFixed S) := do
  match ← (liftM (prepareAuthSendMk S P sid u bundle m0 m1 hst) : SlotM Bytes (PreparedAuthSend S))
    with
  | .done resp hst' => pure (resp, hst')
  | .idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk
      drKey rk1 spqrSalt? pqRatchetMsg msgPlain =>
    finishAuthSendAfterMkSlot P idx useIdealMkAt sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst
def finishAuthRecvUnmatchedAfterMk {S : Setup} (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    ProbComp (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt rSlot then do
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys ← sampleMessageKeys80
    pure (finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys)
  else do
    let mkSeed ← sampMkAt rSlot
    let ck1_1 ← sampleBytes32
    let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
    pure (finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys)
def finishAuthRecvUnmatchedAfterMkSlot {S : Setup} (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (rSlot recvCount' : Nat)
    (mkSaltCache : List ((SessionId S × Option Bytes) × (Nat × MessageKeys))) :
    SlotM Bytes (AuthResponse × AuthHybridStateFixed S) :=
  if useIdealMkAt rSlot then
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys ← sampleMessageKeys80
      pure (finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys))
  else do
    let mkSeed ← getRkAtSlot idx rSlot
    liftM (do
      let ck1_1 ← sampleBytes32
      let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
      pure (finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' mkSaltCache deriveMessageKeys))
def authMkRecvWith (S : Setup) (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : ProbComp (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  let rSlot := S.N_send_tot + hst.recvCount
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                          mkSaltCache := hst.mkSaltCache })
          | some (_pqrStB, spqrSalt?) =>
            let (deriveMessageKeys, mkSaltCache') ←
              if useIdealMkAt (sessionSlotIndex s.sid) then
                if sameSaltKey spqrSalt? s.spqrSalt? then
                  pure (s.deriveMessageKeys, hst.mkSaltCache)
                else
                  match hst.mkSaltCache.find? (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
                  | some (_, (_, mk)) => pure (mk, hst.mkSaltCache)
                  | none => do
                    let mk ← sampleMessageKeys80
                    pure (mk, ((s.sid, spqrSalt?), (hst.recvCount, mk)) :: hst.mkSaltCache)
              else
                pure (P.deriveMsgKeys s.mkSeed spqrSalt?, hst.mkSaltCache)
            pure (finishAuthRecvMk P msg prep s.drKey s.rk1 s.ck1_1 recvCount' mkSaltCache' deriveMessageKeys)
        else
          let rk1 ← sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                          mkSaltCache := hst.mkSaltCache })
          | some (_pqrStB, spqrSalt?) =>
            finishAuthRecvUnmatchedAfterMk P sampMkAt useIdealMkAt msg prep s.drKey rk1
              spqrSalt? rSlot recvCount' hst.mkSaltCache
      | none =>
        let drKey ← sampleDRKey96
        let rk1 ← sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache })
        | some (_pqrStB, spqrSalt?) =>
          finishAuthRecvUnmatchedAfterMk P sampMkAt useIdealMkAt msg prep drKey rk1
            spqrSalt? rSlot recvCount' hst.mkSaltCache
    else
      let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
      let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache drKey.rootKey
        prep.dhRatchet
      let mkSeed := P.chainKdfSeed ck1_0
      let ck1_1 := P.chainKdfNext ck1_0
      match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none =>
        let (resp, hst') := prep.finish none
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                      mkSaltCache := hst.mkSaltCache })
      | some (_pqrStB, spqrSalt?) =>
        let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
        let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
        let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
          (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
        let (resp, hst') := prep.finish res?
        pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                      mkSaltCache := hst.mkSaltCache })
def authMkRecvSlot (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) : SlotM Bytes (AuthResponse × AuthHybridStateFixed S) := do
  let recvCount' := hst.recvCount + 1
  let rSlot := S.N_send_tot + hst.recvCount
  match prep? with
  | none => pure (.noneResp, { hst with recvCount := recvCount' })
  | some prep =>
    let st := prep.hstDec.base
    let useIdealBranch : Bool := prep.matchedSess?.isSome || prep.isUncorruptedHonestSender
    if useIdealBranch then
      match prep.matchedSess? with
      | some s =>
        if prep.sameEph then
          liftM (show ProbComp (AuthResponse × AuthHybridStateFixed S) from do
            match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
            | none =>
              let (resp, hst') := prep.finish none
              pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                            mkSaltCache := hst.mkSaltCache })
            | some (_pqrStB, spqrSalt?) =>
              let (deriveMessageKeys, mkSaltCache') ←
                if useIdealMkAt (sessionSlotIndex s.sid) then
                  if sameSaltKey spqrSalt? s.spqrSalt? then
                    pure (s.deriveMessageKeys, hst.mkSaltCache)
                  else
                    match hst.mkSaltCache.find?
                        (fun (k, _) => mkSaltKeyMatch k s.sid spqrSalt?) with
                    | some (_, (_, mk)) => pure (mk, hst.mkSaltCache)
                    | none => do
                      let mk ← sampleMessageKeys80
                      pure (mk, ((s.sid, spqrSalt?), (hst.recvCount, mk)) :: hst.mkSaltCache)
                else
                  pure (P.deriveMsgKeys s.mkSeed spqrSalt?, hst.mkSaltCache)
              pure (finishAuthRecvMk P msg prep s.drKey s.rk1 s.ck1_1 recvCount' mkSaltCache'
                deriveMessageKeys))
        else
          let rk1 ← liftM sampleBytes32
          match P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none =>
            let (resp, hst') := prep.finish none
            pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                          mkSaltCache := hst.mkSaltCache })
          | some (_pqrStB, spqrSalt?) =>
            finishAuthRecvUnmatchedAfterMkSlot P idx useIdealMkAt msg prep s.drKey rk1
              spqrSalt? rSlot recvCount' hst.mkSaltCache
      | none =>
        let drKey ← liftM sampleDRKey96
        let rk1 ← liftM sampleBytes32
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache })
        | some (_pqrStB, spqrSalt?) =>
          finishAuthRecvUnmatchedAfterMkSlot P idx useIdealMkAt msg prep drKey rk1
            spqrSalt? rSlot recvCount' hst.mkSaltCache
    else
      liftM (do
        let (drKey, roCache') ← evalHkdfOrRo true P st.roCache prep.secrets
        let ((rk1, ck1_0), rootRoCache') ← evalRootKdfOrRo true P st.rootRoCache drKey.rootKey
          prep.dhRatchet
        let mkSeed := P.chainKdfSeed ck1_0
        let ck1_1 := P.chainKdfNext ck1_0
        match P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none =>
          let (resp, hst') := prep.finish none
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache })
        | some (_pqrStB, spqrSalt?) =>
          let deriveMessageKeys := P.deriveMsgKeys mkSeed spqrSalt?
          let ad := firstMsgAD msg.hdr.ikAPk prep.kEntry.ikAPk msg.ephAPk msg.pqRatchetMsg
          let res? := (P.aeadDec deriveMessageKeys ad msg.aeadCt).map (fun pt =>
            (drKey, rk1, ck1_1, pt, roCache', rootRoCache'))
          let (resp, hst') := prep.finish res?
          pure (resp, { toAuthHybridState := hst', recvCount := recvCount',
                        mkSaltCache := hst.mkSaltCache }))
def authMkStepWith (S : Setup) (P : Primitives)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    ProbComp ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authMkSendWith S P sampMkAt useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authMkSendWith S P sampMkAt useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authMkRecvWith S P sampMkAt useIdealMkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authMkRecvWith S P sampMkAt useIdealMkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    authCkOtherStep S P qOther hst
def authMkStepSlot (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM Bytes ((authSpec S).Range q × AuthHybridStateFixed S) :=
  match q with
  | .sendOPK u i bundle m0 m1 =>
    if bundle.opkB?.isNone then pure (.noneResp, hst)
    else authMkSendSlot S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  | .sendNoOPK u i bundle m0 m1 =>
    if bundle.opkB?.isSome then pure (.noneResp, hst)
    else authMkSendSlot S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  | .recvOPK k j o msg =>
    authMkRecvSlot S P idx useIdealMkAt msg
      (prepareAuthHybridRecvOPK true P k j o msg hst.toAuthHybridState) hst
  | .recvNoOPK k j l msg =>
    authMkRecvSlot S P idx useIdealMkAt msg
      (prepareAuthHybridRecvNoOPK true P k j l msg hst.toAuthHybridState) hst
  | qOther =>
    liftM (authCkOtherStep S P qOther hst)
theorem authMkSendSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst) := by
  unfold authMkSendSlot finishAuthSendAfterMkSlot
  apply SlotM.SlotComp.liftComp_bind
  intro prep
  cases prep
  · exact SlotM.SlotComp.pure sampleBytes32 _
  · dsimp only
    split
    · exact SlotM.SlotComp.liftComp sampleBytes32 _
    · exact slotComp_getRkAtSlot_bind_liftM idx (sessionSlotIndex sid) _
theorem authMkRecvSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkRecvSlot S P idx useIdealMkAt msg prep? hst) := by
  unfold authMkRecvSlot finishAuthRecvUnmatchedAfterMkSlot; dsimp only
  repeat (first
    | apply SlotM.SlotComp.pure
    | apply SlotM.SlotComp.liftComp
    | apply slotComp_getRkAtSlot_bind_liftM
    | (apply SlotM.SlotComp.liftComp_bind; intro _)
    | split)
theorem authMkStepSlot_slotComp (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotM.SlotComp sampleBytes32 (authMkStepSlot S P idx useIdealMkAt q hst) := by
  cases q <;> unfold authMkStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authMkSendSlot_slotComp S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotM.SlotComp.pure sampleBytes32 _
    · exact authMkSendSlot_slotComp S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authMkRecvSlot_slotComp S P idx useIdealMkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_slotComp S P idx useIdealMkAt msg _ hst
  all_goals
    exact SlotM.SlotComp.liftComp sampleBytes32 _
theorem authMkSendSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (mkSeedStar : Bytes) (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 :
      Bytes)
    (hst : AuthHybridStateFixed S) :
    (authMkSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst).run' (some mkSeedStar) =
      authMkSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt
        sid u bundle m0 m1 hst := by
  unfold authMkSendSlot authMkSendWith finishAuthSendAfterMkSlot finishAuthSendAfterMk
  rw [SlotM.run'_liftComp_bind]
  congr 1; funext prep
  cases prep
  · exact SlotM.run'_pure _ _
  · dsimp only
    split
    · exact SlotM.run'_liftComp _ _
    · exact run'_getRkAtSlot_bind_liftM_some idx (sessionSlotIndex sid) mkSeedStar _
theorem authMkRecvSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (mkSeedStar : Bytes) (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) :
    (authMkRecvSlot S P idx useIdealMkAt msg prep? hst).run' (some mkSeedStar) =
      authMkRecvWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt
        msg prep? hst := by
  unfold authMkRecvSlot authMkRecvWith finishAuthRecvUnmatchedAfterMkSlot
    finishAuthRecvUnmatchedAfterMk
  dsimp only
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [SlotM.run'_liftComp]
    | rw [run'_getRkAtSlot_bind_liftM_some]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)
theorem authMkStepSlot_run'_some (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkStepSlot S P idx useIdealMkAt q hst).run' (some mkSeedStar) =
      authMkStepWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt
        q hst := by
  cases q <;> unfold authMkStepSlot authMkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendOPK u i) u bundle m0 m1
        hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_some S P idx useIdealMkAt mkSeedStar (.sendNoOPK u i) u bundle m0 m1
        hst
  case recvOPK k j o msg =>
    exact authMkRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_run'_some S P idx useIdealMkAt mkSeedStar msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]
theorem authMkSendSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) :
    (authMkSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst).run' none =
      authMkSendWith S P (fun _ => sampleBytes32) useIdealMkAt sid u bundle m0 m1 hst := by
  unfold authMkSendSlot authMkSendWith finishAuthSendAfterMkSlot finishAuthSendAfterMk
  rw [SlotM.run'_liftComp_bind]
  congr 1; funext prep
  cases prep
  · exact SlotM.run'_pure _ _
  · dsimp only
    split
    · exact SlotM.run'_liftComp _ _
    · exact run'_getRkAtSlot_bind_liftM_none idx (sessionSlotIndex sid) _
theorem authMkRecvSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)) (hst : AuthHybridStateFixed S) :
    (authMkRecvSlot S P idx useIdealMkAt msg prep? hst).run' none =
      authMkRecvWith S P (fun _ => sampleBytes32) useIdealMkAt msg prep? hst := by
  unfold authMkRecvSlot authMkRecvWith finishAuthRecvUnmatchedAfterMkSlot
    finishAuthRecvUnmatchedAfterMk
  dsimp only
  repeat (first
    | rfl
    | rw [SlotM.run'_pure]
    | rw [SlotM.run'_liftComp]
    | rw [run'_getRkAtSlot_bind_liftM_none]
    | (rw [SlotM.run'_liftComp_bind]; congr 1; funext _)
    | split)
theorem authMkStepSlot_run'_none (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat →
  Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    (authMkStepSlot S P idx useIdealMkAt q hst).run' none =
      authMkStepWith S P (fun _ => sampleBytes32) useIdealMkAt q hst := by
  cases q <;> unfold authMkStepSlot authMkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_none S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst
  case sendNoOPK u i bundle m0 m1 =>
    split
    · rw [SlotM.run'_pure]
    · exact authMkSendSlot_run'_none S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst
  case recvOPK k j o msg =>
    exact authMkRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_run'_none S P idx useIdealMkAt msg _ hst
  all_goals
    rw [SlotM.run'_liftComp]
theorem slotFireAtAuth_finishAuthSendAfterMkSlot {S : Setup} (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool) (sid : SessionId S) (uEntry : PrincipalEntry)
    (peerPrincipal? : Option (Nat × PrincipalEntry)) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes) (hst : AuthHybridStateFixed S)
    (hSend : sendSlotIndex? sid = some (sessionSlotIndex sid)) :
    SlotFireAtAuth S idx
      (finishAuthSendAfterMkSlot P idx useIdealMkAt sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst) := by
  unfold finishAuthSendAfterMkSlot
  split
  · exact SlotFireAtAuth.liftComp idx _
  · refine SlotFireAtAuth.getRkAtSlot_bind_liftM idx (sessionSlotIndex sid) _ (fun hEq mkSeed x hx
      => ?_)
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨ck1_1, _, rfl⟩
    exact authSlotFired_finishAuthSendMk_self P idx sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg msgPlain
      hst (P.deriveMsgKeys mkSeed spqrSalt?) (hEq ▸ hSend)
theorem slotFireAtAuth_finishAuthRecvUnmatchedAfterMkSlot {S : Setup} (P : Primitives)
    (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S) (drKey : DRKey) (rk1 : Bytes)
    (spqrSalt? : Option Bytes) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx
      (finishAuthRecvUnmatchedAfterMkSlot P idx useIdealMkAt msg prep drKey rk1
        spqrSalt? (S.N_send_tot + hst.recvCount) (hst.recvCount + 1) hst.mkSaltCache) := by
  unfold finishAuthRecvUnmatchedAfterMkSlot
  split
  · exact SlotFireAtAuth.liftComp idx _
  · refine SlotFireAtAuth.getRkAtSlot_bind_liftM idx (S.N_send_tot + hst.recvCount) _ (fun hEq
      mkSeed x hx => ?_)
    simp only [MonadAttach.mem_support_bind, support_pure, Set.mem_singleton_iff] at hx
    rcases hx with ⟨ck1_1, _, rfl⟩
    exact authSlotFired_finishAuthRecvMk_self P idx msg prep drKey rk1 ck1_1 hst hst.mkSaltCache
      (P.deriveMsgKeys mkSeed spqrSalt?) hEq
theorem authMkSendSlot_fire (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hSend : sendSlotIndex? sid = some (sessionSlotIndex sid)) :
    SlotFireAtAuth S idx (authMkSendSlot S P idx useIdealMkAt sid u bundle m0 m1 hst) := by
  unfold authMkSendSlot
  apply SlotFireAtAuth.liftComp_bind
  intro prep
  cases prep
  · exact SlotFireAtAuth.pure idx _
  · exact slotFireAtAuth_finishAuthSendAfterMkSlot P idx useIdealMkAt sid _ _ bundle m0 m1
      _ _ _ _ _ _ _ _ _ _ _ hst hSend
theorem authMkRecvSlot_fire (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authMkRecvSlot S P idx useIdealMkAt msg prep? hst) := by
  unfold authMkRecvSlot; dsimp only
  repeat (first
    | apply SlotFireAtAuth.pure
    | apply SlotFireAtAuth.liftComp
    | apply slotFireAtAuth_finishAuthRecvUnmatchedAfterMkSlot
    | (apply SlotFireAtAuth.liftComp_bind; intro _)
    | split)
theorem authMkStepSlot_fire (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) :
    SlotFireAtAuth S idx (authMkStepSlot S P idx useIdealMkAt q hst) := by
  cases q <;> unfold authMkStepSlot <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authMkSendSlot_fire S P idx useIdealMkAt (.sendOPK u i) u bundle m0 m1 hst rfl
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact SlotFireAtAuth.pure idx _
    · exact authMkSendSlot_fire S P idx useIdealMkAt (.sendNoOPK u i) u bundle m0 m1 hst rfl
  case recvOPK k j o msg =>
    exact authMkRecvSlot_fire S P idx useIdealMkAt msg _ hst
  case recvNoOPK k j l msg =>
    exact authMkRecvSlot_fire S P idx useIdealMkAt msg _ hst
  all_goals
    exact SlotFireAtAuth.liftComp idx _
theorem authMkSendWith_congr_slot {S : Setup} (P : Primitives)
    (samp1 samp2 : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hEq : samp1 (sessionSlotIndex sid) = samp2 (sessionSlotIndex sid)) :
    authMkSendWith S P samp1 useIdealMkAt sid u bundle m0 m1 hst =
      authMkSendWith S P samp2 useIdealMkAt sid u bundle m0 m1 hst := by
  unfold authMkSendWith finishAuthSendAfterMk
  congr 1; funext prep
  cases prep <;> [rfl; simp only [hEq]]
theorem authMkRecvWith_congr_slot {S : Setup} (P : Primitives)
    (samp1 samp2 : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)) (hst : AuthHybridStateFixed S)
    (hEq : samp1 (S.N_send_tot + hst.recvCount) = samp2 (S.N_send_tot + hst.recvCount)) :
    authMkRecvWith S P samp1 useIdealMkAt msg prep? hst =
      authMkRecvWith S P samp2 useIdealMkAt msg prep? hst := by
  unfold authMkRecvWith finishAuthRecvUnmatchedAfterMk
  simp only [hEq]
def PreparedAuthSendFiredAt (S : Setup) (idx : Nat) (mx : ProbComp (PreparedAuthSend S)) : Prop :=
  ∀ p ∈ support mx, match p with
    | .done _ hst' => authSlotFired S idx hst' = true
    | .idealMk _ _ _ _ _ _ _ _ _ _ _ _ _ => True
theorem PreparedAuthSendFiredAt.done {S : Setup} {idx : Nat} {resp : AuthResponse} {hst' :
  AuthHybridStateFixed S}
    (h : authSlotFired S idx hst' = true) :
    PreparedAuthSendFiredAt S idx (pure (.done resp hst')) := by
  intro p hp; simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; exact h
theorem PreparedAuthSendFiredAt.idealMk {S : Setup} {idx : Nat}
    {uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg
      msgPlain} :
    PreparedAuthSendFiredAt S idx
      (pure (.idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
        pqRatchetMsg msgPlain)) := by
  intro p hp; simp only [support_pure, Set.mem_singleton_iff] at hp; subst hp; trivial
theorem PreparedAuthSendFiredAt.bind {S : Setup} {α : Type} {idx : Nat}
    (mx : ProbComp α) {f : α → ProbComp (PreparedAuthSend S)}
    (hf : ∀ a, PreparedAuthSendFiredAt S idx (f a)) :
    PreparedAuthSendFiredAt S idx (mx >>= f) := by
  intro p hp; simp only [MonadAttach.mem_support_bind] at hp; rcases hp with ⟨a, _, hp'⟩; exact hf a
    p hp'
theorem prepareAuthSendMk_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hFired : authSlotFired S idx hst = true) :
    PreparedAuthSendFiredAt S idx (prepareAuthSendMk S P sid u bundle m0 m1 hst) := by
  unfold prepareAuthSendMk; dsimp only
  repeat (first
    | exact PreparedAuthSendFiredAt.done hFired
    | exact PreparedAuthSendFiredAt.done
        (authSlotFired_finishAuthHybridSend_mono P idx sid _ _ _ bundle m0 m1 _ _ _ _ _ _ _ _ _ _ _
          _ _ _ _ _ _ _ _ hst hFired)
    | exact PreparedAuthSendFiredAt.idealMk
    | (with_reducible apply PreparedAuthSendFiredAt.bind; intro _)
    | split)
theorem authMkSendWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authMkSendWith S P sampMkAt useIdealMkAt sid u bundle m0 m1 hst) := by
  intro y hy
  change y ∈ support (prepareAuthSendMk S P sid u bundle m0 m1 hst >>= _) at hy
  rw [MonadAttach.mem_support_bind] at hy
  rcases hy with ⟨prep, hPrep, hy⟩
  have hP := prepareAuthSendMk_slotFired_mono S P idx sid u bundle m0 m1 hst hFired prep hPrep
  cases prep with
  | done resp hst' =>
    exact AuthSlotFiredAt.pure hP y hy
  | idealMk uEntry peerPrincipal? ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt?
    pqRatchetMsg msgPlain =>
    dsimp only at hy
    revert y hy
    change AuthSlotFiredAt S idx
      (finishAuthSendAfterMk P sampMkAt useIdealMkAt sid uEntry peerPrincipal? bundle m0 m1
        ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst)
    unfold finishAuthSendAfterMk
    split
    · apply AuthSlotFiredAt.bind; intro ck1_1
      apply AuthSlotFiredAt.bind; intro mKeys
      exact AuthSlotFiredAt.pure (authSlotFired_finishAuthSendMk_mono P idx sid _ _ bundle m0 m1
        _ _ _ _ _ _ _ _ _ _ _ _ _ hst mKeys hFired)
    · apply AuthSlotFiredAt.bind; intro mkSeed
      apply AuthSlotFiredAt.bind; intro ck1_1
      exact AuthSlotFiredAt.pure (authSlotFired_finishAuthSendMk_mono P idx sid _ _ bundle m0 m1
        _ _ _ _ _ _ _ _ _ _ _ _ _ hst _ hFired)
theorem authMkRecvWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S)) (hst : AuthHybridStateFixed S)
    (hPrepUsed : ∀ prep, prep? = some prep →
      ∀ res?, (prep.finish res?).2.base.usedSendSessions =
        hst.toAuthHybridState.base.usedSendSessions)
    (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authMkRecvWith S P sampMkAt useIdealMkAt msg prep? hst) := by
  cases hPrep : prep? with
  | none =>
    unfold authMkRecvWith; dsimp only
    apply AuthSlotFiredAt.pure
    exact authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired rfl (Nat.le_succ _)
  | some prep =>
    have hUsed : ∀ res?, (prep.finish res?).2.base.usedSendSessions =
        hst.toAuthHybridState.base.usedSendSessions := hPrepUsed prep hPrep
    have hFinish : ∀ res? cache',
        authSlotFired S idx
          { toAuthHybridState := (prep.finish res?).2,
            recvCount := hst.recvCount + 1, mkSaltCache := cache' } = true :=
      fun res? _ => authSlotFired_of_usedSendSessions_eq_and_recvCount_le hFired (hUsed res?)
        (Nat.le_succ _)
    unfold authMkRecvWith finishAuthRecvUnmatchedAfterMk finishAuthRecvMk; dsimp only
    repeat (first
      | (with_reducible apply AuthSlotFiredAt.pure; exact hFinish _ _)
      | (with_reducible apply AuthSlotFiredAt.bind; intro _)
      | split)
theorem authMkStepWith_slotFired_mono (S : Setup) (P : Primitives) (idx : Nat)
    (sampMkAt : Nat → ProbComp Bytes) (useIdealMkAt : Nat → Bool)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hFired : authSlotFired S idx hst = true) :
    AuthSlotFiredAt S idx (authMkStepWith S P sampMkAt useIdealMkAt q hst) := by
  cases q <;> unfold authMkStepWith <;> dsimp only
  case sendOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authMkSendWith_slotFired_mono S P idx sampMkAt useIdealMkAt (.sendOPK u i) u bundle m0
        m1 hst hFired
  case sendNoOPK u i bundle m0 m1 =>
    split
    · exact AuthSlotFiredAt.pure hFired
    · exact authMkSendWith_slotFired_mono S P idx sampMkAt useIdealMkAt (.sendNoOPK u i) u bundle m0
        m1 hst hFired
  case recvOPK k j o msg =>
    exact authMkRecvWith_slotFired_mono S P idx sampMkAt useIdealMkAt msg _ hst
      (fun prep hPrep res? => prepareAuthHybridRecvOPK_usedSendSessions true P k j o msg
        hst.toAuthHybridState hPrep res?)
      hFired
  case recvNoOPK k j l msg =>
    exact authMkRecvWith_slotFired_mono S P idx sampMkAt useIdealMkAt msg _ hst
      (fun prep hPrep res? => prepareAuthHybridRecvNoOPK_usedSendSessions true P k j l msg
        hst.toAuthHybridState hPrep res?)
      hFired
  all_goals
    exact authCkOtherStep_slotFired_mono S P idx _ hst
      (fun _ _ _ _ _ h => by cases h) (fun _ _ _ _ _ h => by cases h)
      (fun _ _ _ _ h => by cases h) (fun _ _ _ _ h => by cases h) hFired
theorem prepareAuthSendMk_of_usedSendSessions_contains {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S)
    (hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = true) :
    prepareAuthSendMk S P sid u bundle m0 m1 hst = pure (.done .noneResp hst) := by
  unfold prepareAuthSendMk; dsimp only
  rw [hCont]
  split <;> [rfl; (split <;> rfl)]
theorem authMkStepWith_after (S : Setup) (P : Primitives) (idx : Nat) (useIdealMkAt : Nat → Bool)
    (mkSeedStar : Bytes) (q : AuthQuery S) (hst : AuthHybridStateFixed S)
    (hFired : authSlotFired S idx hst = true) :
    authMkStepWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt q
      hst =
      authMkStepWith S P (fun _ => sampleBytes32) useIdealMkAt q hst ∧
    ∀ x ∈ support (authMkStepWith S P (fun _ => sampleBytes32) useIdealMkAt q hst),
      authSlotFired S idx x.2 = true := by
  refine ⟨?_, authMkStepWith_slotFired_mono S P idx _ useIdealMkAt q hst hFired⟩
  have hSendEq : ∀ (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 :
    Bytes),
      sendSlotIndex? sid = some (sessionSlotIndex sid) →
      authMkSendWith S P (fun s => if s == idx then pure mkSeedStar else sampleBytes32) useIdealMkAt
        sid u bundle m0 m1 hst =
        authMkSendWith S P (fun _ => sampleBytes32) useIdealMkAt sid u bundle m0 m1 hst := by
    intro sid u bundle m0 m1 hSend
    by_cases hEq : (sessionSlotIndex sid == idx) = true
    · rw [beq_iff_eq] at hEq
      have hCont : hst.toAuthHybridState.base.usedSendSessions.contains sid = true :=
        contains_sid_of_authSlotFired hFired (hEq ▸ hSend)
      unfold authMkSendWith
      rw [prepareAuthSendMk_of_usedSendSessions_contains P sid u bundle m0 m1 hst hCont]
      rfl
    · apply authMkSendWith_congr_slot
      simp only [hEq, Bool.false_eq_true, ↓reduceIte]
  cases q
  case sendOPK u i bundle m0 m1 =>
    unfold authMkStepWith; dsimp only
    split
    · rfl
    · exact hSendEq (.sendOPK u i) u bundle m0 m1 rfl
  case sendNoOPK u i bundle m0 m1 =>
    unfold authMkStepWith; dsimp only
    split
    · rfl
    · exact hSendEq (.sendNoOPK u i) u bundle m0 m1 rfl
  case recvOPK k' j o msg =>
    unfold authMkStepWith; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authMkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  case recvNoOPK k' j l msg =>
    unfold authMkStepWith; dsimp only
    have hne : S.N_send_tot + hst.recvCount ≠ idx := recvSlot_ne_of_authSlotFired hFired
    have hEqF : (S.N_send_tot + hst.recvCount == idx) = false := beq_eq_false_iff_ne.mpr hne
    apply authMkRecvWith_congr_slot
    simp only [hEqF, Bool.false_eq_true, ↓reduceIte]
  all_goals rfl
def authMkCutoffImpl (S : Setup) (P : Primitives) (cutoff : Nat) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authMkStepWith S P (fun _ => sampleBytes32) (fun s => decide (s < cutoff)) q)
def prfMkAuthImpl (S : Setup) (P : Primitives) (idx : Nat) (mkSeedStar : Bytes) :
    QueryImpl (authSpec S) (StateT (AuthHybridStateFixed S) ProbComp) :=
  fun q => StateT.mk (authMkStepWith S P (fun s => if s == idx then pure mkSeedStar else
    sampleBytes32)
    (fun s => decide (s < idx)) q)
noncomputable def authMkPreSampleRun (S : Setup) (P : Primitives)
    (idx : Nat) (mkSeedStar : Bytes) (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + prfMkAuthImpl S P idx mkSeedStar
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState
noncomputable def authMkCutoffExp (S : Setup) (P : Primitives) (cutoff : Nat)
    (A : AuthAdversary S) : ProbComp Bool := do
  let secb ← $ᵗ Bool
  let initSt := AuthHybridStateFixed.empty S secb
  let fullImpl := (QueryImpl.ofLift unifSpec ProbComp).liftTarget
    (StateT (AuthHybridStateFixed S) ProbComp) + authMkCutoffImpl S P cutoff
  let (b', finalSt) ← (simulateQ fullImpl A.run).run initSt
  finalizeAuthFixed P secb b' finalSt.toAuthHybridState
theorem evalDist_preSample_authMk_eq_cutoff (S : Setup) (P : Primitives)
    (idx : Nat) (A : AuthAdversary S) :
    𝒟[do
        let mkSeedStar ← sampleBytes32
        authMkPreSampleRun S P idx mkSeedStar A] =
      𝒟[authMkCutoffExp S P idx A] := by
  unfold authMkPreSampleRun authMkCutoffExp
  rw [OracleComp.evalDist_bind_bind_swap]
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  exact SlotM.evalDist_preSample_eq_lazy_of_slotStep
    sampleBytes32
    (authSlotFired S idx) (authMkCutoffImpl S P idx)
    (fun mkSeedStar => prfMkAuthImpl S P idx mkSeedStar)
    (authMkStepSlot S P idx (fun s => decide (s < idx)))
    (authMkStepSlot_slotComp S P idx (fun s => decide (s < idx)))
    (authMkStepSlot_run'_some S P idx (fun s => decide (s < idx))) (fun q hst g => by
      dsimp only [authMkCutoffImpl, StateT.run_mk]
      rw [authMkStepSlot_run'_none S P idx (fun s => decide (s < idx)) q hst])
    (fun mkSeedStar q hst hFired => authMkStepWith_after S P idx (fun s => decide (s < idx))
      mkSeedStar q hst hFired)
    (authMkStepSlot_fire S P idx (fun s => decide (s < idx)))
    A.run
    (AuthHybridStateFixed.empty S secb)
    (fun x => finalizeAuthFixed P secb x.1 x.2.toAuthHybridState)
private theorem bool_eq_false_or_eq_true (b : Bool) :
    b = false ∨ b = true := by
  cases b <;> simp
private theorem forall_support_bind {α β : Type} (m : ProbComp α) (f : α → ProbComp β) (P : β →
  Prop)
    (h : ∀ a, ∀ b ∈ support (f a), P b) :
    ∀ b ∈ support (m >>= f), P b := by
  intro b hb
  simp only [support_bind, Set.mem_iUnion, exists_prop] at hb
  rcases hb with ⟨a, _, hb⟩
  exact h a b hb
private theorem forall_support_pure {α : Type} (x : α) (P : α → Prop) (h : P x) :
    ∀ b ∈ support (pure x : ProbComp α), P b := by
  intro b hb
  rw [support_pure, Set.mem_singleton_iff] at hb
  exact hb ▸ h
theorem finishAuthSendCk_eq_finishAuthSendMk {S : Setup} (P : Primitives)
    (sid : SessionId S) (uEntry : PrincipalEntry) (peerPrincipal? : Option (Nat × PrincipalEntry))
    (bundle : PreKeyBundleInput) (m0 m1 : Bytes) (ekASk ekAPk ss kemCt ephASk ephAPk : Bytes)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes) (pqRatchetMsg msgPlain : Bytes)
    (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = []) (mkSeed ck1_1 : Bytes) :
    finishAuthSendCk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 spqrSalt? pqRatchetMsg msgPlain hst (mkSeed,
        ck1_1) =
    finishAuthSendMk P sid uEntry peerPrincipal? bundle m0 m1
      ekASk ekAPk ss kemCt ephASk ephAPk drKey rk1 mkSeed ck1_1 spqrSalt? pqRatchetMsg msgPlain hst
      (P.deriveMsgKeys mkSeed spqrSalt?) := by
  unfold finishAuthSendCk finishAuthSendMk
  rw [hCache]
  rfl
theorem finishAuthRecvCk_eq_finishAuthRecvMk {S : Setup} (P : Primitives)
    (msg : PreKeyMsg) (prep : PreparedAuthRecv S)
    (drKey : DRKey) (rk1 : Bytes) (spqrSalt? : Option Bytes)
    (recvCount' : Nat) (mkSeed ck1_1 : Bytes) :
    finishAuthRecvCk P msg prep drKey rk1 spqrSalt? recvCount' (mkSeed, ck1_1) =
      finishAuthRecvMk P msg prep drKey rk1 ck1_1 recvCount' [] (P.deriveMsgKeys mkSeed spqrSalt?)
        := by
  rfl
theorem authMkSendWith_zero_eq_authCkSendWith {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = []) :
    authMkSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) sid u bundle m0 m1 hst =
      authCkSendWith S P (fun _ => do let r1 ← sampleBytes32; let r2 ← sampleBytes32; pure (r1, r2))
        sid u bundle m0 m1 hst := by
  have hCut0 : decide (sessionSlotIndex sid < 0) = false := by simp
  unfold authMkSendWith prepareAuthSendMk finishAuthSendAfterMk authCkSendWith
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;>
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases (m0.length != m1.length) <;> simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  cases (hst.base.usedSendSessions.contains sid) <;> simp only [Bool.false_eq_true, ↓reduceIte,
    pure_bind]
  cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => simp only [pure_bind]
  | some p =>
    rcases p with ⟨_, uEntry⟩
    dsimp only
    cases hpeer : findHonestPrincipal P hst.base.principals bundle.ikB with
    | none =>
      dsimp only
      cases (m0 != m1) <;> simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte,
        pure_bind]
      cases (!koskBundleOk P hst.base.principals hst.base.spkBundles
        hst.base.opkEntries hst.base.advKeys bundle) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      congr 1; funext ekASk
      congr 1; funext kemCoins
      congr 1; funext ephASk
      congr 1; funext spqrCoins
      cases (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC bundle.spkB)
        bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp only [pure_bind]
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte,
          bind_assoc]
        congr 1; funext ⟨drKey, roCache'⟩
        congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
        cases P.spqrInitSend drKey.pqrKey spqrCoins with
        | none => simp only [pure_bind]
        | some spqr =>
          rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩
          simp only [pure_bind, hCache]
    | some peer =>
      rcases peer with ⟨pIdx, pEntry⟩
      dsimp only
      cases (! !pEntry.corrupted && (m0 != m1)) <;> simp only [Bool.false_eq_true, ↓reduceIte,
        pure_bind]
      cases (!koskBundleOk P hst.base.principals hst.base.spkBundles
        hst.base.opkEntries hst.base.advKeys bundle) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind, bind_assoc]
      congr 1; funext ekASk
      congr 1; funext kemCoins
      congr 1; funext ephASk
      congr 1; funext spqrCoins
      cases (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC bundle.spkB)
        bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => simp only [pure_bind]
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        dsimp only
        split
        · simp only [bind_assoc]
          congr 1; funext drKey
          congr 1; funext rk1
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => simp only [pure_bind]
          | some spqr =>
            rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩
            simp only [pure_bind, hCut0, Bool.false_eq_true, ↓reduceIte,
              finishAuthSendCk_eq_finishAuthSendMk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hst hCache]
        · simp only [bind_assoc]
          congr 1; funext ⟨drKey, roCache'⟩
          congr 1; funext ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => simp only [pure_bind]
          | some spqr =>
            rcases spqr with ⟨_, spqrSalt?, pqRatchetMsg⟩
            simp only [pure_bind, hCache]
theorem evalDist_authCkSendWith_end_eq_authMkSendWith_zero {S : Setup} (P : Primitives)
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = [])
    (hSid : sessionSlotIndex sid < S.N_sess_tot)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[authCkSendWith S P (fun s => sampCkPair P (s < S.N_sess_tot)) sid u bundle m0 m1 hst >>= k] =
      𝒟[authMkSendWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) sid u bundle m0 m1 hst
        >>= k] := by
  rw [authMkSendWith_zero_eq_authCkSendWith P sid u bundle m0 m1 hst hCache]
  have hCutEnd : decide (sessionSlotIndex sid < S.N_sess_tot) = true := decide_eq_true hSid
  unfold authCkSendWith
  dsimp only
  cases hst.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte]
  cases (m0.length != m1.length) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  cases (hst.base.usedSendSessions.contains sid) <;> simp only [Bool.false_eq_true, ↓reduceIte]
  cases hst.base.principals.find? (fun (idx, _) => idx == u.val) with
  | none => rfl
  | some p =>
    rcases p with ⟨_, uEntry⟩
    dsimp only
    cases findHonestPrincipal P hst.base.principals bundle.ikB with
    | none =>
      dsimp only
      cases (m0 != m1) <;> simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
      cases (!koskBundleOk P hst.base.principals hst.base.spkBundles
        hst.base.opkEntries hst.base.advKeys bundle) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      cases (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC bundle.spkB)
        bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => rfl
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        simp only [Option.isSome, Bool.false_and, Bool.or_false, Bool.false_eq_true, ↓reduceIte]
    | some peer =>
      rcases peer with ⟨pIdx, pEntry⟩
      dsimp only
      cases (! !pEntry.corrupted && (m0 != m1)) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      cases (!koskBundleOk P hst.base.principals hst.base.spkBundles
        hst.base.opkEntries hst.base.advKeys bundle) <;>
        simp only [Bool.false_eq_true, ↓reduceIte, bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ekASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun kemCoins _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ephASk _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun spqrCoins _ => ?_)
      cases (!(P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeEC bundle.spkB)
        bundle.spkSig &&
               P.sigVerify (resolveSigPk P hst.base.principals bundle.ikB) (encodeKEM bundle.pqspkB)
                 bundle.pqspkSig)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      cases P.kemEncaps bundle.pqspkB kemCoins with
      | none => rfl
      | some pair =>
        rcases pair with ⟨ss, kemCt⟩
        dsimp only
        split
        · simp only [bind_assoc]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun drKey _ => ?_)
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rk1 _ => ?_)
          cases P.spqrInitSend drKey.pqrKey spqrCoins with
          | none => rfl
          | some spqr =>
            rcases spqr with ⟨_pqrStA, spqrSalt?, pqRatchetMsg⟩
            simp only [sampCkPair, hCutEnd, ↓reduceIte, bind_assoc, pure_bind,
              evalDist_sampleBytes32_bind_const]
        · rfl
theorem support_authCkSendWith_inv {S : Setup} (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (sid : SessionId S) (u : Fin S.N_id) (bundle : PreKeyBundleInput) (m0 m1 : Bytes)
    (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = []) :
    ∀ x ∈ support (authCkSendWith S P sampAt sid u bundle m0 m1 hst),
      x.2.mkSaltCache = [] ∧ x.2.recvCount = hst.recvCount := by
  unfold authCkSendWith
  dsimp only
  cases hst.toAuthHybridState.base.hasWonAuth <;> simp only [Bool.false_eq_true, ↓reduceIte] <;>
  repeat (first
    | exact forall_support_pure _ _ ⟨hCache, rfl⟩
    | exact forall_support_pure _ _ ⟨rfl, rfl⟩
    | (refine forall_support_bind _ _ _ (fun _ => ?_))
    | split)
theorem evalDist_authCkRecvWith_end_eq_authMkRecvWith_zero {S : Setup} (P : Primitives)
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = [])
    (hCut : S.N_send_tot + hst.recvCount < S.N_sess_tot)
    (k : AuthResponse × AuthHybridStateFixed S → ProbComp Bool) :
    𝒟[authCkRecvWith S P (fun s => sampCkPair P (s < S.N_sess_tot)) msg prep? hst >>= k] =
      𝒟[authMkRecvWith S P (fun _ => sampleBytes32) (fun s => decide (s < 0)) msg prep? hst >>= k]
        := by
  have hCutEnd : decide (S.N_send_tot + hst.recvCount < S.N_sess_tot) = true := decide_eq_true hCut
  have hCut0 : ∀ n : Nat, decide (n < 0) = false := fun _ => by simp
  unfold authCkRecvWith authMkRecvWith finishAuthRecvUnmatchedAfterMk sampCkPair
  dsimp only
  simp only [hCut0, hCutEnd, Bool.false_eq_true, ↓reduceIte]
  cases prep? with
  | none => rfl
  | some prep =>
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp only [pure_bind, hCache]
          | some pqr =>
            rcases pqr with ⟨_pqrStB, spqrSalt?⟩
            simp only [pure_bind, hCache, finishAuthRecvCk_eq_finishAuthRecvMk]
        · simp only [bind_assoc]
          refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rk1 _ => ?_)
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => simp only [pure_bind, hCache]
          | some pqr =>
            rcases pqr with ⟨_pqrStB, spqrSalt?⟩
            simp only [bind_assoc, pure_bind, evalDist_sampleBytes32_bind_const, hCache,
              finishAuthRecvCk_eq_finishAuthRecvMk]
      | none =>
        dsimp only
        simp only [bind_assoc]
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun drKey _ => ?_)
        refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun rk1 _ => ?_)
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => simp only [pure_bind, hCache]
        | some pqr =>
          rcases pqr with ⟨_pqrStB, spqrSalt?⟩
          simp only [bind_assoc, pure_bind, evalDist_sampleBytes32_bind_const, hCache,
            finishAuthRecvCk_eq_finishAuthRecvMk]
    · simp only [bind_assoc]
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨drKey, roCache'⟩ _ => ?_)
      refine OracleComp.evalDist_bind_congr_of_support _ _ _ (fun ⟨⟨rk1, ck1_0⟩, rootRoCache'⟩ _ =>
        ?_)
      cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
      | none => simp only [pure_bind, hCache]
      | some pqr =>
        rcases pqr with ⟨_pqrStB, spqrSalt?⟩
        simp only [pure_bind, hCache]
theorem support_authCkRecvWith_inv {S : Setup} (P : Primitives)
    (sampAt : Nat → ProbComp (Bytes × Bytes))
    (msg : PreKeyMsg) (prep? : Option (PreparedAuthRecv S))
    (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = []) :
    ∀ x ∈ support (authCkRecvWith S P sampAt msg prep? hst),
      x.2.mkSaltCache = [] ∧ x.2.recvCount = hst.recvCount + 1 := by
  unfold authCkRecvWith
  cases prep? with
  | none =>
    exact forall_support_pure _ _ ⟨hCache, rfl⟩
  | some prep =>
    dsimp only
    split
    · cases prep.matchedSess? with
      | some s =>
        dsimp only
        split
        · cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => exact forall_support_pure _ _ ⟨rfl, rfl⟩
          | some pqr => exact forall_support_pure _ _ ⟨rfl, rfl⟩
        · refine forall_support_bind _ _ _ (fun rk1 => ?_)
          cases P.spqrInitRecv s.drKey.pqrKey msg.pqRatchetMsg with
          | none => exact forall_support_pure _ _ ⟨rfl, rfl⟩
          | some pqr =>
            refine forall_support_bind _ _ _ (fun p => ?_)
            exact forall_support_pure _ _ ⟨rfl, rfl⟩
      | none =>
        dsimp only
        refine forall_support_bind _ _ _ (fun drKey => ?_)
        refine forall_support_bind _ _ _ (fun rk1 => ?_)
        cases P.spqrInitRecv drKey.pqrKey msg.pqRatchetMsg with
        | none => exact forall_support_pure _ _ ⟨rfl, rfl⟩
        | some pqr =>
          refine forall_support_bind _ _ _ (fun p => ?_)
          exact forall_support_pure _ _ ⟨rfl, rfl⟩
    · refine forall_support_bind _ _ _ (fun _ => ?_)
      refine forall_support_bind _ _ _ (fun _ => ?_)
      cases P.spqrInitRecv _ msg.pqRatchetMsg with
      | none => exact forall_support_pure _ _ ⟨rfl, rfl⟩
      | some pqr => exact forall_support_pure _ _ ⟨rfl, rfl⟩
theorem step_authCk_end_eq_authMkStepWith_zero {S : Setup} (P : Primitives)
    (q : AuthQuery S) (hst : AuthHybridStateFixed S) (hCache : hst.mkSaltCache = [])
    (hRecv : isAuthRecvQueryB (.inr q) = true → hst.recvCount < S.N_recv_tot) :
    (∀ (k : (authSpec S).Range q × AuthHybridStateFixed S → ProbComp Bool),
      𝒟[(StateT.mk (fun hst => authCkStepWith S P (fun s => sampCkPair P (s < S.N_sess_tot)) q
        hst)).run hst >>= k] =
        𝒟[(authMkCutoffImpl S P 0 q).run hst >>= k]) ∧
    (∀ x ∈ support ((StateT.mk (fun hst => authCkStepWith S P (fun s => sampCkPair P (s <
      S.N_sess_tot)) q hst)).run hst),
      x.2.mkSaltCache = [] ∧ x.2.recvCount ≤ hst.recvCount + (if isAuthRecvQueryB (.inr q) then 1
        else 0)) := by
  dsimp only [authMkCutoffImpl, StateT.run_mk]
  cases q with
  | sendOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith, authMkStepWith]
    rcases bool_eq_false_or_eq_true bundle.opkB?.isNone with hOpt | hOpt <;>
      simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
    · refine ⟨evalDist_authCkSendWith_end_eq_authMkSendWith_zero P (.sendOPK u i) u bundle m0 m1 hst
        hCache hSid,
        fun x hx => ?_⟩
      obtain ⟨hC, hCnt⟩ := support_authCkSendWith_inv P _ (.sendOPK u i) u bundle m0 m1 hst hCache x
        hx
      exact ⟨hC, by omega⟩
    · refine ⟨fun _ => trivial, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; dsimp only; exact ⟨hCache, by omega⟩
  | sendNoOPK u i bundle m0 m1 =>
    have hSid : sessionSlotIndex (SessionId.sendNoOPK u i) < S.N_sess_tot := by
      have := _root_.Proofs.SignalPqxdh.Security.sessionSlotIndex_lt (.sendNoOPK u i) (h := trivial)
      unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith, authMkStepWith]
    rcases bool_eq_false_or_eq_true bundle.opkB?.isSome with hOpt | hOpt <;>
      simp only [hOpt, Bool.false_eq_true, ↓reduceIte]
    · refine ⟨evalDist_authCkSendWith_end_eq_authMkSendWith_zero P (.sendNoOPK u i) u bundle m0 m1
        hst hCache hSid,
        fun x hx => ?_⟩
      obtain ⟨hC, hCnt⟩ := support_authCkSendWith_inv P _ (.sendNoOPK u i) u bundle m0 m1 hst hCache
        x hx
      exact ⟨hC, by omega⟩
    · refine ⟨fun _ => trivial, fun x hx => ?_⟩
      simp only [support_pure, Set.mem_singleton_iff] at hx
      subst hx; dsimp only; exact ⟨hCache, by omega⟩
  | recvOPK k' j o msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith, authMkStepWith]
    refine ⟨evalDist_authCkRecvWith_end_eq_authMkRecvWith_zero P msg _ hst hCache hLt,
      fun x hx => ?_⟩
    obtain ⟨hC, hCnt⟩ := support_authCkRecvWith_inv P _ msg _ hst hCache x hx
    exact ⟨hC, by omega⟩
  | recvNoOPK k' j l msg =>
    have hLt : S.N_send_tot + hst.recvCount < S.N_sess_tot := by
      have := hRecv rfl; unfold Setup.N_sess_tot; omega
    simp only [isAuthRecvQueryB, ↓reduceIte, authCkStepWith, authMkStepWith]
    refine ⟨evalDist_authCkRecvWith_end_eq_authMkRecvWith_zero P msg _ hst hCache hLt,
      fun x hx => ?_⟩
    obtain ⟨hC, hCnt⟩ := support_authCkRecvWith_inv P _ msg _ hst hCache x hx
    exact ⟨hC, by omega⟩
  | _ =>
    simp only [isAuthRecvQueryB, Bool.false_eq_true, ↓reduceIte, authCkStepWith, authMkStepWith]
    refine ⟨fun _ => trivial, fun x hx => ?_⟩
    unfold authCkOtherStep at hx; split at hx
    · simp only [support_pure, Set.mem_singleton_iff] at hx; subst hx; dsimp only
      exact ⟨hCache, by omega⟩
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hx
    rcases hx with ⟨⟨resp, base'⟩, _, rfl⟩
    dsimp only
    exact ⟨hCache, by omega⟩
theorem evalDist_authMkCutoffExp_zero_eq_g3_7 (S : Setup) (P : Primitives)
    (b : QueryBudget) (A : BoundedAdv (AuthAdversary S) b) :
    𝒟[authMkCutoffExp S P 0 A.1] = 𝒟[authFixedExpAtStage .g3_7 S P A.1] := by
  rw [← evalDist_authCkCutoffExp_end_eq_g3_7 S P b A]
  symm
  unfold authCkCutoffExp authMkCutoffExp
  refine OracleComp.evalDist_bind_congr_of_support ($ᵗ Bool) _ _ (fun secb _ => ?_)
  have hBound : OracleComp.IsQueryBoundP A.1.run (fun q => isAuthRecvQueryB q = true) S.N_recv_tot
    := by
    simpa only [isAuthRecvQueryB_eq_true_iff] using A.2.2.2.1
  exact evalDist_simulateQ_proj_inv_bound
    (id : AuthHybridStateFixed S → AuthHybridStateFixed S) (fun hst => hst.mkSaltCache = [])
    (fun hst => hst.recvCount) (isAuthRecvQueryB (S := S)) (fun _ => rfl)
    S.N_recv_tot
    (fun q => StateT.mk (fun hst =>
      authCkStepWith S P (fun s => sampCkPair P (s < S.N_sess_tot)) q hst))
    (authMkCutoffImpl S P 0)
    (fun q hst hCache hRecv => step_authCk_end_eq_authMkStepWith_zero P q hst hCache hRecv)
    A.1.run
    S.N_recv_tot
    hBound
    (AuthHybridStateFixed.empty S secb)
    rfl
    (by simp [AuthHybridStateFixed.empty])
    (fun (b', finalSt) => finalizeAuthFixed P secb b' finalSt.toAuthHybridState)
end SignalPqxdh.Security.AuthSubHops1to3
