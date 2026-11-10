/-
Copyright 2026 Google LLC

All code is licensed under the Apache License, Version 2.0 (the "Apache 2.0"); you may not use this file except in compliance with the Apache 2.0 license. You may obtain a copy of the License at https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software distributed under the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the License for the specific language governing permissions and
limitations under the License.
-/

module
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreK -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.AuthHandshakeShCr -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyShCr -- proof-setup: allow-public-import

/-!
# Two-Fuel `(K_on, K_ro)` Handshake and ShCR Branches

Defines two-fuel `(K_on, K_ro)` handshake (`sendKC`, `recvKB`) and `KemShCr` simulator branches
re-exported by `AuthCoreKArms`.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs

open _root_.ReductionDsl (Ty Var Expr Comp)
open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)
open _root_.SignalPqxdh.Security.ReductionDsl (authStateTy principalEntryTy spkBundleEntryTy)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthHs (
  Ext v letV bindV caseOptV eAny eFind eMap eCaseOpt
  natEq nat2Eq nat3Eq sidEq optU32Eq optFst optSnd getDBytes
  sendQTy recvQTy shcrStTy pauseTy RS SCS FinTy
  stPrin stSpks stOpks stSess stUsedS stUsedO stUsedN stKyb stSecb stUpd
  rs aNone aSendUnfresh aSendFresh aRecvUnfresh aRecvHonest
  peSecIKA0 peIkAPk peCorrupted
  buIkB buSpkB buSpkId buSpkSig buPqspkB buPqspkId buPqspkSig buOpkB
  sbSpkPk sbSpkSk sbPqspkPk sbPqspkSk oeConsumed oeOpkSk oeUpd
  pmHdr pmEphAPk pmPqMsg pmAeadCt
  hdMk hdSpkId hdPqspkId hdOpkId hdIkAPk hdEkAPk hdKemCt seMk
  encEC encKEM buildSecretsE firstMsgADE kyberCheckE
  findHonestC koskBundleOkC koskSenderOkC resolveSigPkC hkdfOrRoC rootRoC
  pdSid pdBu pdM0 pdM1 pdUI scBase scCnt scRR scUpd onBase
  preCheckC checkSigsC shcrFinC sendGuardE
)

@[expose] def sendKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .iteC (.boolNot (natEq (.bytesLen (v m0)) (.bytesLen (v m1)))) (.ret (rs aNone (v st))) <|
  .iteC (eAny K_on (stUsedS (v st)) fun e => sidEq (v e) (v sid)) (.ret (rs aNone (v st))) <|
  caseOptV (eFind K_on (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (rs aNone (v st))) fun uE =>
  bindV (findHonestC S K_on st (buIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  .iteC (.boolAnd (.boolNot (v fresh)) (.boolNot (.bytesBeq (v m0) (v m1))))
    (.ret (rs aNone (v st))) <|
  letV (.ite (v fresh) (.ite (stSecb (v st)) (v m1) (v m0)) (v m0)) fun pt =>
  bindV (koskBundleOkC S K_on st bu) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (rs aNone (v st))) <|
  bindV .sampleBytes32 fun ekSk =>
  bindV .sampleBytes32 fun coins =>
  bindV .sampleBytes32 fun ephSk =>
  bindV .sampleBytes32 fun spqrCoins =>
  bindV (resolveSigPkC S K_on st (buIkB (v bu))) fun spk =>
  bindV (.queryPrim (.sigVerify 33)
      (.pair (v spk) (.pair (encEC (buSpkB (v bu))) (buSpkSig (v bu))))) fun v1 =>
  bindV (.queryPrim (.sigVerify 1569)
      (.pair (v spk) (.pair (encKEM (buPqspkB (v bu))) (buPqspkSig (v bu))))) fun v2 =>
  .iteC (.boolNot (.boolAnd (v v1) (v v2))) (.ret (rs aNone (v st))) <|
  bindV (.queryPrim .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc) (.ret (rs aNone (v st))) fun sc =>
  bindV (.queryPrim .x25519Base (v ekSk)) fun ekPk =>
  bindV (.queryPrim .x25519 (.pair (peSecIKA0 (.snd (v uE))) (buSpkB (v bu)))) fun dh1 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buIkB (v bu)))) fun dh2 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buSpkB (v bu)))) fun dh3 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (getDBytes (optSnd (buOpkB (v bu)))))) fun dh4 =>
  bindV (hkdfOrRoC K_ro true st (buildSecretsE (v dh1) (v dh2) (v dh3)
      (eCaseOpt (buOpkB (v bu)) .noneE fun _ => .someE (v dh4)) (.fst (v sc)))) fun dr =>
  bindV (.queryPrim .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrim .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (rootRoC K_ro st (.fst (.fst (v dr))) (v dhR)) fun rkOut =>
  bindV (.queryPrim .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrim .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrim (.spqrInitSend 32 32) (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins)))
    fun sp? =>
  caseOptV (v sp?) (.ret (rs aNone (v st))) fun sp =>
  bindV (.queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (.snd (v uE))) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp))))
    fun ad =>
  bindV (.queryPrim (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad) (v pt)))) fun ct =>
  letV (.pair (hdMk (peIkAPk (.snd (v uE))) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) (.pair (v ephPk) (.pair (.snd (.snd (v sp))) (v ct))))
    fun wm =>
  letV (eCaseOpt (v pp) (.pair (.litBool false) (.litBool false)) fun p =>
      .pair (eAny K_on (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))
        (eAny K_on (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))) fun hon =>
  letV (seMk (v sid) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu))) (buPqspkB (v bu))
      (.fst (v hon)) (.litBool false) (.snd (v hon)) (v ekSk) (v ephSk) (v fresh)
      (.boolAnd (v fresh) (.boolNot (.bytesBeq (v m0) (v m1))))) fun se =>
  .ret (rs (eCaseOpt (v pp) (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
      (usedS := .listCons (v sid) (stUsedS (v st))) (ro := .snd (v dr)) (root := .snd (v rkOut))))

@[expose] def recvTailKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    (kE : Var Γ₃ principalEntryTy) (bE : Var Γ₄ spkBundleEntryTy)
    (oSk? : Expr pqxdhOps Δ (.opt (B 32)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  letV oSk? fun oSk? =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  bindV (.queryPrim .isCanonical (hdEkAPk (v hdr))) fun can =>
  bindV (.queryPrim .isCanonical (pmEphAPk (v msg))) fun canE =>
  letV (kyberCheckE K_on (stKyb (v st)) (.pair (.fst (v x)) (.pair (hdPqspkId (v hdr))
      (.pair (hdSpkId (v hdr)) (hdEkAPk (v hdr)))))) fun kc =>
  .iteC (.boolOr (.boolOr (.boolNot (.fst (v kc))) (.boolNot (v can))) (.boolNot (v canE)))
    (.ret (rs aNone (v st))) <|
  bindV (.queryPrim .kemDecaps (.pair (sbPqspkSk (v bE)) (hdKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (rs aNone (v st))) fun ss =>
  bindV (.queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdIkAPk (v hdr)))) fun dh1 =>
  bindV (.queryPrim .x25519 (.pair (peSecIKA0 (v kE)) (hdEkAPk (v hdr)))) fun dh2 =>
  bindV (.queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdEkAPk (v hdr)))) fun dh3 =>
  bindV (if opk then
      bindV (.queryPrim .x25519 (.pair (getDBytes (v oSk?)) (hdEkAPk (v hdr)))) fun dh4 =>
        .ret (.someE (v dh4))
    else .ret .noneE) fun dh4? =>
  bindV (hkdfOrRoC K_ro true st (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss))) fun dr =>
  bindV (.queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pmEphAPk (v msg)))) fun dhR =>
  bindV (rootRoC K_ro st (.fst (.fst (v dr))) (v dhR)) fun rkOut =>
  bindV (.queryPrim .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrim .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrim (.spqrInitRecv 32 32) (.pair (.snd (.snd (.fst (v dr)))) (pmPqMsg (v msg))))
    fun sp? =>
  caseOptV (v sp?) (.ret (rs aNone (v st))) fun sp =>
  bindV (.queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mk =>
  bindV (.queryPrim (.aeadDec 158 32 32)
      (.pair (v mk) (.pair (firstMsgADE (hdIkAPk (v hdr)) (peIkAPk (v kE))
        (pmEphAPk (v msg)) (pmPqMsg (v msg))) (pmAeadCt (v msg))))) fun pt? =>
  caseOptV (v pt?) (.ret (rs aNone (v st))) fun pt =>
  bindV (findHonestC S K_on st (hdIkAPk (v hdr))) fun snd? =>
  letV (if opk then
      stUpd (v st)
        (opks := eMap K_on (stOpks (v st)) fun e =>
          .ite (nat3Eq (.fst (v e)) (v kjo))
            (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .litBool true))) (v e))
        (usedO := .listCons (v kjo) (stUsedO (v st)))
        (kyb := .snd (v kc)) (ro := .snd (v dr)) (root := .snd (v rkOut))
    else
      stUpd (v st)
        (usedN := .listCons (v kjo) (stUsedN (v st)))
        (kyb := .snd (v kc)) (ro := .snd (v dr)) (root := .snd (v rkOut))) fun st' =>
  .ret (rs (eCaseOpt (v snd?) (aRecvUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v pt))
      fun _ => aRecvHonest) (v st'))

@[expose] def recvKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RS :=
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  .iteC (.boolNot (.boolAnd (.boolAnd (.boolAnd (.boolAnd (.boolAnd
      (.u32Beq (hdSpkId (v hdr)) (.u32OfNat (.fst (.snd (v x)))))
      (.u32Beq (hdPqspkId (v hdr)) (.u32OfNat (.fst (.snd (v x))))))
      (optU32Eq (hdOpkId (v hdr))
        (if opk then .someE (.u32OfNat (.fst (.snd (.snd (v x))))) else .noneE)))
      (natEq (.bytesLen (hdIkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (hdEkAPk (v hdr))) (.litNat 32)))
      (natEq (.bytesLen (pmEphAPk (v msg))) (.litNat 32))))
    (.ret (rs aNone (v st))) <|
  .iteC (eAny K_on (if opk then stUsedO (v st) else stUsedN (v st)) fun e => nat3Eq (v e) (v kjo))
    (.ret (rs aNone (v st))) <|
  bindV (koskSenderOkC S K_on st (hdIkAPk (v hdr))) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (rs aNone (v st))) <|
  caseOptV (eFind K_on (stPrin (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (rs aNone (v st))) fun kE =>
  caseOptV (eFind K_on (stSpks (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (rs aNone (v st))) fun bE =>
  letV (.snd (v kE)) fun kE' => letV (.snd (v bE)) fun bE' =>
  if opk then
    caseOptV (eFind K_on (stOpks (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
      (.ret (rs aNone (v st))) fun oE =>
    .iteC (oeConsumed (.snd (v oE))) (.ret (rs aNone (v st))) <|
    recvTailKC S K_on K_ro true st x kE' bE' (.someE (oeOpkSk (.snd (v oE))))
  else
    recvTailKC S K_on K_ro false st x kE' bE' .noneE

@[expose] def shcrFinishSendKC (K_on K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (st : Var Γ₁ authStateTy) (d : Var Γ₂ pauseTy)
    (ks : Var Γ₃ (.prod (B 32) (.prod (B 32) (B 32))))
    (sc : Var Γ₄ (.prod (B 32) (B 1568)))
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ FinTy :=
  letV (pdSid (v d)) fun sid => letV (pdBu (v d)) fun bu =>
  letV (pdM0 (v d)) fun m0 => letV (pdM1 (v d)) fun m1 =>
  letV (.fst (pdUI (v d))) fun uE => letV (.fst (.snd (pdUI (v d)))) fun pp =>
  letV (.snd (.snd (pdUI (v d)))) fun pt =>
  letV (.fst (v ks)) fun ekSk => letV (.fst (.snd (v ks))) fun ephSk =>
  letV (.snd (.snd (v ks))) fun spqrCoins =>
  letV (eCaseOpt (v pp) (.litBool false) fun p => .boolNot (peCorrupted (.snd (v p))))
    fun fresh =>
  bindV (.queryPrim .x25519Base (v ekSk)) fun ekPk =>
  bindV (.queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (buSpkB (v bu)))) fun dh1 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buIkB (v bu)))) fun dh2 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (buSpkB (v bu)))) fun dh3 =>
  bindV (.queryPrim .x25519 (.pair (v ekSk) (getDBytes (optSnd (buOpkB (v bu)))))) fun dh4 =>
  bindV (hkdfOrRoC K_ro true st (buildSecretsE (v dh1) (v dh2) (v dh3)
      (eCaseOpt (buOpkB (v bu)) .noneE fun _ => .someE (v dh4)) (.fst (v sc)))) fun dr =>
  bindV (.queryPrim .x25519Base (v ephSk)) fun ephPk =>
  bindV (.queryPrim .x25519 (.pair (v ephSk) (buSpkB (v bu)))) fun dhR =>
  bindV (rootRoC K_ro st (.fst (.fst (v dr))) (v dhR)) fun rkOut =>
  bindV (.queryPrim .chainKdfSeed (.snd (.fst (v rkOut)))) fun mkSeed =>
  bindV (.queryPrim .chainKdfNext (.snd (.fst (v rkOut)))) fun ck11 =>
  bindV (.queryPrim (.spqrInitSend 32 32) (.pair (.snd (.snd (.fst (v dr)))) (v spqrCoins)))
    fun sp? =>
  caseOptV (v sp?) (.ret (.pair aNone .noneE)) fun sp =>
  bindV (.queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.fst (.snd (v sp))))) fun mk =>
  letV (firstMsgADE (peIkAPk (v uE)) (buIkB (v bu)) (v ephPk) (.snd (.snd (v sp)))) fun ad =>
  bindV (.queryPrim (.aeadEnc 158 32 32) (.pair (v mk) (.pair (v ad) (v pt)))) fun ct =>
  letV (.pair (hdMk (peIkAPk (v uE)) (v ekPk) (buSpkId (v bu)) (optFst (buOpkB (v bu)))
      (buPqspkId (v bu)) (.snd (v sc))) (.pair (v ephPk) (.pair (.snd (.snd (v sp))) (v ct))))
    fun wm =>
  letV (eCaseOpt (v pp) (.pair (.litBool false) (.litBool false)) fun p =>
      .pair (eAny K_on (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbSpkPk (.snd (v b))) (buSpkB (v bu))))
        (eAny K_on (stSpks (v st)) fun b => .boolAnd (natEq (.fst (.fst (v b))) (.fst (v p)))
          (.bytesBeq (sbPqspkPk (.snd (v b))) (buPqspkB (v bu))))) fun hon =>
  letV (seMk (v sid) (buIkB (v bu)) (buSpkB (v bu)) (optSnd (buOpkB (v bu))) (buPqspkB (v bu))
      (.fst (v hon)) (.litBool false) (.snd (v hon)) (v ekSk) (v ephSk) (v fresh)
      (.boolAnd (v fresh) (.boolNot (.bytesBeq (v m0) (v m1))))) fun se =>
  .ret (.pair (eCaseOpt (v pp) (aSendUnfresh (.fst (v dr)) (.fst (.fst (v rkOut))) (v ck11) (v wm))
      fun _ => aSendFresh (v wm))
    (.someE (stUpd (v st) (sess := .listCons (v se) (stSess (v st)))
      (usedS := .listCons (v sid) (stUsedS (v st))) (ro := .snd (v dr)) (root := .snd (v rkOut)))))

@[expose] def shcrSendKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  .iteC (sendGuardE opk (v x)) (.ret (.pair aNone (v s))) <|
  letV (scBase (v s)) fun st =>
  bindV (preCheckC S K_on opk st x) fun pc =>
  caseOptV (v pc) (.ret (.pair aNone (v s))) fun d =>
  bindV .sampleBytes32 fun ekSk =>
  bindV .sampleBytes32 fun coins =>
  bindV .sampleBytes32 fun ephSk =>
  bindV .sampleBytes32 fun spqrCoins =>
  letV (pdBu (v d)) fun bu =>
  bindV (checkSigsC S K_on st bu) fun ok =>
  .iteC (.boolNot (v ok)) (.ret (.pair aNone (v s))) <|
  bindV (.queryPrim .kemEncaps (.pair (buPqspkB (v bu)) (v coins))) fun enc =>
  caseOptV (v enc)
    (.ret (.pair aNone (scUpd (v s) (cnt := .add (scCnt (v s)) (.litNat 1))))) fun sc =>
  letV (.pair (v ekSk) (.pair (v ephSk) (v spqrCoins))) fun ks =>
  bindV (shcrFinishSendKC K_on K_ro st d ks sc) fun out =>
  shcrFinC s (pdSid (v d)) (buPqspkB (v bu)) sc out

@[expose] def shcrAcceptKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (s : Var Γ₁ shcrStTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  bindV (onBase s fun g => recvKB S K_on K_ro opk g x) fun r =>
  letV (pmHdr (.snd (.snd (.snd (v x))))) fun hdr =>
  caseOptV (eFind K_on (stSpks (scBase (.snd (v r)))) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (v r)) fun bE =>
  bindV (.queryPrim .kemDecaps (.pair (sbPqspkSk (.snd (v bE))) (hdKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (v r)) fun ss =>
  .ret (.pair (.fst (v r)) (scUpd (.snd (v r)) (rR := .listCons
    (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.pair (sbPqspkPk (.snd (v bE)))
      (.pair (sbPqspkSk (.snd (v bE))) (.pair (hdKemCt (v hdr)) (v ss))))))
    (scRR (.snd (v r))))))

@[expose] def shcrResumeKC (K_on1 K_ro : ℕ) {Γ₁ Γ₂ Γ₃ Δ : List (Ty pqSig)}
    (sc : Var Γ₁ (.prod (B 32) (B 1568))) (d : Var Γ₂ pauseTy) (s : Var Γ₃ shcrStTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] : Comp pqxdhOps pqPrimIface Δ SCS :=
  letV (scBase (v s)) fun st =>
  bindV .sampleBytes32 fun ekSk =>
  bindV .sampleBytes32 fun ephSk =>
  bindV .sampleBytes32 fun spqrCoins =>
  letV (.pair (v ekSk) (.pair (v ephSk) (v spqrCoins))) fun ks =>
  bindV (shcrFinishSendKC K_on1 K_ro st d ks sc) fun out =>
  bindV (shcrFinC s (pdSid (v d)) (buPqspkB (pdBu (v d))) sc out) fun r =>
  .ret (.pair (.fst (v r)) (scUpd (.snd (v r)) (chosen := buPqspkB (pdBu (v d)))))

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsHs
