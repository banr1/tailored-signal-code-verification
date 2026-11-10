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
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfCk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfMk -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyAeadCpa -- proof-setup: allow-public-import
public import Computational.Proofs.SignalPqxdh.Security.ReductionDsl.Auth1KeyPrfHmac -- proof-setup: allow-public-import

/-!
# Two-Fuel `(K_on, K_ro)` PRF and AEAD Branches

Defines two-fuel `(K_on, K_ro)` send and receive simulator branches for the kind-split one-key
`Auth` PRF and AEAD reductions.
-/

public section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase

open _root_.ReductionDsl (Ty Var Expr Comp Env Iface)
open _root_.SignalPqxdh (Setup)
open _root_.SignalPqxdh.LegacyCosted (pqSig pqxdhOps pqPrimIface B)

section PrfBranches

open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrf (
  Ext v letV bindV caseOptV caseSumV eAny eFind eCaseOpt
  natEq natLt sidEq bytesLen bytesBeq litB boolOr isSomeE optSnd
  samplePrim queryPrim
  sendQTy recvQTy authHybridStateFixedTy RSF prfMkCoreTy prfMkStepPreTy
  aNone sendGuardE ahsfHybrid ahsfSlots ahsfRecvCount ahsfMkSlots ahsfUpd ahsfUpdSlots
  ahsBase asHasWonAuth asUsedSendSessions asPrincipals asSecb asSpkBundles asRoCache asRootRoCache
  peCorrupted peIkAPk peSecIKA0 peIkSignPk
  pkbIkB pkbSpkB pkbSpkSig pkbPqspkB pkbPqspkSig pkbOpkB? sbSpkPk sbSpkSk sbPqspkPk sbPqspkSk
  encEC encKEM buildSecretsE firstMsgADE
  findHonestC koskBundleOkC resolveSigPkC checkBundleSpkHonIdealC hkdfRoC rootRoC
  allocSendSlotE allocRecvSlotE sampAtCkC finishAuthHybridSendC
  prepareAuthHybridRecvC parHstDec parFinishTag parMatchedSess? parIsUncorrSender parSameEph
  parSecrets parDhRatchet parKEntry pkmPqRatchetMsg pkmHdr pkmEphAPk pkmAeadCt hdrIkAPk
  iasDrKey iasRk1 iasMkSeed iasCk1_1 iasSid iasSpqrSalt? iasMsgKeys
  mkcSecb mkcIdx mkcSentChal mkcFhst mkcMk ahsfMkSaltCache
  lookupSendSlotOrZeroE sameSaltKeyE
  recvFinishTagRunC finishAuthRecvCkC finishAuthSendMkC finishAuthRecvMkC finishRecvUnmatchedMkPreC
  checkBundleProvenanceExactC koskSenderOkC kyberCheckE findMV matchIdealAuthHandshakeC
  eMap nat2Eq nat3Eq u32Beq u32OfNat optU32Eq
  asUsedRecvOPK asUsedRecvNoOPK asOpkEntries asUsedKyberTriples
  opkEntryTy oeConsumed oeOpkSk oeOpkPk oeUpd
  hdrSpkId hdrPqspkId hdrOpkId? hdrEkAPk hdrKemCt rkrMk ahsUpd ahsRecvKemRecs ahsIdealSessions
  iasEphAPk aRecvUnfresh aRecvHonest stUpd ahsfMk
)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthAead (
  cpaSlotSendResTy getDBytes iasAdE iasAeadCtE iasMsgPlainE iasCk1_0E finishCpaC spkHonIdealFromPeerC
)
open _root_.SignalPqxdh.Security.ReductionDsl.AuthPrfHmac (
  muStTy intPrepTy schedPrepArgsTy schedPrepTy schedArgsTy schedResTy hmRecvDataTy hmResTy hmPreTy
  hmSendTailC hmSchedFinC finErasedE hmRecvPrepC
)

@[expose] def authCkSendKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (.pair aNone (v fhst) : Expr pqxdhOps _ RSF) fun noneDone =>
  .ite (sendGuardE opk (v x)) (.ret (v noneDone)) <|
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (ahsBase (v hst)) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (v noneDone)) <|
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret (v noneDone)) <|
  .ite (eAny K_on (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid))
    (.ret (v noneDone)) <|
  caseOptV (eFind K_on (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneDone)) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K_on st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1))))
    (.ret (v noneDone)) <|
  letV (.ite (v isFresh) (.ite (asSecb (v st)) (v m1) (v m0)) (v m0)) fun msgPlain =>
  bindV (koskBundleOkC S K_on st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneDone)) <|
  bindV (samplePrim .bytes32) fun ekASk =>
  bindV (samplePrim .bytes32) fun kemCoins =>
  bindV (samplePrim .bytes32) fun ephASk =>
  bindV (samplePrim .bytes32) fun spqrCoins =>
  bindV (resolveSigPkC S K_on st (pkbIkB (v bu))) fun sigPkB =>
  bindV (queryPrim (.sigVerify 33)
    (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu))))) fun v1 =>
  bindV (queryPrim (.sigVerify 1569)
    (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu))))) fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
  letV (.fst (v sc)) fun ssKem =>
  letV (.snd (v sc)) fun kemCt =>
  bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
  bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
  bindV (checkBundleSpkHonIdealC S K_on st bu) fun spkHonIdeal =>
  letV (eCaseOpt (v pp) (.bool false) fun p =>
    eAny K_on (asSpkBundles (v st)) fun b =>
      .and (natEq (.fst (.fst (v b))) (.fst (v p)))
        (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))) fun pqspkHon =>
  letV (boolOr (v isFresh) (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (v pqspkHon)))
    fun isIdealSend =>
  letV (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ssKem) (.pair (v kemCt)
      (.pair (v ephASk) (v ephAPk)))))) fun keys6 =>
  .ite (v isIdealSend)
    (bindV (samplePrim .drKey96) fun drKey =>
     bindV (samplePrim .bytes32) fun rk1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     letV (allocSendSlotE (v ss) (v sid)) fun sa =>
     bindV (sampAtCkC (v idx) (v chalP) (.fst (v sa))) fun p =>
     letV (.fst (v p)) fun mkSeed =>
     letV (.snd (v p)) fun ck1_1 =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K_on hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (litB 32 [])
             (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (asRoCache (v st)) (asRootRoCache (v st))))))))))))))))))) fun out =>
     .ret (.pair (.fst (v out))
       (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (.snd (v sa)))))
    (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
     bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
       bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
       .ret (.some (v d4))) fun dh4? =>
     letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ssKem)) fun secrets =>
     bindV (hkdfRoC K_ro st (v secrets)) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
     bindV (rootRoC K_ro st (.fst (v drKey)) (v dhR)) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K_on hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
     .ret (.pair (.fst (v out))
       (ahsfMkSlots (.snd (v out)) (ahsfRecvCount (v fhst)) .nil (v ss))))

@[expose] def authCkRecvKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (chalP : Var Γ₂ (.prod (B 32) (B 32)))
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsfRecvCount (v fhst)) fun rc =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (.add (v rc) (.nat 1)) fun rc' =>
  bindV (prepareAuthHybridRecvC S K_on opk hst x) fun prep? =>
  caseOptV (v prep?) (.ret (.pair aNone (ahsfUpd (v fhst) (rc := v rc')))) fun prep =>
  letV (ahsBase (parHstDec (v prep))) fun st =>
  letV (parFinishTag (v prep)) fun fTag =>
  letV (boolOr (isSomeE (parMatchedSess? (v prep))) (parIsUncorrSender (v prep))) fun useIdeal =>
  .ite (v useIdeal)
    (caseOptV (parMatchedSess? (v prep))
      (bindV (samplePrim .drKey96) fun drKey =>
       bindV (samplePrim .bytes32) fun rk1 =>
       bindV (queryPrim (.spqrInitRecv 32 32)
         (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
       caseOptV (v sp?)
         (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
          .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
         fun sp =>
           letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
           bindV (sampAtCkC (v idx) (v chalP) (.fst (v ra))) fun p =>
           bindV (finishAuthRecvCkC S K_on msg prep (v drKey) (v rk1) (.snd (v sp)) (v rc') (v p)) fun res =>
           .ret (.pair (.fst (v res)) (ahsfUpdSlots (.snd (v res)) (slots := .snd (v ra)))))
      fun s =>
        .ite (parSameEph (v prep))
          (bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
              .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
             fun sp =>
               bindV (finishAuthRecvCkC S K_on msg prep (iasDrKey (v s)) (iasRk1 (v s)) (.snd (v sp))
                 (v rc') (.pair (iasMkSeed (v s)) (iasCk1_1 (v s)))) fun res =>
               .ret (.pair (.fst (v res)) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))
          (bindV (samplePrim .bytes32) fun rk1 =>
           bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
              .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
             fun sp =>
               letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
               bindV (sampAtCkC (v idx) (v chalP) (.fst (v ra))) fun p =>
               bindV (finishAuthRecvCkC S K_on msg prep (iasDrKey (v s)) (v rk1) (.snd (v sp))
                 (v rc') (v p)) fun res =>
               .ret (.pair (.fst (v res)) (ahsfUpdSlots (.snd (v res)) (slots := .snd (v ra))))))
    (bindV (hkdfRoC K_ro st (parSecrets (v prep))) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (rootRoC K_ro st (.fst (v drKey)) (parDhRatchet (v prep))) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitRecv 32 32)
       (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
     caseOptV (v sp?)
       (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
        .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))
       fun sp =>
         bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mks =>
         letV (firstMsgADE (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (parKEntry (v prep)))
             (pkmEphAPk (v msg)) (pkmPqRatchetMsg (v msg))) fun ad =>
         bindV (queryPrim (.aeadDec 158 32 32)
           (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))) fun pt? =>
         letV (eCaseOpt (v pt?) .none fun pt =>
           .some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
             (.pair (v pt) (.pair (v roC') (v rootC'))))))) fun res? =>
         bindV (recvFinishTagRunC S K_on fTag (v res?)) fun out =>
         .ret (.pair (.fst (v out)) (ahsfMkSlots (.snd (v out)) (v rc') .nil (v ss))))

@[expose] def authMkSendPreKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  letV (mkcSecb (v core)) fun secb =>
  letV (mkcIdx (v core)) fun idx =>
  letV (mkcSentChal (v core)) fun sentChal =>
  letV (mkcFhst (v core)) fun fhst =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (.inl (.pair aNone (v core)) : Expr pqxdhOps _ prfMkStepPreTy) fun noneDone =>
  .ite (sendGuardE opk (v x)) (.ret (v noneDone)) <|
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  .ite (asHasWonAuth (v st)) (.ret (v noneDone)) <|
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret (v noneDone)) <|
  .ite (eAny K_on (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)) (.ret (v noneDone)) <|
  caseOptV (eFind K_on (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneDone)) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K_on st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1))))
    (.ret (v noneDone)) <|
  letV (.ite (v isFresh) (.ite (asSecb (v st)) (v m1) (v m0)) (v m0)) fun msgPlain =>
  bindV (koskBundleOkC S K_on st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneDone)) <|
  bindV (samplePrim .bytes32) fun ekASk =>
  bindV (samplePrim .bytes32) fun kemCoins =>
  bindV (samplePrim .bytes32) fun ephASk =>
  bindV (samplePrim .bytes32) fun spqrCoins =>
  bindV (resolveSigPkC S K_on st (pkbIkB (v bu))) fun sigPkB =>
  bindV (queryPrim (.sigVerify 33)
    (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu))))) fun v1 =>
  bindV (queryPrim (.sigVerify 1569)
    (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu))))) fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
  letV (.fst (v sc)) fun ssKem =>
  letV (.snd (v sc)) fun kemCt =>
  bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
  bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
  bindV (checkBundleSpkHonIdealC S K_on st bu) fun spkHonIdeal =>
  letV (eCaseOpt (v pp) (.bool false) fun p =>
    eAny K_on (asSpkBundles (v st)) fun b =>
      .and (natEq (.fst (.fst (v b))) (.fst (v p)))
        (bytesBeq 1568 (sbPqspkPk (.snd (v b))) (pkbPqspkB (v bu)))) fun pqspkHon =>
  letV (boolOr (v isFresh) (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (v pqspkHon)))
    fun isIdealSend =>
  letV (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ssKem) (.pair (v kemCt)
      (.pair (v ephASk) (v ephAPk)))))) fun keys6 =>
  .ite (v isIdealSend)
    (bindV (samplePrim .drKey96) fun drKey =>
     bindV (samplePrim .bytes32) fun rk1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     letV (allocSendSlotE (v ss) (v sid)) fun sa =>
     letV (.fst (v sa)) fun sIdx =>
     letV (ahsfUpdSlots (v fhst) (slots := .snd (v sa))) fun fhst' =>
     .ite (.and (.not (v sentChal)) (natEq (v sIdx) (v idx)))
       (bindV (samplePrim .bytes32) fun ck1_1 =>
        .ret (.inr (.pair (v spqrSalt?)
          (.inl (.pair (v secb) (.pair (v idx) (.pair (v fhst')
            (.pair (v sid) (.pair (v uE) (.pair (v pp)
              (.pair (v isFresh) (.pair (v bu) (.pair (.pair (v m0) (v m1))
                (.pair (v keys6) (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
                  (.pair (v spqrSalt?) (.pair (v pqMsg) (v msgPlain))))))))))))))))))))
       (.ite (natLt (v sIdx) (v idx))
         (bindV (samplePrim .bytes32) fun ck1_1 =>
          bindV (samplePrim .msgKeys80) fun mks =>
          bindV (finishAuthSendMkC S K_on fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
            (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (litB 32 []) (v ck1_1)
            (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
          .ret (.inl (.pair (.fst (v res))
            (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))
         (bindV (samplePrim .bytes32) fun mkSeed =>
          bindV (samplePrim .bytes32) fun ck1_1 =>
          bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
          bindV (finishAuthSendMkC S K_on fhst' (v sid) (v uE) (v pp) (v isFresh) (v bu)
            (.pair (v m0) (v m1)) (v keys6) (v drKey) (v rk1) (v mkSeed) (v ck1_1)
            (v spqrSalt?) (v pqMsg) (v msgPlain) (v mks)) fun res =>
          .ret (.inl (.pair (.fst (v res))
            (mkcMk (v secb) (v idx) (v sentChal) (.snd (v res))))))))
    (bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
     bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
     bindV (caseOptV (pkbOpkB? (v bu)) (.ret .none) fun oP =>
       bindV (queryPrim .x25519 (.pair (v ekASk) (.snd (v oP)))) fun d4 =>
       .ret (.some (v d4))) fun dh4? =>
     letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ssKem)) fun secrets =>
     bindV (hkdfRoC K_ro st (v secrets)) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
     bindV (rootRoC K_ro st (.fst (v drKey)) (v dhR)) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitSend 32 32)
       (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
     caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
     letV (.fst (.snd (v sp))) fun spqrSalt? =>
     letV (.snd (.snd (v sp))) fun pqMsg =>
     bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mks =>
     letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishAuthHybridSendC S K_on hst
       (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v isFresh) (.pair (v bu)
         (.pair (.pair (v m0) (v m1)) (.pair (v keys6)
           (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
             (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v mks)
               (.pair (v ad) (.pair (v aeadCt) (.pair (v msgPlain)
                 (.pair (v roC') (v rootC')))))))))))))))))) fun out =>
     .ret (.inl (.pair (.fst (v out))
       (mkcMk (v secb) (v idx) (v sentChal)
         (ahsfUpd (v fhst) (hst := .snd (v out)))))))

@[expose] def authMkRecvPreKB (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (core : Var Γ₁ prfMkCoreTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ prfMkStepPreTy :=
  letV (mkcSecb (v core)) fun secb =>
  letV (mkcIdx (v core)) fun idx =>
  letV (mkcSentChal (v core)) fun sentChal =>
  letV (mkcFhst (v core)) fun fhst =>
  letV (ahsfSlots (v fhst)) fun ss =>
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsfRecvCount (v fhst)) fun rc =>
  letV (ahsfMkSaltCache (v fhst)) fun cache =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (.add (v rc) (.nat 1)) fun rc' =>
  bindV (prepareAuthHybridRecvC S K_on opk hst x) fun prep? =>
  caseOptV (v prep?)
    (.ret (.inl (.pair aNone
      (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpd (v fhst) (rc := v rc'))))))
    fun prep =>
  letV (ahsBase (parHstDec (v prep))) fun st =>
  letV (parFinishTag (v prep)) fun fTag =>
  letV (boolOr (isSomeE (parMatchedSess? (v prep))) (parIsUncorrSender (v prep))) fun useIdeal =>
  .ite (v useIdeal)
    (caseOptV (parMatchedSess? (v prep))
      (bindV (samplePrim .drKey96) fun drKey =>
       bindV (samplePrim .bytes32) fun rk1 =>
       bindV (queryPrim (.spqrInitRecv 32 32)
         (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
       caseOptV (v sp?)
         (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
          .ret (.inl (.pair (.fst (v out))
            (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
         fun sp =>
           letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
           letV (mkcMk (v secb) (v idx) (v sentChal)
             (ahsfUpdSlots (v fhst) (slots := .snd (v ra)))) fun core' =>
           finishRecvUnmatchedMkPreC S K_on core' msg prep (v drKey) (v rk1) (.snd (v sp))
             (.fst (v ra)) (v rc'))
      fun s =>
        .ite (parSameEph (v prep))
          (bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
              .ret (.inl (.pair (.fst (v out))
                (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
             fun sp =>
               letV (.snd (v sp)) fun spqrSalt? =>
               letV (lookupSendSlotOrZeroE (v ss) (iasSid (v s))) fun sIdx =>
               letV (.pair (iasSid (v s)) (v spqrSalt?)) fun cKey =>
               .ite (natEq (v sIdx) (v idx))
                 (.ite (sameSaltKeyE (v spqrSalt?) (iasSpqrSalt? (v s)))
                   (bindV (finishAuthRecvMkC S K_on msg prep (iasDrKey (v s)) (iasRk1 (v s))
                       (iasCk1_1 (v s)) (v rc') (v cache) (iasMsgKeys (v s))) fun res =>
                    .ret (.inl (.pair (.fst (v res))
                      (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))
                   (caseOptV (eFind K_on (v cache) fun e =>
                       .and (sidEq (.fst (.fst (v e))) (iasSid (v s)))
                         (sameSaltKeyE (.snd (.fst (v e))) (v spqrSalt?)))
                     (.ret (.inr (.pair (v spqrSalt?)
                       (.inr (.pair (v secb) (.pair (v idx) (.pair (v sentChal)
                         (.pair (v msg) (.pair (v prep)
                           (.pair (iasDrKey (v s)) (.pair (iasRk1 (v s)) (.pair (iasCk1_1 (v s))
                             (.pair (v rc') (.pair (v cache)
                               (.pair (v ss) (.some (.pair (v cKey) (v rc))))))))))))))))))
                     fun cEntry =>
                       bindV (finishAuthRecvMkC S K_on msg prep (iasDrKey (v s)) (iasRk1 (v s))
                         (iasCk1_1 (v s)) (v rc') (v cache) (.snd (.snd (v cEntry)))) fun res =>
                       .ret (.inl (.pair (.fst (v res))
                         (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss)))))))
                 (.ite (natLt (v sIdx) (v idx))
                   (.ite (sameSaltKeyE (v spqrSalt?) (iasSpqrSalt? (v s)))
                     (bindV (finishAuthRecvMkC S K_on msg prep (iasDrKey (v s)) (iasRk1 (v s))
                         (iasCk1_1 (v s)) (v rc') (v cache) (iasMsgKeys (v s))) fun res =>
                      .ret (.inl (.pair (.fst (v res))
                        (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))
                     (caseOptV (eFind K_on (v cache) fun e =>
                       .and (sidEq (.fst (.fst (v e))) (iasSid (v s)))
                         (sameSaltKeyE (.snd (.fst (v e))) (v spqrSalt?)))
                       (bindV (samplePrim .msgKeys80) fun mk =>
                        letV (.cons (.pair (v cKey) (.pair (v rc) (v mk))) (v cache))
                          fun cache' =>
                        bindV (finishAuthRecvMkC S K_on msg prep (iasDrKey (v s)) (iasRk1 (v s))
                          (iasCk1_1 (v s)) (v rc') (v cache') (v mk)) fun res =>
                        .ret (.inl (.pair (.fst (v res))
                          (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))
                       fun cEntry =>
                         bindV (finishAuthRecvMkC S K_on msg prep (iasDrKey (v s)) (iasRk1 (v s))
                           (iasCk1_1 (v s)) (v rc') (v cache) (.snd (.snd (v cEntry)))) fun res =>
                         .ret (.inl (.pair (.fst (v res))
                           (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss)))))))
                   (bindV (queryPrim (.deriveMsgKeys 32) (.pair (iasMkSeed (v s)) (v spqrSalt?)))
                      fun mk =>
                    bindV (finishAuthRecvMkC S K_on msg prep (iasDrKey (v s)) (iasRk1 (v s))
                      (iasCk1_1 (v s)) (v rc') (v cache) (v mk)) fun res =>
                    .ret (.inl (.pair (.fst (v res))
                      (mkcMk (v secb) (v idx) (v sentChal) (ahsfUpdSlots (.snd (v res)) (slots := v ss))))))))
          (bindV (samplePrim .bytes32) fun rk1 =>
           bindV (queryPrim (.spqrInitRecv 32 32)
              (.pair (.snd (.snd (iasDrKey (v s)))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
           caseOptV (v sp?)
             (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
              .ret (.inl (.pair (.fst (v out))
                (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
             fun sp =>
               letV (allocRecvSlotE (v ss) (v rc)) fun ra =>
               letV (mkcMk (v secb) (v idx) (v sentChal)
                 (ahsfUpdSlots (v fhst) (slots := .snd (v ra)))) fun core' =>
               finishRecvUnmatchedMkPreC S K_on core' msg prep (iasDrKey (v s)) (v rk1) (.snd (v sp))
                 (.fst (v ra)) (v rc')))
    (bindV (hkdfRoC K_ro st (parSecrets (v prep))) fun drOut =>
     letV (.fst (v drOut)) fun drKey =>
     letV (.snd (v drOut)) fun roC' =>
     bindV (rootRoC K_ro st (.fst (v drKey)) (parDhRatchet (v prep))) fun rkOut =>
     letV (.fst (.fst (v rkOut))) fun rk1 =>
     letV (.snd (.fst (v rkOut))) fun ck1_0 =>
     letV (.snd (v rkOut)) fun rootC' =>
     bindV (queryPrim .chainKdfSeed (v ck1_0)) fun mkSeed =>
     bindV (queryPrim .chainKdfNext (v ck1_0)) fun ck1_1 =>
     bindV (queryPrim (.spqrInitRecv 32 32)
       (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
     caseOptV (v sp?)
       (bindV (recvFinishTagRunC S K_on fTag .none) fun out =>
        .ret (.inl (.pair (.fst (v out))
          (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))
       fun sp =>
         bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (.snd (v sp)))) fun mks =>
         letV (firstMsgADE (hdrIkAPk (pkmHdr (v msg))) (peIkAPk (parKEntry (v prep)))
             (pkmEphAPk (v msg)) (pkmPqRatchetMsg (v msg))) fun ad =>
         bindV (queryPrim (.aeadDec 158 32 32)
           (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))) fun pt? =>
         letV (eCaseOpt (v pt?) .none fun pt =>
           .some (.pair (v drKey) (.pair (v rk1) (.pair (v ck1_1)
             (.pair (v pt) (.pair (v roC') (v rootC'))))))) fun res? =>
         bindV (recvFinishTagRunC S K_on fTag (v res?)) fun out =>
         .ret (.inl (.pair (.fst (v out))
           (mkcMk (v secb) (v idx) (v sentChal) (ahsfMkSlots (.snd (v out)) (v rc') (v cache) (v ss))))))

@[expose] def cpaSendSlotKB (S : Setup) (K_on K_ro : ℕ) (opk allowPause : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (idx : Var Γ₁ .nat) (ns : Var Γ₂ .nat)
    (fhst : Var Γ₃ authHybridStateFixedTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] :
    Comp pqxdhOps pqPrimIface Δ cpaSlotSendResTy :=
  letV (.inl (.pair aNone (.pair (v ns) (v fhst))) : Expr pqxdhOps _ cpaSlotSendResTy) fun noneDone =>
  .ite (sendGuardE opk (v x)) (.ret (v noneDone)) <|
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret (v noneDone)) <|
  .ite (eAny K_on (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)) (.ret (v noneDone)) <|
  caseOptV (eFind K_on (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneDone)) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K_on st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1))))
    (.ret (v noneDone)) <|
  bindV (koskBundleOkC S K_on st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneDone)) <|
  bindV (samplePrim .bytes32) fun ekASk =>
  bindV (samplePrim .bytes32) fun kemCoins =>
  bindV (samplePrim .bytes32) fun ephASk =>
  bindV (samplePrim .bytes32) fun spqrCoins =>
  letV (eCaseOpt (v pp) (pkbIkB (v bu)) fun p => peIkSignPk (.snd (v p))) fun sigPkB =>
  bindV (queryPrim (.sigVerify 33)
      (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu)))))
    fun v1 =>
  bindV (queryPrim (.sigVerify 1569)
      (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu)))))
    fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret (v noneDone)) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret (v noneDone)) fun sc =>
  letV (.fst (v sc)) fun ss =>
  letV (.snd (v sc)) fun kemCt =>
  bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
  bindV (checkBundleProvenanceExactC S K_on st bu) fun prov =>
  bindV (spkHonIdealFromPeerC S K_on st pp bu) fun spkHonIdeal =>
  letV (boolOr (v isFresh)
      (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (.snd (.snd (v prov)))))
    fun isIdealSend =>
  bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (getDBytes (optSnd (pkbOpkB? (v bu)))))) fun dh4Raw =>
  letV (eCaseOpt (pkbOpkB? (v bu)) .none fun _ => .some (v dh4Raw)) fun dh4? =>
  letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
  bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
  bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .drKey96) fun dk => .ret (.pair (v dk) (asRoCache (v st))))
      (hkdfRoC K_ro st (v secrets))) fun drOut =>
  letV (.fst (v drOut)) fun drKey =>
  letV (.snd (v drOut)) fun roC' =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
        .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))
      (rootRoC K_ro st (.fst (v drKey)) (v dhR))) fun rkOut =>
  letV (.fst (.fst (v rkOut))) fun rk1 =>
  letV (.snd (.fst (v rkOut))) fun ck1_0 =>
  letV (.snd (v rkOut)) fun rootC' =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
        .ret (.pair (v ms) (v cn)))
      (bindV (queryPrim .chainKdfSeed (v ck1_0)) fun ms =>
       bindV (queryPrim .chainKdfNext (v ck1_0)) fun cn => .ret (.pair (v ms) (v cn)))) fun mkc =>
  letV (.fst (v mkc)) fun mkSeed =>
  letV (.snd (v mkc)) fun ck1_1 =>
  bindV (queryPrim (.spqrInitSend 32 32) (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
  caseOptV (v sp?) (.ret (v noneDone)) fun sp =>
  letV (.fst (.snd (v sp))) fun spqrSalt? =>
  letV (.snd (.snd (v sp))) fun pqMsg =>
  letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
  letV (.pair (v sid) (.pair (v uE) (.pair (v pp) (.pair (v bu) (.pair (.pair (v m0) (v m1))
      (.pair (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ss) (.pair (v kemCt)
        (.pair (v ephASk) (v ephAPk))))))
      (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
        (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v ad) (.pair (v prov)
          (.pair (v roC') (v rootC')))))))))))))) fun pl =>
  .ite (v isFresh)
    (letV (.ite (natLt (v ns) (v idx)) (v m0) (v m1)) fun msgPlain =>
     (if allowPause then
        .ite (natEq (v ns) (v idx))
          (.ret (.inr (.pair (.pair (v ad) (.pair (v m0) (v m1)))
            (.pair (v pl) (.pair (v ns) (v fhst))))))
      else id) <|
     bindV (samplePrim .msgKeys80) fun mks =>
     bindV (queryPrim (.aeadEnc 158 32 32)
       (.pair (v mks) (.pair (v ad) (v msgPlain)))) fun aeadCt =>
     bindV (finishCpaC fhst (.bool true) (.bool true) (v pl) (v aeadCt)) fun res =>
     .ret (.inl (.pair (.fst (v res)) (.pair (.add (v ns) (.nat 1)) (.snd (v res))))))
    (bindV (.ite (v isIdealSend) (samplePrim .msgKeys80)
        (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?)))) fun mks =>
     bindV (queryPrim (.aeadEnc 158 32 32) (.pair (v mks) (.pair (v ad) (v m0)))) fun aeadCt =>
     bindV (finishCpaC fhst (.bool false) (v isIdealSend) (v pl) (v aeadCt)) fun res =>
     .ret (.inl (.pair (.fst (v res)) (.pair (v ns) (.snd (v res))))))

@[expose] def cpaRecvKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool) {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ RSF :=
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.add (ahsfRecvCount (v fhst)) (.nat 1)) fun rc' =>
  letV (.pair aNone (ahsfUpd (v fhst) (rc := v rc')) : Expr pqxdhOps _ RSF) fun noneRc =>
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (pkmHdr (v msg)) fun hdr =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  .ite (.not (.and (.and (.and (.and (.and
      (u32Beq (hdrSpkId (v hdr)) (u32OfNat (.fst (.snd (v x)))))
      (u32Beq (hdrPqspkId (v hdr)) (u32OfNat (.fst (.snd (v x))))))
      (optU32Eq (hdrOpkId? (v hdr))
        (if opk then .some (u32OfNat (.fst (.snd (.snd (v x))))) else .none)))
      (natEq (bytesLen 32 (hdrIkAPk (v hdr))) (.nat 32)))
      (natEq (bytesLen 32 (hdrEkAPk (v hdr))) (.nat 32)))
      (natEq (bytesLen 32 (pkmEphAPk (v msg))) (.nat 32))))
    (.ret (v noneRc)) <|
  .ite (eAny K_on (if opk then asUsedRecvOPK (v st) else asUsedRecvNoOPK (v st))
      fun e => nat3Eq (v e) (v kjo))
    (.ret (v noneRc)) <|
  bindV (koskSenderOkC S K_on st (hdrIkAPk (v hdr))) fun koskOk =>
  .ite (.not (v koskOk)) (.ret (v noneRc)) <|
  caseOptV (eFind K_on (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret (v noneRc)) fun kPair =>
  caseOptV (eFind K_on (asSpkBundles (v st)) fun e =>
      nat2Eq (.fst (v e)) (.pair (.fst (v x)) (.fst (.snd (v x)))))
    (.ret (v noneRc)) fun bPair =>
  letV (.snd (v kPair)) fun kE =>
  letV (.snd (v bPair)) fun bE =>
  bindV (if opk then
      caseOptV (eFind K_on (asOpkEntries (v st)) fun e => nat3Eq (.fst (v e)) (v kjo))
        (.ret (.inl .unit)) fun oPair =>
      .ite (oeConsumed (.snd (v oPair))) (.ret (.inl .unit))
        (.ret (.inr (.some (.snd (v oPair)))))
    else .ret (.inr .none) : Comp pqxdhOps pqPrimIface _ (.sum .unit (.opt opkEntryTy))) fun oRes =>
  caseSumV (v oRes) (fun _ => .ret (v noneRc)) fun oE? =>
  letV (kyberCheckE K_on (asUsedKyberTriples (v st)) (.pair (.fst (v x)) (.pair (hdrPqspkId (v hdr))
      (.pair (hdrSpkId (v hdr)) (hdrEkAPk (v hdr)))))) fun kc =>
  bindV (queryPrim .isCanonical (hdrEkAPk (v hdr))) fun can =>
  bindV (queryPrim .isCanonical (pkmEphAPk (v msg))) fun canE =>
  .ite (boolOr (boolOr (.not (.fst (v kc))) (.not (v can))) (.not (v canE)))
    (.ret (v noneRc)) <|
  bindV (queryPrim .kemDecaps (.pair (sbPqspkSk (v bE)) (hdrKemCt (v hdr)))) fun ss? =>
  caseOptV (v ss?) (.ret (v noneRc)) fun ss =>
  letV (rkrMk (.fst (v x)) (.fst (.snd (v x))) (sbPqspkPk (v bE)) (sbPqspkSk (v bE))
      (hdrKemCt (v hdr)) (v ss)) fun rRec =>
  letV (ahsUpd (v hst) (recvR := .cons (v rRec) (ahsRecvKemRecs (v hst)))) fun hstDec =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrIkAPk (v hdr)))) fun dh1 =>
  bindV (queryPrim .x25519 (.pair (peSecIKA0 (v kE)) (hdrEkAPk (v hdr)))) fun dh2 =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (hdrEkAPk (v hdr)))) fun dh3 =>
  bindV (caseOptV (v oE?) (.ret .none) fun oE =>
      bindV (queryPrim .x25519 (.pair (oeOpkSk (v oE)) (hdrEkAPk (v hdr)))) fun dh4 =>
      .ret (.some (v dh4))) fun dh4? =>
  letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
  letV (eCaseOpt (v oE?) .none fun oE => .some (oeOpkPk (v oE))) fun opkBPk? =>
  letV (ahsfMkSaltCache (v fhst)) fun cache =>
  letV (ahsfRecvCount (v fhst)) fun rc =>
  bindV (findHonestC S K_on st (hdrIkAPk (v hdr))) fun snd? =>
  letV (eCaseOpt (v snd?) (.bool false) fun sP => .not (peCorrupted (.snd (v sP))))
    fun isUncorr =>
  letV (peIkAPk (v kE)) fun ikBPk =>
  letV (sbSpkPk (v bE)) fun spkBPk =>
  letV (sbPqspkPk (v bE)) fun pqspkBPk =>
  bindV (findMV (min K_on S.N_sess_tot) (ahsIdealSessions (v hstDec)) fun s =>
      matchIdealAuthHandshakeC ikBPk spkBPk opkBPk? pqspkBPk hdr s) fun matched? =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .drKey96) fun dk => .ret (.pair (v dk) (asRoCache (v st))))
        (hkdfRoC K_ro st (v secrets)))
      fun s => .ret (.pair (iasDrKey (v s)) (asRoCache (v st)))) fun drOut =>
  letV (.fst (v drOut)) fun drKey =>
  letV (.snd (v drOut)) fun roC' =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pkmEphAPk (v msg)))) fun dhR =>
  bindV (caseOptV (v matched?) (.ret (.bool false)) fun s =>
      bindV (queryPrim .pow8 (pkmEphAPk (v msg))) fun p1 =>
      bindV (queryPrim .pow8 (iasEphAPk (v s))) fun p2 =>
      .ret (bytesBeq 32 (v p1) (v p2))) fun sameEph =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
          .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))
        (rootRoC K_ro st (.fst (v drKey)) (v dhR)))
      fun s => .ite (v sameEph)
        (.ret (.pair (.pair (iasRk1 (v s)) (iasCk1_0E (v s))) (asRootRoCache (v st))))
        (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
          .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))) fun rkOut =>
  letV (.fst (.fst (v rkOut))) fun rk1 =>
  letV (.snd (.fst (v rkOut))) fun ck1_0 =>
  letV (.snd (v rkOut)) fun rootC' =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
          .ret (.pair (v ms) (v cn)))
        (bindV (queryPrim .chainKdfSeed (v ck1_0)) fun ms =>
         bindV (queryPrim .chainKdfNext (v ck1_0)) fun cn => .ret (.pair (v ms) (v cn))))
      fun s => .ite (v sameEph)
        (.ret (.pair (iasMkSeed (v s)) (iasCk1_1 (v s))))
        (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
          .ret (.pair (v ms) (v cn))))
    fun mkc =>
  letV (.fst (v mkc)) fun mkSeed =>
  letV (.snd (v mkc)) fun ck1_1 =>
  bindV (queryPrim (.spqrInitRecv 32 32)
      (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
  letV (ahsUpd (v hstDec)) fun hstDecV =>
  caseOptV (v sp?)
    (.ret (.pair aNone (ahsfMk (v hstDecV) (v rc') (v cache)))) fun sp =>
  letV (.snd (v sp)) fun spqrSalt? =>
  letV (eCaseOpt (v matched?) (.bool false) fun s =>
      .and (v sameEph) (sameSaltKeyE (v spqrSalt?) (iasSpqrSalt? (v s)))) fun sameMk =>
  bindV (caseOptV (v matched?)
      (.ite (v isUncorr)
        (bindV (samplePrim .msgKeys80) fun mk => .ret (.pair (v mk) (v cache)))
        (bindV (queryPrim (.deriveMsgKeys 32) (.pair (v mkSeed) (v spqrSalt?))) fun mk =>
          .ret (.pair (v mk) (v cache))))
      fun s => .ite (v sameMk) (.ret (.pair (iasMsgKeys (v s)) (v cache)))
        (.ite (v sameEph)
          (letV (.pair (iasSid (v s)) (v spqrSalt?)) fun cKey =>
           caseOptV (eFind K_on (v cache) fun e =>
               .and (sidEq (.fst (.fst (v e))) (iasSid (v s)))
                 (sameSaltKeyE (.snd (.fst (v e))) (v spqrSalt?)))
             (bindV (samplePrim .msgKeys80) fun mk =>
               .ret (.pair (v mk) (.cons (.pair (v cKey) (.pair (v rc) (v mk))) (v cache))))
             fun e => .ret (.pair (.snd (.snd (v e))) (v cache)))
          (bindV (samplePrim .msgKeys80) fun mk => .ret (.pair (v mk) (v cache))))) fun mkOut =>
  letV (.fst (v mkOut)) fun mks =>
  letV (.snd (v mkOut)) fun cache' =>
  letV (firstMsgADE (hdrIkAPk (v hdr)) (peIkAPk (v kE)) (pkmEphAPk (v msg))
      (pkmPqRatchetMsg (v msg))) fun ad =>
  letV (.pair aNone (ahsfMk (v hstDecV) (v rc') (v cache')) : Expr pqxdhOps _ RSF) fun noneDec =>
  bindV (.ite (v sameMk)
      (.ret (eCaseOpt (v matched?) .none fun s =>
        .ite (.and (bytesBeq 158 (v ad) (iasAdE (v s)))
            (bytesBeq 32 (pkmAeadCt (v msg)) (iasAeadCtE (v s))))
          (.some (iasMsgPlainE (v s))) .none))
      (.ite (v isUncorr) (.ret .none)
        (queryPrim (.aeadDec 158 32 32)
          (.pair (v mks) (.pair (v ad) (pkmAeadCt (v msg))))))) fun pt? =>
  caseOptV (v pt?) (.ret (v noneDec)) fun pt =>
  bindV (findHonestC S K_on st (hdrIkAPk (v hdr))) fun snd2? =>
  letV (eCaseOpt (v snd2?) (aRecvUnfresh (v drKey) (v rk1) (v ck1_1) (v pt)) fun _ => aRecvHonest)
    fun resp =>
  letV (ahsBase (v hstDec)) fun stD =>
  letV (if opk then
      stUpd (v stD)
        (opks := eMap K_on (asOpkEntries (v st)) fun e =>
          .ite (nat3Eq (.fst (v e)) (v kjo))
            (.pair (.fst (v e)) (oeUpd (.snd (v e)) (consumed := .bool true))) (v e))
        (usedO := .cons (v kjo) (asUsedRecvOPK (v st)))
        (kyb := .snd (v kc)) (ro := v roC') (root := v rootC')
    else
      stUpd (v stD)
        (usedN := .cons (v kjo) (asUsedRecvNoOPK (v st)))
        (kyb := .snd (v kc)) (ro := v roC') (root := v rootC')) fun base' =>
  .ret (.pair (v resp) (ahsfMk (ahsUpd (v hstDec) (base := v base')) (v rc') (v cache')))

@[expose] def intSendPrepKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Δ : List (Ty pqSig)}
    (fhst : Var Γ₁ authHybridStateFixedTy) (x : Var Γ₂ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] : Comp pqxdhOps pqPrimIface Δ (.opt intPrepTy) :=
  letV (ahsfHybrid (v fhst)) fun hst =>
  letV (ahsBase (v hst)) fun st =>
  letV (.fst (.snd (.snd (v x)))) fun bu =>
  letV (.fst (.snd (.snd (.snd (v x))))) fun m0 =>
  letV (.snd (.snd (.snd (.snd (v x))))) fun m1 =>
  letV (if opk then .inl (.pair (.fst (v x)) (.fst (.snd (v x))))
    else .inr (.inl (.pair (.fst (v x)) (.fst (.snd (v x)))))) fun sid =>
  .ite (.not (natEq (bytesLen 32 (v m0)) (bytesLen 32 (v m1)))) (.ret .none) <|
  .ite (eAny K_on (asUsedSendSessions (v st)) fun e => sidEq (v e) (v sid)) (.ret .none) <|
  caseOptV (eFind K_on (asPrincipals (v st)) fun e => natEq (.fst (v e)) (.fst (v x)))
    (.ret .none) fun uPair =>
  letV (.snd (v uPair)) fun uE =>
  bindV (findHonestC S K_on st (pkbIkB (v bu))) fun pp =>
  letV (eCaseOpt (v pp) (.bool false) fun p => .not (peCorrupted (.snd (v p)))) fun isFresh =>
  .ite (.and (.not (v isFresh)) (.not (bytesBeq 32 (v m0) (v m1)))) (.ret .none) <|
  letV (.ite (v isFresh) (.ite (asSecb (v st)) (v m1) (v m0)) (v m0)) fun msgPlain =>
  bindV (koskBundleOkC S K_on st bu) fun koskOk =>
  .ite (.not (v koskOk)) (.ret .none) <|
  bindV (samplePrim .bytes32) fun ekASk =>
  bindV (samplePrim .bytes32) fun kemCoins =>
  bindV (samplePrim .bytes32) fun ephASk =>
  bindV (samplePrim .bytes32) fun spqrCoins =>
  letV (eCaseOpt (v pp) (pkbIkB (v bu)) fun p => peIkSignPk (.snd (v p))) fun sigPkB =>
  bindV (queryPrim (.sigVerify 33)
      (.pair (v sigPkB) (.pair (encEC (pkbSpkB (v bu))) (pkbSpkSig (v bu)))))
    fun v1 =>
  bindV (queryPrim (.sigVerify 1569)
      (.pair (v sigPkB) (.pair (encKEM (pkbPqspkB (v bu))) (pkbPqspkSig (v bu)))))
    fun v2 =>
  .ite (.not (.and (v v1) (v v2))) (.ret .none) <|
  bindV (queryPrim .kemEncaps (.pair (pkbPqspkB (v bu)) (v kemCoins))) fun enc? =>
  caseOptV (v enc?) (.ret .none) fun sc =>
  letV (.fst (v sc)) fun ss =>
  letV (.snd (v sc)) fun kemCt =>
  bindV (queryPrim .x25519Base (v ekASk)) fun ekAPk =>
  bindV (checkBundleProvenanceExactC S K_on st bu) fun prov =>
  bindV (spkHonIdealFromPeerC S K_on st pp bu) fun spkHonIdeal =>
  letV (boolOr (v isFresh)
      (.and (.and (isSomeE (v pp)) (v spkHonIdeal)) (.snd (.snd (v prov)))))
    fun isIdealSend =>
  bindV (queryPrim .x25519 (.pair (peSecIKA0 (v uE)) (pkbSpkB (v bu)))) fun dh1 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (pkbIkB (v bu)))) fun dh2 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (pkbSpkB (v bu)))) fun dh3 =>
  bindV (queryPrim .x25519 (.pair (v ekASk) (getDBytes (optSnd (pkbOpkB? (v bu))))))
    fun dh4Raw =>
  letV (eCaseOpt (pkbOpkB? (v bu)) .none fun _ => .some (v dh4Raw)) fun dh4? =>
  letV (buildSecretsE (v dh1) (v dh2) (v dh3) (v dh4?) (v ss)) fun secrets =>
  bindV (queryPrim .x25519Base (v ephASk)) fun ephAPk =>
  bindV (queryPrim .x25519 (.pair (v ephASk) (pkbSpkB (v bu)))) fun dhR =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .drKey96) fun dk => .ret (.pair (v dk) (asRoCache (v st))))
      (hkdfRoC K_ro st (v secrets))) fun drOut =>
  letV (.fst (v drOut)) fun drKey =>
  letV (.snd (v drOut)) fun roC' =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
        .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))
      (rootRoC K_ro st (.fst (v drKey)) (v dhR))) fun rkOut =>
  letV (.fst (.fst (v rkOut))) fun rk1 =>
  letV (.snd (.fst (v rkOut))) fun ck1_0 =>
  letV (.snd (v rkOut)) fun rootC' =>
  bindV (.ite (v isIdealSend)
      (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
        .ret (.pair (v ms) (v cn)))
      (bindV (queryPrim .chainKdfSeed (v ck1_0)) fun ms =>
       bindV (queryPrim .chainKdfNext (v ck1_0)) fun cn => .ret (.pair (v ms) (v cn)))) fun mkc =>
  letV (.fst (v mkc)) fun mkSeed =>
  letV (.snd (v mkc)) fun ck1_1 =>
  bindV (queryPrim (.spqrInitSend 32 32) (.pair (.snd (.snd (v drKey))) (v spqrCoins))) fun sp? =>
  caseOptV (v sp?) (.ret .none) fun sp =>
  letV (.fst (.snd (v sp))) fun spqrSalt? =>
  letV (.snd (.snd (v sp))) fun pqMsg =>
  letV (firstMsgADE (peIkAPk (v uE)) (pkbIkB (v bu)) (v ephAPk) (v pqMsg)) fun ad =>
  .ret (.some (.pair (v uE) (.pair (v pp) (.pair (.pair (v isFresh)
      (.pair (v isIdealSend) (v msgPlain)))
    (.pair (.pair (v ekASk) (.pair (v ekAPk) (.pair (v ss) (.pair (v kemCt)
        (.pair (v ephASk) (v ephAPk))))))
      (.pair (v drKey) (.pair (.pair (v rk1) (.pair (v ck1_0) (.pair (v mkSeed) (v ck1_1))))
        (.pair (v spqrSalt?) (.pair (v pqMsg) (.pair (v ad) (.pair (v prov)
          (.pair (v roC') (v rootC')))))))))))))

@[expose] def hmSendKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ sendQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  .ite (sendGuardE opk (v x)) (.ret (.inl (.pair (.pair aNone (v fhst)) (v mst)))) <|
  bindV (intSendPrepKC S K_on K_ro opk fhst x) fun p? =>
  caseOptV (v p?) (.ret (.inl (.pair (.pair aNone (v fhst)) (v mst)))) fun p =>
  hmSendTailC S K_on opk jt fhst mst x p

@[expose] def hmSchedPrepKC (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedPrepArgsTy) : Comp pqxdhOps pqPrimIface Δ (.opt schedPrepTy) :=
  letV a fun a =>
  letV (.fst (v a)) fun hstDec =>
  letV (.fst (.snd (v a))) fun kE =>
  letV (.fst (.snd (.snd (v a)))) fun bE =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun opkBPk? =>
  letV (.fst (.snd (.snd (.snd (.snd (v a)))))) fun secrets =>
  letV (.snd (.snd (.snd (.snd (.snd (v a)))))) fun msg =>
  letV (ahsBase (v hstDec)) fun st =>
  letV (pkmHdr (v msg)) fun hdr =>
  bindV (findHonestC S K_on st (hdrIkAPk (v hdr))) fun snd? =>
  letV (eCaseOpt (v snd?) (.bool false) fun sP => .not (peCorrupted (.snd (v sP))))
    fun isUncorr =>
  letV (peIkAPk (v kE)) fun ikBPk =>
  letV (sbSpkPk (v bE)) fun spkBPk =>
  letV (sbPqspkPk (v bE)) fun pqspkBPk =>
  bindV (findMV (min K_on S.N_sess_tot) (ahsIdealSessions (v hstDec)) fun s =>
      matchIdealAuthHandshakeC ikBPk spkBPk opkBPk? pqspkBPk hdr s) fun matched? =>
  letV (boolOr (isSomeE (v matched?)) (v isUncorr)) fun useIdeal =>
  bindV (.ite (v useIdeal)
      (caseOptV (v matched?)
        (bindV (samplePrim .drKey96) fun dk => .ret (.pair (v dk) (asRoCache (v st))))
        fun s => .ret (.pair (iasDrKey (v s)) (asRoCache (v st))))
      (hkdfRoC K_ro st (v secrets))) fun drOut =>
  letV (.fst (v drOut)) fun drKey =>
  letV (.snd (v drOut)) fun roC' =>
  bindV (queryPrim .x25519 (.pair (sbSpkSk (v bE)) (pkmEphAPk (v msg)))) fun dhR =>
  bindV (caseOptV (v matched?) (.ret (.bool false)) fun s =>
      bindV (queryPrim .pow8 (pkmEphAPk (v msg))) fun p1 =>
      bindV (queryPrim .pow8 (iasEphAPk (v s))) fun p2 =>
      .ret (bytesBeq 32 (v p1) (v p2))) fun sameEph =>
  bindV (.ite (v useIdeal)
      (caseOptV (v matched?)
        (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
          .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st))))
        fun s => .ite (v sameEph)
          (.ret (.pair (.pair (iasRk1 (v s)) (iasCk1_0E (v s))) (asRootRoCache (v st))))
          (bindV (samplePrim .bytes32) fun r => bindV (samplePrim .bytes32) fun c =>
            .ret (.pair (.pair (v r) (v c)) (asRootRoCache (v st)))))
      (rootRoC K_ro st (.fst (v drKey)) (v dhR))) fun rkOut =>
  letV (.fst (.fst (v rkOut))) fun rk1 =>
  letV (.snd (.fst (v rkOut))) fun ck1_0 =>
  letV (.snd (v rkOut)) fun rootC' =>
  bindV (.ite (v useIdeal)
      (caseOptV (v matched?)
        (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
          .ret (.pair (v ms) (v cn)))
        fun s => .ite (v sameEph)
          (.ret (.pair (iasMkSeed (v s)) (iasCk1_1 (v s))))
          (bindV (samplePrim .bytes32) fun ms => bindV (samplePrim .bytes32) fun cn =>
            .ret (.pair (v ms) (v cn))))
      (bindV (queryPrim .chainKdfSeed (v ck1_0)) fun ms =>
       bindV (queryPrim .chainKdfNext (v ck1_0)) fun cn => .ret (.pair (v ms) (v cn))))
    fun mkc =>
  letV (.fst (v mkc)) fun mkSeed =>
  letV (.snd (v mkc)) fun ck1_1 =>
  bindV (queryPrim (.spqrInitRecv 32 32)
      (.pair (.snd (.snd (v drKey))) (pkmPqRatchetMsg (v msg)))) fun sp? =>
  caseOptV (v sp?) (.ret .none) fun sp =>
  .ret (.some (.pair (v isUncorr) (.pair (v matched?) (.pair (v useIdeal) (.pair (v drKey)
    (.pair (v roC') (.pair (v sameEph) (.pair (v rk1) (.pair (v ck1_0) (.pair (v rootC')
      (.pair (v mkSeed) (.pair (v ck1_1) (.snd (v sp))))))))))))))

@[expose] def hmSchedKC (S : Setup) (K_on K_ro : ℕ) {Δ : List (Ty pqSig)}
    (a : Expr pqxdhOps Δ schedArgsTy) : Comp pqxdhOps pqPrimIface Δ schedResTy :=
  letV a fun a =>
  letV (.fst (v a)) fun jt =>
  letV (.fst (.snd (v a))) fun rc =>
  letV (.fst (.snd (.snd (v a)))) fun cache =>
  letV (.fst (.snd (.snd (.snd (v a))))) fun pa =>
  letV (.snd (.snd (.snd (.snd (v a))))) fun mst =>
  bindV (hmSchedPrepKC S K_on K_ro (v pa)) fun sp? =>
  caseOptV (v sp?) (.ret (.pair (.pair .none (v cache)) (v mst))) fun sp =>
  hmSchedFinC S K_on (.pair (v jt) (.pair (.fst (.snd (v pa)))
    (.pair (.snd (.snd (.snd (.snd (.snd (v pa))))))
      (.pair (v rc) (.pair (v cache) (.pair (v sp) (v mst)))))))

@[expose] def hmRecvTailKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Γ₅ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy) (d : Var Γ₅ hmRecvDataTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] [Ext Γ₅ Δ] :
    Comp pqxdhOps pqPrimIface Δ hmResTy :=
  letV (.snd (.snd (.snd (v x)))) fun msg =>
  letV (.pair (.fst (v x)) (.pair (.fst (.snd (v x))) (.fst (.snd (.snd (v x)))))) fun kjo =>
  letV (.fst (v d)) fun kE =>
  letV (.fst (.snd (v d))) fun bE =>
  letV (.fst (.snd (.snd (v d)))) fun opkPk? =>
  letV (.fst (.snd (.snd (.snd (v d))))) fun secrets =>
  letV (.fst (.snd (.snd (.snd (.snd (v d)))))) fun hstDec =>
  letV (.fst (.snd (.snd (.snd (.snd (.snd (v d))))))) fun usedT' =>
  letV (.snd (.snd (.snd (.snd (.snd (.snd (v d))))))) fun sndHon =>
  bindV (hmSchedKC S K_on K_ro (.pair (v jt) (.pair (ahsfRecvCount (v fhst))
      (.pair (ahsfMkSaltCache (v fhst))
        (.pair (.pair (v hstDec) (.pair (v kE) (.pair (v bE) (.pair (v opkPk?)
          (.pair (v secrets) (v msg)))))) (v mst)))))) fun so =>
  letV (.fst (.fst (v so))) fun res? =>
  letV (.snd (.fst (v so))) fun cache' =>
  letV (.snd (v so)) fun mst' =>
  letV (finErasedE K_on opk kjo usedT' sndHon hstDec res?) fun fin =>
  .ret (.pair (.pair (.fst (v fin))
      (ahsfMk (.snd (v fin)) (.add (ahsfRecvCount (v fhst)) (.nat 1)) (v cache')))
    (v mst'))

@[expose] def hmRecvKC (S : Setup) (K_on K_ro : ℕ) (opk : Bool)
    {Γ₁ Γ₂ Γ₃ Γ₄ Δ : List (Ty pqSig)}
    (jt : Var Γ₁ .nat) (fhst : Var Γ₂ authHybridStateFixedTy)
    (mst : Var Γ₃ muStTy) (x : Var Γ₄ recvQTy)
    [Ext Γ₁ Δ] [Ext Γ₂ Δ] [Ext Γ₃ Δ] [Ext Γ₄ Δ] : Comp pqxdhOps pqPrimIface Δ hmPreTy :=
  bindV (hmRecvPrepC S K_on opk fhst x) fun d? =>
  caseOptV (v d?)
    (.ret (.inl (.pair (.pair aNone
      (ahsfUpd (v fhst) (rc := .add (ahsfRecvCount (v fhst)) (.nat 1)))) (v mst))))
    fun d =>
  bindV (hmRecvTailKC S K_on K_ro opk jt fhst mst x d) fun r => .ret (.inl (v r))

end PrfBranches

end Computational.Proofs.SignalPqxdh.Security.ReductionDsl.KindSplit.AuthCoreKArmsBase
