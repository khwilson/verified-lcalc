/-
Copyright (c) 2026 Kevin Wilson. All rights reserved.
Part of verified-lcalc.
Authors: Kevin Wilson
-/
module

public import VerifiedLcalc.Verification.StoredInvariants
public import VerifiedLcalc.Certificate.Witnesses.FinitePrimes

/-! # Proof-carrying arithmetic data of one rational curve

Finite checks retain their actual mathematical types. The conductor, sign and
level exponents take an explicit arithmetic modular realization as input.
-/

public section

namespace VerifiedLcalc

open EllipticCurve NumberField WeierstrassCurve

/-- Retain exactly the supplied factors for which an intrinsic equality is available. -/
@[expose] def checkedTamagawaFacts (curve : WeierstrassCurve ℤ)
    (rows : List LocalReductionClaim)
    (h : ∀ row ∈ rows, row.TamagawaSpec curve) : List (LocalTamagawaFact curve) :=
  rows.attach.filterMap fun row =>
    match hc : row.val.tamagawaNumber, hs : tamagawaExpected? curve row.val.prime with
    | some value, some _ =>
      let proof := h row.val row.property value hc
      some ⟨⟨row.val.prime, Classical.choose proof⟩, value,
        Classical.choose_spec proof (by simp [hs])⟩
    | _, _ => none

/-- Retain only checked symbols or additive-family information from the supplied rows. -/
@[expose] def checkedKodairaFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] (rows : List LocalReductionClaim)
    (h : ∀ row ∈ rows, row.KodairaSpec curve) : List (LocalKodairaFact curve) :=
  rows.attach.filterMap fun row =>
    match hc : row.val.kodairaSymbol with
    | none => none
    | some code =>
      let proof := h row.val row.property
      some ⟨⟨row.val.prime, Classical.choose proof⟩, kodairaIIndex code,
        Classical.choose_spec proof code hc⟩

/-- Retain the supplied local arithmetic signs with minimality and transcript validity. -/
@[expose] def checkedLocalRootNumberFacts (curve : WeierstrassCurve ℤ)
    [(curve.baseChange ℚ).IsElliptic] (rows : List LocalReductionClaim) (d : WildData)
    (hm : IsGlobalMinimal (𝓞 ℚ) (curve.baseChange ℚ)) (hd : d.Valid curve)
    (h : ∀ row ∈ rows, row.RootNumberSpec curve d) : List (LocalRootNumberFact curve) :=
  rows.attach.filterMap fun row =>
    match hc : row.val.rootNumber with
    | none => none
    | some value =>
      let proof := h row.val row.property value hc
      let hp := Classical.choose proof
      letI : Fact row.val.prime.Prime := ⟨hp⟩
      let correct := Classical.choose_spec proof
      some ⟨⟨row.val.prime, hp⟩, hm.isMinimal (rationalPlace row.val.prime), d, hd, value,
        correct.1, correct.2⟩

end VerifiedLcalc
