import A306559
import Spec_A306559
import Check_Spec_A306559
import Check_AntiVacuite_A306559

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# AxiomsReport_A306559 : couverture exhaustive des axiomes

Perimetre cible A306559 (4 modules) : le module
principal `A306559` (auto-contenu, `import Mathlib`) +
`Spec_A306559` + `Check_Spec_A306559` +
`Check_AntiVacuite_A306559`.
132 declarations auditees ci-dessous.
Le `deriving DecidableEq` de l'inductif
`A306559.Letter306559` produit une instance
automatique sans declaration source : pas de ligne
`#print axioms` pour elle (couverte via les usagers).
Attendu partout : [propext, Classical.choice, Quot.sound].
-/

-- A306559 (83 decls)
#print axioms A306559.Letter306559
#print axioms A306559.isVowel306559
#print axioms A306559.name306559
#print axioms A306559.iter306559
#print axioms A306559.step306559
#print axioms A306559.wordOf306559
#print axioms A306559.cum306559
#print axioms A306559.nextVowel306559
#print axioms A306559.vpos306559
#print axioms A306559.run306559
#print axioms A306559.W306559
#print axioms A306559.Mstep306559
#print axioms A306559.bitsAux306559
#print axioms A306559.bits306559
#print axioms A306559.Mfold306559
#print axioms A306559.M306559
#print axioms A306559.aStar306559
#print axioms A306559.off1306559
#print axioms A306559.off2306559
#print axioms A306559.nlen306559
#print axioms A306559.conjectureEX306559
#print axioms A306559.conjectureUN306559
#print axioms name306559_len_pos
#print axioms name306559_len_ge3
#print axioms fin2_eq_zero_or_one
#print axioms nlen306559_pos
#print axioms nlen306559_sub_off2
#print axioms off2_sub_off1
#print axioms off1_eq306559
#print axioms off2_eq_nlen_sub_one
#print axioms off1_lt_nlen
#print axioms off2_lt_nlen
#print axioms name306559_castLE
#print axioms name_castLE_len
#print axioms name_castLE_getD_lt_off1
#print axioms name_castLE_getD_mid
#print axioms name_castLE_getD_off1
#print axioms name_castLE_getD_off2
#print axioms iter306559_add
#print axioms iter_within306559
#print axioms iter_cum306559
#print axioms iter_at306559
#print axioms wordOf_eq306559
#print axioms iter_invariant306559
#print axioms nextVowel_eq306559
#print axioms nextVowel_ge306559
#print axioms nextVowel_lt_not_vowel306559
#print axioms vpos_lt_succ306559
#print axioms vpos_lt_of_lt306559
#print axioms nextVowel_agree306559
#print axioms bitsAux306559_fuel
#print axioms bits306559_ne_nil
#print axioms bits306559_bit0
#print axioms bits306559_bit1
#print axioms dropLast_cons306559
#print axioms M306559_zero
#print axioms M306559_odd
#print axioms M306559_even
#print axioms M306559_even_one
#print axioms M306559_odd_neg
#print axioms aStar306559_tail
#print axioms aStar306559_val
#print axioms cum306559_succ
#print axioms cum_mono306559
#print axioms cum_congr306559
#print axioms len_aStar306559
#print axioms cum_aStar306559
#print axioms vpos_aStar306559_0
#print axioms vpos_aStar306559_1
#print axioms vpos_aStar306559_2
#print axioms vpos_aStar306559_3
#print axioms vpos_aStar306559_4
#print axioms vpos_aStar306559_5
#print axioms vpos_aStar306559_6
#print axioms cum_aStar306559_3
#print axioms vpos_pair306559
#print axioms run_pair306559
#print axioms aStar306559_selfdesc
#print axioms vpos_aStar306559_lt_cum
#print axioms isVowel_vpos306559_aStar
#print axioms vpos_congr306559
#print axioms aStar306559_unique
#print axioms A306559

-- Spec_A306559 (20 decls)
#print axioms SpecA306559.letterSpec
#print axioms SpecA306559.isVowelSpec
#print axioms SpecA306559.nameSpec
#print axioms SpecA306559.iterSpec
#print axioms SpecA306559.stepSpec
#print axioms SpecA306559.wordOfSpec
#print axioms SpecA306559.cumSpec
#print axioms SpecA306559.nextVowelSpec
#print axioms SpecA306559.vposSpec
#print axioms SpecA306559.runSpec
#print axioms SpecA306559.WSpec
#print axioms SpecA306559.MstepSpec
#print axioms SpecA306559.bitsAuxSpec
#print axioms SpecA306559.bitsSpec
#print axioms SpecA306559.MfoldSpec
#print axioms SpecA306559.MSpec
#print axioms SpecA306559.aStarSpec
#print axioms SpecPropEXA306559
#print axioms SpecPropUNA306559
#print axioms SpecPropA306559

-- Check_Spec_A306559 (21 decls)
#print axioms spec_eq_letter306559
#print axioms spec_eq_isVowel306559
#print axioms spec_eq_name306559
#print axioms spec_eq_iter306559
#print axioms spec_eq_step306559
#print axioms spec_eq_wordOf306559
#print axioms spec_eq_cum306559
#print axioms spec_eq_nextVowel306559
#print axioms spec_eq_vpos306559
#print axioms spec_eq_run306559
#print axioms spec_eq_W306559
#print axioms spec_eq_Mstep306559
#print axioms spec_eq_bitsAux306559
#print axioms spec_eq_bits306559
#print axioms spec_eq_Mfold306559
#print axioms spec_eq_M306559
#print axioms spec_eq_aStar306559
#print axioms spec_prop_EX306559
#print axioms spec_prop_UN306559
#print axioms spec_prop_full306559
#print axioms proven_A306559

-- Check_AntiVacuite_A306559 (8 decls)
#print axioms antiVac_sat306559
#print axioms antiVac_M_prefix306559
#print axioms antiVac_aStar_prefix306559
#print axioms antiVac_vpos_prefix306559
#print axioms antiVac_run_prefix306559
#print axioms antiVac_M_nonconstant306559
#print axioms aBad306559
#print axioms antiVac_ablation306559
