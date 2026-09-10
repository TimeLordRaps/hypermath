"""Reviewed declaration identity baseline, not an assertion of consistency.

Captured with Lean4.14.0 from the existing69 axiom declarations and target
statement at Git revision db141d669491ce6b51d7fe15602c0925398f3154.
The reporter only requests kernel observations; it adds no assumptions.
Changes to this policy require explicit mathematical review, not regeneration
as an automatic response to a failing gate.
"""

AXIOM_DECLARATIONS = {'Hypermath.Congruent': 'axiom Hypermath.Congruent : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.D': 'axiom Hypermath.D : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.Definition': 'axiom Hypermath.Definition : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.DerivationPath': 'axiom Hypermath.DerivationPath : Type',
 'Hypermath.Derives': 'axiom Hypermath.Derives : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.Discharge': 'axiom Hypermath.Discharge : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.Form': 'axiom Hypermath.Form : Type',
 'Hypermath.FormClosure': 'axiom Hypermath.FormClosure : Hypermath.Form → Prop',
 'Hypermath.HMSyntax': 'axiom Hypermath.HMSyntax : Hypermath.Form → Prop',
 'Hypermath.Semantics': 'axiom Hypermath.Semantics : Hypermath.Form → Prop',
 'Hypermath.Similar': 'axiom Hypermath.Similar : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.Simulation': 'axiom Hypermath.Simulation : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.Substance': 'axiom Hypermath.Substance : Hypermath.Form → Prop',
 'Hypermath.axBox': 'axiom Hypermath.axBox : ∀ (x : Hypermath.Form), Hypermath.structOrbits '
                    '(Hypermath.f2f (Hypermath.f2f x)) x',
 'Hypermath.axComposeAssoc': 'axiom Hypermath.axComposeAssoc : ∀ (p q r : '
                             'Hypermath.DerivationPath), Hypermath.congruentPath '
                             '(Hypermath.compose p (Hypermath.compose q r)) (Hypermath.compose '
                             '(Hypermath.compose p q) r)',
 'Hypermath.axComposeIdentity': 'axiom Hypermath.axComposeIdentity : ∀ (p : '
                                'Hypermath.DerivationPath), And (Hypermath.congruentPath '
                                '(Hypermath.compose p Hypermath.pathGround) p) '
                                '(Hypermath.congruentPath (Hypermath.compose Hypermath.pathGround '
                                'p) p)',
 'Hypermath.axComposeNonempty': 'axiom Hypermath.axComposeNonempty : Hypermath.Form → '
                                'Hypermath.Form → Exists fun p => Not (Hypermath.congruentPath p '
                                'Hypermath.pathGround)',
 'Hypermath.axCoop': 'axiom Hypermath.axCoop : ∀ (a b : Hypermath.Form), Exists fun c => And '
                     '(Hypermath.Similar c a) (Hypermath.Similar c b)',
 'Hypermath.axCoopComm': 'axiom Hypermath.axCoopComm : ∀ (a b : Hypermath.Form), Exists fun ca => '
                         'Exists fun cab => And (Hypermath.Similar ca a) (And (Hypermath.Similar '
                         'ca b) (And (Hypermath.Similar cab b) (And (Hypermath.Similar cab a) '
                         '(Hypermath.Congruent ca cab))))',
 'Hypermath.axCoopIdentity': 'axiom Hypermath.axCoopIdentity : ∀ (a : Hypermath.Form), Exists fun '
                             'c => And (Hypermath.Similar c a) (Hypermath.Congruent c a)',
 'Hypermath.axDiff': 'axiom Hypermath.axDiff : ∀ (x : Hypermath.Form), Hypermath.structDistinct '
                     '(Hypermath.f2f x) Hypermath.ground',
 'Hypermath.axFormClosesLoop': 'axiom Hypermath.axFormClosesLoop : ∀ (x : Hypermath.Form), '
                               'Hypermath.HMSyntax x → Hypermath.Semantics x → '
                               'Hypermath.FormClosure x',
 'Hypermath.axGroundSelf': 'axiom Hypermath.axGroundSelf : Hypermath.structContinues '
                           'Hypermath.ground Hypermath.ground',
 'Hypermath.axGroundSemanticsAx': 'axiom Hypermath.axGroundSemanticsAx : Hypermath.Semantics '
                                  'Hypermath.ground',
 'Hypermath.axGroundSubstanceAx': 'axiom Hypermath.axGroundSubstanceAx : Hypermath.Substance '
                                  'Hypermath.ground',
 'Hypermath.axGroundSyntaxAx': 'axiom Hypermath.axGroundSyntaxAx : Hypermath.HMSyntax '
                               'Hypermath.ground',
 'Hypermath.axLimitDerives': 'axiom Hypermath.axLimitDerives : Exists fun limitPath => And '
                             '(Hypermath.Similar (Hypermath.pathStart limitPath) Hypermath.ground) '
                             '(Hypermath.Congruent (Hypermath.pathEnd limitPath) '
                             'Hypermath.ordinalLimit)',
 'Hypermath.axLimitIsLimit': 'axiom Hypermath.axLimitIsLimit : ∀ (y : Hypermath.Form), (∀ (n : '
                             'Nat), Hypermath.Derives (Nat.repeat Hypermath.f2f n '
                             'Hypermath.ground) y) → Hypermath.Derives Hypermath.ordinalLimit y',
 'Hypermath.axLimitNotFinite': 'axiom Hypermath.axLimitNotFinite : ∀ (n : Nat), Not '
                               '(Hypermath.Simulation (Nat.repeat Hypermath.f2f n '
                               'Hypermath.ground) Hypermath.ordinalLimit)',
 'Hypermath.axSemanticsRequiresSyntax': 'axiom Hypermath.axSemanticsRequiresSyntax : ∀ (x : '
                                        'Hypermath.Form), Hypermath.Semantics x → '
                                        'Hypermath.HMSyntax x',
 'Hypermath.axSeq': 'axiom Hypermath.axSeq : ∀ (a b : Hypermath.Form), Exists fun c => And '
                    '(Hypermath.Similar c a) (Hypermath.Similar c b)',
 'Hypermath.axSeqAsymm': 'axiom Hypermath.axSeqAsymm : ∀ (a b : Hypermath.Form), Not '
                         '(Hypermath.Congruent a b) → Exists fun c => Exists fun d => And '
                         '(Hypermath.Similar c a) (And (Hypermath.Similar c b) (And '
                         '(Hypermath.Similar d b) (And (Hypermath.Similar d a) (Not '
                         '(Hypermath.Congruent c d)))))',
 'Hypermath.axSeqIdentityL': 'axiom Hypermath.axSeqIdentityL : ∀ (a : Hypermath.Form), Exists fun '
                             'c => And (Hypermath.Similar c a) (Hypermath.Congruent c a)',
 'Hypermath.axSeqIdentityR': 'axiom Hypermath.axSeqIdentityR : ∀ (a : Hypermath.Form), Exists fun '
                             'c => And (Hypermath.Similar c a) (Hypermath.Congruent c a)',
 'Hypermath.axSim': 'axiom Hypermath.axSim : ∀ (x : Hypermath.Form), Hypermath.structContinues '
                    '(Hypermath.f2f x) Hypermath.ground',
 'Hypermath.axSubstanceRequiresSemantics': 'axiom Hypermath.axSubstanceRequiresSemantics : ∀ (x : '
                                           'Hypermath.Form), Hypermath.Substance x → '
                                           'Hypermath.Semantics x',
 'Hypermath.axSuccExtends': 'axiom Hypermath.axSuccExtends : ∀ (x : Hypermath.Form), And '
                            '(Hypermath.Derives x (Hypermath.ordinalSucc x)) (Not '
                            '(Hypermath.Simulation (Hypermath.ordinalSucc x) x))',
 'Hypermath.axSyntaxRequiresSubstance': 'axiom Hypermath.axSyntaxRequiresSubstance : ∀ (x : '
                                        'Hypermath.Form), Hypermath.HMSyntax x → '
                                        'Hypermath.Substance x',
 'Hypermath.closeDefinitionOpaque': 'axiom Hypermath.closeDefinitionOpaque : ∀ (n x : '
                                    'Hypermath.Form), Iff (Hypermath.Definition n x) '
                                    '(Hypermath.Derives n x)',
 'Hypermath.closeDerivesOpaque': 'axiom Hypermath.closeDerivesOpaque : ∀ (x y : Hypermath.Form), '
                                 'Iff (Hypermath.Derives x y) (Exists fun n => Hypermath.Congruent '
                                 '(Nat.repeat Hypermath.f2f n x) y)',
 'Hypermath.closeDischargeOpaque': 'axiom Hypermath.closeDischargeOpaque : ∀ (c e : '
                                   'Hypermath.Form), Iff (Hypermath.Discharge c e) '
                                   '(Hypermath.Derives e c)',
 'Hypermath.closeFormClosureOpaque': 'axiom Hypermath.closeFormClosureOpaque : ∀ (x : '
                                     'Hypermath.Form), Iff (Hypermath.FormClosure x) (And '
                                     '(Hypermath.HMSyntax x) (And (Hypermath.Substance x) '
                                     '(Hypermath.Semantics x)))',
 'Hypermath.closeSemanticsOpaque': 'axiom Hypermath.closeSemanticsOpaque : ∀ (x : Hypermath.Form), '
                                   'Iff (Hypermath.Semantics x) (Hypermath.Simulation x x)',
 'Hypermath.closeStructContinues': 'axiom Hypermath.closeStructContinues : ∀ (x : Hypermath.Form), '
                                   'Iff (Hypermath.structContinues x Hypermath.ground) '
                                   '(Hypermath.Similar x Hypermath.ground)',
 'Hypermath.closeStructDistinct': 'axiom Hypermath.closeStructDistinct : ∀ (x y : Hypermath.Form), '
                                  'Iff (Hypermath.structDistinct x y) (Not (Hypermath.Simulation x '
                                  'y))',
 'Hypermath.closeStructOrbits': 'axiom Hypermath.closeStructOrbits : ∀ (x : Hypermath.Form), Iff '
                                '(Hypermath.structOrbits (Hypermath.f2f (Hypermath.f2f x)) x) '
                                '(Hypermath.Similar (Hypermath.f2f (Hypermath.f2f x)) x)',
 'Hypermath.closeSubstanceOpaque': 'axiom Hypermath.closeSubstanceOpaque : ∀ (x : Hypermath.Form), '
                                   'Iff (Hypermath.Substance x) (Hypermath.Congruent x x)',
 'Hypermath.closeSyntaxOpaque': 'axiom Hypermath.closeSyntaxOpaque : ∀ (x : Hypermath.Form), Iff '
                                '(Hypermath.HMSyntax x) (Exists fun n => Hypermath.Similar '
                                '(Nat.repeat Hypermath.f2f n Hypermath.ground) x)',
 'Hypermath.compose': 'axiom Hypermath.compose : Hypermath.DerivationPath → '
                      'Hypermath.DerivationPath → Hypermath.DerivationPath',
 'Hypermath.congruentPath': 'axiom Hypermath.congruentPath : Hypermath.DerivationPath → '
                            'Hypermath.DerivationPath → Prop',
 'Hypermath.deriver': 'axiom Hypermath.deriver : Hypermath.Form',
 'Hypermath.f2f': 'axiom Hypermath.f2f : Hypermath.Form → Hypermath.Form',
 'Hypermath.filtrationCongSim': 'axiom Hypermath.filtrationCongSim : ∀ (x y : Hypermath.Form), '
                                'Hypermath.Congruent x y → Hypermath.Similar x y',
 'Hypermath.filtrationSimCong': 'axiom Hypermath.filtrationSimCong : ∀ (x y : Hypermath.Form), '
                                'Hypermath.Simulation x y → Hypermath.Congruent x y',
 'Hypermath.finiteApplyFromGround': 'axiom Hypermath.finiteApplyFromGround : Hypermath.Form → Prop',
 'Hypermath.ground': 'axiom Hypermath.ground : Hypermath.Form',
 'Hypermath.ordinalApply': 'axiom Hypermath.ordinalApply : Hypermath.Form → Hypermath.Form → '
                           'Hypermath.Form',
 'Hypermath.ordinalLimit': 'axiom Hypermath.ordinalLimit : Hypermath.Form',
 'Hypermath.ordinalSucc': 'axiom Hypermath.ordinalSucc : Hypermath.Form → Hypermath.Form',
 'Hypermath.pathEnd': 'axiom Hypermath.pathEnd : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.pathGround': 'axiom Hypermath.pathGround : Hypermath.DerivationPath',
 'Hypermath.pathLength': 'axiom Hypermath.pathLength : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.pathStart': 'axiom Hypermath.pathStart : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.pathStep': 'axiom Hypermath.pathStep : Hypermath.Form → Hypermath.Form → '
                       'Hypermath.DerivationPath',
 'Hypermath.pathTrace': 'axiom Hypermath.pathTrace : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.structContinues': 'axiom Hypermath.structContinues : Hypermath.Form → Hypermath.Form → '
                              'Prop',
 'Hypermath.structDistinct': 'axiom Hypermath.structDistinct : Hypermath.Form → Hypermath.Form → '
                             'Prop',
 'Hypermath.structOrbits': 'axiom Hypermath.structOrbits : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.traceLevels': 'axiom Hypermath.traceLevels : ∀ (x : Hypermath.Form), And '
                          '(Hypermath.Similar (Hypermath.f2f x) x) (And (Hypermath.Congruent '
                          '(Hypermath.f2f x) x → Hypermath.Similar (Hypermath.f2f x) x) '
                          '(Hypermath.Simulation (Hypermath.f2f x) x → Hypermath.Congruent '
                          '(Hypermath.f2f x) x))'}

TARGET_STATEMENT = 'theorem Hypermath.selfDerivation : And (Hypermath.structContinues Hypermath.ground Hypermath.ground) (And (∀ (x : Hypermath.Form), Hypermath.D x x) (And (∀ (p : Hypermath.DerivationPath), And (Hypermath.congruentPath (Hypermath.compose p Hypermath.pathGround) p) (Hypermath.congruentPath (Hypermath.compose Hypermath.pathGround p) p)) (Hypermath.Simulation (Hypermath.f2f (Hypermath.f2f Hypermath.deriver)) Hypermath.deriver)))'

AUDIT_SOURCE_SHA256 = '588dc4d324e048206b633714a14e54a087daf8f021c0752ec906cd33080b97dd'
COUNTERMODEL_SOURCE_SHA256 = 'fbd5a0c209b83e353d4d795b46b680fa82b930d1cf8ba713dd245f561b4c3f5f'
LEAN_BUILTINS = frozenset({"propext", "Classical.choice", "Quot.sound"})
