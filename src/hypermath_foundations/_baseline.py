"""Reviewed declaration identity baseline, not an assertion of consistency.

Initially captured with Lean 4.14.0 at revision db141d669491ce6b51d7fe15602c0925398f3154.
The finite-trace repair removes D from the allowance: its reviewed definitions
and constructive milestone statements are bound separately below. The remaining
67 declarations retain their original meaning. The finite ground closure is now
defined as well; the refuted universal ground-spanning statement is only a claim.
Three unconstrained ordinal-computation theorems are now retained as claims after
a full-clause model refuted them. The reporter only requests kernel observations;
it adds no assumptions.
Changes to this policy require explicit mathematical review, not regeneration
as an automatic response to a failing gate.
"""

AXIOM_DECLARATIONS = {'Hypermath.Congruent': 'axiom Hypermath.Congruent : Hypermath.Form → Hypermath.Form → Prop',
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

AUDIT_SOURCE_SHA256 = '3363bd416af4ba6588d505b34cfd935d5d253cb1cc60c36dfc15d765fe1a0130'
COUNTERMODEL_SOURCE_SHA256 = 'b822d53b244418db1c3a505332b6090d9da72bc6e0fe3ce620bd9e5c5413adc7'
LEAN_BUILTINS = frozenset({"propext", "Classical.choice", "Quot.sound"})

# Reviewed finite congruence-preserving trace construction.
DEFINITION_DECLARATIONS = {'Hypermath.D': 'def Hypermath.D : Hypermath.Form → Hypermath.Form → Prop := fun x y => Nonempty '
                '(Hypermath.DEntry x y)',
 'Hypermath.DStep': 'def Hypermath.DStep : Hypermath.Form → Hypermath.Form → Prop := fun x y => '
                    'And (Eq y (Hypermath.f2f x)) (Hypermath.Congruent y x)',
 'Hypermath.DEntry': '@[reducible] def Hypermath.DEntry : Hypermath.Form → Hypermath.Form → Type '
                     ':= fun x y => Hypermath.Trace Hypermath.DStep x y',
 'Hypermath.selfRead': 'def Hypermath.selfRead : (x : Hypermath.Form) → Hypermath.DEntry x x := '
                       'fun x => Hypermath.Trace.nil x',
 'Hypermath.dEntryStep': 'def Hypermath.dEntryStep : (x : Hypermath.Form) → Hypermath.Congruent '
                         '(Hypermath.f2f x) x → Hypermath.DEntry x (Hypermath.f2f x) := fun x h => '
                         'Hypermath.Trace.cons ⋯ (Hypermath.Trace.nil (Hypermath.f2f x))',
 'Hypermath.dEntryCompose': 'def Hypermath.dEntryCompose : {x y z : Hypermath.Form} → '
                            'Hypermath.DEntry x y → Hypermath.DEntry y z → Hypermath.DEntry x z := '
                            'fun {x y z} p q => Hypermath.Trace.compose p q',
 'Hypermath.reflexionTrace': 'def Hypermath.reflexionTrace : (x : Hypermath.Form) → '
                             'Hypermath.DEntry x x := fun x => Hypermath.selfRead x'}

PROVED_DECLARATIONS = {'Hypermath.selfReadLength': 'theorem Hypermath.selfReadLength : ∀ (x : Hypermath.Form), Eq '
                             '(Hypermath.Trace.length (Hypermath.selfRead x)) 0',
 'Hypermath.dEntryStepLength': 'theorem Hypermath.dEntryStepLength : ∀ (x : Hypermath.Form) (h : '
                               'Hypermath.Congruent (Hypermath.f2f x) x), Eq '
                               '(Hypermath.Trace.length (Hypermath.dEntryStep x h)) 1',
 'Hypermath.dEntryEndpointIteration': 'theorem Hypermath.dEntryEndpointIteration : ∀ {x y : '
                                      'Hypermath.Form} (p : Hypermath.DEntry x y), Eq (Nat.repeat '
                                      'Hypermath.f2f (Hypermath.Trace.length p) x) y',
 'Hypermath.dEntryNoSteps': 'theorem Hypermath.dEntryNoSteps : (∀ (x y : Hypermath.Form), Not '
                            '(Hypermath.DStep x y)) → ∀ {x y : Hypermath.Form} (p : '
                            'Hypermath.DEntry x y), And (Eq (Hypermath.Trace.length p) 0) (Eq x y)',
 'Hypermath.dIsReflexive': 'theorem Hypermath.dIsReflexive : ∀ (x : Hypermath.Form), Hypermath.D x '
                           'x',
 'Hypermath.dIsTransitive': 'theorem Hypermath.dIsTransitive : ∀ {x y z : Hypermath.Form}, '
                            'Hypermath.D x y → Hypermath.D y z → Hypermath.D x z',
 'Hypermath.reflexionTraceComposeIdentity': 'theorem Hypermath.reflexionTraceComposeIdentity : ∀ '
                                            '{x y : Hypermath.Form} (p : Hypermath.DEntry x y), '
                                            'And (Eq (Hypermath.dEntryCompose '
                                            '(Hypermath.reflexionTrace x) p) p) (Eq '
                                            '(Hypermath.dEntryCompose p (Hypermath.reflexionTrace '
                                            'y)) p)'}

TRACE_SOURCE_SHA256 = '82eb4b0d3cfb8a903421686eccddbbe9f9ca63abb70eb4826d4a876911b5cfac'

TRACE_CHECKS_SOURCE_SHA256 = 'f7e8168384b8f56c4a07f29ea21649c91756702a7dc9cd172b0a7ffff29329b2'

# Reviewed least finite closure and Form-valued observations.
DEFINITION_DECLARATIONS.update({'Hypermath.groundSpanningClaim': 'def Hypermath.groundSpanningClaim : Prop := ∀ (y : '
                                  'Hypermath.Form), Hypermath.D Hypermath.ground y',
 'Hypermath.finiteApplyPosition': 'def Hypermath.finiteApplyPosition : Nat → Hypermath.Form := fun '
                                  'n => Nat.repeat Hypermath.f2f n Hypermath.ground',
 'Hypermath.finiteApplyFromGround': 'def Hypermath.finiteApplyFromGround : Hypermath.Form → Prop '
                                    ':= fun x => Exists fun n => Eq (Hypermath.finiteApplyPosition '
                                    'n) x',
 'Hypermath.finiteTraceLength': 'def Hypermath.finiteTraceLength : {x y : Hypermath.Form} → '
                                'Hypermath.DEntry x y → Hypermath.Form := fun {x y} p => '
                                'Hypermath.finiteApplyPosition (Hypermath.Trace.length p)'})

PROVED_DECLARATIONS.update({'Hypermath.finiteApplyIffIteration': 'theorem Hypermath.finiteApplyIffIteration : ∀ (x : '
                                      'Hypermath.Form), Iff (Hypermath.finiteApplyFromGround x) '
                                      '(Exists fun n => Eq (Nat.repeat Hypermath.f2f n '
                                      'Hypermath.ground) x)',
 'Hypermath.finiteApplyGround': 'theorem Hypermath.finiteApplyGround : '
                                'Hypermath.finiteApplyFromGround Hypermath.ground',
 'Hypermath.finiteApplyPositionMember': 'theorem Hypermath.finiteApplyPositionMember : ∀ (n : '
                                        'Nat), Hypermath.finiteApplyFromGround '
                                        '(Hypermath.finiteApplyPosition n)',
 'Hypermath.finiteApplyClosed': 'theorem Hypermath.finiteApplyClosed : ∀ {x : Hypermath.Form}, '
                                'Hypermath.finiteApplyFromGround x → '
                                'Hypermath.finiteApplyFromGround (Hypermath.f2f x)',
 'Hypermath.finiteApplyMinimal': 'theorem Hypermath.finiteApplyMinimal : ∀ (P : Hypermath.Form → '
                                 'Prop), P Hypermath.ground → (∀ (x : Hypermath.Form), P x → P '
                                 '(Hypermath.f2f x)) → ∀ {x : Hypermath.Form}, '
                                 'Hypermath.finiteApplyFromGround x → P x',
 'Hypermath.finiteApplyIterationAdd': 'theorem Hypermath.finiteApplyIterationAdd : ∀ (m n : Nat) '
                                      '(x : Hypermath.Form), Eq (Nat.repeat Hypermath.f2f '
                                      '(HAdd.hAdd m n) x) (Nat.repeat Hypermath.f2f n (Nat.repeat '
                                      'Hypermath.f2f m x))',
 'Hypermath.finiteTraceLengthMember': 'theorem Hypermath.finiteTraceLengthMember : ∀ {x y : '
                                      'Hypermath.Form} (p : Hypermath.DEntry x y), '
                                      'Hypermath.finiteApplyFromGround '
                                      '(Hypermath.finiteTraceLength p)',
 'Hypermath.finiteTraceLengthSelfRead': 'theorem Hypermath.finiteTraceLengthSelfRead : ∀ (x : '
                                        'Hypermath.Form), Eq (Hypermath.finiteTraceLength '
                                        '(Hypermath.selfRead x)) Hypermath.ground',
 'Hypermath.finiteTraceLengthStep': 'theorem Hypermath.finiteTraceLengthStep : ∀ (x : '
                                    'Hypermath.Form) (h : Hypermath.Congruent (Hypermath.f2f x) '
                                    'x), Eq (Hypermath.finiteTraceLength (Hypermath.dEntryStep x '
                                    'h)) (Hypermath.f2f Hypermath.ground)',
 'Hypermath.finiteTraceLengthCompose': 'theorem Hypermath.finiteTraceLengthCompose : ∀ {x y z : '
                                       'Hypermath.Form} (p : Hypermath.DEntry x y) (q : '
                                       'Hypermath.DEntry y z), Eq (Hypermath.finiteTraceLength '
                                       '(Hypermath.dEntryCompose p q)) (Nat.repeat Hypermath.f2f '
                                       '(Hypermath.Trace.length q) (Hypermath.finiteTraceLength '
                                       'p))',
 'Hypermath.finiteTraceLengthExpand': 'theorem Hypermath.finiteTraceLengthExpand : ∀ {x y : '
                                      'Hypermath.Form} (e : Hypermath.TraceExpr Hypermath.DStep x '
                                      'y), Eq (Hypermath.finiteTraceLength e.expand) '
                                      '(Hypermath.finiteApplyPosition e.length)',
 'Hypermath.finiteTraceLengthExpandSeq': 'theorem Hypermath.finiteTraceLengthExpandSeq : ∀ {x y z '
                                         ': Hypermath.Form} (p : Hypermath.TraceExpr '
                                         'Hypermath.DStep x y) (q : Hypermath.TraceExpr '
                                         'Hypermath.DStep y z), Eq (Hypermath.finiteTraceLength '
                                         '(p.seq q).expand) (Nat.repeat Hypermath.f2f q.length '
                                         '(Hypermath.finiteApplyPosition p.length))',
 'Hypermath.dEntryFromGroundFinite': 'theorem Hypermath.dEntryFromGroundFinite : ∀ {y : '
                                     'Hypermath.Form}, Hypermath.DEntry Hypermath.ground y → '
                                     'Hypermath.finiteApplyFromGround y',
 'Hypermath.finiteApplyPositionSimulation': 'theorem Hypermath.finiteApplyPositionSimulation : ∀ '
                                            '(n : Nat), Hypermath.Simulation '
                                            '(Hypermath.finiteApplyPosition n) '
                                            '(Hypermath.finiteApplyPosition n)',
 'Hypermath.finiteApplyLimitExcluded': 'theorem Hypermath.finiteApplyLimitExcluded : Not '
                                       '(Hypermath.finiteApplyFromGround Hypermath.ordinalLimit)',
 'Hypermath.ordinalLimitNotInD': 'theorem Hypermath.ordinalLimitNotInD : Not (Hypermath.D '
                                 'Hypermath.ground Hypermath.ordinalLimit)',
 'Hypermath.notGroundSpanningClaim': 'theorem Hypermath.notGroundSpanningClaim : Not '
                                     'Hypermath.groundSpanningClaim'})

# Exact dependencies distinguish pure constructions from source-relative refutations.
PROVED_DEPENDENCIES = {'Hypermath.selfReadLength': ('Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'),
 'Hypermath.dEntryStepLength': ('Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'),
 'Hypermath.dEntryEndpointIteration': ('Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'),
 'Hypermath.dEntryNoSteps': ('Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'),
 'Hypermath.dIsReflexive': ('Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'),
 'Hypermath.dIsTransitive': ('Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.f2f'),
 'Hypermath.reflexionTraceComposeIdentity': ('Hypermath.Congruent',
                                             'Hypermath.Form',
                                             'Hypermath.f2f'),
 'Hypermath.finiteApplyIffIteration': ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
 'Hypermath.finiteApplyGround': ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
 'Hypermath.finiteApplyPositionMember': ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
 'Hypermath.finiteApplyClosed': ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
 'Hypermath.finiteApplyMinimal': ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
 'Hypermath.finiteApplyIterationAdd': ('Hypermath.Form', 'Hypermath.f2f'),
 'Hypermath.finiteTraceLengthMember': ('Hypermath.Congruent',
                                       'Hypermath.Form',
                                       'Hypermath.f2f',
                                       'Hypermath.ground'),
 'Hypermath.finiteTraceLengthSelfRead': ('Hypermath.Congruent',
                                         'Hypermath.Form',
                                         'Hypermath.f2f',
                                         'Hypermath.ground'),
 'Hypermath.finiteTraceLengthStep': ('Hypermath.Congruent',
                                     'Hypermath.Form',
                                     'Hypermath.f2f',
                                     'Hypermath.ground'),
 'Hypermath.finiteTraceLengthCompose': ('Hypermath.Congruent',
                                        'Hypermath.Form',
                                        'Hypermath.f2f',
                                        'Hypermath.ground'),
 'Hypermath.finiteTraceLengthExpand': ('Hypermath.Congruent',
                                       'Hypermath.Form',
                                       'Hypermath.f2f',
                                       'Hypermath.ground'),
 'Hypermath.finiteTraceLengthExpandSeq': ('Hypermath.Congruent',
                                          'Hypermath.Form',
                                          'Hypermath.f2f',
                                          'Hypermath.ground'),
 'Hypermath.dEntryFromGroundFinite': ('Hypermath.Congruent',
                                      'Hypermath.Form',
                                      'Hypermath.f2f',
                                      'Hypermath.ground'),
 'Hypermath.finiteApplyPositionSimulation': ('Hypermath.Congruent',
                                             'Hypermath.Form',
                                             'Hypermath.HMSyntax',
                                             'Hypermath.Semantics',
                                             'Hypermath.Similar',
                                             'Hypermath.Simulation',
                                             'Hypermath.axSubstanceRequiresSemantics',
                                             'Hypermath.axSyntaxRequiresSubstance',
                                             'Hypermath.closeSemanticsOpaque',
                                             'Hypermath.closeSyntaxOpaque',
                                             'Hypermath.f2f',
                                             'Hypermath.ground',
                                             'Hypermath.traceLevels'),
 'Hypermath.finiteApplyLimitExcluded': ('Hypermath.Congruent',
                                        'Hypermath.Form',
                                        'Hypermath.HMSyntax',
                                        'Hypermath.Semantics',
                                        'Hypermath.Similar',
                                        'Hypermath.Simulation',
                                        'Hypermath.axLimitNotFinite',
                                        'Hypermath.axSubstanceRequiresSemantics',
                                        'Hypermath.axSyntaxRequiresSubstance',
                                        'Hypermath.closeSemanticsOpaque',
                                        'Hypermath.closeSyntaxOpaque',
                                        'Hypermath.f2f',
                                        'Hypermath.ground',
                                        'Hypermath.ordinalLimit',
                                        'Hypermath.traceLevels'),
 'Hypermath.ordinalLimitNotInD': ('Hypermath.Congruent',
                                  'Hypermath.Form',
                                  'Hypermath.HMSyntax',
                                  'Hypermath.Semantics',
                                  'Hypermath.Similar',
                                  'Hypermath.Simulation',
                                  'Hypermath.axLimitNotFinite',
                                  'Hypermath.axSubstanceRequiresSemantics',
                                  'Hypermath.axSyntaxRequiresSubstance',
                                  'Hypermath.closeSemanticsOpaque',
                                  'Hypermath.closeSyntaxOpaque',
                                  'Hypermath.f2f',
                                  'Hypermath.ground',
                                  'Hypermath.ordinalLimit',
                                  'Hypermath.traceLevels'),
 'Hypermath.notGroundSpanningClaim': ('Hypermath.Congruent',
                                      'Hypermath.Form',
                                      'Hypermath.HMSyntax',
                                      'Hypermath.Semantics',
                                      'Hypermath.Similar',
                                      'Hypermath.Simulation',
                                      'Hypermath.axLimitNotFinite',
                                      'Hypermath.axSubstanceRequiresSemantics',
                                      'Hypermath.axSyntaxRequiresSubstance',
                                      'Hypermath.closeSemanticsOpaque',
                                      'Hypermath.closeSyntaxOpaque',
                                      'Hypermath.f2f',
                                      'Hypermath.ground',
                                      'Hypermath.ordinalLimit',
                                      'Hypermath.traceLevels')}

OBSERVATION_SOURCE_SHA256 = '528fc4fe96beeca0e4b06783652348f66c5bc273f47446230cf684821a78413b'

OBSERVATION_CHECKS_SOURCE_SHA256 = '0cb28bb33dd2711c764732d41536f331d150b27b7854f7b96580608a09d2ffcd'

FULL_MODEL_SOURCE_SHA256 = '4640c5facb2d6c96a4aca11ca0f421e0be05aabe63838f78ecd9d0d50fd01bdb'

# Reviewed finite-action criterion and retained ordinal computation claims.
DEFINITION_DECLARATIONS.update({
    'Hypermath.ordinalZeroIdentityClaim':
        'def Hypermath.ordinalZeroIdentityClaim : Prop := ∀ (x : Hypermath.Form), '
        'Hypermath.Congruent (Hypermath.ordinalApply Hypermath.ground x) x',
    'Hypermath.ordinalSuccAppliesClaim':
        'def Hypermath.ordinalSuccAppliesClaim : Prop := ∀ (p x : Hypermath.Form), '
        'Hypermath.Congruent (Hypermath.ordinalApply (Hypermath.ordinalSucc p) x) '
        '(Hypermath.f2f (Hypermath.ordinalApply p x))',
    'Hypermath.pathLengthArithmeticClaim':
        'def Hypermath.pathLengthArithmeticClaim : Prop := ∀ (p q : '
        'Hypermath.DerivationPath), Hypermath.Congruent (Hypermath.pathLength '
        '(Hypermath.compose p q)) (Hypermath.ordinalApply (Hypermath.pathLength q) '
        '(Hypermath.pathLength p))',
    'Hypermath.FiniteNumeralEq':
        'def Hypermath.FiniteNumeralEq : Nat → Nat → Prop := fun m n => Eq '
        '(Hypermath.finiteApplyPosition m) (Hypermath.finiteApplyPosition n)',
    'Hypermath.FiniteActionCompatible':
        'def Hypermath.FiniteActionCompatible : Prop := ∀ (m n : Nat), '
        'Hypermath.FiniteNumeralEq m n → ∀ (x : Hypermath.Form), Eq '
        '(Nat.repeat Hypermath.f2f m x) (Nat.repeat Hypermath.f2f n x)',
    'Hypermath.ExactFiniteAction':
        'def Hypermath.ExactFiniteAction : (Hypermath.Form → Hypermath.Form → '
        'Hypermath.Form) → Prop := fun action => ∀ (n : Nat) (x : Hypermath.Form), '
        'Eq (action (Hypermath.finiteApplyPosition n) x) (Nat.repeat Hypermath.f2f n x)',
    'Hypermath.hostFiniteAction':
        'def Hypermath.hostFiniteAction : Hypermath.Form → Hypermath.Form → '
        'Hypermath.Form := Hypermath.FiniteAction.chosenAction Hypermath.f2f Hypermath.ground',
    'Hypermath.FiniteOrbit':
        'def Hypermath.FiniteOrbit : Type := Subtype fun x => '
        'Hypermath.finiteApplyFromGround x',
    'Hypermath.finiteOrbitEncode':
        'def Hypermath.finiteOrbitEncode : Nat → Hypermath.FiniteOrbit := '
        'fun n => ⟨Hypermath.finiteApplyPosition n, ⋯⟩',
    'Hypermath.finiteOrbitDecode':
        'def Hypermath.finiteOrbitDecode : Hypermath.FiniteOrbit → Nat := '
        'fun x => Classical.choose ⋯',
    'Hypermath.FiniteOrbitInjective':
        'def Hypermath.FiniteOrbitInjective : Prop := ∀ {m n : Nat}, Eq '
        '(Hypermath.finiteApplyPosition m) (Hypermath.finiteApplyPosition n) → Eq m n',
})

PROVED_DECLARATIONS.update({
    'Hypermath.finiteNumeralEq_action_on_finite_orbit':
        'theorem Hypermath.finiteNumeralEq_action_on_finite_orbit : ∀ {m n : Nat}, '
        'Hypermath.FiniteNumeralEq m n → ∀ (k : Nat), Eq (Nat.repeat Hypermath.f2f m '
        '(Hypermath.finiteApplyPosition k)) (Nat.repeat Hypermath.f2f n '
        '(Hypermath.finiteApplyPosition k))',
    'Hypermath.finiteNumeralEq_add':
        'theorem Hypermath.finiteNumeralEq_add : ∀ {m n p q : Nat}, '
        'Hypermath.FiniteNumeralEq m n → Hypermath.FiniteNumeralEq p q → '
        'Hypermath.FiniteNumeralEq (HAdd.hAdd m p) (HAdd.hAdd n q)',
    'Hypermath.finiteNumeralEq_mul':
        'theorem Hypermath.finiteNumeralEq_mul : ∀ {m n p q : Nat}, '
        'Hypermath.FiniteNumeralEq m n → Hypermath.FiniteNumeralEq p q → '
        'Hypermath.FiniteNumeralEq (HMul.hMul m p) (HMul.hMul n q)',
    'Hypermath.finiteOrbitEncode_surjective':
        'theorem Hypermath.finiteOrbitEncode_surjective : ∀ (x : '
        'Hypermath.FiniteOrbit), Exists fun n => Eq (Hypermath.finiteOrbitEncode n) x',
    'Hypermath.finiteOrbitDecode_spec':
        'theorem Hypermath.finiteOrbitDecode_spec : ∀ (x : Hypermath.FiniteOrbit), '
        'Eq (Hypermath.finiteApplyPosition (Hypermath.finiteOrbitDecode x)) x.val',
    'Hypermath.finiteOrbitEquivalence_laws':
        'theorem Hypermath.finiteOrbitEquivalence_laws : '
        'Hypermath.FiniteOrbitInjective → And (∀ (n : Nat), Eq '
        '(Hypermath.finiteOrbitDecode (Hypermath.finiteOrbitEncode n)) n) '
        '(∀ (x : Hypermath.FiniteOrbit), Eq (Hypermath.finiteOrbitEncode '
        '(Hypermath.finiteOrbitDecode x)) x)',
    'Hypermath.finiteOrbitInjective_implies_actionCompatible':
        'theorem Hypermath.finiteOrbitInjective_implies_actionCompatible : '
        'Hypermath.FiniteOrbitInjective → Hypermath.FiniteActionCompatible',
    'Hypermath.exactFiniteAction_implies_compatible':
        'theorem Hypermath.exactFiniteAction_implies_compatible : ∀ {action : '
        'Hypermath.Form → Hypermath.Form → Hypermath.Form}, '
        'Hypermath.ExactFiniteAction action → Hypermath.FiniteActionCompatible',
    'Hypermath.hostFiniteAction_exact':
        'theorem Hypermath.hostFiniteAction_exact : Hypermath.FiniteActionCompatible → '
        'Hypermath.ExactFiniteAction Hypermath.hostFiniteAction',
    'Hypermath.finiteActionCompatible_iff_exists_exact':
        'theorem Hypermath.finiteActionCompatible_iff_exists_exact : Iff '
        'Hypermath.FiniteActionCompatible (Exists fun action => '
        'Hypermath.ExactFiniteAction action)',
    'Hypermath.finiteNumeralEqualityExact_iff_injective':
        'theorem Hypermath.finiteNumeralEqualityExact_iff_injective : Iff '
        '(Hypermath.Observation.Compatible Hypermath.finiteApplyPosition '
        'Hypermath.Observation.equalityQuery) Hypermath.FiniteOrbitInjective',
})

PROVED_DEPENDENCIES.update({
    'Hypermath.finiteNumeralEq_action_on_finite_orbit':
        ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.finiteNumeralEq_add':
        ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.finiteNumeralEq_mul':
        ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.finiteOrbitEncode_surjective':
        ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.finiteOrbitDecode_spec':
        ('Classical.choice', 'Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.finiteOrbitEquivalence_laws':
        ('Classical.choice', 'Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.finiteOrbitInjective_implies_actionCompatible':
        ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.exactFiniteAction_implies_compatible':
        ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
    'Hypermath.hostFiniteAction_exact':
        ('Classical.choice', 'Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground',
         'Quot.sound', 'propext'),
    'Hypermath.finiteActionCompatible_iff_exists_exact':
        ('Classical.choice', 'Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground',
         'Quot.sound', 'propext'),
    'Hypermath.finiteNumeralEqualityExact_iff_injective':
        ('Hypermath.Form', 'Hypermath.f2f', 'Hypermath.ground'),
})

FINITE_ACTION_SOURCE_SHA256 = 'e5f5a0ef525088b1bf87f0669c7e0fecb6ab9a4e5fcda432a13825f8d96e609c'

ACTION_COUNTERMODEL_SOURCE_SHA256 = '063d90e0624efc28e7c088a9b9b132ec5ababec734b6cc787b2b413b986b4936'

# Reviewed finite syntax of L0 Section I and instances of exactly the four
# Section III rules. This checker does not assert semantic Form injectivity.
GROUND_SYNTAX_SOURCE_SHA256 = '4561060a14c243bed7c877ac52e9e966ce9a6b19021e3e2e1fda36265560a133'
GROUND_SYNTAX_CHECKS_SOURCE_SHA256 = 'b7b9f98de31b6ae57f6d86b68c4f603d6104e6d90e223e7d805ffb94216bcdbe'

GROUND_DERIVATION_SOURCE_SHA256 = '1b955b15be275738203dd4eda567e6915d848dca5ebbd8214d7d4b98fa22cc59'
GROUND_DERIVATION_CHECKS_SOURCE_SHA256 = 'c44607ae44c1556f86da8d7430d24a03b617bbe26d3a33a002f3d85a4cc04a9a'

# Packed tree and composed record encoding, with explicit host dependencies.
GROUND_CODE_SOURCE_SHA256 = 'c6c6d161c336b9b6a45fcddff51f0cc07b2478e3c44c67f55d4c0972753d40e3'
RECORD_ENCODING_SOURCE_SHA256 = '1300264388fe739c2d4a0648295696f3cae284861b56286e0fac28885642f8a0'
RECORD_ENCODING_CHECKS_SOURCE_SHA256 = '803f0ad6fcb2a05780587a1258809bda97746a8453384df5c053779024c11829'
