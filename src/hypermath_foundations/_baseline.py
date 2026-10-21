"""Reviewed declaration identity baseline, not an assertion of consistency.

Initially captured with Lean 4.14.0 at revision db141d669491ce6b51d7fe15602c0925398f3154.
The finite-trace repair removes D from the allowance: its reviewed definitions
and constructive milestone statements are bound separately below. The transfinite
separation removes seven more: the ordinal limit, successor and application, and
the four laws over them, are now projections of a single assumed structure,
Hypermath.ordinatics, supplied by the ordinatics package. Those 61
declarations retain their original meaning; five reviewed closing clauses were
added later, giving 66. The finite ground closure is now
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
 'Hypermath.axBox': 'axiom Hypermath.axBox : ∀ (x : Hypermath.Form), Hypermath.structOrbits (Hypermath.f2f (Hypermath.f2f x)) x',
 'Hypermath.axComposeAssoc': 'axiom Hypermath.axComposeAssoc : ∀ (p q r : Hypermath.DerivationPath), Hypermath.congruentPath (Hypermath.compose p (Hypermath.compose q r)) (Hypermath.compose (Hypermath.compose p q) r)',
 'Hypermath.axComposeIdentity': 'axiom Hypermath.axComposeIdentity : ∀ (p : Hypermath.DerivationPath), And (Hypermath.congruentPath (Hypermath.compose p Hypermath.pathGround) p) (Hypermath.congruentPath (Hypermath.compose Hypermath.pathGround p) p)',
 'Hypermath.axComposeNonempty': 'axiom Hypermath.axComposeNonempty : Hypermath.Form → Hypermath.Form → Exists fun p => Not (Hypermath.congruentPath p Hypermath.pathGround)',
 'Hypermath.axCongruentPathSymm': 'axiom Hypermath.axCongruentPathSymm : ∀ (p q : Hypermath.DerivationPath), Hypermath.congruentPath p q → Hypermath.congruentPath q p',
 'Hypermath.axCongruentTrans': 'axiom Hypermath.axCongruentTrans : ∀ (x y z : Hypermath.Form), Hypermath.Congruent x y → Hypermath.Congruent y z → Hypermath.Congruent x z',
 'Hypermath.axCoop': 'axiom Hypermath.axCoop : ∀ (a b : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Similar c b)',
 'Hypermath.axCoopComm': 'axiom Hypermath.axCoopComm : ∀ (a b : Hypermath.Form), Exists fun ca => Exists fun cab => And (Hypermath.Similar ca a) (And (Hypermath.Similar ca b) (And (Hypermath.Similar cab b) (And (Hypermath.Similar cab a) (Hypermath.Congruent ca cab))))',
 'Hypermath.axCoopIdentity': 'axiom Hypermath.axCoopIdentity : ∀ (a : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Congruent c a)',
 'Hypermath.axDiff': 'axiom Hypermath.axDiff : ∀ (x : Hypermath.Form), Hypermath.structDistinct (Hypermath.f2f x) Hypermath.ground',
 'Hypermath.axDiffCongruent': 'axiom Hypermath.axDiffCongruent : ∀ (x : Hypermath.Form), Not (Hypermath.Congruent (Hypermath.f2f x) Hypermath.ground)',
 'Hypermath.axFormClosesLoop': 'axiom Hypermath.axFormClosesLoop : ∀ (x : Hypermath.Form), Hypermath.HMSyntax x → Hypermath.Semantics x → Hypermath.FormClosure x',
 'Hypermath.axGroundSelf': 'axiom Hypermath.axGroundSelf : Hypermath.structContinues Hypermath.ground Hypermath.ground',
 'Hypermath.axGroundSemanticsAx': 'axiom Hypermath.axGroundSemanticsAx : Hypermath.Semantics Hypermath.ground',
 'Hypermath.axGroundSubstanceAx': 'axiom Hypermath.axGroundSubstanceAx : Hypermath.Substance Hypermath.ground',
 'Hypermath.axGroundSyntaxAx': 'axiom Hypermath.axGroundSyntaxAx : Hypermath.HMSyntax Hypermath.ground',
 'Hypermath.axSemanticsRequiresSyntax': 'axiom Hypermath.axSemanticsRequiresSyntax : ∀ (x : Hypermath.Form), Hypermath.Semantics x → Hypermath.HMSyntax x',
 'Hypermath.axSeq': 'axiom Hypermath.axSeq : ∀ (a b : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Similar c b)',
 'Hypermath.axSeqAsymm': 'axiom Hypermath.axSeqAsymm : ∀ (a b : Hypermath.Form), Not (Hypermath.Congruent a b) → Exists fun c => Exists fun d => And (Hypermath.Similar c a) (And (Hypermath.Similar c b) (And (Hypermath.Similar d b) (And (Hypermath.Similar d a) (Not (Hypermath.Congruent c d)))))',
 'Hypermath.axSeqIdentityL': 'axiom Hypermath.axSeqIdentityL : ∀ (a : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Congruent c a)',
 'Hypermath.axSeqIdentityR': 'axiom Hypermath.axSeqIdentityR : ∀ (a : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Congruent c a)',
 'Hypermath.axSim': 'axiom Hypermath.axSim : ∀ (x : Hypermath.Form), Hypermath.structContinues (Hypermath.f2f x) Hypermath.ground',
 'Hypermath.axSimilarRefl': 'axiom Hypermath.axSimilarRefl : ∀ (x : Hypermath.Form), Hypermath.Similar x x',
 'Hypermath.axSimilarSymm': 'axiom Hypermath.axSimilarSymm : ∀ (x y : Hypermath.Form), Hypermath.Similar x y → Hypermath.Similar y x',
 'Hypermath.axSubstanceRequiresSemantics': 'axiom Hypermath.axSubstanceRequiresSemantics : ∀ (x : Hypermath.Form), Hypermath.Substance x → Hypermath.Semantics x',
 'Hypermath.axSyntaxRequiresSubstance': 'axiom Hypermath.axSyntaxRequiresSubstance : ∀ (x : Hypermath.Form), Hypermath.HMSyntax x → Hypermath.Substance x',
 'Hypermath.closeDefinitionOpaque': 'axiom Hypermath.closeDefinitionOpaque : ∀ (n x : Hypermath.Form), Iff (Hypermath.Definition n x) (Hypermath.Derives n x)',
 'Hypermath.closeDerivesOpaque': 'axiom Hypermath.closeDerivesOpaque : ∀ (x y : Hypermath.Form), Iff (Hypermath.Derives x y) (Exists fun n => Hypermath.Congruent (Nat.repeat Hypermath.f2f n x) y)',
 'Hypermath.closeDischargeOpaque': 'axiom Hypermath.closeDischargeOpaque : ∀ (c e : Hypermath.Form), Iff (Hypermath.Discharge c e) (Hypermath.Derives e c)',
 'Hypermath.closeFormClosureOpaque': 'axiom Hypermath.closeFormClosureOpaque : ∀ (x : Hypermath.Form), Iff (Hypermath.FormClosure x) (And (Hypermath.HMSyntax x) (And (Hypermath.Substance x) (Hypermath.Semantics x)))',
 'Hypermath.closeSemanticsOpaque': 'axiom Hypermath.closeSemanticsOpaque : ∀ (x : Hypermath.Form), Iff (Hypermath.Semantics x) (Hypermath.Simulation x x)',
 'Hypermath.closeStructContinues': 'axiom Hypermath.closeStructContinues : ∀ (x : Hypermath.Form), Iff (Hypermath.structContinues x Hypermath.ground) (Hypermath.Similar x Hypermath.ground)',
 'Hypermath.closeStructDistinct': 'axiom Hypermath.closeStructDistinct : ∀ (x y : Hypermath.Form), Iff (Hypermath.structDistinct x y) (Not (Hypermath.Simulation x y))',
 'Hypermath.closeStructOrbits': 'axiom Hypermath.closeStructOrbits : ∀ (x : Hypermath.Form), Iff (Hypermath.structOrbits (Hypermath.f2f (Hypermath.f2f x)) x) (Hypermath.Similar (Hypermath.f2f (Hypermath.f2f x)) x)',
 'Hypermath.closeSubstanceOpaque': 'axiom Hypermath.closeSubstanceOpaque : ∀ (x : Hypermath.Form), Iff (Hypermath.Substance x) (Hypermath.Congruent x x)',
 'Hypermath.closeSyntaxOpaque': 'axiom Hypermath.closeSyntaxOpaque : ∀ (x : Hypermath.Form), Iff (Hypermath.HMSyntax x) (Exists fun n => Hypermath.Similar (Nat.repeat Hypermath.f2f n Hypermath.ground) x)',
 'Hypermath.compose': 'axiom Hypermath.compose : Hypermath.DerivationPath → Hypermath.DerivationPath → Hypermath.DerivationPath',
 'Hypermath.congruentPath': 'axiom Hypermath.congruentPath : Hypermath.DerivationPath → Hypermath.DerivationPath → Prop',
 'Hypermath.deriver': 'axiom Hypermath.deriver : Hypermath.Form',
 'Hypermath.f2f': 'axiom Hypermath.f2f : Hypermath.Form → Hypermath.Form',
 'Hypermath.filtrationCongSim': 'axiom Hypermath.filtrationCongSim : ∀ (x y : Hypermath.Form), Hypermath.Congruent x y → Hypermath.Similar x y',
 'Hypermath.filtrationSimCong': 'axiom Hypermath.filtrationSimCong : ∀ (x y : Hypermath.Form), Hypermath.Simulation x y → Hypermath.Congruent x y',
 'Hypermath.ground': 'axiom Hypermath.ground : Hypermath.Form',
 'Hypermath.ordinatics': 'axiom Hypermath.ordinatics : Ordinatics.Transfinite Hypermath.ground Hypermath.f2f Hypermath.Similar Hypermath.Congruent Hypermath.Simulation Hypermath.Derives Hypermath.pathStart Hypermath.pathEnd Hypermath.deriver',
 'Hypermath.pathEnd': 'axiom Hypermath.pathEnd : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.pathGround': 'axiom Hypermath.pathGround : Hypermath.DerivationPath',
 'Hypermath.pathLength': 'axiom Hypermath.pathLength : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.pathStart': 'axiom Hypermath.pathStart : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.pathStep': 'axiom Hypermath.pathStep : Hypermath.Form → Hypermath.Form → Hypermath.DerivationPath',
 'Hypermath.pathTrace': 'axiom Hypermath.pathTrace : Hypermath.DerivationPath → Hypermath.Form',
 'Hypermath.structContinues': 'axiom Hypermath.structContinues : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.structDistinct': 'axiom Hypermath.structDistinct : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.structOrbits': 'axiom Hypermath.structOrbits : Hypermath.Form → Hypermath.Form → Prop',
 'Hypermath.traceLevels': 'axiom Hypermath.traceLevels : ∀ (x : Hypermath.Form), And (Hypermath.Similar (Hypermath.f2f x) x) (And (Hypermath.Congruent (Hypermath.f2f x) x → Hypermath.Similar (Hypermath.f2f x) x) (Hypermath.Simulation (Hypermath.f2f x) x → Hypermath.Congruent (Hypermath.f2f x) x))'}

TARGET_STATEMENT = 'theorem Hypermath.selfDerivation : And (Hypermath.structContinues Hypermath.ground Hypermath.ground) (And (∀ (x : Hypermath.Form), Hypermath.D x x) (And (∀ (p : Hypermath.DerivationPath), And (Hypermath.congruentPath (Hypermath.compose p Hypermath.pathGround) p) (Hypermath.congruentPath (Hypermath.compose Hypermath.pathGround p) p)) (Hypermath.Simulation (Hypermath.f2f (Hypermath.f2f Hypermath.deriver)) Hypermath.deriver)))'

# The definition retains exactly the closed proposition above. Its successful
# elaboration is not a proof, and the strict gate still requires a theorem.
TARGET_CLAIM = TARGET_STATEMENT.replace(
    'theorem Hypermath.selfDerivation : ', 'def Hypermath.selfDerivation : Prop := ', 1)

AUDIT_SOURCE_SHA256 = '13388378b5a8535f7833cee44b1ee83ccaab550c786a5dc8c7c2683e663a215e'
COUNTERMODEL_SOURCE_SHA256 = 'e436ac7192f3486abc2498439a54a9136de51b2fb6dd2cd9528274b385a00799'
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

TRACE_SOURCE_SHA256 = 'd325a9c8073e2c8a6689fe2e5abff3465eea03d71b9505da027b4bba0d560b28'

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

FULL_MODEL_SOURCE_SHA256 = 'f40944a53d61caed8801bf94310e073471a1557ed773aa77d1f3aed331e27b1f'

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

ACTION_COUNTERMODEL_SOURCE_SHA256 = '8600aae110c9505fecab54a8882f17db6bd62ef0fcaf9cd528b3f88fd8a3007e'
TARGET_AT_LIMIT_SOURCE_SHA256 = '0a6cdaf30946b82fb7b7e2dcd8cbb7d9e982b0812a5e34ddb0725e02e1a7b514'

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
RECORD_MACHINE_SOURCE_SHA256 = 'ca5dfb31a584dfac8aae7641e3f752384044f26ac8c614d10951f23c5f97432b'
RECORD_MACHINE_CHECKS_SOURCE_SHA256 = 'a5c9ed88270482d1893983076bf836fb9f7df9375e712ef1c16bc9be1d8d4fc8'

# Retained claims and conditional assembly. None proves the cycle itself.
DEFINITION_DECLARATIONS.update({
    'Hypermath.driverCycleClaim':
        'def Hypermath.driverCycleClaim : Prop := Hypermath.Simulation '
        '(Hypermath.f2f (Hypermath.f2f Hypermath.deriver)) Hypermath.deriver',
    'Hypermath.simulationPairExistsClaim':
        'def Hypermath.simulationPairExistsClaim : Prop := Exists fun x => '
        'Exists fun y => And (Hypermath.Similar x y) '
        '(And (Hypermath.Simulation x y) (Not (Eq x y)))',
})
PROVED_DECLARATIONS.update({
    'Hypermath.driverInDAtSimulationOfCycle':
        'theorem Hypermath.driverInDAtSimulationOfCycle : Hypermath.driverCycleClaim → '
        'And (Hypermath.D Hypermath.deriver Hypermath.deriver) '
        '(Hypermath.Simulation (Hypermath.f2f (Hypermath.f2f Hypermath.deriver)) Hypermath.deriver)',
    'Hypermath.selfDerivationOfCycle':
        'theorem Hypermath.selfDerivationOfCycle : Hypermath.driverCycleClaim → Hypermath.selfDerivation',
    'Hypermath.selfDerivation_iff_driverCycleClaim':
        'theorem Hypermath.selfDerivation_iff_driverCycleClaim : '
        'Iff Hypermath.selfDerivation Hypermath.driverCycleClaim',
})
PROVED_DEPENDENCIES.update({
    'Hypermath.driverInDAtSimulationOfCycle':
        ('Hypermath.Congruent', 'Hypermath.Form', 'Hypermath.Simulation',
         'Hypermath.deriver', 'Hypermath.f2f'),
    **{name: ('Hypermath.Congruent', 'Hypermath.DerivationPath', 'Hypermath.Form',
              'Hypermath.Simulation', 'Hypermath.axComposeIdentity', 'Hypermath.axGroundSelf',
              'Hypermath.compose', 'Hypermath.congruentPath', 'Hypermath.deriver',
              'Hypermath.f2f', 'Hypermath.ground', 'Hypermath.pathGround', 'Hypermath.structContinues')
       for name in ('Hypermath.selfDerivationOfCycle', 'Hypermath.selfDerivation_iff_driverCycleClaim')},
})

# Source-cycle witnesses: exact edges, length, and the explicit successor premise.
DEFINITION_DECLARATIONS.update({'Hypermath.SimulationStep': 'def Hypermath.SimulationStep : Hypermath.Form → Hypermath.Form → '
                             'Prop := fun x y => And (Eq y (Hypermath.f2f x)) '
                             '(Hypermath.Simulation y x)',
 'Hypermath.SimulationEntry': '@[reducible] def Hypermath.SimulationEntry : Hypermath.Form → '
                              'Hypermath.Form → Type := fun x y => Hypermath.Trace '
                              'Hypermath.SimulationStep x y',
 'Hypermath.simulationEntryToDEntry': 'def Hypermath.simulationEntryToDEntry : {x y : '
                                      'Hypermath.Form} → Hypermath.SimulationEntry x y → '
                                      'Hypermath.DEntry x y := fun {x y} path => '
                                      'Hypermath.Trace.map id '
                                      '(@Hypermath.simulationEntryToDEntry.proof_1) path',
 'Hypermath.DriverCycleWitness': 'structure Hypermath.DriverCycleWitness : Type number of '
                                 'parameters: 0 constructor: Hypermath.DriverCycleWitness.mk : '
                                 '(path : Hypermath.SimulationEntry Hypermath.deriver '
                                 '(Hypermath.f2f (Hypermath.f2f Hypermath.deriver))) → Eq '
                                 '(Hypermath.Trace.length path) 2 → Hypermath.driverCycleClaim → '
                                 'Hypermath.DriverCycleWitness fields: path : '
                                 'Hypermath.SimulationEntry Hypermath.deriver (Hypermath.f2f '
                                 '(Hypermath.f2f Hypermath.deriver)) length_two : Eq '
                                 '(Hypermath.Trace.length self.path) 2 closes : '
                                 'Hypermath.driverCycleClaim',
 'Hypermath.driverCycleWitnessOfSteps': 'def Hypermath.driverCycleWitnessOfSteps : '
                                        'Hypermath.Simulation (Hypermath.f2f Hypermath.deriver) '
                                        'Hypermath.deriver → Hypermath.Simulation (Hypermath.f2f '
                                        '(Hypermath.f2f Hypermath.deriver)) (Hypermath.f2f '
                                        'Hypermath.deriver) → Hypermath.driverCycleClaim → '
                                        'Hypermath.DriverCycleWitness := fun first second closes '
                                        '=> { path := Hypermath.Trace.cons ⋯ (Hypermath.Trace.cons '
                                        '⋯ (Hypermath.Trace.nil (Hypermath.f2f (Hypermath.f2f '
                                        'Hypermath.deriver)))), length_two := ⋯, closes := closes '
                                        '}',
 'Hypermath.SuccessorAgreement':
     'def Hypermath.SuccessorAgreement : Prop := ∀ (x : Hypermath.Form), Eq (Hypermath.ordinalSucc x) (Hypermath.f2f x)',
 'Hypermath.SimulationTransitive':
     'def Hypermath.SimulationTransitive : Prop := ∀ (x y z : Hypermath.Form), Hypermath.Simulation x y → Hypermath.Simulation y z → Hypermath.Simulation x z',
 'Hypermath.FiniteSuccessorAgreement': 'def Hypermath.FiniteSuccessorAgreement : Prop := ∀ (n : '
                                       'Nat), Eq (Hypermath.ordinalSucc '
                                       '(Hypermath.finiteApplyPosition n)) '
                                       '(Hypermath.finiteApplyPosition (HAdd.hAdd n 1))'})
PROVED_DECLARATIONS.update({'Hypermath.simulationEntryToDEntry_length': 'theorem Hypermath.simulationEntryToDEntry_length : ∀ '
                                             '{x y : Hypermath.Form} (path : '
                                             'Hypermath.SimulationEntry x y), Eq '
                                             '(Hypermath.Trace.length '
                                             '(Hypermath.simulationEntryToDEntry path)) '
                                             '(Hypermath.Trace.length path)',
 'Hypermath.selfDerivationOfWitness': 'theorem Hypermath.selfDerivationOfWitness : '
                                      'Hypermath.DriverCycleWitness → Hypermath.selfDerivation',
 'Hypermath.witness_has_two_D_steps': 'theorem Hypermath.witness_has_two_D_steps : '
                                      'Hypermath.DriverCycleWitness → Exists fun path => Eq '
                                      '(Hypermath.Trace.length path) 2',
 'Hypermath.no_simulation_step_at_finite_of_successor_agreement': 'theorem '
                                                                  'Hypermath.no_simulation_step_at_finite_of_successor_agreement '
                                                                  ': '
                                                                  'Hypermath.FiniteSuccessorAgreement '
                                                                  '→ ∀ {x : Hypermath.Form}, '
                                                                  'Hypermath.finiteApplyFromGround '
                                                                  'x → Not (Hypermath.Simulation '
                                                                  '(Hypermath.f2f x) x)',
 'Hypermath.simulation_trace_from_finite_is_empty': 'theorem '
                                                    'Hypermath.simulation_trace_from_finite_is_empty '
                                                    ': Hypermath.FiniteSuccessorAgreement → ∀ {x y '
                                                    ': Hypermath.Form}, '
                                                    'Hypermath.finiteApplyFromGround x → ∀ (path : '
                                                    'Hypermath.SimulationEntry x y), Eq '
                                                    '(Hypermath.Trace.length path) 0',
 'Hypermath.no_simulation_step_of_successor_agreement':
     'theorem Hypermath.no_simulation_step_of_successor_agreement : Hypermath.SuccessorAgreement → ∀ (x : Hypermath.Form), Not (Hypermath.Simulation (Hypermath.f2f x) x)',
 'Hypermath.simulation_entry_is_empty_of_successor_agreement':
     'theorem Hypermath.simulation_entry_is_empty_of_successor_agreement : Hypermath.SuccessorAgreement → ∀ {x y : Hypermath.Form} (path : Hypermath.SimulationEntry x y), Eq (Hypermath.Trace.length path) 0',
 'Hypermath.no_driver_cycle_witness_of_successor_agreement':
     'theorem Hypermath.no_driver_cycle_witness_of_successor_agreement : Hypermath.SuccessorAgreement → Not (Nonempty Hypermath.DriverCycleWitness)',
 'Hypermath.simulationEntry_two':
     'theorem Hypermath.simulationEntry_two : ∀ {x y : Hypermath.Form} (path : Hypermath.SimulationEntry x y), Eq (Hypermath.Trace.length path) 2 → And (Eq y (Hypermath.f2f (Hypermath.f2f x))) (And (Hypermath.Simulation (Hypermath.f2f x) x) (Hypermath.Simulation (Hypermath.f2f (Hypermath.f2f x)) (Hypermath.f2f x)))',
 'Hypermath.driverCycleWitness_iff':
     'theorem Hypermath.driverCycleWitness_iff : Iff (Nonempty Hypermath.DriverCycleWitness) (And (Hypermath.Simulation (Hypermath.f2f Hypermath.deriver) Hypermath.deriver) (And (Hypermath.Simulation (Hypermath.f2f (Hypermath.f2f Hypermath.deriver)) (Hypermath.f2f Hypermath.deriver)) Hypermath.driverCycleClaim))',
 'Hypermath.driverCycleClaim_of_steps':
     'theorem Hypermath.driverCycleClaim_of_steps : Hypermath.SimulationTransitive → Hypermath.Simulation (Hypermath.f2f Hypermath.deriver) Hypermath.deriver → Hypermath.Simulation (Hypermath.f2f (Hypermath.f2f Hypermath.deriver)) (Hypermath.f2f Hypermath.deriver) → Hypermath.driverCycleClaim',
 'Hypermath.driverCycleWitness_iff_of_transitive':
     'theorem Hypermath.driverCycleWitness_iff_of_transitive : Hypermath.SimulationTransitive → Iff (Nonempty Hypermath.DriverCycleWitness) (And (Hypermath.Simulation (Hypermath.f2f Hypermath.deriver) Hypermath.deriver) (Hypermath.Simulation (Hypermath.f2f (Hypermath.f2f Hypermath.deriver)) (Hypermath.f2f Hypermath.deriver)))',
 'Hypermath.driverCycleWitness_of_fixed_deriver':
     'theorem Hypermath.driverCycleWitness_of_fixed_deriver : Eq (Hypermath.f2f Hypermath.deriver) Hypermath.deriver → Hypermath.Simulation Hypermath.deriver Hypermath.deriver → Nonempty Hypermath.DriverCycleWitness',
 'Hypermath.no_driver_cycle_witness_at_finite_successor': 'theorem '
                                                          'Hypermath.no_driver_cycle_witness_at_finite_successor '
                                                          ': Hypermath.FiniteSuccessorAgreement → '
                                                          'Hypermath.finiteApplyFromGround '
                                                          'Hypermath.deriver → Not (Nonempty '
                                                          'Hypermath.DriverCycleWitness)',
 'Hypermath.driverCycleWitness_exists_of_steps': 'theorem '
                                                 'Hypermath.driverCycleWitness_exists_of_steps : '
                                                 'Hypermath.Simulation (Hypermath.f2f '
                                                 'Hypermath.deriver) Hypermath.deriver → '
                                                 'Hypermath.Simulation (Hypermath.f2f '
                                                 '(Hypermath.f2f Hypermath.deriver)) '
                                                 '(Hypermath.f2f Hypermath.deriver) → '
                                                 'Hypermath.driverCycleClaim → Nonempty '
                                                 'Hypermath.DriverCycleWitness'})
PROVED_DEPENDENCIES.update({'Hypermath.simulationEntryToDEntry_length': ('Hypermath.Congruent',
                                              'Hypermath.Form',
                                              'Hypermath.Simulation',
                                              'Hypermath.f2f',
                                              'Hypermath.filtrationSimCong'),
 'Hypermath.selfDerivationOfWitness': ('Hypermath.Congruent',
                                       'Hypermath.DerivationPath',
                                       'Hypermath.Form',
                                       'Hypermath.Simulation',
                                       'Hypermath.axComposeIdentity',
                                       'Hypermath.axGroundSelf',
                                       'Hypermath.compose',
                                       'Hypermath.congruentPath',
                                       'Hypermath.deriver',
                                       'Hypermath.f2f',
                                       'Hypermath.ground',
                                       'Hypermath.pathGround',
                                       'Hypermath.structContinues'),
 'Hypermath.witness_has_two_D_steps': ('Hypermath.Congruent',
                                       'Hypermath.Form',
                                       'Hypermath.Simulation',
                                       'Hypermath.deriver',
                                       'Hypermath.f2f',
                                       'Hypermath.filtrationSimCong'),
 'Hypermath.no_simulation_step_at_finite_of_successor_agreement': ('Hypermath.Derives',
                                                                   'Hypermath.Form',
                                                                   'Hypermath.Simulation',
                                                                   'Hypermath.axSuccExtends',
                                                                   'Hypermath.f2f',
                                                                   'Hypermath.ground',
                                                                   'Hypermath.ordinalSucc'),
 'Hypermath.simulation_trace_from_finite_is_empty': ('Hypermath.Derives',
                                                     'Hypermath.Form',
                                                     'Hypermath.Simulation',
                                                     'Hypermath.axSuccExtends',
                                                     'Hypermath.f2f',
                                                     'Hypermath.ground',
                                                     'Hypermath.ordinalSucc'),
 'Hypermath.no_driver_cycle_witness_at_finite_successor': ('Hypermath.Derives',
                                                           'Hypermath.Form',
                                                           'Hypermath.Simulation',
                                                           'Hypermath.axSuccExtends',
                                                           'Hypermath.deriver',
                                                           'Hypermath.f2f',
                                                           'Hypermath.ground',
                                                           'Hypermath.ordinalSucc'),
 'Hypermath.driverCycleWitness_exists_of_steps': ('Hypermath.Form',
                                                  'Hypermath.Simulation',
                                                  'Hypermath.deriver',
                                                  'Hypermath.f2f')})

# The transfinite declarations are sourced from the ordinatics package. The
# three ordinal operations are no longer assumed here: each is a projection of
# the single Ordinatics.Transfinite structure named by Hypermath.ordinatics.
DEFINITION_DECLARATIONS.update({
    'Hypermath.ordinalApply':
        ('def Hypermath.ordinalApply : Hypermath.Form → Hypermath.Form → Hypermath.Form := '
         'Hypermath.ordinatics.apply'),
    'Hypermath.ordinalLimit':
        'def Hypermath.ordinalLimit : Hypermath.Form := Hypermath.ordinatics.limit',
    'Hypermath.ordinalSucc':
        'def Hypermath.ordinalSucc : Hypermath.Form → Hypermath.Form := Hypermath.ordinatics.succ',
})

# The four transfinite laws are likewise projections, so they are proved here
# rather than assumed. Their statements are unchanged from the axioms they replace.
PROVED_DECLARATIONS.update({
    'Hypermath.axLimitNotFinite':
        ('theorem Hypermath.axLimitNotFinite : ∀ (n : Nat), Not (Hypermath.Simulation (Nat.repeat '
         'Hypermath.f2f n Hypermath.ground) Hypermath.ordinalLimit)'),
    'Hypermath.axLimitDerives':
        ('theorem Hypermath.axLimitDerives : Exists fun limitPath => And (Hypermath.Similar '
         '(Hypermath.pathStart limitPath) Hypermath.ground) (Hypermath.Congruent (Hypermath.pathEnd '
         'limitPath) Hypermath.ordinalLimit)'),
    'Hypermath.axSuccExtends':
        ('theorem Hypermath.axSuccExtends : ∀ (x : Hypermath.Form), And (Hypermath.Derives x '
         '(Hypermath.ordinalSucc x)) (Not (Hypermath.Simulation (Hypermath.ordinalSucc x) x))'),
    'Hypermath.axLimitIsLimit':
        ('theorem Hypermath.axLimitIsLimit : ∀ (y : Hypermath.Form), (∀ (n : Nat), Hypermath.Derives '
         '(Nat.repeat Hypermath.f2f n Hypermath.ground) y) → Hypermath.Derives Hypermath.ordinalLimit '
         'y'),
})

# Hypermath.ordinatics is a single assumption carrying five clauses. Anything that
# has to cover the logical content of the source expands it into these names: a
# model satisfies the structure exactly when it satisfies each clause below.
TRANSFINITE_CLAUSES = (
    "Hypermath.axLimitNotFinite", "Hypermath.axLimitDerives",
    "Hypermath.axSuccExtends", "Hypermath.axLimitIsLimit",
    "Hypermath.axDeriverAtLimit",
)

# The deriver is declared at the ordinal limit. axDeriverAtLimit is that
# declaration, read off the ordinatics structure; the eight statements after it
# are what it buys, what it costs, and what replaces the cost.
PROVED_DECLARATIONS.update({
    'Hypermath.axDeriverAtLimit':
        'theorem Hypermath.axDeriverAtLimit : Eq Hypermath.deriver Hypermath.ordinalLimit',
    'Hypermath.noFinitePositionSimulatesDeriver':
        ('theorem Hypermath.noFinitePositionSimulatesDeriver : ∀ (n : Nat), Not (Hypermath.Simulation '
         '(Hypermath.finiteApplyPosition n) Hypermath.deriver)'),
    'Hypermath.groundDoesNotSimulateDeriver':
        ('theorem Hypermath.groundDoesNotSimulateDeriver : Not (Hypermath.Simulation Hypermath.ground '
         'Hypermath.deriver)'),
    'Hypermath.deriverNotFinite':
        'theorem Hypermath.deriverNotFinite : Not (Hypermath.finiteApplyFromGround Hypermath.deriver)',
    'Hypermath.noFiniteObstructionAtDeriver':
        ('theorem Hypermath.noFiniteObstructionAtDeriver : Not (Exists fun _agreement => '
         'Hypermath.finiteApplyFromGround Hypermath.deriver)'),
    'Hypermath.deriverNotInD':
        'theorem Hypermath.deriverNotInD : Not (Hypermath.D Hypermath.ground Hypermath.deriver)',
    'Hypermath.deriverReachedByLimitPath':
        ('theorem Hypermath.deriverReachedByLimitPath : Exists fun limitPath => And (Hypermath.Similar '
         '(Hypermath.pathStart limitPath) Hypermath.ground) (Hypermath.Congruent (Hypermath.pathEnd '
         'limitPath) Hypermath.deriver)'),
    'Hypermath.deriverIsLeastUpperBound':
        ('theorem Hypermath.deriverIsLeastUpperBound : ∀ (y : Hypermath.Form), (∀ (n : Nat), '
         'Hypermath.Derives (Hypermath.finiteApplyPosition n) y) → Hypermath.Derives Hypermath.deriver '
         'y'),
    'Hypermath.deriverExtends':
        ('theorem Hypermath.deriverExtends : And (Hypermath.Derives Hypermath.deriver '
         '(Hypermath.ordinalSucc Hypermath.deriver)) (Not (Hypermath.Simulation (Hypermath.ordinalSucc '
         'Hypermath.deriver) Hypermath.deriver))'),
})

# These six milestones previously depended on axLimitNotFinite or axSuccExtends.
# Those assumptions are gone; each milestone now depends on Hypermath.ordinatics,
# whose type mentions every substrate parameter the structure is stated over.
# The restatements below supersede the reviewed entries above.
PROVED_DEPENDENCIES.update({
    'Hypermath.finiteApplyLimitExcluded':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.HMSyntax',
         'Hypermath.Semantics',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.axSubstanceRequiresSemantics',
         'Hypermath.axSyntaxRequiresSubstance',
         'Hypermath.closeSemanticsOpaque',
         'Hypermath.closeSyntaxOpaque',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart',
         'Hypermath.traceLevels'),
    'Hypermath.ordinalLimitNotInD':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.HMSyntax',
         'Hypermath.Semantics',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.axSubstanceRequiresSemantics',
         'Hypermath.axSyntaxRequiresSubstance',
         'Hypermath.closeSemanticsOpaque',
         'Hypermath.closeSyntaxOpaque',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart',
         'Hypermath.traceLevels'),
    'Hypermath.notGroundSpanningClaim':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.HMSyntax',
         'Hypermath.Semantics',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.axSubstanceRequiresSemantics',
         'Hypermath.axSyntaxRequiresSubstance',
         'Hypermath.closeSemanticsOpaque',
         'Hypermath.closeSyntaxOpaque',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart',
         'Hypermath.traceLevels'),
    'Hypermath.no_simulation_step_at_finite_of_successor_agreement':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.simulation_trace_from_finite_is_empty':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.no_simulation_step_of_successor_agreement':
        ('Hypermath.Congruent', 'Hypermath.DerivationPath', 'Hypermath.Derives', 'Hypermath.Form', 'Hypermath.Similar', 'Hypermath.Simulation', 'Hypermath.deriver', 'Hypermath.f2f', 'Hypermath.ground', 'Hypermath.ordinatics', 'Hypermath.pathEnd', 'Hypermath.pathStart'),
    'Hypermath.simulation_entry_is_empty_of_successor_agreement':
        ('Hypermath.Congruent', 'Hypermath.DerivationPath', 'Hypermath.Derives', 'Hypermath.Form', 'Hypermath.Similar', 'Hypermath.Simulation', 'Hypermath.deriver', 'Hypermath.f2f', 'Hypermath.ground', 'Hypermath.ordinatics', 'Hypermath.pathEnd', 'Hypermath.pathStart'),
    'Hypermath.no_driver_cycle_witness_of_successor_agreement':
        ('Hypermath.Congruent', 'Hypermath.DerivationPath', 'Hypermath.Derives', 'Hypermath.Form', 'Hypermath.Similar', 'Hypermath.Simulation', 'Hypermath.deriver', 'Hypermath.f2f', 'Hypermath.ground', 'Hypermath.ordinatics', 'Hypermath.pathEnd', 'Hypermath.pathStart'),
    'Hypermath.simulationEntry_two':
        ('Hypermath.Form', 'Hypermath.Simulation', 'Hypermath.f2f'),
    'Hypermath.driverCycleWitness_iff':
        ('Hypermath.Form', 'Hypermath.Simulation', 'Hypermath.deriver', 'Hypermath.f2f'),
    'Hypermath.driverCycleClaim_of_steps':
        ('Hypermath.Form', 'Hypermath.Simulation', 'Hypermath.deriver', 'Hypermath.f2f'),
    'Hypermath.driverCycleWitness_iff_of_transitive':
        ('Hypermath.Form', 'Hypermath.Simulation', 'Hypermath.deriver', 'Hypermath.f2f'),
    'Hypermath.driverCycleWitness_of_fixed_deriver':
        ('Hypermath.Form', 'Hypermath.Simulation', 'Hypermath.deriver', 'Hypermath.f2f'),
    'Hypermath.no_driver_cycle_witness_at_finite_successor':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
})

# Dependencies of the transfinite projections and of the declared deriver position.
PROVED_DEPENDENCIES.update({
    'Hypermath.axLimitNotFinite':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.axLimitDerives':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.axSuccExtends':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.axLimitIsLimit':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.axDeriverAtLimit':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.noFinitePositionSimulatesDeriver':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.groundDoesNotSimulateDeriver':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.deriverNotFinite':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.HMSyntax',
         'Hypermath.Semantics',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.axSubstanceRequiresSemantics',
         'Hypermath.axSyntaxRequiresSubstance',
         'Hypermath.closeSemanticsOpaque',
         'Hypermath.closeSyntaxOpaque',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart',
         'Hypermath.traceLevels'),
    'Hypermath.noFiniteObstructionAtDeriver':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.HMSyntax',
         'Hypermath.Semantics',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.axSubstanceRequiresSemantics',
         'Hypermath.axSyntaxRequiresSubstance',
         'Hypermath.closeSemanticsOpaque',
         'Hypermath.closeSyntaxOpaque',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart',
         'Hypermath.traceLevels'),
    'Hypermath.deriverNotInD':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.HMSyntax',
         'Hypermath.Semantics',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.axSubstanceRequiresSemantics',
         'Hypermath.axSyntaxRequiresSubstance',
         'Hypermath.closeSemanticsOpaque',
         'Hypermath.closeSyntaxOpaque',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart',
         'Hypermath.traceLevels'),
    'Hypermath.deriverReachedByLimitPath':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.deriverIsLeastUpperBound':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
    'Hypermath.deriverExtends':
        ('Hypermath.Congruent',
         'Hypermath.DerivationPath',
         'Hypermath.Derives',
         'Hypermath.Form',
         'Hypermath.Similar',
         'Hypermath.Simulation',
         'Hypermath.deriver',
         'Hypermath.f2f',
         'Hypermath.ground',
         'Hypermath.ordinatics',
         'Hypermath.pathEnd',
         'Hypermath.pathStart'),
})

RULE_SUBSTITUTION_SOURCE_SHA256 = '7e0ab21054b84b7158d67a77a8bde8c75c4edc64850e13f7fe1f978c1f3e3d07'

SEQUENTIAL_SOURCE_SHA256 = '55f7883c1adf34cf4538feb09e6651e3f8749ff4f1df21cd607c9ade523329ce'

LAYERED_DERIVATION_SOURCE_SHA256 = 'c1e78f4245f070d3d238122005afef14db0a5dae5b2fedbfb1672b424b45c949'

LAYERED_DERIVATION_CHECKS_SOURCE_SHA256 = 'ff582ed98aa54d7fab21b98dd53e73cf58f5170fc78214d8e09d22cc44147b42'

SURFACE_BRIDGE_SOURCE_SHA256 = 'ca86535a5c39a02588b7af8791313a802e3c4d86dd88ab69a2ff0de2d4d870da'

UNARY_FORMATION_SOURCE_SHA256 = '1fcd0a58b8d801f3227c00e85f15617f9174ebd216a977048eef32ae2d6f11e8'

CONTEXTUAL_COMPOSITION_SOURCE_SHA256 = '737280bf9d5678e5fc000807a4b564026e2171ad7d78dedcd87e342f13c85878'

OPERATIONAL_CORRESPONDENCE_SOURCE_SHA256 = 'c1697e69cf4f3bd03eb818752c490c2199cb1c53d9e995d194e50be1f3119809'

TERMINAL_RETENTION_SOURCE_SHA256 = '4a49f9d30796e6b543843cb4d29b041d0544552f63477d5b450b46407af34a28'

RETAINED_EXECUTION_SOURCE_SHA256 = '0e9d5c57e1ffce15646169e33e4855d3a37c661b7f83ebcb4ccafa212d3fcb60'

PATH_LAYERS_SOURCE_SHA256 = 'c6904b4f24c4d5375e0f3e776899b3adf67071df738abd198373aba0fb3dc10a'
PATH_TRANSPORT_SOURCE_SHA256 = '7e03c457d47673f9a575c590b054a134a77f7cfd4c4b45a17348deec037d5a17'
TRANSPORT_COUNTERMODEL_SOURCE_SHA256 = '06cccf058f41f1716a90a2bd8a74b72dfbf0cb400133e706ba37461c7ca89c08'
NONDEGENERATE_CYCLE_SOURCE_SHA256 = '085bc005b67a3dc00c8d7e0bc6cb037b4b4d216269cf13c3d080620a2a55675a'


# §IV.c: the two upper reflexivities are one condition, and it is reachability.
PROVED_DECLARATIONS.update({
    'Hypermath.triangleVerticesCoincide':
        'theorem Hypermath.triangleVerticesCoincide : ∀ (x : Hypermath.Form), Iff (Hypermath.HMSyntax x) (Hypermath.Substance x)',
    'Hypermath.reflexivityLevelsCoincide':
        ('theorem Hypermath.reflexivityLevelsCoincide : ∀ (x : Hypermath.Form), Iff '
         '(Hypermath.Congruent x x) (Hypermath.Simulation x x)'),
    'Hypermath.reflexivityIsGroundReachability':
        ('theorem Hypermath.reflexivityIsGroundReachability : ∀ (x : Hypermath.Form), Iff '
         '(Hypermath.Congruent x x) (Exists fun n => Hypermath.Similar (Nat.repeat '
         'Hypermath.f2f n Hypermath.ground) x)'),
    'Hypermath.upperReflexivitiesAndReachabilityAgree':
        ('theorem Hypermath.upperReflexivitiesAndReachabilityAgree : ∀ (x : Hypermath.Form), '
         'And (Iff (Hypermath.Simulation x x) (Hypermath.Congruent x x)) (Iff '
         '(Hypermath.Congruent x x) (Exists fun n => Hypermath.Similar (Nat.repeat '
         'Hypermath.f2f n Hypermath.ground) x))'),
    'Hypermath.globalCongruentReflexivityIsCofinality':
        ('theorem Hypermath.globalCongruentReflexivityIsCofinality : Iff (∀ (x : '
         'Hypermath.Form), Hypermath.Congruent x x) (∀ (x : Hypermath.Form), Exists fun '
         'n => Hypermath.Similar (Nat.repeat Hypermath.f2f n Hypermath.ground) x)'),
})

PROVED_DEPENDENCIES.update({
    'Hypermath.triangleVerticesCoincide': (
        'Hypermath.Form',
        'Hypermath.HMSyntax',
        'Hypermath.Substance',
        'Hypermath.axSemanticsRequiresSyntax',
        'Hypermath.axSubstanceRequiresSemantics',
        'Hypermath.axSyntaxRequiresSubstance',
    ),
    'Hypermath.reflexivityLevelsCoincide': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.Semantics',
        'Hypermath.Simulation',
        'Hypermath.Substance',
        'Hypermath.axSemanticsRequiresSyntax',
        'Hypermath.axSubstanceRequiresSemantics',
        'Hypermath.axSyntaxRequiresSubstance',
        'Hypermath.closeSemanticsOpaque',
        'Hypermath.closeSubstanceOpaque',
    ),
    'Hypermath.reflexivityIsGroundReachability': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.HMSyntax',
        'Hypermath.Similar',
        'Hypermath.Substance',
        'Hypermath.axSemanticsRequiresSyntax',
        'Hypermath.axSubstanceRequiresSemantics',
        'Hypermath.axSyntaxRequiresSubstance',
        'Hypermath.closeSubstanceOpaque',
        'Hypermath.closeSyntaxOpaque',
        'Hypermath.f2f',
        'Hypermath.ground',
    ),
    'Hypermath.upperReflexivitiesAndReachabilityAgree': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.HMSyntax',
        'Hypermath.Semantics',
        'Hypermath.Similar',
        'Hypermath.Simulation',
        'Hypermath.Substance',
        'Hypermath.axSemanticsRequiresSyntax',
        'Hypermath.axSubstanceRequiresSemantics',
        'Hypermath.axSyntaxRequiresSubstance',
        'Hypermath.closeSemanticsOpaque',
        'Hypermath.closeSubstanceOpaque',
        'Hypermath.closeSyntaxOpaque',
        'Hypermath.f2f',
        'Hypermath.ground',
    ),
    'Hypermath.globalCongruentReflexivityIsCofinality': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.HMSyntax',
        'Hypermath.Similar',
        'Hypermath.Substance',
        'Hypermath.axSemanticsRequiresSyntax',
        'Hypermath.axSubstanceRequiresSemantics',
        'Hypermath.axSyntaxRequiresSubstance',
        'Hypermath.closeSubstanceOpaque',
        'Hypermath.closeSyntaxOpaque',
        'Hypermath.f2f',
        'Hypermath.ground',
    ),
})

# §VI.a: the filtration characterization, necessity half.
PROVED_DECLARATIONS.update({
    'Hypermath.filtrationConditionsHold':
        'theorem Hypermath.filtrationConditionsHold : And (∀ (x y : Hypermath.Form), Hypermath.Simulation x y → Hypermath.Congruent x y) (And (∀ (x y : Hypermath.Form), Hypermath.Congruent x y → Hypermath.Similar x y) (And (∀ (x : Hypermath.Form), Hypermath.Similar (Hypermath.f2f x) x) (And (∀ (x : Hypermath.Form), Hypermath.Similar (Hypermath.f2f x) Hypermath.ground) (And (∀ (x : Hypermath.Form), Hypermath.Similar (Hypermath.f2f (Hypermath.f2f x)) x) (And (∀ (x : Hypermath.Form), Not (Hypermath.Simulation (Hypermath.f2f x) Hypermath.ground)) (And (∀ (x : Hypermath.Form), Iff (Hypermath.Congruent x x) (Exists fun n => Hypermath.Similar (Nat.repeat Hypermath.f2f n Hypermath.ground) x)) (∀ (x : Hypermath.Form), Iff (Hypermath.Simulation x x) (Exists fun n => Hypermath.Similar (Nat.repeat Hypermath.f2f n Hypermath.ground) x))))))))',
    'Hypermath.simulationDeniesEveryImageAtGround':
        'theorem Hypermath.simulationDeniesEveryImageAtGround : ∀ (x : Hypermath.Form), Not (Hypermath.Simulation (Hypermath.f2f x) Hypermath.ground)',
})
PROVED_DEPENDENCIES.update({
    'Hypermath.filtrationConditionsHold': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.HMSyntax',
        'Hypermath.Semantics',
        'Hypermath.Similar',
        'Hypermath.Simulation',
        'Hypermath.Substance',
        'Hypermath.axBox',
        'Hypermath.axDiff',
        'Hypermath.axSemanticsRequiresSyntax',
        'Hypermath.axSim',
        'Hypermath.axSubstanceRequiresSemantics',
        'Hypermath.axSyntaxRequiresSubstance',
        'Hypermath.closeSemanticsOpaque',
        'Hypermath.closeStructContinues',
        'Hypermath.closeStructDistinct',
        'Hypermath.closeStructOrbits',
        'Hypermath.closeSubstanceOpaque',
        'Hypermath.closeSyntaxOpaque',
        'Hypermath.f2f',
        'Hypermath.filtrationCongSim',
        'Hypermath.filtrationSimCong',
        'Hypermath.ground',
        'Hypermath.structContinues',
        'Hypermath.structDistinct',
        'Hypermath.structOrbits',
        'Hypermath.traceLevels',
    ),
    'Hypermath.simulationDeniesEveryImageAtGround': (
        'Hypermath.Form',
        'Hypermath.Similar',
        'Hypermath.Simulation',
        'Hypermath.axDiff',
        'Hypermath.axSim',
        'Hypermath.closeStructContinues',
        'Hypermath.closeStructDistinct',
        'Hypermath.f2f',
        'Hypermath.ground',
        'Hypermath.structContinues',
        'Hypermath.structDistinct',
    ),
})

# §VII.a: + and additionally are declared by the same propositions.
PROVED_DECLARATIONS.update({
    'Hypermath.sequencingClausesAreCooperationClauses':
        'theorem Hypermath.sequencingClausesAreCooperationClauses : And (And (∀ (a b : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Similar c b)) (∀ (a : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Congruent c a))) (And (∀ (a b : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Similar c b)) (∀ (a : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Congruent c a)))',
})
PROVED_DEPENDENCIES.update({
    'Hypermath.sequencingClausesAreCooperationClauses': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.Similar',
        'Hypermath.axCoop',
        'Hypermath.axCoopIdentity',
        'Hypermath.axSeq',
        'Hypermath.axSeqIdentityR',
    ),
})

# §IV: no clause or law constrains the ordinal application.
PROVED_DECLARATIONS.update({
    'Hypermath.ordinalApplyUnconstrained':
        'theorem Hypermath.ordinalApplyUnconstrained : ∀ (g : Hypermath.Form → Hypermath.Form → Hypermath.Form), Exists fun T => And (Eq T.apply g) (And (Eq T.limit Hypermath.ordinalLimit) (Eq T.succ Hypermath.ordinalSucc))',
})
PROVED_DEPENDENCIES.update({
    'Hypermath.ordinalApplyUnconstrained': (
        'Hypermath.Congruent', 'Hypermath.DerivationPath', 'Hypermath.Derives',
        'Hypermath.Form', 'Hypermath.Similar', 'Hypermath.Simulation',
        'Hypermath.deriver', 'Hypermath.f2f', 'Hypermath.ground',
        'Hypermath.ordinatics', 'Hypermath.pathEnd', 'Hypermath.pathStart',
    ),
})

# §VII.b: four of the seven operation clauses follow from the other two.
PROVED_DECLARATIONS.update({
    'Hypermath.commonWitnessesComeFromCommutativity':
        'theorem Hypermath.commonWitnessesComeFromCommutativity : And (∀ (a b : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Similar c b)) (∀ (a : Hypermath.Form), Exists fun c => And (Hypermath.Similar c a) (Hypermath.Congruent c a))',
})
PROVED_DEPENDENCIES.update({
    'Hypermath.commonWitnessesComeFromCommutativity': (
        'Hypermath.Congruent',
        'Hypermath.Form',
        'Hypermath.Similar',
        'Hypermath.axCoopComm',
        'Hypermath.axCoopIdentity',
    ),
})

LAYER_CONSUMPTION_CHECKS_SOURCE_SHA256 = '4b56ad54a0277bb6d3f623340feedcb9d1cb421c0b4ae82c5979d54186b3256e'

# Every public declaration in lean4/Hypermath/, with the file that declares it.
# The sweep reports one axiom list per entry; the entries themselves are the
# inventory a new declaration has to join before it can be measured.
LAYER_DECLARATION_HOME = {
    'Hypermath.AbstractedFrom': 'QuadrilateralFiltration',
    'Hypermath.AbstractionProfile': 'QuadrilateralFiltration',
    'Hypermath.CongruentFromPath': 'QuadrilateralFiltration',
    'Hypermath.CongruentProfile': 'QuadrilateralFiltration',
    'Hypermath.ContextualComposition.base_check': 'ContextualComposition',
    'Hypermath.ContextualComposition.check_compose': 'ContextualComposition',
    'Hypermath.ContextualComposition.checked_context': 'ContextualComposition',
    'Hypermath.ContextualComposition.compose': 'ContextualComposition',
    'Hypermath.ContextualComposition.joinCall': 'ContextualComposition',
    'Hypermath.ContextualComposition.join_call_runs': 'ContextualComposition',
    'Hypermath.ContextualComposition.join_history': 'ContextualComposition',
    'Hypermath.ContextualComposition.joined_trace_check': 'ContextualComposition',
    'Hypermath.ContextualComposition.joint_state': 'ContextualComposition',
    'Hypermath.ContextualComposition.lifted_check': 'ContextualComposition',
    'Hypermath.ContextualComposition.lifted_history': 'ContextualComposition',
    'Hypermath.ContextualComposition.lifted_recovery': 'ContextualComposition',
    'Hypermath.ContextualComposition.trace_append': 'ContextualComposition',
    'Hypermath.D': 'L1Relations',
    'Hypermath.DEntry': 'L1Relations',
    'Hypermath.DExpr': 'QuadrilateralFiltration',
    'Hypermath.DExpr.quanta': 'QuadrilateralFiltration',
    'Hypermath.DExpr.retrace': 'QuadrilateralFiltration',
    'Hypermath.DExpr.seq': 'QuadrilateralFiltration',
    'Hypermath.DStep': 'L1Relations',
    'Hypermath.DerivesIn': 'L1Relations',
    'Hypermath.ExactFiniteAction': 'FiniteAction',
    'Hypermath.FiniteAction.CongruentActionAgreement': 'FiniteAction',
    'Hypermath.FiniteAction.ExactFiniteAction': 'FiniteAction',
    'Hypermath.FiniteAction.FiniteActionCompatible': 'FiniteAction',
    'Hypermath.FiniteAction.NumeralEq': 'FiniteAction',
    'Hypermath.FiniteAction.RelationActionCompatible': 'FiniteAction',
    'Hypermath.FiniteAction.action_eq_on_finite_orbit': 'FiniteAction',
    'Hypermath.FiniteAction.agreement_implies_relation_compatible': 'FiniteAction',
    'Hypermath.FiniteAction.chosenAction': 'FiniteAction',
    'Hypermath.FiniteAction.chosen_action_exact': 'FiniteAction',
    'Hypermath.FiniteAction.compatible_iff_exists_exact': 'FiniteAction',
    'Hypermath.FiniteAction.exact_implies_compatible': 'FiniteAction',
    'Hypermath.FiniteAction.iteration_add': 'FiniteAction',
    'Hypermath.FiniteAction.iteration_commute': 'FiniteAction',
    'Hypermath.FiniteAction.numeralEq_add': 'FiniteAction',
    'Hypermath.FiniteAction.numeralEq_mul': 'FiniteAction',
    'Hypermath.FiniteAction.numeralEq_mul_right': 'FiniteAction',
    'Hypermath.FiniteAction.numeralEq_refl': 'FiniteAction',
    'Hypermath.FiniteAction.numeralEq_symm': 'FiniteAction',
    'Hypermath.FiniteAction.numeralEq_trans': 'FiniteAction',
    'Hypermath.FiniteAction.numeralSetoid': 'FiniteAction',
    'Hypermath.FiniteActionCompatible': 'FiniteAction',
    'Hypermath.FiniteNumeralEq': 'FiniteAction',
    'Hypermath.FiniteOrbit': 'FiniteAction',
    'Hypermath.FiniteOrbitInjective': 'FiniteAction',
    'Hypermath.SuccessorAgreement': 'L3Ordinatics',
    'Hypermath.SimulationTransitive': 'L3Ordinatics',
    'Hypermath.simulationEntry_two': 'L3Ordinatics',
    'Hypermath.driverCycleWitness_iff': 'L3Ordinatics',
    'Hypermath.driverCycleClaim_of_steps': 'L3Ordinatics',
    'Hypermath.driverCycleWitness_of_fixed_deriver': 'L3Ordinatics',
    'Hypermath.driverCycleWitness_iff_of_transitive': 'L3Ordinatics',
    'Hypermath.no_simulation_step_of_successor_agreement': 'L3Ordinatics',
    'Hypermath.simulation_entry_is_empty_of_successor_agreement': 'L3Ordinatics',
    'Hypermath.no_driver_cycle_witness_of_successor_agreement': 'L3Ordinatics',
    'Hypermath.FiniteSuccessorAgreement': 'L3Ordinatics',
    'Hypermath.GroundCode.Tree.bits': 'GroundCode',
    'Hypermath.GroundCode.Tree.bits_length': 'GroundCode',
    'Hypermath.GroundCode.Tree.code': 'GroundCode',
    'Hypermath.GroundCode.Tree.size': 'GroundCode',
    'Hypermath.GroundCode.Tree.toTerm': 'GroundCode',
    'Hypermath.GroundCode.code_injective': 'GroundCode',
    'Hypermath.GroundCode.decodeNumber': 'GroundCode',
    'Hypermath.GroundCode.decodeTerm': 'GroundCode',
    'Hypermath.GroundCode.decode_code': 'GroundCode',
    'Hypermath.GroundCode.decode_toTerm': 'GroundCode',
    'Hypermath.GroundCode.pack': 'GroundCode',
    'Hypermath.GroundCode.pack_bounds': 'GroundCode',
    'Hypermath.GroundCode.parse': 'GroundCode',
    'Hypermath.GroundCode.parse_bits': 'GroundCode',
    'Hypermath.GroundCode.toTerm_injective': 'GroundCode',
    'Hypermath.GroundCode.unpack': 'GroundCode',
    'Hypermath.GroundCode.unpack_pack': 'GroundCode',
    'Hypermath.GroundDerivation.Formula.holds': 'GroundDerivation',
    'Hypermath.GroundDerivation.Record.conclusion': 'GroundDerivation',
    'Hypermath.GroundDerivation.Record.derive': 'GroundDerivation',
    'Hypermath.GroundDerivation.Record.valid': 'GroundDerivation',
    'Hypermath.GroundDerivation.check': 'GroundDerivation',
    'Hypermath.GroundDerivation.check_iff': 'GroundDerivation',
    'Hypermath.GroundDerivation.check_join_iff': 'GroundDerivation',
    'Hypermath.GroundDerivation.check_quote': 'GroundDerivation',
    'Hypermath.GroundDerivation.check_sound': 'GroundDerivation',
    'Hypermath.GroundDerivation.conclusion_quote': 'GroundDerivation',
    'Hypermath.GroundDerivation.derivation_sound': 'GroundDerivation',
    'Hypermath.GroundDerivation.nativeModel': 'GroundDerivation',
    'Hypermath.GroundDerivation.native_check_sound': 'GroundDerivation',
    'Hypermath.GroundDerivation.observe_derive': 'GroundDerivation',
    'Hypermath.GroundDerivation.quote': 'GroundDerivation',
    'Hypermath.GroundDerivation.quote_derive': 'GroundDerivation',
    'Hypermath.GroundDerivation.reconstruct': 'GroundDerivation',
    'Hypermath.GroundDerivation.reconstruct_retains_record': 'GroundDerivation',
    'Hypermath.GroundDerivation.represented_iff_derivable': 'GroundDerivation',
    'Hypermath.GroundDerivation.separation': 'GroundDerivation',
    'Hypermath.GroundDerivation.valid_quote': 'GroundDerivation',
    'Hypermath.GroundSyntax.AxiomInstance.conclusion': 'GroundSyntax',
    'Hypermath.GroundSyntax.Statement.holds': 'GroundSyntax',
    'Hypermath.GroundSyntax.Term.depth': 'GroundSyntax',
    'Hypermath.GroundSyntax.Term.depth_ofDepth': 'GroundSyntax',
    'Hypermath.GroundSyntax.Term.interpret': 'GroundSyntax',
    'Hypermath.GroundSyntax.Term.interpret_ofDepth': 'GroundSyntax',
    'Hypermath.GroundSyntax.Term.ofDepth': 'GroundSyntax',
    'Hypermath.GroundSyntax.Term.ofDepth_depth': 'GroundSyntax',
    'Hypermath.GroundSyntax.check': 'GroundSyntax',
    'Hypermath.GroundSyntax.check_encode': 'GroundSyntax',
    'Hypermath.GroundSyntax.check_iff': 'GroundSyntax',
    'Hypermath.GroundSyntax.check_sound': 'GroundSyntax',
    'Hypermath.GroundSyntax.decode': 'GroundSyntax',
    'Hypermath.GroundSyntax.decode_encode': 'GroundSyntax',
    'Hypermath.GroundSyntax.encode': 'GroundSyntax',
    'Hypermath.GroundSyntax.encode_injective': 'GroundSyntax',
    'Hypermath.GroundSyntax.instance_sound': 'GroundSyntax',
    'Hypermath.GroundSyntax.nativeModel': 'GroundSyntax',
    'Hypermath.GroundSyntax.native_check_sound': 'GroundSyntax',
    'Hypermath.GroundSyntax.nextArgument': 'GroundSyntax',
    'Hypermath.GroundSyntax.observe': 'GroundSyntax',
    'Hypermath.GroundSyntax.observe_encode': 'GroundSyntax',
    'Hypermath.GroundSyntax.reuse': 'GroundSyntax',
    'Hypermath.GroundSyntax.reuseMany': 'GroundSyntax',
    'Hypermath.GroundSyntax.reuse_encode': 'GroundSyntax',
    'Hypermath.GroundSyntax.reuse_many_encode': 'GroundSyntax',
    'Hypermath.LayeredDerivation.Evidence': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.Expression.run': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.Expression.run_sound': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.Expression.tree': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.SameExpansion': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.Surface': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.check': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.checkDecodedSurface': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.checkGroundTerm': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.checkGroundTerm_groundTerm': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.check_iff': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.check_iterateLift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.check_lift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.check_seq': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.check_sound': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.combine': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.combine_associative': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.combine_left_identity': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.combine_right_identity': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.composition_lift_preserves': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.decode': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.decode_encode': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.encode': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.encode_injective': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.groundTerm': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.iterateLift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.lift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.liftMap': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.lift_injective': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.lift_preserves_composition': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.lift_reflects_expansion': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.lowerAtom': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.lowerAtom_lift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.observe_groundTerm': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.observe_iterateLift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.payload': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.readExpression': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.readExpression_tree': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.readGroundTerm': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.readGroundTerm_groundTerm': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.readPayload': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.readPayload_payload': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.recoverThrough': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.recoverThrough_iterateLift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.sequencing': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.unfold': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.unfold_iterateLift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.unfold_lift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.unfold_seq': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.unfold_sound': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.unfolded_claims_sound': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.valid': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.valid_lift': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.valid_seq': 'LayeredDerivation',
    'Hypermath.LayeredDerivation.wrong_layer_rejected': 'LayeredDerivation',
    'Hypermath.Observation.Compatible': 'Observation',
    'Hypermath.Observation.Decodes': 'Observation',
    'Hypermath.Observation.Image': 'Observation',
    'Hypermath.Observation.RespectsEncoding': 'Observation',
    'Hypermath.Observation.chosenDecoder': 'Observation',
    'Hypermath.Observation.chosenDecoder_correct': 'Observation',
    'Hypermath.Observation.compatible_iff_decoder': 'Observation',
    'Hypermath.Observation.decoder_implies_compatible': 'Observation',
    'Hypermath.Observation.decoder_unique_on_image': 'Observation',
    'Hypermath.Observation.endpoint_decoder_cannot_recover_distinct_lengths': 'Observation',
    'Hypermath.Observation.endpoints_eq_of_step': 'Observation',
    'Hypermath.Observation.equalityQuery': 'Observation',
    'Hypermath.Observation.equality_queries_iff_injective': 'Observation',
    'Hypermath.Observation.no_endpoint_length_decoder': 'Observation',
    'Hypermath.Observation.reuse': 'Observation',
    'Hypermath.Observation.reuse_preserves_observations': 'Observation',
    'Hypermath.Observation.reuse_respects_encoding': 'Observation',
    'Hypermath.Observation.toImage': 'Observation',
    'Hypermath.OperationalCorrespondence.Frame.accept': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.Frame.advance': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.Frame.initial': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.LiftRespects': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.Respects': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.accept_run_initial': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.lift_compose': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.lift_run_decodes': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.represented_check': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.represented_composition_check': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.represented_run': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.run': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.run_append': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.run_decodes': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.run_encoded': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.run_frame': 'OperationalCorrespondence',
    'Hypermath.OperationalCorrespondence.run_lift_commutes': 'OperationalCorrespondence',
    'Hypermath.PathLayers.Checks.Forward': 'PathLayers',
    'Hypermath.PathLayers.Checks.first': 'PathLayers',
    'Hypermath.PathLayers.Checks.grouping_has_same_path': 'PathLayers',
    'Hypermath.PathLayers.Checks.grouping_remains_distinct': 'PathLayers',
    'Hypermath.PathLayers.Checks.nested_paths_recovered': 'PathLayers',
    'Hypermath.PathLayers.Checks.probe': 'PathLayers',
    'Hypermath.PathLayers.Checks.second': 'PathLayers',
    'Hypermath.PathLayers.Checks.two_steps_retained': 'PathLayers',
    'Hypermath.PathLayers.Expression.expand': 'PathLayers',
    'Hypermath.PathLayers.NativeSurface': 'PathLayers',
    'Hypermath.PathLayers.Surface': 'PathLayers',
    'Hypermath.PathLayers.compose': 'PathLayers',
    'Hypermath.PathLayers.composed_edges_preserved': 'PathLayers',
    'Hypermath.PathLayers.composed_length_preserved': 'PathLayers',
    'Hypermath.PathLayers.composition_lift_preserves': 'PathLayers',
    'Hypermath.PathLayers.cycle_surface_iff_witness': 'PathLayers',
    'Hypermath.PathLayers.cycle_witness_length_preserved': 'PathLayers',
    'Hypermath.PathLayers.expand': 'PathLayers',
    'Hypermath.PathLayers.expand_compose': 'PathLayers',
    'Hypermath.PathLayers.expand_identity': 'PathLayers',
    'Hypermath.PathLayers.expand_iterateLift': 'PathLayers',
    'Hypermath.PathLayers.expand_lift': 'PathLayers',
    'Hypermath.PathLayers.expand_promote': 'PathLayers',
    'Hypermath.PathLayers.identity': 'PathLayers',
    'Hypermath.PathLayers.iterateLift': 'PathLayers',
    'Hypermath.PathLayers.lift': 'PathLayers',
    'Hypermath.PathLayers.loopLiftMap': 'PathLayers',
    'Hypermath.PathLayers.loopSequencing': 'PathLayers',
    'Hypermath.PathLayers.lowerAtom': 'PathLayers',
    'Hypermath.PathLayers.lowerAtom_lift': 'PathLayers',
    'Hypermath.PathLayers.native_composition_lift_preserves': 'PathLayers',
    'Hypermath.PathLayers.native_endpoint_preserved': 'PathLayers',
    'Hypermath.PathLayers.native_reachability_iff': 'PathLayers',
    'Hypermath.PathLayers.native_without_steps': 'PathLayers',
    'Hypermath.PathLayers.no_steps_remains_empty': 'PathLayers',
    'Hypermath.PathLayers.nonempty_iff_base': 'PathLayers',
    'Hypermath.PathLayers.promote': 'PathLayers',
    'Hypermath.PathLayers.recoverCycle': 'PathLayers',
    'Hypermath.PathLayers.recoverCycle_reifyCycle': 'PathLayers',
    'Hypermath.PathLayers.recoverThrough': 'PathLayers',
    'Hypermath.PathLayers.recoverThrough_iterateLift': 'PathLayers',
    'Hypermath.PathLayers.reifyCycle': 'PathLayers',
    'Hypermath.PathTransport.Alignment.compose': 'PathTransport',
    'Hypermath.PathTransport.Alignment.ends': 'PathTransport',
    'Hypermath.PathTransport.Alignment.length_eq': 'PathTransport',
    'Hypermath.PathTransport.Alignment.starts': 'PathTransport',
    'Hypermath.PathTransport.Checks.AllRelated': 'PathTransport',
    'Hypermath.PathTransport.Checks.Next': 'PathTransport',
    'Hypermath.PathTransport.Checks.OneEdge': 'PathTransport',
    'Hypermath.PathTransport.Checks.Point': 'PathTransport',
    'Hypermath.PathTransport.Checks.SameHeight': 'PathTransport',
    'Hypermath.PathTransport.Checks.certificate': 'PathTransport',
    'Hypermath.PathTransport.Checks.first': 'PathTransport',
    'Hypermath.PathTransport.Checks.original': 'PathTransport',
    'Hypermath.PathTransport.Checks.original_and_copy_retained': 'PathTransport',
    'Hypermath.PathTransport.Checks.path_preserves_component': 'PathTransport',
    'Hypermath.PathTransport.Checks.probe': 'PathTransport',
    'Hypermath.PathTransport.Checks.related_without_connector': 'PathTransport',
    'Hypermath.PathTransport.Checks.relation_alone_insufficient': 'PathTransport',
    'Hypermath.PathTransport.Checks.reproduced_copy_changes_endpoint': 'PathTransport',
    'Hypermath.PathTransport.Checks.transfer': 'PathTransport',
    'Hypermath.PathTransport.Composition.path': 'PathTransport',
    'Hypermath.PathTransport.NativeOneStepLaw': 'PathTransport',
    'Hypermath.PathTransport.Reproduction.append': 'PathTransport',
    'Hypermath.PathTransport.StepTransfer': 'PathTransport',
    'Hypermath.PathTransport.atLayer': 'PathTransport',
    'Hypermath.PathTransport.composeAcross': 'PathTransport',
    'Hypermath.PathTransport.composed_edges': 'PathTransport',
    'Hypermath.PathTransport.composed_endpoint_related': 'PathTransport',
    'Hypermath.PathTransport.composed_length': 'PathTransport',
    'Hypermath.PathTransport.nativeTransfer': 'PathTransport',
    'Hypermath.PathTransport.native_law_iff_transfer': 'PathTransport',
    'Hypermath.PathTransport.raise': 'PathTransport',
    'Hypermath.PathTransport.raise_preserves_path': 'PathTransport',
    'Hypermath.PathTransport.raise_recovers_surface': 'PathTransport',
    'Hypermath.PathTransport.raise_retains_certificate': 'PathTransport',
    'Hypermath.PathTransport.reproduce': 'PathTransport',
    'Hypermath.PathTransport.reproduce_compose': 'PathTransport',
    'Hypermath.Realizer': 'QuadrilateralFiltration',
    'Hypermath.RecordEncoding.checkDecoded': 'RecordEncoding',
    'Hypermath.RecordEncoding.checkNumbers': 'RecordEncoding',
    'Hypermath.RecordEncoding.checkNumbers_codes': 'RecordEncoding',
    'Hypermath.RecordEncoding.checkNumbers_sound': 'RecordEncoding',
    'Hypermath.RecordEncoding.checkTerms': 'RecordEncoding',
    'Hypermath.RecordEncoding.checkTerms_quote': 'RecordEncoding',
    'Hypermath.RecordEncoding.checkTerms_terms': 'RecordEncoding',
    'Hypermath.RecordEncoding.decodeFormula': 'RecordEncoding',
    'Hypermath.RecordEncoding.decodeFormula_recordCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.decodeRecord': 'RecordEncoding',
    'Hypermath.RecordEncoding.decodeRecord_formulaCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.decode_formulaCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.decode_formulaTerm': 'RecordEncoding',
    'Hypermath.RecordEncoding.decode_recordCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.decode_recordTerm': 'RecordEncoding',
    'Hypermath.RecordEncoding.formulaCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.formulaTerm': 'RecordEncoding',
    'Hypermath.RecordEncoding.formulaTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.joinCodes': 'RecordEncoding',
    'Hypermath.RecordEncoding.joinCodes_recordCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.observe_recordCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.observe_recordTerm': 'RecordEncoding',
    'Hypermath.RecordEncoding.readFormula': 'RecordEncoding',
    'Hypermath.RecordEncoding.readFormula_formulaTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.readRecord': 'RecordEncoding',
    'Hypermath.RecordEncoding.readRecord_recordTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.readStatement': 'RecordEncoding',
    'Hypermath.RecordEncoding.readStatement_statementTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.readTag': 'RecordEncoding',
    'Hypermath.RecordEncoding.readTag_number': 'RecordEncoding',
    'Hypermath.RecordEncoding.readTerm': 'RecordEncoding',
    'Hypermath.RecordEncoding.readTerm_termTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.recordCode': 'RecordEncoding',
    'Hypermath.RecordEncoding.recordCode_injective': 'RecordEncoding',
    'Hypermath.RecordEncoding.recordTerm': 'RecordEncoding',
    'Hypermath.RecordEncoding.recordTerm_injective': 'RecordEncoding',
    'Hypermath.RecordEncoding.recordTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.semantic_record_recovery': 'RecordEncoding',
    'Hypermath.RecordEncoding.statementTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.tag': 'RecordEncoding',
    'Hypermath.RecordEncoding.termTree': 'RecordEncoding',
    'Hypermath.RecordEncoding.unwrap': 'RecordEncoding',
    'Hypermath.RecordEncoding.unwrap_tag': 'RecordEncoding',
    'Hypermath.RecordMachine.State': 'RecordMachine',
    'Hypermath.RecordMachine.check': 'RecordMachine',
    'Hypermath.RecordMachine.checkDecoded': 'RecordMachine',
    'Hypermath.RecordMachine.checkNumbers': 'RecordMachine',
    'Hypermath.RecordMachine.checkNumbers_agrees': 'RecordMachine',
    'Hypermath.RecordMachine.checkNumbers_codes': 'RecordMachine',
    'Hypermath.RecordMachine.checkNumbers_sound': 'RecordMachine',
    'Hypermath.RecordMachine.checkTrace': 'RecordMachine',
    'Hypermath.RecordMachine.checkTrace_iff': 'RecordMachine',
    'Hypermath.RecordMachine.checkTrace_quote': 'RecordMachine',
    'Hypermath.RecordMachine.checkTrace_sound': 'RecordMachine',
    'Hypermath.RecordMachine.checkTrace_trace': 'RecordMachine',
    'Hypermath.RecordMachine.check_agrees': 'RecordMachine',
    'Hypermath.RecordMachine.check_quote': 'RecordMachine',
    'Hypermath.RecordMachine.check_sound': 'RecordMachine',
    'Hypermath.RecordMachine.compiled_trace_length': 'RecordMachine',
    'Hypermath.RecordMachine.endpoint': 'RecordMachine',
    'Hypermath.RecordMachine.endpoint_trace': 'RecordMachine',
    'Hypermath.RecordMachine.execute': 'RecordMachine',
    'Hypermath.RecordMachine.execute_append': 'RecordMachine',
    'Hypermath.RecordMachine.execute_program': 'RecordMachine',
    'Hypermath.RecordMachine.nodeCount': 'RecordMachine',
    'Hypermath.RecordMachine.program': 'RecordMachine',
    'Hypermath.RecordMachine.program_length': 'RecordMachine',
    'Hypermath.RecordMachine.replace': 'RecordMachine',
    'Hypermath.RecordMachine.replay': 'RecordMachine',
    'Hypermath.RecordMachine.replay_iff': 'RecordMachine',
    'Hypermath.RecordMachine.replay_trace': 'RecordMachine',
    'Hypermath.RecordMachine.replay_unique': 'RecordMachine',
    'Hypermath.RecordMachine.step': 'RecordMachine',
    'Hypermath.RecordMachine.trace': 'RecordMachine',
    'Hypermath.RecordMachine.trace_length': 'RecordMachine',
    'Hypermath.RetainedExecution.Checks.composed': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.composed_frames_accepted': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.composed_frames_retained': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.encoded_erasure_still_decodes': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.erased': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.erased_composition_rejected': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.erased_frame_rejected': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.erased_history_rejected': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.erased_history_retained': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.erased_record_still_valid': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.first': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.firstRecord': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.incomplete': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.incomplete_frame_rejected': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.probe': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.repeated_frames_retained': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.second': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.secondRecord': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.wrongState': 'RetainedExecution',
    'Hypermath.RetainedExecution.Checks.wrong_state_rejected': 'RetainedExecution',
    'Hypermath.RetainedExecution.Surface': 'RetainedExecution',
    'Hypermath.RetainedExecution.accepted': 'RetainedExecution',
    'Hypermath.RetainedExecution.accepted_combine': 'RetainedExecution',
    'Hypermath.RetainedExecution.accepted_frame_sound': 'RetainedExecution',
    'Hypermath.RetainedExecution.check': 'RetainedExecution',
    'Hypermath.RetainedExecution.check_iterateLift': 'RetainedExecution',
    'Hypermath.RetainedExecution.check_lift': 'RetainedExecution',
    'Hypermath.RetainedExecution.check_seq': 'RetainedExecution',
    'Hypermath.RetainedExecution.checked_surface_sound': 'RetainedExecution',
    'Hypermath.RetainedExecution.composition_lift_preserves': 'RetainedExecution',
    'Hypermath.RetainedExecution.decode': 'RetainedExecution',
    'Hypermath.RetainedExecution.decode_encode': 'RetainedExecution',
    'Hypermath.RetainedExecution.encode': 'RetainedExecution',
    'Hypermath.RetainedExecution.finished_frame_check': 'RetainedExecution',
    'Hypermath.RetainedExecution.frameTree': 'RetainedExecution',
    'Hypermath.RetainedExecution.frameTree_injective': 'RetainedExecution',
    'Hypermath.RetainedExecution.inspect': 'RetainedExecution',
    'Hypermath.RetainedExecution.inspect_iterateLift': 'RetainedExecution',
    'Hypermath.RetainedExecution.inspect_lift': 'RetainedExecution',
    'Hypermath.RetainedExecution.inspect_seq': 'RetainedExecution',
    'Hypermath.RetainedExecution.instructionTree': 'RetainedExecution',
    'Hypermath.RetainedExecution.iterateLift': 'RetainedExecution',
    'Hypermath.RetainedExecution.lift': 'RetainedExecution',
    'Hypermath.RetainedExecution.liftMap': 'RetainedExecution',
    'Hypermath.RetainedExecution.lift_preserves_composition': 'RetainedExecution',
    'Hypermath.RetainedExecution.lowerAtom': 'RetainedExecution',
    'Hypermath.RetainedExecution.lowerAtom_lift': 'RetainedExecution',
    'Hypermath.RetainedExecution.payload': 'RetainedExecution',
    'Hypermath.RetainedExecution.readFrame': 'RetainedExecution',
    'Hypermath.RetainedExecution.readFrame_frameTree': 'RetainedExecution',
    'Hypermath.RetainedExecution.readInstruction': 'RetainedExecution',
    'Hypermath.RetainedExecution.readInstruction_instructionTree': 'RetainedExecution',
    'Hypermath.RetainedExecution.readPayload': 'RetainedExecution',
    'Hypermath.RetainedExecution.readPayload_payload': 'RetainedExecution',
    'Hypermath.RetainedExecution.record_only_protocol_rejected': 'RetainedExecution',
    'Hypermath.RetainedExecution.recoverThrough': 'RetainedExecution',
    'Hypermath.RetainedExecution.recoverThrough_iterateLift': 'RetainedExecution',
    'Hypermath.RetainedExecution.sequencing': 'RetainedExecution',
    'Hypermath.RetainedExecution.submitted_frame_check': 'RetainedExecution',
    'Hypermath.RetainedExecution.submitted_frame_recovered': 'RetainedExecution',
    'Hypermath.RetainedExecution.wrong_layer_rejected': 'RetainedExecution',
    'Hypermath.RuleSubstitution.Application.code': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.Application.instantiate': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.Application.run': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.Application.toTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.Application.tree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.Call.code': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.Call.toTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.Call.tree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.FormulaPattern.instantiate': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.RuleName.index': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.TermPattern.instantiate': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.call_toTerm_injective': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.check': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.check_agrees': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.check_quote': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.check_sound': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.compile': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.consume': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.decodeCall': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.decodeCall_code': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.decodeCall_toTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.decodeNumber': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.decodeTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.decode_code': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.decode_toTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedCheck': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedCheck_agrees': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedCheck_quote': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedCheck_sound': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedExecute': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedExecute_agrees': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedExecute_program': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedStep': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.encodedStep_agrees': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.execute': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.execute_agrees': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.execute_program': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.formula_code_rejected': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.instantiateAll': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.listTree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.no_rule_only_instantiation': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readApplication': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readApplication_tree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readCall': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readCall_tree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readList': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readList_listTree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readRule': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readRule_index': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readState': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.readState_stateTree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.record_code_rejected': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runCallNumber': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runCallNumber_code': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runCallTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runCallTerm_toTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runNumber': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runNumber_code': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.runTerm_toTerm': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.schema': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.stateTree': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.step': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.step_agrees': 'RuleSubstitution',
    'Hypermath.RuleSubstitution.toTerm_injective': 'RuleSubstitution',
    'Hypermath.Sequential.Commutative': 'Sequential',
    'Hypermath.Sequential.Noncommutative': 'Sequential',
    'Hypermath.Sequential.Program': 'Sequential',
    'Hypermath.Sequential.SourceOperationExists': 'Sequential',
    'Hypermath.Sequential.TwoSidedIdentity': 'Sequential',
    'Hypermath.Sequential.UniformSeparation': 'Sequential',
    'Hypermath.Sequential.distinct_nonempty_programs_commute': 'Sequential',
    'Hypermath.Sequential.firstProgram': 'Sequential',
    'Hypermath.Sequential.naturalSequencing': 'Sequential',
    'Hypermath.Sequential.natural_commutative': 'Sequential',
    'Hypermath.Sequential.natural_no_inverses': 'Sequential',
    'Hypermath.Sequential.no_source_operation': 'Sequential',
    'Hypermath.Sequential.no_uniform_separation': 'Sequential',
    'Hypermath.Sequential.programLength': 'Sequential',
    'Hypermath.Sequential.programSequencing': 'Sequential',
    'Hypermath.Sequential.program_associative': 'Sequential',
    'Hypermath.Sequential.program_composition_executes': 'Sequential',
    'Hypermath.Sequential.program_identity': 'Sequential',
    'Hypermath.Sequential.program_length_forgets_order': 'Sequential',
    'Hypermath.Sequential.program_length_not_faithful': 'Sequential',
    'Hypermath.Sequential.program_length_preserves_composition': 'Sequential',
    'Hypermath.Sequential.program_noncommutative': 'Sequential',
    'Hypermath.Sequential.program_not_commutative': 'Sequential',
    'Hypermath.Sequential.program_order_changes_result': 'Sequential',
    'Hypermath.Sequential.program_uniform_separation_fails': 'Sequential',
    'Hypermath.Sequential.secondProgram': 'Sequential',
    'Hypermath.Sequential.uniform_separation_double_negates_unit': 'Sequential',
    'Hypermath.Sequential.unit_commutes': 'Sequential',
    'Hypermath.SimulationEntry': 'L3Ordinatics',
    'Hypermath.SimulationStep': 'L3Ordinatics',
    'Hypermath.TerminalRetention.finished': 'TerminalRetention',
    'Hypermath.TerminalRetention.finished_check': 'TerminalRetention',
    'Hypermath.TerminalRetention.finished_fixed': 'TerminalRetention',
    'Hypermath.TerminalRetention.finished_record': 'TerminalRetention',
    'Hypermath.TerminalRetention.merged_fixed_states': 'TerminalRetention',
    'Hypermath.TerminalRetention.run_fixed': 'TerminalRetention',
    'Hypermath.Trace.compose': 'Trace',
    'Hypermath.Trace.compose_assoc': 'Trace',
    'Hypermath.Trace.edges': 'Trace',
    'Hypermath.Trace.length': 'Trace',
    'Hypermath.Trace.eq_of_length_zero': 'Trace',
    'Hypermath.Trace.uncons_of_length_succ': 'Trace',
    'Hypermath.Trace.map': 'Trace',
    'Hypermath.TraceExpr.edges_expand_seq': 'Trace',
    'Hypermath.TraceExpr.expand': 'Trace',
    'Hypermath.TraceExpr.length': 'Trace',
    'Hypermath.TrajectoryHomotopy': 'QuadrilateralFiltration',
    'Hypermath.UnaryFormation.IgnoresFirst': 'UnaryFormation',
    'Hypermath.UnaryFormation.IgnoresSecond': 'UnaryFormation',
    'Hypermath.UnaryFormation.Term.eval': 'UnaryFormation',
    'Hypermath.UnaryFormation.eval_ignores_an_input': 'UnaryFormation',
    'Hypermath.UnaryFormation.identity_collapses_relation': 'UnaryFormation',
    'Hypermath.UnaryFormation.natural_add_not_a_term': 'UnaryFormation',
    'Hypermath.UnaryFormation.no_term_identity': 'UnaryFormation',
    'Hypermath.UnaryFormation.no_term_pair_encoder': 'UnaryFormation',
    'Hypermath.UnaryFormation.pair_recovery_collapses': 'UnaryFormation',
    'Hypermath.UnaryFormation.singleton_term_identity': 'UnaryFormation',
    'Hypermath.UnaryFormation.universal_relation_term_identity': 'UnaryFormation',
    'Hypermath.abstractedFromAgreesOnDerives': 'QuadrilateralFiltration',
    'Hypermath.abstractedNotCongruentAtCycle': 'QuadrilateralFiltration',
    'Hypermath.abstractedRefl': 'QuadrilateralFiltration',
    'Hypermath.abstractedSymm': 'QuadrilateralFiltration',
    'Hypermath.abstractedTrans': 'QuadrilateralFiltration',
    'Hypermath.additionallyStaysSimilar': 'L2Operations',
    'Hypermath.afaDecorationUniqueness': 'QuadrilateralFiltration',
    'Hypermath.apgBisimulation': 'QuadrilateralFiltration',
    'Hypermath.apgDecoration': 'QuadrilateralFiltration',
    'Hypermath.applyGroundContinues': 'L0Ground',
    'Hypermath.applyGroundIsCongruentToItself': 'L0Ground',
    'Hypermath.applyGroundIsDistinct': 'L0Ground',
    'Hypermath.axBoxInRelationLanguage': 'L1Relations',
    'Hypermath.axDeriverAtLimit': 'L3Ordinatics',
    'Hypermath.axDiffInRelationLanguage': 'L1Relations',
    'Hypermath.axLimitDerives': 'L3Ordinatics',
    'Hypermath.axLimitIsLimit': 'L3Ordinatics',
    'Hypermath.axLimitNotFinite': 'L3Ordinatics',
    'Hypermath.axSimInRelationLanguage': 'L1Relations',
    'Hypermath.axSuccExtends': 'L3Ordinatics',
    'Hypermath.classProjection': 'QuadrilateralFiltration',
    'Hypermath.commonWitnessesComeFromCommutativity': 'L2Operations',
    'Hypermath.compositionLengthAdditiveClaim': 'L2Operations',
    'Hypermath.compositionalityChain3': 'QuadrilateralFiltration',
    'Hypermath.compositionalityChain3Quanta': 'QuadrilateralFiltration',
    'Hypermath.congruentFromPathRefines': 'QuadrilateralFiltration',
    'Hypermath.congruentPathInternals': 'L3Ordinatics',
    'Hypermath.congruentProfileFactorsThroughAbstraction': 'QuadrilateralFiltration',
    'Hypermath.cyclicalCompletion': 'QuadrilateralFiltration',
    'Hypermath.dEntryCompose': 'L1Relations',
    'Hypermath.dEntryEqOrCongruent': 'L2Operations',
    'Hypermath.dEntryEndpointIteration': 'L1Relations',
    'Hypermath.dEntryFromGroundFinite': 'L3Ordinatics',
    'Hypermath.dEntryLengthAdditive': 'L2Operations',
    'Hypermath.dEntryNoSteps': 'L1Relations',
    'Hypermath.dEntryStep': 'L1Relations',
    'Hypermath.dEntryStepLength': 'L1Relations',
    'Hypermath.dExprToDerives': 'QuadrilateralFiltration',
    'Hypermath.dExprToDerivesIn': 'QuadrilateralFiltration',
    'Hypermath.dForgetsQuanta': 'L1Relations',
    'Hypermath.dIsReflexive': 'L1Relations',
    'Hypermath.dIsTransitive': 'L1Relations',
    'Hypermath.definitionIsAbstractionTier': 'L1Relations',
    'Hypermath.definitionOfGround': 'L0Ground',
    'Hypermath.definitionOfGround_L1': 'L1Relations',
    'Hypermath.deriverExtends': 'L3Ordinatics',
    'Hypermath.deriverIsLeastUpperBound': 'L3Ordinatics',
    'Hypermath.deriverNotFinite': 'L3Ordinatics',
    'Hypermath.deriverNotInD': 'L3Ordinatics',
    'Hypermath.deriverReachedByLimitPath': 'L3Ordinatics',
    'Hypermath.derivesForgetsQuanta': 'L1Relations',
    'Hypermath.derivesInToDerives': 'L1Relations',
    'Hypermath.derivesIsAbstractionOfDerivesIn': 'L1Relations',
    'Hypermath.derivesIsDirectional': 'L1Relations',
    'Hypermath.derivesIsDirectional_FRAME': 'L0Ground',
    'Hypermath.derivesLosesQuanta': 'QuadrilateralFiltration',
    'Hypermath.dischargeIsAbstractionTier': 'L1Relations',
    'Hypermath.doubleApplyGroundOrbits': 'L0Ground',
    'Hypermath.driverCycleClaim': 'L1Relations',
    'Hypermath.driverCycleWitnessOfSteps': 'L3Ordinatics',
    'Hypermath.driverCycleWitness_exists_of_steps': 'L3Ordinatics',
    'Hypermath.driverInDAtSimulationOfCycle': 'L3Ordinatics',
    'Hypermath.driverIsInD': 'L1Relations',
    'Hypermath.emptyRealizer': 'QuadrilateralFiltration',
    'Hypermath.exactFiniteAction_implies_compatible': 'FiniteAction',
    'Hypermath.f2fGroundNeGround': 'L1Relations',
    'Hypermath.filtrationConditionsHold': 'L1Relations',
    'Hypermath.finiteActionCompatible_iff_exists_exact': 'FiniteAction',
    'Hypermath.finiteApplyClosed': 'L3Ordinatics',
    'Hypermath.finiteApplyFromGround': 'L3Ordinatics',
    'Hypermath.finiteApplyGround': 'L3Ordinatics',
    'Hypermath.finiteApplyIffIteration': 'L3Ordinatics',
    'Hypermath.finiteApplyIterationAdd': 'L3Ordinatics',
    'Hypermath.finiteApplyLimitExcluded': 'L3Ordinatics',
    'Hypermath.finiteApplyMinimal': 'L3Ordinatics',
    'Hypermath.finiteApplyPosition': 'L3Ordinatics',
    'Hypermath.finiteApplyPositionMember': 'L3Ordinatics',
    'Hypermath.finiteApplyPositionSimulation': 'L3Ordinatics',
    'Hypermath.finiteNumeralEq_action_on_finite_orbit': 'FiniteAction',
    'Hypermath.finiteNumeralEq_add': 'FiniteAction',
    'Hypermath.finiteNumeralEq_iff_generic': 'FiniteAction',
    'Hypermath.finiteNumeralEq_mul': 'FiniteAction',
    'Hypermath.finiteNumeralEqualityExact_iff_injective': 'FiniteAction',
    'Hypermath.finiteOrbitDecode': 'FiniteAction',
    'Hypermath.finiteOrbitDecode_spec': 'FiniteAction',
    'Hypermath.finiteOrbitEncode': 'FiniteAction',
    'Hypermath.finiteOrbitEncode_surjective': 'FiniteAction',
    'Hypermath.finiteOrbitEquivalence': 'FiniteAction',
    'Hypermath.finiteOrbitEquivalence_laws': 'FiniteAction',
    'Hypermath.finiteOrbitInjective_implies_actionCompatible': 'FiniteAction',
    'Hypermath.finitePathExists': 'L2Operations',
    'Hypermath.finiteTraceLength': 'L3Ordinatics',
    'Hypermath.finiteTraceLengthCompose': 'L3Ordinatics',
    'Hypermath.finiteTraceLengthExpand': 'L3Ordinatics',
    'Hypermath.finiteTraceLengthExpandSeq': 'L3Ordinatics',
    'Hypermath.finiteTraceLengthMember': 'L3Ordinatics',
    'Hypermath.finiteTraceLengthSelfRead': 'L3Ordinatics',
    'Hypermath.finiteTraceLengthStep': 'L3Ordinatics',
    'Hypermath.fractalSubformMembership': 'QuadrilateralFiltration',
    'Hypermath.globalCongruentReflexivityIsCofinality': 'L1Relations',
    'Hypermath.groundDoesNotSimulateDeriver': 'L3Ordinatics',
    'Hypermath.groundFixedPoint': 'L1Relations',
    'Hypermath.groundIsCongruentToItself': 'L1Relations',
    'Hypermath.groundIsFormClosed': 'L0Ground',
    'Hypermath.groundSimulatesItself': 'L1Relations',
    'Hypermath.groundSpanningClaim': 'L1Relations',
    'Hypermath.hostFiniteAction': 'FiniteAction',
    'Hypermath.hostFiniteAction_exact': 'FiniteAction',
    'Hypermath.instantiateMetamathTheorem': 'QuadrilateralFiltration',
    'Hypermath.memOrdinatics': 'QuadrilateralFiltration',
    'Hypermath.nc1_L0': 'L0Ground',
    'Hypermath.nc1_L1': 'L1Relations',
    'Hypermath.nc1_L2': 'L2Operations',
    'Hypermath.nc2_L0': 'L0Ground',
    'Hypermath.nc2_L1': 'L1Relations',
    'Hypermath.nc2_L2': 'L2Operations',
    'Hypermath.nc3_L0': 'L0Ground',
    'Hypermath.nc3_L2': 'L2Operations',
    'Hypermath.nc4_L0': 'L0Ground',
    'Hypermath.nc4_L1': 'L1Relations',
    'Hypermath.nc4_L2': 'L2Operations',
    'Hypermath.noFiniteObstructionAtDeriver': 'L3Ordinatics',
    'Hypermath.noFinitePositionSimulatesDeriver': 'L3Ordinatics',
    'Hypermath.no_driver_cycle_witness_at_finite_successor': 'L3Ordinatics',
    'Hypermath.no_simulation_step_at_finite_of_successor_agreement': 'L3Ordinatics',
    'Hypermath.notGroundSpanningClaim': 'L3Ordinatics',
    'Hypermath.orbitHasReturn': 'L0Ground',
    'Hypermath.orbitReflexionHypothesisIsAbstraction': 'QuadrilateralFiltration',
    'Hypermath.orbitReflexionQuotient': 'L2Operations',
    'Hypermath.orbitStructure': 'L1Relations',
    'Hypermath.ordinalApply': 'L3Ordinatics',
    'Hypermath.ordinalApplyUnconstrained': 'L3Ordinatics',
    'Hypermath.ordinalLimit': 'L3Ordinatics',
    'Hypermath.ordinalLimitNotInD': 'L3Ordinatics',
    'Hypermath.ordinalSucc': 'L3Ordinatics',
    'Hypermath.ordinalSuccAppliesClaim': 'L3Ordinatics',
    'Hypermath.ordinalZeroIdentityClaim': 'L3Ordinatics',
    'Hypermath.pathGroundIsIdentity': 'L2Operations',
    'Hypermath.pathLengthArithmeticClaim': 'L3Ordinatics',
    'Hypermath.plusAndAdditionallyAreDistinct': 'L2Operations',
    'Hypermath.plusStaysSimilar': 'L2Operations',
    'Hypermath.quantaAdditive': 'QuadrilateralFiltration',
    'Hypermath.quineAtomSelfMembership': 'QuadrilateralFiltration',
    'Hypermath.realize': 'QuadrilateralFiltration',
    'Hypermath.realizeSelf': 'QuadrilateralFiltration',
    'Hypermath.reflexion': 'L2Operations',
    'Hypermath.reflexionTrace': 'L2Operations',
    'Hypermath.reflexionTraceComposeIdentity': 'L2Operations',
    'Hypermath.reflexivityIsGroundReachability': 'L1Relations',
    'Hypermath.reflexivityLevelsCoincide': 'L1Relations',
    'Hypermath.repeatApplyInner': 'L0Ground',
    'Hypermath.retraceAssoc': 'QuadrilateralFiltration',
    'Hypermath.retraceCanFail': 'QuadrilateralFiltration',
    'Hypermath.retraceSelfIdentity': 'QuadrilateralFiltration',
    'Hypermath.retraceSeq': 'QuadrilateralFiltration',
    'Hypermath.retraceSound': 'QuadrilateralFiltration',
    'Hypermath.selfDerivation': 'L3Ordinatics',
    'Hypermath.selfDerivationOfCycle': 'L3Ordinatics',
    'Hypermath.selfDerivationOfWitness': 'L3Ordinatics',
    'Hypermath.selfDerivation_iff_driverCycleClaim': 'L3Ordinatics',
    'Hypermath.selfRead': 'L1Relations',
    'Hypermath.selfReadLength': 'L1Relations',
    'Hypermath.sequencingClausesAreCooperationClauses': 'L2Operations',
    'Hypermath.similarClosureIsTotal': 'QuadrilateralFiltration',
    'Hypermath.similarClosureToGround': 'QuadrilateralFiltration',
    'Hypermath.similarReflexive': 'L1Relations',
    'Hypermath.similarSymmetric': 'L1Relations',
    'Hypermath.simulationDeniesEveryImageAtGround': 'L1Relations',
    'Hypermath.simulationEntryToDEntry': 'L3Ordinatics',
    'Hypermath.simulationEntryToDEntry_length': 'L3Ordinatics',
    'Hypermath.simulationPairExistsClaim': 'L3Ordinatics',
    'Hypermath.simulationPairExists_L1': 'L1Relations',
    'Hypermath.simulation_trace_from_finite_is_empty': 'L3Ordinatics',
    'Hypermath.trajectoryCompose': 'QuadrilateralFiltration',
    'Hypermath.trajectoryIdentity': 'QuadrilateralFiltration',
    'Hypermath.triangleVerticesCoincide': 'L1Relations',
    'Hypermath.twoMembersInClass': 'L0Ground',
    'Hypermath.upperReflexivitiesAndReachabilityAgree': 'L1Relations',
    'Hypermath.witness_has_two_D_steps': 'L3Ordinatics',
    'HypermathNondegenerateCycleModel.Congruent': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.Definition': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.DerivationPath': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.Derives': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.Discharge': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.FormClosure': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.HMSyntax': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.InLimitCycle': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.Semantics': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.Similar': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.Simulation': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.SimulationEntry': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.SimulationStep': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.Substance': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.apply_moves_the_deriver': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.compose': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.congruentPath': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.cycleWitness': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.cycle_has_two_steps': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.deriver': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.driverCycleClaim': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.f2f': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.finite_position_outside': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.forming_stays_outside': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.full_axioms_hold': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.ground': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.nondegenerate_cycle_with_all_clauses': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.nondegenerate_violates_axDiffCongruent': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.ordinalLimit': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.ordinalSucc': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.pathEnd': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.pathGround': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.pathStart': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.semanticClass': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.simulation_limit_iff': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.structContinues': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.structDistinct': 'NondegenerateCycle',
    'HypermathNondegenerateCycleModel.structOrbits': 'NondegenerateCycle',
    'HypermathTransportCountermodel.Congruent': 'TransportCountermodel',
    'HypermathTransportCountermodel.D': 'TransportCountermodel',
    'HypermathTransportCountermodel.DEntry': 'TransportCountermodel',
    'HypermathTransportCountermodel.DStep': 'TransportCountermodel',
    'HypermathTransportCountermodel.Definition': 'TransportCountermodel',
    'HypermathTransportCountermodel.DerivationPath': 'TransportCountermodel',
    'HypermathTransportCountermodel.Derives': 'TransportCountermodel',
    'HypermathTransportCountermodel.Discharge': 'TransportCountermodel',
    'HypermathTransportCountermodel.FormClosure': 'TransportCountermodel',
    'HypermathTransportCountermodel.HMSyntax': 'TransportCountermodel',
    'HypermathTransportCountermodel.InCycle': 'TransportCountermodel',
    'HypermathTransportCountermodel.NativeOneStepLaw': 'TransportCountermodel',
    'HypermathTransportCountermodel.Semantics': 'TransportCountermodel',
    'HypermathTransportCountermodel.Similar': 'TransportCountermodel',
    'HypermathTransportCountermodel.Simulation': 'TransportCountermodel',
    'HypermathTransportCountermodel.SimulationEntry': 'TransportCountermodel',
    'HypermathTransportCountermodel.SimulationStep': 'TransportCountermodel',
    'HypermathTransportCountermodel.Substance': 'TransportCountermodel',
    'HypermathTransportCountermodel.compose': 'TransportCountermodel',
    'HypermathTransportCountermodel.congruentPath': 'TransportCountermodel',
    'HypermathTransportCountermodel.congruent_is_total': 'TransportCountermodel',
    'HypermathTransportCountermodel.cycleForm': 'TransportCountermodel',
    'HypermathTransportCountermodel.cycleWitness': 'TransportCountermodel',
    'HypermathTransportCountermodel.cycle_has_two_steps': 'TransportCountermodel',
    'HypermathTransportCountermodel.deriver': 'TransportCountermodel',
    'HypermathTransportCountermodel.deriver_is_not_finite': 'TransportCountermodel',
    'HypermathTransportCountermodel.distinctOperationsClaim': 'TransportCountermodel',
    'HypermathTransportCountermodel.distinct_operations_claim_fails': 'TransportCountermodel',
    'HypermathTransportCountermodel.driverCycleClaim': 'TransportCountermodel',
    'HypermathTransportCountermodel.f2f': 'TransportCountermodel',
    'HypermathTransportCountermodel.finiteApplyFromGround': 'TransportCountermodel',
    'HypermathTransportCountermodel.finiteApplyPosition': 'TransportCountermodel',
    'HypermathTransportCountermodel.finite_position_not_limit': 'TransportCountermodel',
    'HypermathTransportCountermodel.forming_preserves_not_limit': 'TransportCountermodel',
    'HypermathTransportCountermodel.full_axioms_hold': 'TransportCountermodel',
    'HypermathTransportCountermodel.full_model_with_cycle_without_reproduction': 'TransportCountermodel',
    'HypermathTransportCountermodel.ground': 'TransportCountermodel',
    'HypermathTransportCountermodel.native_one_step_law_fails': 'TransportCountermodel',
    'HypermathTransportCountermodel.no_finite_reproduction': 'TransportCountermodel',
    'HypermathTransportCountermodel.no_incongruence_is_derivable': 'TransportCountermodel',
    'HypermathTransportCountermodel.no_step_transfer': 'TransportCountermodel',
    'HypermathTransportCountermodel.nothing_separates_the_two_operations': 'TransportCountermodel',
    'HypermathTransportCountermodel.ordinalApply': 'TransportCountermodel',
    'HypermathTransportCountermodel.ordinalLimit': 'TransportCountermodel',
    'HypermathTransportCountermodel.ordinalSucc': 'TransportCountermodel',
    'HypermathTransportCountermodel.pathEnd': 'TransportCountermodel',
    'HypermathTransportCountermodel.pathGround': 'TransportCountermodel',
    'HypermathTransportCountermodel.pathLength': 'TransportCountermodel',
    'HypermathTransportCountermodel.pathStart': 'TransportCountermodel',
    'HypermathTransportCountermodel.pathStep': 'TransportCountermodel',
    'HypermathTransportCountermodel.pathTrace': 'TransportCountermodel',
    'HypermathTransportCountermodel.path_stays_in_cycle': 'TransportCountermodel',
    'HypermathTransportCountermodel.probe': 'TransportCountermodel',
    'HypermathTransportCountermodel.related_starts_are_ground_generated': 'TransportCountermodel',
    'HypermathTransportCountermodel.selfDerivation': 'TransportCountermodel',
    'HypermathTransportCountermodel.self_derivation_holds': 'TransportCountermodel',
    'HypermathTransportCountermodel.semanticClass': 'TransportCountermodel',
    'HypermathTransportCountermodel.sequencing_asymmetry_never_applies': 'TransportCountermodel',
    'HypermathTransportCountermodel.transport_violates_axDiffCongruent': 'TransportCountermodel',
    'HypermathTransportCountermodel.simulation_is_equivalence': 'TransportCountermodel',
    'HypermathTransportCountermodel.simulation_limit_iff': 'TransportCountermodel',
    'HypermathTransportCountermodel.step_stays_in_cycle': 'TransportCountermodel',
    'HypermathTransportCountermodel.structContinues': 'TransportCountermodel',
    'HypermathTransportCountermodel.structDistinct': 'TransportCountermodel',
    'HypermathTransportCountermodel.structOrbits': 'TransportCountermodel',
    'HypermathTransportCountermodel.unmatchedStep': 'TransportCountermodel',
}
