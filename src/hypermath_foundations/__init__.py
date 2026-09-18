# Copyright 2026 Tyler Roost / TimeLordRaps
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

"""Audit Hypermath proof evidence and formal foundational meta-features."""

from .abstraction import (
    AbstractionChain,
    AbstractionProof,
    FiltrationRetraceError,
    FiltrationTier,
    FormTerm,
    QuadrilateralFiltration,
    SemanticEquivalence,
    SubstanceWitness,
)
from .audit import run_audit
from .calculus_bridge import (
    HyperCalculus,
    LanguageCalculus,
    MathCalculus,
    MetaCalculus,
    MetamathDatabase,
    OrdinalCalculus,
    form_to_metamath,
)
from .gate import evaluate_gate
from .meta_fractal import (
    AccessiblePointedGraph,
    ConstructiveMembership,
    Hyperkernel,
    OrdinalPolynomial,
    QuineAtom,
)
from .objectification import (
    ObjectificationError,
    ObjectifiedClass,
    ProofTrajectory,
    TrajectoryHomotopy,
    TrajectoryStep,
)

__version__ = "0.1.0"
__all__ = [
    "AbstractionChain",
    "AbstractionProof",
    "AccessiblePointedGraph",
    "ConstructiveMembership",
    "FiltrationRetraceError",
    "FiltrationTier",
    "FormTerm",
    "HyperCalculus",
    "Hyperkernel",
    "LanguageCalculus",
    "MathCalculus",
    "MetaCalculus",
    "MetamathDatabase",
    "ObjectifiedClass",
    "ObjectificationError",
    "OrdinalCalculus",
    "OrdinalPolynomial",
    "ProofTrajectory",
    "QuadrilateralFiltration",
    "QuineAtom",
    "SemanticEquivalence",
    "SubstanceWitness",
    "TrajectoryHomotopy",
    "TrajectoryStep",
    "evaluate_gate",
    "form_to_metamath",
    "run_audit",
]
