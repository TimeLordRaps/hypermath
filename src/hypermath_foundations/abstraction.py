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

"""Quadrilateral Filtration and Transitive Abstraction Layer (~=).

Formalizes the four-node commutative/re-entrant diagram:

                            [ Abstraction (~=) ]
                           ↗                    \\
                          /                      \\  Conditional Retrace
                         /                        \\  around Substance
            (off-branch)/                          ↘
        [ Syntax (~~) ] ───────────────────────────> [ Semantics (==) ]
                        \\                          ↗
                         \\                        /
                          \\                      /
                           ↘                    /
                            [ Substance (=~) ]

Bridging Syntax -> Abstraction -> Semantics conditioned on physical/operational
substance realizability witnesses.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from enum import Enum
from typing import Any


class FiltrationTier(str, Enum):
    """The four nodes in the quadrilateral filtration diagram."""

    SYNTAX = "syntax"              # ~~ (continuation similarity, structural prefix)
    SUBSTANCE = "substance"        # =~ (operational trace conservation, physical energy/steps)
    SEMANTICS = "semantics"        # == (behavioral simulation identity)
    ABSTRACTION = "abstraction"    # ~= (transitive structural/algebraic abstraction)


class FiltrationRetraceError(ValueError):
    """Raised when an abstraction cannot retrace to semantics due to invalid substance witness."""


@dataclass(frozen=True)
class FormTerm:
    """Foundational term representation in the Hypermath term algebra."""

    symbol: str
    args: tuple[FormTerm, ...] = field(default_factory=tuple)

    @classmethod
    def ground(cls) -> FormTerm:
        return cls("ground")

    @classmethod
    def f2f(cls, inner: FormTerm) -> FormTerm:
        return cls("f2f", (inner,))

    @classmethod
    def box(cls, inner: FormTerm) -> FormTerm:
        return cls("box", (inner,))

    @classmethod
    def compose(cls, left: FormTerm, right: FormTerm) -> FormTerm:
        return cls("compose", (left, right))

    @classmethod
    def var(cls, name: str) -> FormTerm:
        return cls(f"var:{name}")

    def is_variable(self) -> bool:
        return self.symbol.startswith("var:")

    def depth(self) -> int:
        if not self.args:
            return 0
        return 1 + max(arg.depth() for arg in self.args)

    def size(self) -> int:
        return 1 + sum(arg.size() for arg in self.args)

    def digest(self) -> str:
        payload = json.dumps(self.to_dict(), sort_keys=True).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()

    def to_dict(self) -> dict[str, Any]:
        return {
            "symbol": self.symbol,
            "args": [arg.to_dict() for arg in self.args],
        }

    @classmethod
    def from_dict(cls, data: dict[str, Any]) -> FormTerm:
        return cls(
            symbol=data["symbol"],
            args=tuple(cls.from_dict(arg) for arg in data.get("args", [])),
        )

    def __str__(self) -> str:
        if not self.args:
            return self.symbol
        inner = ", ".join(str(a) for a in self.args)
        return f"{self.symbol}({inner})"


@dataclass(frozen=True)
class SubstanceWitness:
    """Certification that an abstract identity is physically or operationally realizable.

    Carries energy/matter bounds, step counts, and an invariant certificate.
    """

    source_digest: str
    target_digest: str
    step_count: int
    energy_bound: int
    state_trace: tuple[str, ...]
    is_valid: bool = True

    def verify_conservation(self) -> bool:
        """Substance (=~) requires non-negative steps, bounded energy, and valid certificate."""
        return (
            self.is_valid
            and isinstance(self.step_count, int)
            and isinstance(self.energy_bound, int)
            and self.step_count >= 0
            and self.energy_bound >= self.step_count
            and len(self.state_trace) == self.step_count + 1
            and not (self.step_count == 0 and self.source_digest != self.target_digest)
        )


@dataclass(frozen=True)
class AbstractionProof:
    """Formal proof of transitive abstraction equivalence (lhs ~= rhs)."""

    lhs: FormTerm
    rhs: FormTerm
    rule_name: str
    justification: str
    premises: tuple[AbstractionProof, ...] = field(default_factory=tuple)

    def verify(self) -> bool:
        """Verify the abstraction equivalence proof."""
        if self.rule_name == "reflexive":
            return self.lhs == self.rhs
        if self.rule_name == "symmetric":
            return (
                len(self.premises) == 1
                and self.premises[0].verify()
                and self.premises[0].lhs == self.rhs
                and self.premises[0].rhs == self.lhs
            )
        if self.rule_name == "transitive":
            if len(self.premises) != 2:
                return False
            p1, p2 = self.premises
            return (
                p1.verify()
                and p2.verify()
                and p1.lhs == self.lhs
                and p1.rhs == p2.lhs
                and p2.rhs == self.rhs
            )
        if self.rule_name == "syntax_off_branch":
            # Syntax (~~) lifts into Abstraction (~=)
            return QuadrilateralFiltration.syntax_similarity(self.lhs, self.rhs)
        if self.rule_name == "schema_congruence":
            if self.lhs == self.rhs:
                return True
            if self.lhs.is_variable() or self.rhs.is_variable():
                return True
            return len(self.lhs.args) == len(self.rhs.args)
        return False


@dataclass(frozen=True)
class SemanticEquivalence:
    """Result of conditional retrace: full mutual simulation semantics (lhs == rhs)."""

    lhs: FormTerm
    rhs: FormTerm
    abstraction_proof: AbstractionProof
    substance_witness: SubstanceWitness
    certified: bool

    def is_sound(self) -> bool:
        return (
            self.certified
            and self.abstraction_proof.verify()
            and self.substance_witness.verify_conservation()
            and self.abstraction_proof.lhs.digest() == self.substance_witness.source_digest
            and self.abstraction_proof.rhs.digest() == self.substance_witness.target_digest
        )


class QuadrilateralFiltration:
    """Engine executing the quadrilateral filtration and abstraction layer."""

    @staticmethod
    def syntax_similarity(a: FormTerm, b: FormTerm) -> bool:
        """Syntax continuation similarity (~~). Reflexive, symmetric, non-transitive."""
        if a == b:
            return True
        # Structural continuation: share root operator or match variable pattern
        if a.is_variable() or b.is_variable():
            return True
        return a.symbol == b.symbol and len(a.args) == len(b.args)

    @classmethod
    def syntax_to_abstraction(cls, a: FormTerm, b: FormTerm) -> AbstractionProof:
        """Off-branch translation: Syntax (~~) -> Abstraction (~=).

        Lifts continuation similarity into an abstract equivalence class.
        """
        if not cls.syntax_similarity(a, b):
            raise ValueError(f"Terms {a} and {b} do not satisfy continuation syntax (~~)")
        return AbstractionProof(
            lhs=a,
            rhs=b,
            rule_name="syntax_off_branch",
            justification=f"Off-branch lifted from syntax similarity: {a} ~~ {b}",
        )

    @staticmethod
    def abstraction_reflexive(term: FormTerm) -> AbstractionProof:
        """Reflexivity: forall x, x ~= x."""
        return AbstractionProof(
            lhs=term,
            rhs=term,
            rule_name="reflexive",
            justification=f"Reflexive abstraction: {term} ~= {term}",
        )

    @staticmethod
    def abstraction_symmetric(proof: AbstractionProof) -> AbstractionProof:
        """Symmetry: x ~= y implies y ~= x."""
        if not proof.verify():
            raise ValueError("Premise proof is not valid")
        return AbstractionProof(
            lhs=proof.rhs,
            rhs=proof.lhs,
            rule_name="symmetric",
            justification=f"Symmetric abstraction from {proof.lhs} ~= {proof.rhs}",
            premises=(proof,),
        )

    @staticmethod
    def abstraction_transitive(p1: AbstractionProof, p2: AbstractionProof) -> AbstractionProof:
        """Strict transitivity: (a ~= b) and (b ~= c) implies (a ~= c)."""
        if not p1.verify() or not p2.verify():
            raise ValueError("One or both premise proofs are invalid")
        if p1.rhs != p2.lhs:
            raise ValueError(
                f"Transitivity mismatch: intermediate terms differ ({p1.rhs} != {p2.lhs})"
            )
        return AbstractionProof(
            lhs=p1.lhs,
            rhs=p2.rhs,
            rule_name="transitive",
            justification=f"Transitive abstraction: {p1.lhs} ~= {p1.rhs} and {p2.lhs} ~= {p2.rhs}",
            premises=(p1, p2),
        )

    @staticmethod
    def conditional_retrace(
        proof: AbstractionProof, witness: SubstanceWitness
    ) -> SemanticEquivalence:
        """Conditional retrace around substance: (x ~= y) and W_substance(x, y) => (x == y).

        Connects abstraction directly back to semantics conditioned on substance realizability.
        Fails closed if the witness is invalid or violates conservation laws.
        """
        if not proof.verify():
            raise FiltrationRetraceError("Abstraction proof is invalid; retrace rejected")
        if not witness.verify_conservation():
            raise FiltrationRetraceError(
                "Substance witness failed conservation; retrace around substance rejected"
            )
        if proof.lhs.digest() != witness.source_digest or proof.rhs.digest() != witness.target_digest:
            raise FiltrationRetraceError(
                "Substance witness endpoints do not bind to abstraction proof digests"
            )
        return SemanticEquivalence(
            lhs=proof.lhs,
            rhs=proof.rhs,
            abstraction_proof=proof,
            substance_witness=witness,
            certified=True,
        )


class AbstractionChain:
    """Downstream compositionality: chaining transitive abstraction steps.

    Macro-lemmas and rewrites compose algebraically:
    (P0 ~= P1) o (P1 ~= P2) o ... o (Pn-1 ~= Pn) => (P0 ~= Pn)
    without carrying intermediate operational run-time traces.
    """

    def __init__(self, initial_term: FormTerm) -> None:
        self.current_term = initial_term
        self.start_term = initial_term
        self.steps: list[AbstractionProof] = []

    def extend(self, next_term: FormTerm, rule_name: str = "schema_congruence") -> AbstractionChain:
        step_proof = AbstractionProof(
            lhs=self.current_term,
            rhs=next_term,
            rule_name=rule_name,
            justification=f"Chain step {len(self.steps) + 1}: {self.current_term} ~= {next_term}",
        )
        self.steps.append(step_proof)
        self.current_term = next_term
        return self

    def collapse(self) -> AbstractionProof:
        """Collapse the entire composition chain into a single transitive AbstractionProof."""
        if not self.steps:
            return QuadrilateralFiltration.abstraction_reflexive(self.start_term)
        result = self.steps[0]
        for next_step in self.steps[1:]:
            result = QuadrilateralFiltration.abstraction_transitive(result, next_step)
        return result

    def length(self) -> int:
        return len(self.steps)
