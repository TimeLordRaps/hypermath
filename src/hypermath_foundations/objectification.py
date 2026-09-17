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

"""Objectification: Lifting Equivalence Classes and Proof Trajectories into First-Class Algebra.

In orthodox metatheory, equivalence classes and proof trajectories are external
metalogical constructs. Under Objectification, they are reified into first-class
mathematical objects within the foundational algebra, forming a 2-category structure:
  - 0-cells: Foundational Forms / Terms
  - 1-cells: Proof Trajectories (Derivation Paths with Associative Composition)
  - 2-cells: Trajectory Homotopies (Algebraic Commutation of Derivations)
"""

from __future__ import annotations

import collections
import hashlib
import json
from dataclasses import dataclass, field
from typing import Any, Callable, Sequence, TypeVar

from .abstraction import FormTerm

T = TypeVar("T")


class ObjectificationError(ValueError):
    """Raised when an objectification or trajectory operation is invalid."""


@dataclass(frozen=True)
class ObjectifiedClass:
    """An equivalence class lifted into a first-class mathematical object.

    Represents [x]_R with a canonical representative, member set, and relation binding.
    Satisfies the universal property of the quotient: any morphism constant on classes
    factors uniquely through the canonical quotient projection pi: X -> X / R.
    """

    representative: FormTerm
    relation_name: str
    members: frozenset[FormTerm] = field(default_factory=frozenset)
    invariants: tuple[tuple[str, Any], ...] = field(default_factory=tuple)

    def __post_init__(self) -> None:
        if self.representative not in self.members:
            # Ensure representative is always included in member set
            object.__setattr__(
                self, "members", self.members | frozenset([self.representative])
            )

    def contains(self, term: FormTerm) -> bool:
        return term in self.members

    def add_member(self, term: FormTerm) -> ObjectifiedClass:
        return ObjectifiedClass(
            representative=self.representative,
            relation_name=self.relation_name,
            members=self.members | frozenset([term]),
            invariants=self.invariants,
        )

    def direct_product(self, other: ObjectifiedClass) -> ObjectifiedClass:
        """Tensor / Direct product of two objectified classes: [x] (x) [y] = [(x, y)]."""
        prod_rep = FormTerm.compose(self.representative, other.representative)
        prod_members = frozenset(
            FormTerm.compose(m1, m2) for m1 in self.members for m2 in other.members
        )
        return ObjectifiedClass(
            representative=prod_rep,
            relation_name=f"{self.relation_name}_x_{other.relation_name}",
            members=prod_members,
            invariants=self.invariants + other.invariants,
        )

    def factor_morphism(self, morphism: Callable[[FormTerm], T]) -> T:
        """Evaluate a morphism that factors through the quotient class.

        Universal Property: phi([x]) = f(x).
        """
        # Morphism must be constant on all members
        rep_val = morphism(self.representative)
        for m in self.members:
            if morphism(m) != rep_val:
                raise ObjectificationError(
                    f"Morphism {morphism} is not well-defined on equivalence class: "
                    f"differs on {m} ({morphism(m)}) vs {self.representative} ({rep_val})"
                )
        return rep_val

    def digest(self) -> str:
        rep_dict = self.representative.to_dict()
        members_sorted = sorted([m.digest() for m in self.members])
        payload = json.dumps(
            {"relation": self.relation_name, "rep": rep_dict, "members": members_sorted},
            sort_keys=True,
        ).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()


@dataclass(frozen=True)
class TrajectoryStep:
    """An individual atomic transition within a proof trajectory."""

    step_index: int
    source: FormTerm
    target: FormTerm
    rule: str
    metadata: tuple[tuple[str, str], ...] = field(default_factory=tuple)

    def digest(self) -> str:
        payload = json.dumps(
            {
                "index": self.step_index,
                "source": self.source.to_dict(),
                "target": self.target.to_dict(),
                "rule": self.rule,
                "metadata": list(self.metadata),
            },
            sort_keys=True,
        ).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()


@dataclass(frozen=True)
class ProofTrajectory:
    """A formal derivation path lifted into a first-class 1-cell.

    Equipped with associative composition, identity trajectories, path reversal,
    and invariant certificate hashing.
    """

    start: FormTerm
    end: FormTerm
    steps: tuple[TrajectoryStep, ...] = field(default_factory=tuple)

    def __post_init__(self) -> None:
        if not self.steps:
            if self.start != self.end:
                raise ObjectificationError(
                    f"Identity / empty trajectory must have start == end ({self.start} != {self.end})"
                )
        else:
            if self.steps[0].source != self.start:
                raise ObjectificationError(
                    f"First step source ({self.steps[0].source}) does not match trajectory start ({self.start})"
                )
            if self.steps[-1].target != self.end:
                raise ObjectificationError(
                    f"Last step target ({self.steps[-1].target}) does not match trajectory end ({self.end})"
                )
            for i in range(len(self.steps) - 1):
                if self.steps[i].target != self.steps[i + 1].source:
                    raise ObjectificationError(
                        f"Trajectory step discontinuity at index {i}: "
                        f"{self.steps[i].target} != {self.steps[i + 1].source}"
                    )

    @classmethod
    def identity(cls, term: FormTerm) -> ProofTrajectory:
        """Identity trajectory id_x: x -> x."""
        return cls(start=term, end=term, steps=())

    @classmethod
    def single_step(
        cls,
        source: FormTerm,
        target: FormTerm,
        rule: str,
        metadata: tuple[tuple[str, str], ...] = (),
    ) -> ProofTrajectory:
        step = TrajectoryStep(
            step_index=0, source=source, target=target, rule=rule, metadata=metadata
        )
        return cls(start=source, end=target, steps=(step,))

    def length(self) -> int:
        return len(self.steps)

    def compose(self, other: ProofTrajectory) -> ProofTrajectory:
        """Associative trajectory composition: (self o other).

        self: A -> B, other: B -> C => (self o other): A -> C.
        """
        if self.end != other.start:
            raise ObjectificationError(
                f"Cannot compose trajectories: endpoint mismatch ({self.end} != {other.start})"
            )
        offset = len(self.steps)
        reindexed_other = tuple(
            TrajectoryStep(
                step_index=offset + i,
                source=s.source,
                target=s.target,
                rule=s.rule,
                metadata=s.metadata,
            )
            for i, s in enumerate(other.steps)
        )
        return ProofTrajectory(
            start=self.start,
            end=other.end,
            steps=self.steps + reindexed_other,
        )

    def invert(self) -> ProofTrajectory:
        """Inversion of a reversible proof trajectory."""
        reversed_steps = tuple(
            TrajectoryStep(
                step_index=i,
                source=s.target,
                target=s.source,
                rule=f"inv({s.rule})",
                metadata=s.metadata,
            )
            for i, s in enumerate(reversed(self.steps))
        )
        return ProofTrajectory(
            start=self.end,
            end=self.start,
            steps=reversed_steps,
        )

    def digest(self) -> str:
        payload = json.dumps(
            {
                "start": self.start.to_dict(),
                "end": self.end.to_dict(),
                "steps": [s.digest() for s in self.steps],
            },
            sort_keys=True,
        ).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()

    def intermediate_states(self) -> list[FormTerm]:
        states = [self.start]
        for step in self.steps:
            states.append(step.target)
        return states


@dataclass(frozen=True)
class TrajectoryHomotopy:
    """A 2-cell relating two proof trajectories tau_1 and tau_2 with identical boundaries.

    Represents algebraic transformation / rewrite equivalence between derivation paths.
    """

    source_trajectory: ProofTrajectory
    target_trajectory: ProofTrajectory
    rewrite_rule: str
    certified: bool = True

    def __post_init__(self) -> None:
        if (
            self.source_trajectory.start != self.target_trajectory.start
            or self.source_trajectory.end != self.target_trajectory.end
        ):
            raise ObjectificationError(
                "Homotopy requires identical endpoints: "
                f"({self.source_trajectory.start}, {self.source_trajectory.end}) vs "
                f"({self.target_trajectory.start}, {self.target_trajectory.end})"
            )

    @staticmethod
    def are_homotopic(
        tau1: ProofTrajectory,
        tau2: ProofTrajectory,
        commutation_pairs: Sequence[tuple[str, str]] = (),
    ) -> bool:
        """Check if two trajectories are homotopic under known rule commutation symmetries."""
        if tau1.start != tau2.start or tau1.end != tau2.end:
            return False
        if tau1.digest() == tau2.digest():
            return True
        if len(tau1.steps) != len(tau2.steps):
            return False

        w1 = tuple(s.rule for s in tau1.steps)
        w2 = tuple(s.rule for s in tau2.steps)
        if sorted(w1) != sorted(w2):
            return False

        comm_set = set(commutation_pairs) | set((b, a) for a, b in commutation_pairs)
        if not comm_set:
            return False

        # BFS over word permutations generated by adjacent commuting swaps
        visited_words = {w1}
        queue = collections.deque([w1])
        while queue:
            curr = queue.popleft()
            if curr == w2:
                return True
            for i in range(len(curr) - 1):
                pair = (curr[i], curr[i + 1])
                if pair in comm_set:
                    swapped = curr[:i] + (curr[i + 1], curr[i]) + curr[i + 2 :]
                    if swapped not in visited_words:
                        visited_words.add(swapped)
                        queue.append(swapped)
        return False
