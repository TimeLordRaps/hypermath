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

"""Meta-Fractalization: Self-Referential Feedback Loops and Terminal Self-Derivation.

Derives Non-Well-Founded Hyperset Theory (Aczel's AFA, Quine atoms, circular sets)
constructively from Ordinatics arithmetic fractal representations and terminal
Hyperkernel fixed points.
"""

from __future__ import annotations

import hashlib
import json
from dataclasses import dataclass, field
from typing import Callable

from .abstraction import FormTerm


@dataclass(frozen=True)
class OrdinalPolynomial:
    """Ordinal below omega^omega represented as polynomial coefficients in omega.

    alpha = sum_{i=0}^k a_i * omega^i (a_i in N).
    Equipped with natural Hessenberg addition (+) and natural multiplication (x).
    """

    coefficients: tuple[int, ...]  # index i is the coefficient of omega^i

    def __post_init__(self) -> None:
        coeffs = list(self.coefficients)
        if not coeffs:
            coeffs = [0]
        if not all(isinstance(c, int) and c >= 0 for c in coeffs):
            raise ValueError("Ordinal polynomial coefficients must be non-negative integers")
        while len(coeffs) > 1 and coeffs[-1] == 0:
            coeffs.pop()
        object.__setattr__(self, "coefficients", tuple(coeffs))

    @classmethod
    def zero(cls) -> OrdinalPolynomial:
        return cls((0,))

    @classmethod
    def one(cls) -> OrdinalPolynomial:
        return cls((1,))

    @classmethod
    def omega(cls) -> OrdinalPolynomial:
        return cls((0, 1))

    @classmethod
    def from_int(cls, n: int) -> OrdinalPolynomial:
        if n < 0:
            raise ValueError("Ordinal must be non-negative")
        return cls((n,))

    def degree(self) -> int:
        return len(self.coefficients) - 1

    def natural_add(self, other: OrdinalPolynomial) -> OrdinalPolynomial:
        """Hessenberg natural addition (o+): componentwise coefficient addition."""
        max_deg = max(len(self.coefficients), len(other.coefficients))
        c1 = list(self.coefficients) + [0] * (max_deg - len(self.coefficients))
        c2 = list(other.coefficients) + [0] * (max_deg - len(other.coefficients))
        result = tuple(a + b for a, b in zip(c1, c2))
        return OrdinalPolynomial(result)

    def natural_mul(self, other: OrdinalPolynomial) -> OrdinalPolynomial:
        """Hessenberg natural multiplication (ox): polynomial convolution."""
        if self == self.zero() or other == self.zero():
            return self.zero()
        deg1 = len(self.coefficients)
        deg2 = len(other.coefficients)
        res = [0] * (deg1 + deg2 - 1)
        for i, a in enumerate(self.coefficients):
            for j, b in enumerate(other.coefficients):
                res[i + j] += a * b
        return OrdinalPolynomial(tuple(res))

    def wrap_map(self) -> float:
        """The Ordinatics localization wrap map W(X) = -1/2 partial specialization."""
        return -0.5

    def to_form(self) -> FormTerm:
        """Embed the ordinal polynomial into the foundational Hypermath Form term algebra."""
        terms: list[FormTerm] = []
        for power, coeff in enumerate(self.coefficients):
            if coeff > 0:
                p_term = FormTerm(f"omega^{power}") if power > 0 else FormTerm.ground()
                c_term = FormTerm(f"coeff:{coeff}")
                terms.append(FormTerm("term", (c_term, p_term)))
        if not terms:
            return FormTerm.ground()
        curr = terms[0]
        for t in terms[1:]:
            curr = FormTerm("nat_add", (curr, t))
        return curr

    def __str__(self) -> str:
        parts: list[str] = []
        for power in reversed(range(len(self.coefficients))):
            coeff = self.coefficients[power]
            if coeff == 0 and len(self.coefficients) > 1:
                continue
            if power == 0:
                parts.append(str(coeff))
            elif power == 1:
                parts.append(f"{coeff}*w" if coeff != 1 else "w")
            else:
                parts.append(f"{coeff}*w^{power}" if coeff != 1 else f"w^{power}")
        return " + ".join(parts) if parts else "0"


class ConstructiveMembership:
    """Constructive membership relation (in_O) derived from structural sub-form decomposition.

    x in_O y <=> x is an immediate constituent sub-form or antecedent witness in y.
    """

    @staticmethod
    def is_member(subform: FormTerm, parent: FormTerm) -> bool:
        """Evaluate constructive membership x in_O y."""
        if subform in parent.args:
            return True
        # Quine atom fixed point self-membership
        if parent.symbol == "quine_atom" and subform == parent:
            return True
        # Cyclic recursive membership
        if parent.symbol == "cycle_node" and parent.args and parent.args[0] == subform:
            return True
        # Recursive constituent decomposition
        return any(ConstructiveMembership.is_member(subform, child) for child in parent.args)


@dataclass(frozen=True)
class QuineAtom:
    """The non-well-founded Quine atom Omega = {Omega}.

    Constructed as the zero-degree fixed point of the self-derivation operator:
    Omega = box(Omega) <=> Omega = {Omega}.
    """

    symbol: str = "quine_atom"

    def to_form(self) -> FormTerm:
        return FormTerm("quine_atom")

    def satisfies_self_membership(self) -> bool:
        form = self.to_form()
        return ConstructiveMembership.is_member(form, form)


@dataclass(frozen=True)
class AccessiblePointedGraph:
    """Accessible Pointed Graph (APG) for Non-Well-Founded Hyperset Equations.

    G = (V, E, root), where edges (u -> v) mean v in u.
    """

    nodes: frozenset[str]
    edges: frozenset[tuple[str, str]]  # (u, v) means v is a member of u
    root: str

    def __post_init__(self) -> None:
        if self.root not in self.nodes:
            raise ValueError(f"Root {self.root} must be in nodes")
        for u, v in self.edges:
            if u not in self.nodes or v not in self.nodes:
                raise ValueError(f"Edge ({u}, {v}) references node outside V")
        # Ensure all nodes in self.nodes are accessible from self.root
        reachable = {self.root}
        queue = [self.root]
        adj: dict[str, list[str]] = {}
        for u, v in self.edges:
            adj.setdefault(u, []).append(v)
        while queue:
            curr = queue.pop()
            for nxt in adj.get(curr, []):
                if nxt not in reachable:
                    reachable.add(nxt)
                    queue.append(nxt)
        if reachable != self.nodes:
            unreachable = sorted(self.nodes - reachable)
            raise ValueError(
                f"Nodes {unreachable} are not accessible from root {self.root}"
            )

    def outgoing(self, node: str) -> list[str]:
        return sorted([v for u, v in self.edges if u == node])

    def solve_decoration(self, max_depth: int = 8) -> dict[str, FormTerm]:
        """Aczel's Anti-Foundation Axiom (AFA) constructive solution.

        Computes the unique decoration of the APG into Hypermath Forms.
        Detects self-loops and cycles, resolving them into Quine atoms or cycle forms.
        """
        decorations: dict[str, FormTerm] = {}
        visiting: set[str] = set()

        def unwind(node: str, depth: int) -> FormTerm:
            if node in visiting or depth > max_depth:
                # Cycle detected: return self-referential cycle atom
                return FormTerm(f"cycle_ref:{node}")
            if node in decorations:
                return decorations[node]
            visiting.add(node)
            children = self.outgoing(node)
            if not children:
                res = FormTerm.ground()
            elif len(children) == 1 and children[0] == node:
                # Direct Quine self-loop: Omega = {Omega}
                res = FormTerm("quine_atom")
            else:
                child_terms = tuple(unwind(c, depth + 1) for c in children)
                res = FormTerm(f"hyperset:{node}", child_terms)
            visiting.remove(node)
            decorations[node] = res
            return res

        unwind(self.root, 0)
        return decorations

    @staticmethod
    def are_bisimilar(
        apg1: AccessiblePointedGraph,
        apg2: AccessiblePointedGraph,
    ) -> bool:
        """Check if two APGs are bisimilar.

        In Hyperset Theory, two hypersets are identical iff there is a bisimulation
        between their graphs, corresponding to mutual simulation (==) in Hypermath.
        Computes the maximal bisimulation via greatest fixed-point iteration.
        """
        # Initial candidate relation: all pairs with matching sink / non-sink status
        R = {
            (u, v)
            for u in apg1.nodes
            for v in apg2.nodes
            if (len(apg1.outgoing(u)) == 0) == (len(apg2.outgoing(v)) == 0)
        }

        while True:
            new_R = set()
            for u, v in R:
                out1 = apg1.outgoing(u)
                out2 = apg2.outgoing(v)
                cond1 = all(any((c1, c2) in R for c2 in out2) for c1 in out1)
                if not cond1:
                    continue
                cond2 = all(any((c1, c2) in R for c1 in out1) for c2 in out2)
                if not cond2:
                    continue
                new_R.add((u, v))
            if len(new_R) == len(R):
                break
            R = new_R

        return (apg1.root, apg2.root) in R


@dataclass
class Hyperkernel:
    """The Terminal Self-Derivation Kernel (Self-Meta Kernel).

    Four operational pillars:
      1. state: current computational configuration
      2. self_derivable: endofunctor mapping state -> derived state
      3. self_defined: internal relational predicate
      4. self_verifiable: internal decision procedure
      5. self_representation: injective fractal encoding into foundational Form
    """

    state: FormTerm
    derivation_rule: Callable[[FormTerm], FormTerm]
    decision_procedure: Callable[[FormTerm], bool]
    self_representation: FormTerm = field(init=False)

    def __post_init__(self) -> None:
        # Injective fractal encoding
        state_dict = self.state.to_dict()
        digest = hashlib.sha256(json.dumps(state_dict, sort_keys=True).encode("utf-8")).hexdigest()
        self.self_representation = FormTerm("hyperkernel_rep", (FormTerm(f"digest:{digest}"),))

    def step(self) -> FormTerm:
        """Execute one step of the self-derivation endofunctor."""
        return self.derivation_rule(self.state)

    def verify_state(self) -> bool:
        """Internal self-verification decision procedure."""
        return self.decision_procedure(self.state)

    def cyclical_completion(self) -> bool:
        """Check cyclical completion: terminal self-derivation fixed point.

        Phi(S) == S under mutual simulation.
        """
        next_state = self.step()
        return next_state == self.state
