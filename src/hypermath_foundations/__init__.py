"""Audit Hypermath proof evidence without assuming the source theory is complete."""

from .audit import run_audit
from .gate import evaluate_gate

__version__ = "0.1.0"
__all__ = ["evaluate_gate", "run_audit"]
