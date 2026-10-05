"""Translate `.hm` sources, and say exactly what was and was not translated.

The translator is fail-closed. A construct it cannot translate faithfully is
kept in the IR as *untranslated*, with a reason and a source position, and is
never silently dropped, guessed at, or promoted to a proved statement.

Standard library only. Neither a Lean kernel check nor a Metamath verification of
the output certifies that a translated statement means what the `.hm` statement means.
"""
