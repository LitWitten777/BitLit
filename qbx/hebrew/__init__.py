"""Hebrew primacy: gematria mapping, invariant hash mixing, and the reference
checks of migration 014 (letters, words, gematria functors, Torah sites,
language adjunctions)."""

from qbx.hebrew.functor import functor_problems, functor_value, obligation_problems, rules_problems
from qbx.hebrew.gematria import GEMATRIA, gematria_value, gematria_vector
from qbx.hebrew.mixing import HebrewMixer
from qbx.hebrew.text import (
    LETTER_TABLE,
    letter_table_problems,
    root_problems,
    text_problems,
    word_row_problems,
)
from qbx.hebrew.torah import (
    language_adjunction_problems,
    passage_label,
    passage_sections,
    section_problems,
    site_problems,
    verse_ref_problems,
)

__all__ = [
    "GEMATRIA", "gematria_value", "gematria_vector", "HebrewMixer",
    "LETTER_TABLE", "letter_table_problems", "text_problems", "root_problems",
    "word_row_problems", "rules_problems", "functor_problems", "functor_value",
    "obligation_problems", "verse_ref_problems", "section_problems", "site_problems",
    "passage_label", "passage_sections", "language_adjunction_problems",
]
