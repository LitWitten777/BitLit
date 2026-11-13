"""
src/parsers/sample_lang/errors.py
Error types for the sample_lang parser pipeline.
"""


class CSTParseError(SyntaxError):
    """Raised when the CST builder cannot parse the input."""
    def __init__(self, message: str, position: int = -1):
        super().__init__(message)
        self.position = position


class SemanticError(Exception):
    """Raised when semantic analysis fails (type error, scope error, etc.)."""


class IRValidationError(ValueError):
    """Raised when the emitted IR fails JSON Schema validation."""
