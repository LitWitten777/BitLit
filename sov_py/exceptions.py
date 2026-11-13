"""Domain exception hierarchy for Sedenion research."""


class SedenionError(Exception):
    """Base exception for all sedenion algebra and research domain errors."""


class ZeroDivisorError(SedenionError, ValueError):
    """Raised when encountering an unexpected zero divisor, singular kernel, or annihilator anomaly."""


class AlgebraDimensionError(SedenionError, ValueError):
    """Raised for invalid algebraic dimensions in Cayley-Dickson construction."""


class SignError(SedenionError, ValueError):
    """Raised for invalid vector signs (non-+1/-1 coordinate coefficients)."""


class CSSCodeError(SedenionError, ValueError):
    """Raised when Calderbank-Shor-Steane (CSS) commutativity conditions (H_X * H_Z^T = 0 mod 2) are violated."""
