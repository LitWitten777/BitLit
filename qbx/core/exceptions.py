"""QBX exception hierarchy."""


class QBXError(Exception):
    """Base class for all QBX errors."""


class FunctorLawViolation(QBXError):
    """Raised when a functor law (identity or composition) is violated."""

    def __init__(self, functor_id: str, law: str, details: dict):
        self.functor_id = functor_id
        self.law = law
        self.details = details
        super().__init__(
            f"Functor {functor_id} violated {law} law: {details}"
        )


class CanonicalizationError(QBXError):
    """Raised when canonical serialization fails."""


class PathValidationError(QBXError):
    """Raised when a path signature fails validation."""


class CapabilityRequiredError(QBXError):
    """Raised when an operation requires a capability token that is missing/invalid."""


class HashingError(QBXError):
    """Raised when hashing fails or algorithm is unsupported."""


class WeylEngineError(QBXError):
    """Raised on Weyl engine errors."""


class HebrewMixError(QBXError):
    """Raised on Hebrew mixing errors."""
