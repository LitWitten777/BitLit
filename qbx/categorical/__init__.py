"""Phase 1 categorical engines built on the frozen Phase 0 kernel."""

from qbx.categorical.adjunction import Adjunction, AdjunctionViolation
from qbx.categorical.enriched import (
    EnrichedCategory,
    EnrichedChecker,
    EnrichedViolation,
    Quantale,
    QUANTALES,
    compose_kernels,
)
from qbx.categorical.functors import ComposedFunctor, IdentityFunctor
from qbx.categorical.limits import (
    Cone,
    Diagram,
    LimitChecker,
    LimitViolation,
    all_cones,
    cone_problems,
    is_limit,
)
from qbx.categorical.monad import Comonad, Monad, MonadViolation
from qbx.categorical.two_category import (
    TwoCategory,
    TwoCategoryChecker,
    TwoCategoryViolation,
    codiscrete_two_category,
    one_cell_two_category,
)
from qbx.categorical.fibration import (
    Fibration,
    FibrationChecker,
    FibrationViolation,
    monoid_over_point,
)
from qbx.categorical.sheaf import (
    FiniteSite,
    LinearPresheaf,
    Presheaf,
    SheafChecker,
    SheafViolation,
    constant_presheaf,
    functions_presheaf,
    generated_topology,
)
from qbx.categorical.topos import (
    SubobjectClassifier,
    ToposChecker,
    ToposViolation,
    finite_sets,
    poset,
)
from qbx.categorical.natural_transformation import (
    NaturalTransformation,
    NaturalityViolation,
    compose,
    generates,
    incremental_checked_morphisms,
    legacy_trigger_checked_morphisms,
)

__all__ = [
    "Adjunction",
    "AdjunctionViolation",
    "Comonad",
    "Cone",
    "EnrichedCategory",
    "EnrichedChecker",
    "EnrichedViolation",
    "Quantale",
    "QUANTALES",
    "compose_kernels",
    "Diagram",
    "LimitChecker",
    "LimitViolation",
    "all_cones",
    "cone_problems",
    "is_limit",
    "ComposedFunctor",
    "IdentityFunctor",
    "Monad",
    "MonadViolation",
    "NaturalTransformation",
    "NaturalityViolation",
    "compose",
    "generates",
    "incremental_checked_morphisms",
    "legacy_trigger_checked_morphisms",
    "TwoCategory",
    "TwoCategoryChecker",
    "TwoCategoryViolation",
    "codiscrete_two_category",
    "one_cell_two_category",
    "Fibration",
    "FibrationChecker",
    "FibrationViolation",
    "monoid_over_point",
    "SubobjectClassifier",
    "ToposChecker",
    "ToposViolation",
    "finite_sets",
    "poset",
    "FiniteSite",
    "LinearPresheaf",
    "Presheaf",
    "SheafChecker",
    "SheafViolation",
    "constant_presheaf",
    "functions_presheaf",
    "generated_topology",
]
