"""QBX container format: declared geometric objects with a protocol (decision CNT-001).

A container is a carrier, a declared curvature, a metric, an algebra, a boundary and a version.
Descriptors live in ``QBX/containers/descriptors/*.json``; composites (pipelines, products,
bundles) in ``QBX/containers/composites/*.json``.  This package reads them, checks them against
the curvature rules, composes curvatures, and measures volume profiles of the carriers it can
enumerate.  The Lean counterpart (curvature classes, the product rule, and the correctness of the
hypercube / lattice / tree declarations) is ``QBX/Formal/Foundations/Container.lean``.

    python -m qbx_containers check          # validate every descriptor and composite
    python -m qbx_containers show NAME      # print one container / composite
"""

from qbx_containers.curvature import (
    CURVATURES,
    can_embed,
    classify_profile,
    compose_bundle,
    compose_product,
    compose_sum,
)
from qbx_containers.registry import (
    Container,
    Composite,
    Registry,
    RegistryError,
    classify_revision,
    load_registry,
)
from qbx_containers.carriers import development, volume_profile

__all__ = [
    "CURVATURES",
    "can_embed",
    "classify_profile",
    "compose_bundle",
    "compose_product",
    "compose_sum",
    "Container",
    "Composite",
    "Registry",
    "RegistryError",
    "classify_revision",
    "development",
    "load_registry",
    "volume_profile",
]
