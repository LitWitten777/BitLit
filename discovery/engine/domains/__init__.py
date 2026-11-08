"""Conjecture domains of the discovery loop."""

from .cd_signs import CDSignDomain
from .primes import PrimePolyDomain, QuadFormDomain

ALL_DOMAINS = {d.name: d for d in (CDSignDomain(), QuadFormDomain(), PrimePolyDomain())}
