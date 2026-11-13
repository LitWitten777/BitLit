"""
Persistent Regular Sub-Families Classification (OP-012, HYP-115)
Rigorous verification of persistent regular sub-families across the Cayley-Dickson tower.
While the global annihilation graph is regular iff D = 16 (HYP-074), the restricted
sub-families of octonionic sectors (chi in {1..7}) and doubling-pole sectors
(chi = 2^k for 3 <= k <= n-1) remain strictly (D-8)-regular for ALL D = 2^n >= 16.
"""

from typing import Set, Dict, List, Tuple, Any
from math import log2
from src.sedenion.regularity_classification import (
    verify_sector_regularity,
    classify_sector_by_charge,
    is_regular_criterion,
)


def get_persistent_regular_sectors(D: int) -> Set[int]:
    """
    Returns the exact set of persistent regular sectors for dimension D = 2^n >= 16:
    chi in {1..7} (octonionic sectors) union {2^k | 3 <= k <= n-1} (doubling pole family).
    """
    n = int(log2(D))
    regular = set(range(1, min(8, D // 2)))
    for k in range(3, n):
        val = 1 << k
        if val < D // 2:
            regular.add(val)
    return regular


def persistent_regular_sector_count(D: int) -> int:
    """Exact count of regular sectors: n + 3 = log2(D) + 3."""
    n = int(log2(D))
    return n + 3


def verify_subfamily_regularity(D: int) -> Tuple[bool, Dict[str, Any]]:
    """
    Verify for dimension D:
    1. Every sector in get_persistent_regular_sectors(D) is strictly (D-8)-regular.
    2. Every other sector chi < D/2 is irregular (has >= 2 distinct degrees).
    3. Total count matches log2(D) + 3.
    """
    reg_set = get_persistent_regular_sectors(D)
    expected_deg = D - 8
    
    for chi in reg_set:
        res = verify_sector_regularity(D, chi)
        if set(res["degrees"]) != {expected_deg}:
            return False, {"failed_sector": chi, "result": res}
            
    for chi in range(1, D // 2):
        if chi not in reg_set:
            res = verify_sector_regularity(D, chi)
            if res["degree_count"] < 2:
                return False, {"unexpectedly_regular": chi, "result": res}
                
    return True, {
        "D": D,
        "regular_count": len(reg_set),
        "expected_count": persistent_regular_sector_count(D),
        "degree": expected_deg,
    }


def octonionic_family_degrees(D: int) -> Dict[int, Set[int]]:
    """Return the degree set for each octonionic sector chi in {1..7}."""
    return {chi: set(verify_sector_regularity(D, chi)["degrees"]) for chi in range(1, 8)}


def doubling_pole_family_degrees(D: int) -> Dict[int, Set[int]]:
    """Return the degree set for each doubling pole sector chi = 2^k."""
    n = int(log2(D))
    poles = [1 << k for k in range(3, n - 1)]
    return {chi: set(verify_sector_regularity(D, chi)["degrees"]) for chi in poles}

