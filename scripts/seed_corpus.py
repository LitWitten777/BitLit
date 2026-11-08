#!/usr/bin/env python3
"""
Seed a small canonical corpus into Postgres.

Creates:
  - One category C with objects X, Y, Z and morphisms f, g, h = g∘f, plus identities.
  - One identity functor F: C → C.
  - One path signature for the chain [f, g].
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from qbx.db.connection import pg_transaction
from qbx.db.repositories import CategoryRepository, FunctorRepository, PathSignatureRepository
from qbx.path.signature import PathSignature

def main():
    with pg_transaction() as conn:
        cat_repo = CategoryRepository(conn)
        fun_repo = FunctorRepository(conn)
        path_repo = PathSignatureRepository(conn)

        cat_id = cat_repo.create_category("C_canonical", "Canonical test category")
        X = cat_repo.create_object(cat_id, "X")
        Y = cat_repo.create_object(cat_id, "Y")
        Z = cat_repo.create_object(cat_id, "Z")

        id_X = cat_repo.create_morphism(cat_id, X, X, "id_X")
        id_Y = cat_repo.create_morphism(cat_id, Y, Y, "id_Y")
        id_Z = cat_repo.create_morphism(cat_id, Z, Z, "id_Z")
        cat_repo.add_identity(cat_id, X, id_X)
        cat_repo.add_identity(cat_id, Y, id_Y)
        cat_repo.add_identity(cat_id, Z, id_Z)

        f = cat_repo.create_morphism(cat_id, X, Y, "f")
        g = cat_repo.create_morphism(cat_id, Y, Z, "g")
        h = cat_repo.create_morphism(cat_id, X, Z, "h")
        cat_repo.add_composition(cat_id, f, g, h)  # h = g ∘ f

        F_id = fun_repo.create_functor("Id_C", cat_id, cat_id)
        for obj in (X, Y, Z):
            fun_repo.map_object(F_id, obj, obj)
        for mor in (id_X, id_Y, id_Z, f, g, h):
            fun_repo.map_morphism(F_id, mor, mor)

        sig = PathSignature.build(
            category_id=cat_id,
            start_object_id=X,
            end_object_id=Z,
            morphism_chain=[f, g],
            metadata={"note": "canonical path X→Y→Z"},
        )
        path_repo.insert(sig)

        print(f"Category:  {cat_id}")
        print(f"Functor:   {F_id}")
        print(f"Path sig:  {sig.path_id}")
        print(f"  proof_hash:   {sig.proof_hash}")
        print(f"  address_hash: {sig.address_hash}")

if __name__ == "__main__":
    main()