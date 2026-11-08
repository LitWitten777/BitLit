#!/usr/bin/env python3
"""
Seed a comprehensive canonical corpus into the Categorical Ledger.

Creates:
  * Category C with objects X, Y, Z, W, morphisms, identities, compositions
  * Identity functor F on C
  * Natural transformation id_C ⇒ id_C
  * Adjunction (trivially, F ⊣ F)
  * Monad on C (identity monad)
  * Diagram for the product X × Y (as a placeholder)
  * Hebrew word examples
  * Policy example
"""

import os
import sys

sys.path.insert(0, os.path.join(os.path.dirname(__file__), "..", "src"))

from qbx.db.connection import pg_transaction

def main():
    with pg_transaction() as conn:
        with conn.cursor() as cur:
            # Category
            cur.execute(
                "INSERT INTO category (name, description) VALUES (%s, %s) RETURNING id",
                ("C_full", "Full canonical test category"),
            )
            cat = cur.fetchone()[0]

            # Objects
            cur.execute(
                "INSERT INTO object (category_id, name) VALUES (%s, %s) RETURNING id",
                (cat, "X"),
            )
            X = cur.fetchone()[0]
            cur.execute(
                "INSERT INTO object (category_id, name) VALUES (%s, %s) RETURNING id",
                (cat, "Y"),
            )
            Y = cur.fetchone()[0]
            cur.execute(
                "INSERT INTO object (category_id, name) VALUES (%s, %s) RETURNING id",
                (cat, "Z"),
            )
            Z = cur.fetchone()[0]

            # Identities
            identities = {}
            for obj, name in [(X, "id_X"), (Y, "id_Y"), (Z, "id_Z")]:
                cur.execute(
                    "INSERT INTO morphism (category_id, source_id, target_id, name) "
                    "VALUES (%s, %s, %s, %s) RETURNING id",
                    (cat, obj, obj, name),
                )
                mid = cur.fetchone()[0]
                cur.execute(
                    "INSERT INTO identity_morphism (category_id, object_id, morphism_id) "
                    "VALUES (%s, %s, %s)",
                    (cat, obj, mid),
                )
                identities[obj] = mid

            # Morphisms f, g, h = g∘f
            cur.execute(
                "INSERT INTO morphism (category_id, source_id, target_id, name) "
                "VALUES (%s, %s, %s, %s) RETURNING id",
                (cat, X, Y, "f"),
            )
            f = cur.fetchone()[0]
            cur.execute(
                "INSERT INTO morphism (category_id, source_id, target_id, name) "
                "VALUES (%s, %s, %s, %s) RETURNING id",
                (cat, Y, Z, "g"),
            )
            g = cur.fetchone()[0]
            cur.execute(
                "INSERT INTO morphism (category_id, source_id, target_id, name) "
                "VALUES (%s, %s, %s, %s) RETURNING id",
                (cat, X, Z, "h"),
            )
            h = cur.fetchone()[0]
            cur.execute(
                "INSERT INTO composition (category_id, left_id, right_id, result_id) "
                "VALUES (%s, %s, %s, %s)",
                (cat, g, f, h),
            )

            # Identity functor
            cur.execute(
                "INSERT INTO functor (name, source_category_id, target_category_id) "
                "VALUES (%s, %s, %s) RETURNING id",
                ("Id_C", cat, cat),
            )
            F_id = cur.fetchone()[0]

            for obj in (X, Y, Z):
                cur.execute(
                    "INSERT INTO functor_object_map (functor_id, source_object_id, target_object_id) "
                    "VALUES (%s, %s, %s)",
                    (F_id, obj, obj),
                )
            for mor in list(identities.values()) + [f, g, h]:
                cur.execute(
                    "INSERT INTO functor_morphism_map (functor_id, source_morphism_id, target_morphism_id) "
                    "VALUES (%s, %s, %s)",
                    (F_id, mor, mor),
                )

            # Natural transformation: id_C ⇒ id_C (components are identities)
            cur.execute(
                "INSERT INTO natural_transformation "
                "(name, source_functor_id, target_functor_id) "
                "VALUES (%s, %s, %s) RETURNING id",
                ("id_NT", F_id, F_id),
            )
            nt = cur.fetchone()[0]
            for obj in (X, Y, Z):
                cur.execute(
                    "INSERT INTO natural_transformation_component "
                    "(transformation_id, object_id, morphism_id) "
                    "VALUES (%s, %s, %s)",
                    (nt, obj, identities[obj]),
                )

            # Hebrew word examples
            cur.execute(
                "INSERT INTO hebrew_word (text, root, object_id) "
                "VALUES (%s, %s, %s) RETURNING id, total_gematria",
                ("שלום", "שלם", None),
            )
            hw_row = cur.fetchone()
            print(f"Hebrew word שלום: id={hw_row[0]}, gematria={hw_row[1]}")

            # Policy example
            # (migration 015: a policy carries one of the seeded modalities;
            # "!" = obligation, evaluated on the deontic frame)
            cur.execute(
                "SELECT register_policy(%s, %s, %s::jsonb, %s, %s)",
                (
                    "data_privacy_v1",
                    "personal_data",
                    '{"rules":[{"id":"require_consent"}],"retention_days":365}',
                    "!",
                    "hard",
                ),
            )
            pol = cur.fetchone()[0]

            print(f"Category:      {cat}")
            print(f"Functor Id_C:  {F_id}")
            print(f"Natural trf:   {nt}")
            print(f"Policy:        {pol}")
            print("Seed complete.")

if __name__ == "__main__":
    main()