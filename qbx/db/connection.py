"""
Postgres connection helpers.
"""

from __future__ import annotations

import os
from contextlib import contextmanager
from typing import Iterator, Optional

import psycopg2
from psycopg2.extensions import connection as PGConnection


def get_connection(dsn: Optional[str] = None) -> PGConnection:
    """Open a new Postgres connection."""
    dsn = dsn or os.getenv("PG_DSN", "postgresql://postgres:postgres@localhost:5432/qbx")
    return psycopg2.connect(dsn)


@contextmanager
def pg_transaction(dsn: Optional[str] = None) -> Iterator[PGConnection]:
    """Context manager for a transactional Postgres connection."""
    conn = get_connection(dsn)
    try:
        yield conn
        conn.commit()
    except Exception:
        conn.rollback()
        raise
    finally:
        conn.close()
