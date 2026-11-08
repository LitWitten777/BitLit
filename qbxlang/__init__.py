"""qbxlang — the QBX verifier language: `.qbx` source -> `.qbxir` -> `.qbxcert`, with the
kernel-language claims re-checked by Lean (`RequestProject/QBXCheck.lean`)."""
from .compiler import compile_source  # noqa: F401
