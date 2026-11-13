"""
uds_transport.py — Zero-Plaintext Unix Domain Socket (UDS) Transport.

Implements Layer 1 streaming of rigid 128-byte SovereignFrame packets over
local Unix Domain Sockets, completely bypassing TCP/IP loopback and eliminating
HTTP/JSON serialization overhead.
"""

from __future__ import annotations

import os
import socket
import threading
from collections.abc import Callable
from pathlib import Path
from typing import Any

from .framing import (
    FRAME_SIZE,
    MSG_ABORT,
    MSG_CMD,
    MSG_HEARTBEAT,
    NODE_DESKTOP_PCORES,
    SovereignFrame,
)


class SovereignUDSServer:
    """
    High-speed, zero-copy Unix Domain Socket server streaming 128-byte SovereignFrames.
    Guarantees monotonic sequence ordering and Expander MAC authentication.
    """

    def __init__(
        self,
        socket_path: str | Path = "/tmp/sovereign_ipc.sock",
        node_id: int = NODE_DESKTOP_PCORES,
        key_seed: int = 0,
        handler: Callable[[SovereignFrame], SovereignFrame | None] | None = None,
    ):
        self.socket_path = Path(socket_path)
        self.node_id = node_id
        self.key_seed = key_seed
        self.handler = handler
        self._server_sock: socket.socket | None = None
        self._is_running = False
        self._thread: threading.Thread | None = None
        self._last_seen_seq: dict[int, int] = {}  # node_id -> last sequence

    def start(self) -> None:
        """Starts the UDS listener thread."""
        if self._is_running:
            return

        if self.socket_path.exists():
            self.socket_path.unlink()

        self._server_sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self._server_sock.bind(str(self.socket_path))
        self._server_sock.listen(8)
        self._server_sock.settimeout(0.5)
        self._is_running = True

        self._thread = threading.Thread(target=self._listen_loop, daemon=True)
        self._thread.start()

    def stop(self) -> None:
        """Stops the UDS server and cleans up the socket file."""
        self._is_running = False
        if self._thread and self._thread.is_alive():
            self._thread.join(timeout=1.0)
        if self._server_sock:
            try:
                self._server_sock.close()
            except Exception:
                pass
            self._server_sock = None
        if self.socket_path.exists():
            try:
                self.socket_path.unlink()
            except Exception:
                pass

    def _listen_loop(self) -> None:
        while self._is_running and self._server_sock:
            try:
                conn, _ = self._server_sock.accept()
            except socket.timeout:
                continue
            except OSError:
                break

            client_thread = threading.Thread(
                target=self._handle_client,
                args=(conn,),
                daemon=True,
            )
            client_thread.start()

    def _handle_client(self, conn: socket.socket) -> None:
        conn.settimeout(2.0)
        try:
            while self._is_running:
                data = self._recv_exact(conn, FRAME_SIZE)
                if not data or len(data) < FRAME_SIZE:
                    break

                try:
                    frame = SovereignFrame.unpack(data, key_seed=self.key_seed, verify_mac=True)
                except ValueError as err:
                    # MAC failure or corrupted frame: reject immediately
                    err_frame = SovereignFrame(
                        frame_seq=0,
                        node_id=self.node_id,
                        msg_type=MSG_ABORT,
                        flags=0,
                        nonce=0,
                        payload=str(err)[:100].encode("utf-8"),
                    )
                    conn.sendall(err_frame.pack(key_seed=self.key_seed))
                    continue

                # Anti-replay sequence check
                last_seq = self._last_seen_seq.get(frame.node_id, -1)
                if frame.frame_seq <= last_seq:
                    err_frame = SovereignFrame(
                        frame_seq=last_seq,
                        node_id=self.node_id,
                        msg_type=MSG_ABORT,
                        flags=0,
                        nonce=0,
                        payload=b"REPLAY_DETECTED_ABORT",
                    )
                    conn.sendall(err_frame.pack(key_seed=self.key_seed))
                    continue

                self._last_seen_seq[frame.node_id] = frame.frame_seq

                # Execute handler
                if self.handler:
                    resp = self.handler(frame)
                    if resp:
                        conn.sendall(resp.pack(key_seed=self.key_seed))
                else:
                    # Echo heartbeat default
                    resp = SovereignFrame(
                        frame_seq=frame.frame_seq,
                        node_id=self.node_id,
                        msg_type=MSG_HEARTBEAT,
                        flags=0,
                        nonce=frame.nonce,
                        payload=b"ACK",
                    )
                    conn.sendall(resp.pack(key_seed=self.key_seed))
        except (ConnectionResetError, socket.timeout, BrokenPipeError):
            pass
        finally:
            try:
                conn.close()
            except Exception:
                pass

    @staticmethod
    def _recv_exact(conn: socket.socket, num_bytes: int) -> bytes:
        buf = bytearray()
        while len(buf) < num_bytes:
            chunk = conn.recv(num_bytes - len(buf))
            if not chunk:
                break
            buf.extend(chunk)
        return bytes(buf)


class SovereignUDSClient:
    """
    Client for transmitting SovereignFrames over Unix Domain Sockets.
    """

    def __init__(
        self,
        socket_path: str | Path = "/tmp/sovereign_ipc.sock",
        node_id: int = 0x02,
        key_seed: int = 0,
    ):
        self.socket_path = Path(socket_path)
        self.node_id = node_id
        self.key_seed = key_seed
        self._seq = 1
        self._sock: socket.socket | None = None

    def connect(self) -> None:
        """Establishes connection to the UDS socket."""
        self._sock = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
        self._sock.settimeout(3.0)
        self._sock.connect(str(self.socket_path))

    def close(self) -> None:
        """Closes the client socket."""
        if self._sock:
            try:
                self._sock.close()
            except Exception:
                pass
            self._sock = None

    def __enter__(self) -> SovereignUDSClient:
        self.connect()
        return self

    def __exit__(self, exc_type: Any, exc_val: Any, exc_tb: Any) -> None:
        self.close()

    def send_frame(
        self,
        msg_type: int,
        payload: bytes,
        flags: int = 0,
        nonce: int = 0,
    ) -> SovereignFrame:
        """
        Sends a single SovereignFrame and awaits the verified response frame.
        """
        if not self._sock:
            raise RuntimeError("Client not connected")

        frame = SovereignFrame(
            frame_seq=self._seq,
            node_id=self.node_id,
            msg_type=msg_type,
            flags=flags,
            nonce=nonce,
            payload=payload,
        )
        self._seq += 1

        raw_out = frame.pack(key_seed=self.key_seed)
        self._sock.sendall(raw_out)

        # Receive 128-byte response
        buf = bytearray()
        while len(buf) < FRAME_SIZE:
            chunk = self._sock.recv(FRAME_SIZE - len(buf))
            if not chunk:
                raise ConnectionError("Server closed connection unexpectedly")
            buf.extend(chunk)

        resp = SovereignFrame.unpack(bytes(buf), key_seed=self.key_seed, verify_mac=True)
        return resp
