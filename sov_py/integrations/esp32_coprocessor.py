"""
esp32_coprocessor.py — High-Speed Hardware-in-the-Loop Co-Processor Interface.

Handles framed binary communication with the physical ESP32-S3 microcontroller
running the Sovereign Co-Processor firmware over native USB-CDC / UART.
"""

from __future__ import annotations

import glob
import os
import struct
import subprocess
import sys
import time
from dataclasses import dataclass
from typing import Any

from sedenion.autonomous.framing import (
    FRAME_SIZE,
    HEADER_SIZE,
    MSG_TELEMETRY,
    NODE_ESP32_ENTROPY,
    SovereignFrame,
    expander_mac_32,
)


@dataclass
class ESP32Telemetry:
    """Parsed telemetry frame from physical ESP32 co-processor."""

    frame_seq: int
    noise_vector: list[int]
    syndrome_int: int
    collapse_sector: int
    raw_entropy: int
    mac: int
    mac_valid: bool
    timestamp: float = 0.0


class ESP32Coprocessor:
    """
    Manages serial framed binary streaming and firmware lifecycle for the ESP32-S3.
    """

    def __init__(self, port: str | None = None, baudrate: int = 115200) -> None:
        self.port = port or self._auto_detect_port()
        self.baudrate = baudrate
        self.serial_conn: Any | None = None
        self._last_seq = 0

    def _auto_detect_port(self) -> str | None:
        """Finds active ESP32 USB-Serial/JTAG port."""
        by_id_matches = glob.glob("/dev/serial/by-id/*Espressif*")
        if by_id_matches:
            return os.path.realpath(by_id_matches[0])
        candidates = glob.glob("/dev/ttyACM*") + glob.glob("/dev/ttyUSB*")
        for cand in candidates:
            if os.path.exists(cand):
                return cand
        return None

    def connect(self) -> bool:
        """Opens serial port connection for framed streaming."""
        if not self.port or not os.path.exists(self.port):
            return False
        try:
            import serial
            self.serial_conn = serial.Serial(self.port, baudrate=self.baudrate, timeout=0.5)
            return True
        except Exception:
            self.serial_conn = None
            return False

    def close(self) -> None:
        """Closes serial connection."""
        if self.serial_conn is not None:
            try:
                self.serial_conn.close()
            except Exception:
                pass
            self.serial_conn = None

    def read_frame(self, timeout_sec: float = 0.5) -> SovereignFrame | None:
        """Reads a 128-byte SovereignFrame from the serial stream."""
        if self.serial_conn is None:
            if not self.connect():
                return None

        deadline = time.time() + timeout_sec
        raw_bytes = bytearray()
        while len(raw_bytes) < FRAME_SIZE and time.time() < deadline:
            try:
                chunk = self.serial_conn.read(FRAME_SIZE - len(raw_bytes))
                if chunk:
                    raw_bytes.extend(chunk)
            except Exception:
                break

        if len(raw_bytes) == FRAME_SIZE:
            try:
                frame = SovereignFrame.unpack(bytes(raw_bytes))
                return frame
            except Exception:
                return None
        return None

    def poll_telemetry(self) -> ESP32Telemetry | None:
        """Reads and unpacks high-level quantum telemetry from the co-processor."""
        frame = self.read_frame(timeout_sec=0.2)
        if frame is None:
            return None

        payload = frame.payload
        if len(payload) < 13:
            return None

        noise = list(payload[:7])
        syndrome = payload[7]
        sector = payload[8]
        raw_entropy = struct.unpack("!I", payload[9:13])[0]

        return ESP32Telemetry(
            frame_seq=frame.frame_seq,
            noise_vector=noise,
            syndrome_int=syndrome,
            collapse_sector=sector,
            raw_entropy=raw_entropy,
            mac=frame.mac,
            mac_valid=True,
            timestamp=time.time(),
        )

    def flash_firmware(self, bin_path: str) -> bool:
        """Flashes precompiled firmware binary to ESP32 using esptool."""
        if not self.port or not os.path.exists(bin_path):
            return False
        self.close()
        cmd = [
            sys.executable,
            "-m",
            "esptool",
            "--port",
            self.port,
            "write-flash",
            "0x10000",
            bin_path,
        ]
        try:
            res = subprocess.run(cmd, capture_output=True, text=True, timeout=30.0)
            return res.returncode == 0
        except Exception:
            return False
