"""
veilbreak.py — Client & Integration for veilbreak.ai Research API.

Provides programmatic and CLI access to the veilbreak.ai protocols and experiments
database for optical diffraction, laser wavelength analysis, and visual phenomena.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import urllib.parse
import urllib.request
from pathlib import Path
from typing import Any

ENV_PATH = Path("/home/roku/Documents/env.txt")
DEFAULT_BASE_URL = "https://veilbreak.ai/api"
DEFAULT_CACHE_DIR = Path("data/veilbreak")
DEFAULT_TIMEOUT = 30


def load_api_key_from_env_file(env_file: Path = ENV_PATH) -> str | None:
    """Extracts veilbreak.ai API key from environment file."""
    if not env_file.exists():
        return None
    try:
        content = env_file.read_text(encoding="utf-8")
        # Match vb_ followed by hex string
        match = re.search(r"\b(vb_[a-f0-9]{40,64})\b", content)
        if match:
            return match.group(1)
    except Exception:
        pass
    return None


class VeilbreakClient:
    """Client for querying veilbreak.ai REST API."""

    def __init__(
        self,
        api_key: str | None = None,
        base_url: str = DEFAULT_BASE_URL,
        cache_dir: Path = DEFAULT_CACHE_DIR,
        timeout: int = DEFAULT_TIMEOUT,
    ) -> None:
        self.api_key = (
            api_key
            or os.getenv("VEILBREAK_API_KEY")
            or load_api_key_from_env_file()
        )
        if not self.api_key:
            raise ValueError(
                "Veilbreak API key not found. Set VEILBREAK_API_KEY or verify /home/roku/Documents/env.txt."
            )
        self.base_url = base_url.rstrip("/")
        self.cache_dir = Path(cache_dir)
        self.timeout = timeout

    def _request(self, endpoint: str, params: dict[str, Any] | None = None) -> dict[str, Any]:
        """Executes an authenticated GET request to the veilbreak.ai API with offline cache fallback."""
        url = f"{self.base_url}/{endpoint.lstrip('/')}"
        if params:
            filtered = {k: v for k, v in params.items() if v is not None}
            if filtered:
                url += "?" + urllib.parse.urlencode(filtered)

        headers = {
            "Authorization": f"Bearer {self.api_key}",
            "Content-Type": "application/json",
            "User-Agent": "SovereignEngine/1.0",
        }

        try:
            req = urllib.request.Request(url, headers=headers)
            with urllib.request.urlopen(req, timeout=self.timeout) as resp:
                data = resp.read().decode("utf-8")
                return json.loads(data)
        except Exception as exc:
            # Attempt offline cache fallback
            ep_base = endpoint.strip("/").split("/")[0]
            cache_file = self.cache_dir / f"{ep_base}.json"
            if cache_file.exists():
                cached_data = json.loads(cache_file.read_text(encoding="utf-8"))
                cached_data["_cached"] = True
                return cached_data
            raise exc


    def get_schema(self) -> dict[str, Any]:
        """Retrieve API schema and field definitions."""
        return self._request("schema")

    def get_protocols(
        self,
        search: str | None = None,
        substance: str | None = None,
        equipment: str | None = None,
        laser_class: str | None = None,
        tags: str | None = None,
        wavelength_min: int | None = None,
        wavelength_max: int | None = None,
        sort_by: str | None = None,
        sort_order: str | None = None,
        page: int = 1,
        per_page: int = 10,
    ) -> dict[str, Any]:
        """Retrieve approved protocols with filtering and pagination."""
        params = {
            "search": search,
            "substance": substance,
            "equipment": equipment,
            "laser_class": laser_class,
            "tags": tags,
            "wavelength_min": wavelength_min,
            "wavelength_max": wavelength_max,
            "sort_by": sort_by,
            "sort_order": sort_order,
            "page": page,
            "per_page": per_page,
        }
        return self._request("protocols", params=params)

    def get_protocol(self, protocol_id: int) -> dict[str, Any]:
        """Retrieve a single specific protocol by ID."""
        return self._request(f"protocols/{protocol_id}")

    def get_experiments(
        self,
        search: str | None = None,
        protocol_id: int | None = None,
        observed: bool | None = None,
        substance: str | None = None,
        sort_by: str | None = None,
        sort_order: str | None = None,
        page: int = 1,
        per_page: int = 10,
    ) -> dict[str, Any]:
        """Retrieve approved experiments with filtering and pagination."""
        params = {
            "search": search,
            "protocol_id": protocol_id,
            "observed": str(observed).lower() if observed is not None else None,
            "substance": substance,
            "sort_by": sort_by,
            "sort_order": sort_order,
            "page": page,
            "per_page": per_page,
        }
        return self._request("experiments", params=params)

    def get_experiment(self, experiment_id: int) -> dict[str, Any]:
        """Retrieve a single specific experiment by ID."""
        return self._request(f"experiments/{experiment_id}")

    def sync_to_disk(self, output_dir: str | Path = "data/veilbreak") -> dict[str, int]:
        """Syncs all approved protocols and experiments to local JSON cache."""
        out_path = Path(output_dir)
        out_path.mkdir(parents=True, exist_ok=True)

        protocols = self.get_protocols(per_page=100)
        (out_path / "protocols.json").write_text(json.dumps(protocols, indent=2), encoding="utf-8")

        experiments = self.get_experiments(per_page=100)
        (out_path / "experiments.json").write_text(json.dumps(experiments, indent=2), encoding="utf-8")

        schema = self.get_schema()
        (out_path / "schema.json").write_text(json.dumps(schema, indent=2), encoding="utf-8")

        n_p = len(protocols.get("data", []))
        n_e = len(experiments.get("data", []))
        return {"protocols": n_p, "experiments": n_e}


def main() -> None:
    parser = argparse.ArgumentParser(description="veilbreak.ai Research API Client")
    parser.add_argument("--protocols", action="store_true", help="List protocols")
    parser.add_argument("--experiments", action="store_true", help="List experiments")
    parser.add_argument("--search", type=str, help="Search query string")
    parser.add_argument("--protocol-id", type=int, help="Fetch single protocol by ID")
    parser.add_argument("--experiment-id", type=int, help="Fetch single experiment by ID")
    parser.add_argument("--sync", action="store_true", help="Sync all data to data/veilbreak/")
    parser.add_argument("--per-page", type=int, default=10, help="Results per page (default: 10)")

    args = parser.parse_args()
    client = VeilbreakClient()

    if args.sync:
        res = client.sync_to_disk()
        print(f"Synced {res['protocols']} protocols and {res['experiments']} experiments to data/veilbreak/")
        return

    if args.protocol_id:
        p = client.get_protocol(args.protocol_id)
        print(json.dumps(p, indent=2))
        return

    if args.experiment_id:
        e = client.get_experiment(args.experiment_id)
        print(json.dumps(e, indent=2))
        return

    if args.experiments:
        res = client.get_experiments(search=args.search, per_page=args.per_page)
        print(f"Experiments (total: {res.get('pagination', {}).get('total', 0)}):")
        for item in res.get("data", []):
            print(f"  [{item.get('id')}] {item.get('title')} ({item.get('substance', 'N/A')})")
        return

    # Default: list protocols
    res = client.get_protocols(search=args.search, per_page=args.per_page)
    print(f"Protocols (total: {res.get('pagination', {}).get('total', 0)}):")
    for item in res.get("data", []):
        print(f"  [{item.get('id')}] {item.get('title')} (Laser: {item.get('laser_wavelength', 'N/A')}nm)")


if __name__ == "__main__":
    main()
