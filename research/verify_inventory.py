#!/usr/bin/env python3
"""Verify every recovered payload against the source inventory (standard library).

ZIP containers are not committed; their member bytes and original container hashes
are inventoried. This checks preservation, not mathematical correctness.
"""

import hashlib
import json
from pathlib import Path


def main():
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "research/source_manifest.json").read_text())
    artifacts = manifest["artifacts"]
    errors = []
    unique = {}
    historical = set()
    for artifact in artifacts:
        for member in artifact["members"]:
            relative = member["repository_path"]
            path = (root / relative).resolve()
            if not path.is_relative_to(root):
                errors.append(f"Path outside repository: {relative}")
                continue
            if not path.is_file():
                errors.append(f"Missing payload: {relative}")
                continue
            data = path.read_bytes()
            digest = hashlib.sha256(data).hexdigest()
            if len(data) != member["bytes"] or digest != member["sha256"]:
                errors.append(f"Payload differs from source: {relative}")
            unique[member["sha256"]] = relative
            if relative.startswith("research/archive/files/"):
                historical.add(relative)
    counts = {
        "source_artifact_count": len(artifacts),
        "unique_payload_count": len(unique),
        "historical_payload_count": len(historical),
    }
    for name, actual in counts.items():
        if actual != manifest[name]:
            errors.append(f"{name}: expected {manifest[name]}, found {actual}")
    print(json.dumps({"counts": counts, "errors": errors}, indent=2))
    return bool(errors)


if __name__ == "__main__":
    raise SystemExit(main())
