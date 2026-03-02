import base64
import io
from pathlib import Path

import pytest
from PIL import Image
from pixelmatch.contrib.PIL import pixelmatch

from app import app

SNAPSHOTS = Path(__file__).parent / "snapshots"

DIAGRAM = {
    "nodes": [
        {"id": 0, "type": "input", "ioId": 0},
        {"id": 1, "type": "spider", "color": "Z", "phase": "1/2"},
        {"id": 2, "type": "output", "ioId": 0},
    ],
    "edges": [
        {"src": 0, "tgt": 1},
        {"src": 1, "tgt": 2},
    ],
}


def _decode_png(b64: str) -> Image.Image:
    return Image.open(io.BytesIO(base64.b64decode(b64))).convert("RGBA")


def test_diagram_snapshot():
    client = app.test_client()
    resp = client.post("/diagram", json=DIAGRAM)
    data = resp.get_json()
    assert data["status"] == "ok"

    actual = _decode_png(data["image"])
    snapshot_path = SNAPSHOTS / "test_z_spider.png"

    if not snapshot_path.exists():
        # First run: save reference and skip
        snapshot_path.parent.mkdir(parents=True, exist_ok=True)
        actual.save(snapshot_path)
        pytest.skip(f"Saved new snapshot to {snapshot_path}. Re-run to compare.")

    expected = Image.open(snapshot_path).convert("RGBA")
    assert_images_match(actual, expected, SNAPSHOTS / "test_z_spider_diff.png")


def assert_images_match(actual: Image.Image, expected: Image.Image, diff_path: Path) -> None:
    assert actual.size == expected.size, f"Size mismatch: {actual.size} vs {expected.size}"

    diff_img = Image.new("RGBA", actual.size)
    mismatch = pixelmatch(actual, expected, output=diff_img, threshold=0.1, alpha=0.5)

    if mismatch > 0:
        diff_path.parent.mkdir(parents=True, exist_ok=True)
        diff_img.save(diff_path)
        pytest.fail(f"{mismatch} pixels differ. Diff saved to {diff_path}. Delete snapshot and re-run to update.")
