#!/usr/bin/env python3
"""Read G1 point coordinates directly from the pinned official RFC 9380 text.

These are expected outputs/intermediates, not tests of a hash-to-curve implementation.
The TSV is a convenience for Rust tests; its contents must match the RFC exactly.
"""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / "test-vectors/rfc9380"


def parse_rfc(text):
    if "h_eff: 0xd201000000010001" not in text:
        raise AssertionError("RFC effective-cofactor constant is missing")
    starts = [text.rindex(f"J.{n}.  ") for n in ("9.1", "9.2", "10")]
    points = []
    for index, (start, end) in enumerate(zip(starts, starts[1:]), 1):
        blocks = re.split(r"^   msg     =", text[start:end], flags=re.MULTILINE)[1:]
        if len(blocks) != 5:
            raise AssertionError(f"Expected five messages in RFC section J.9.{index}")
        labels = ("P", "Q0", "Q1") if index == 1 else ("P", "Q")
        for case, block in enumerate(blocks):
            coordinates = {(label, axis): a + b for label, axis, a, b in re.findall(
                r"^   (P|Q0|Q1|Q)\.([xy])\s+= ([0-9a-f]+)\n {13}([0-9a-f]+)$",
                block, flags=re.MULTILINE)}
            if set(coordinates) != {(label, axis) for label in labels for axis in ("x", "y")}:
                raise AssertionError("Unexpected RFC point layout")
            for label in labels:
                x, y = coordinates[label, "x"], coordinates[label, "y"]
                if len(x) != 96 or len(y) != 96:
                    raise AssertionError("Expected 48-byte G1 coordinates")
                points.append((f"J.9.{index}", str(case), label, x, y))
    if len(points) != 25:
        raise AssertionError("Expected all 25 G1 points in RFC 9380 Appendix J.9")
    return points


def tsv(points):
    return "# RFC 9380 section\tmessage index\tpoint\tx\ty\n" + "".join(
        "\t".join(point) + "\n" for point in points)


def fixtures():
    points = parse_rfc((BASE / "rfc9380.txt").read_text())
    if (BASE / "g1-points.tsv").read_text() != tsv(points):
        raise AssertionError("RFC coordinate table does not match the official text")
    return points
