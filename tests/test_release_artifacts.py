"""The public source archive and build pipelines must bind exact, reproducible Git bytes."""

from __future__ import annotations

import csv
import importlib.util
import io
import tarfile
import zipfile
from pathlib import Path

import pytest

REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "release_artifacts.py"

SPEC = importlib.util.spec_from_file_location("hypermath_release_artifacts", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
release_artifacts = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(release_artifacts)


@pytest.mark.parametrize(
    ("raw", "expected"),
    [
        (
            "https://github.com/TimeLordRaps/hypermath.git",
            "https://github.com/TimeLordRaps/hypermath",
        ),
        (
            "https://github.com/TimeLordRaps/hypermath/",
            "https://github.com/TimeLordRaps/hypermath",
        ),
        (
            "git" + "@github.com:TimeLordRaps/hypermath.git",
            "https://github.com/TimeLordRaps/hypermath",
        ),
        (
            "ssh://git" + "@github.com/TimeLordRaps/hypermath.git",
            "https://github.com/TimeLordRaps/hypermath",
        ),
    ],
)
def test_repository_url_spellings_are_canonical(raw: str, expected: str) -> None:
    assert release_artifacts._canonical_repository_url(raw) == expected


def _write_raw_wheel(path: Path, *, newline: bytes, reverse: bool) -> None:
    dist_info = "hypermath_foundations-0.1.0.dist-info"
    members = [
        ("hypermath_foundations/__init__.py", b'__version__ = "0.1.0"\n'),
        (
            f"{dist_info}/METADATA",
            newline.join(
                [
                    b"Metadata-Version: 2.4",
                    b"Name: hypermath-foundations",
                    b"Version: 0.1.0",
                    b"",
                    b"Canonical metadata.",
                    b"",
                ]
            ),
        ),
        (
            f"{dist_info}/WHEEL",
            newline.join(
                [
                    b"Wheel-Version: 1.0",
                    b"Generator: test",
                    b"Root-Is-Purelib: true",
                    b"Tag: py3-none-any",
                    b"",
                ]
            ),
        ),
        (
            f"{dist_info}/entry_points.txt",
            newline.join(
                [
                    b"[console_scripts]",
                    b"hypermath-foundations = hypermath_foundations.__main__:main",
                    b"",
                ]
            ),
        ),
        (f"{dist_info}/RECORD", b"host-generated-record"),
    ]
    if reverse:
        members.reverse()
    with zipfile.ZipFile(path, "w") as bundle:
        for name, data in members:
            info = zipfile.ZipInfo(name, (2026, 1, 2, 3, 4, 4))
            info.create_system = 0 if reverse else 3
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0 if reverse else (0o100755 << 16)
            bundle.writestr(info, data)


def test_wheel_normalization_removes_host_newlines_and_zip_metadata(tmp_path: Path) -> None:
    first_raw = tmp_path / "first.whl"
    second_raw = tmp_path / "second.whl"
    first = tmp_path / "first-normalized.whl"
    second = tmp_path / "second-normalized.whl"
    _write_raw_wheel(first_raw, newline=b"\r\n", reverse=False)
    _write_raw_wheel(second_raw, newline=b"\n", reverse=True)

    epoch = "1787446816"
    release_artifacts._normalize_wheel(first_raw, first, epoch)
    release_artifacts._normalize_wheel(second_raw, second, epoch)
    assert first.read_bytes() == second.read_bytes()

    with zipfile.ZipFile(first) as bundle:
        infos = bundle.infolist()
        assert all(info.create_system == 3 for info in infos)
        assert all(info.compress_type == zipfile.ZIP_STORED for info in infos)
        metadata_name = "hypermath_foundations-0.1.0.dist-info/METADATA"
        assert b"\r" not in bundle.read(metadata_name)
        record_name = "hypermath_foundations-0.1.0.dist-info/RECORD"
        rows = list(csv.reader(io.StringIO(bundle.read(record_name).decode("utf-8"))))
        records = {row[0]: row[1:] for row in rows}
        for info in infos:
            if info.is_dir() or info.filename == record_name:
                continue
            data = bundle.read(info)
            assert records[info.filename] == [
                release_artifacts._record_digest(data),
                str(len(data)),
            ]
        assert records[record_name] == ["", ""]


def _write_raw_sdist(path: Path, *, newline: bytes, reverse: bool) -> None:
    root = "hypermath_foundations-0.1.0"
    members = [
        (
            f"{root}/PKG-INFO",
            newline.join(
                [
                    b"Metadata-Version: 2.4",
                    b"Name: hypermath-foundations",
                    b"Version: 0.1.0",
                    b"",
                ]
            ),
        ),
        (f"{root}/setup.cfg", newline.join([b"[egg_info]", b"tag_build =", b""])),
        (
            f"{root}/src/hypermath_foundations.egg-info/PKG-INFO",
            newline.join(
                [
                    b"Metadata-Version: 2.4",
                    b"Name: hypermath-foundations",
                    b"Version: 0.1.0",
                    b"",
                ]
            ),
        ),
        (f"{root}/README.md", b"Source bytes stay unchanged.\n"),
    ]
    if reverse:
        members.reverse()
    with tarfile.open(path, "w:gz") as bundle:
        for name, data in members:
            info = tarfile.TarInfo(name)
            info.size = len(data)
            info.mtime = 12345
            info.uid = 1001 if reverse else 1000
            info.uname = "testuser"
            bundle.addfile(info, io.BytesIO(data))


def test_sdist_normalization_is_canonical_and_reproducible(tmp_path: Path) -> None:
    first_raw = tmp_path / "first.tar.gz"
    second_raw = tmp_path / "second.tar.gz"
    first = tmp_path / "first-normalized.tar.gz"
    second = tmp_path / "second-normalized.tar.gz"
    _write_raw_sdist(first_raw, newline=b"\r\n", reverse=False)
    _write_raw_sdist(second_raw, newline=b"\n", reverse=True)

    epoch = "1787446816"
    release_artifacts._normalize_sdist(first_raw, first, epoch)
    release_artifacts._normalize_sdist(second_raw, second, epoch)
    assert first.read_bytes() == second.read_bytes()

    with tarfile.open(first, "r:gz") as bundle:
        members = bundle.getmembers()
        assert all(m.mtime == int(epoch) for m in members)
        assert all(m.uid == 0 and m.gid == 0 for m in members)
        assert all(m.uname == "" and m.gname == "" for m in members)


def test_compare_directories_detects_mismatches(tmp_path: Path) -> None:
    dir_a = tmp_path / "a"
    dir_b = tmp_path / "b"
    dir_a.mkdir()
    dir_b.mkdir()
    (dir_a / "file1.txt").write_bytes(b"content")
    (dir_b / "file1.txt").write_bytes(b"content")

    # Identical directories pass
    assert release_artifacts.compare_directories(dir_a, dir_b) == 1

    # Missing file fails
    (dir_a / "extra.txt").write_bytes(b"extra")
    with pytest.raises(release_artifacts.ReleaseError, match="artifact file sets differ"):
        release_artifacts.compare_directories(dir_a, dir_b)

    # Different bytes fail
    (dir_b / "extra.txt").write_bytes(b"different")
    with pytest.raises(release_artifacts.ReleaseError, match="artifact bytes differ"):
        release_artifacts.compare_directories(dir_a, dir_b)
