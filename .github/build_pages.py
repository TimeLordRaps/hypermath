"""Assemble a documentation site from whatever the repository tracks.

Shared across the family, so it may assume no layout. verifier's own builder
knows about `src/`, a component index, and a public CLI; fourteen sibling
repositories have none of those, and a builder that names one repository's
contents is broken in every other one. This one reads `git ls-files` and
renders what is there.

What it emits:

  _site/<path>.html          every tracked markdown document, rendered
  _site/index.html           README.md, or a generated contents page
  _site/<asset>              every non-document file a document links to

The deployment manifest is NOT written here. It is written by
`.github/pages_manifest.py`, which walks the built directory -- so that the
same verification covers a repository that has its own `scripts/build_pages.py`
and never heard of this file.
"""

from __future__ import annotations

import argparse
import hashlib
import html
import pathlib
import posixpath
import re
import subprocess
import sys
import urllib.parse

DOCUMENT_SUFFIXES = (".md", ".markdown")

# Directories whose contents are carried, not authored: vendored upstream
# material and virtual environments. Publishing them would present someone
# else's documents as this repository's site.
EXCLUDED = re.compile(r"(^|/)(\.venv|venv|node_modules|\.git|\.lake|__pycache__)(/|$)")

LINK = re.compile(r"\[[^\]]*\]\(\s*([^)\s]+)\s*\)")

STYLE = """
:root {
  --ink: #16181d; --muted: #5b6270; --rule: #d9dde5;
  --bg: #ffffff; --accent: #2f5fd0; --code-bg: #f4f6fa;
}
@media (prefers-color-scheme: dark) {
  :root {
    --ink: #e6e8ee; --muted: #9aa3b4; --rule: #2b3140;
    --bg: #14161b; --accent: #7aa2f7; --code-bg: #1c2029;
  }
}
* { box-sizing: border-box; }
body {
  margin: 0; background: var(--bg); color: var(--ink);
  font: 16px/1.65 -apple-system, BlinkMacSystemFont, "Segoe UI", Helvetica, Arial, sans-serif;
}
.wrap { max-width: 46rem; margin: 0 auto; padding: 2.5rem 1rem 6rem; }
nav.breadcrumb { font-size: .875rem; color: var(--muted); margin-bottom: 2rem; }
nav.breadcrumb a { color: var(--muted); }
a { color: var(--accent); }
h1, h2, h3, h4 { line-height: 1.25; margin: 2rem 0 .75rem; }
h1 { font-size: 1.75rem; margin-top: 0; }
h2 { font-size: 1.3rem; border-bottom: 1px solid var(--rule); padding-bottom: .3rem; }
pre, code { font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; font-size: .9em; }
pre { background: var(--code-bg); padding: .9rem 1rem; overflow-x: auto; border-radius: 6px; }
code { background: var(--code-bg); padding: .15em .35em; border-radius: 3px; }
pre code { background: none; padding: 0; }
table { border-collapse: collapse; width: 100%; margin: 1rem 0; display: block; overflow-x: auto; }
th, td { border: 1px solid var(--rule); padding: .45rem .7rem; text-align: left; }
th { background: var(--code-bg); }
blockquote { margin: 1rem 0; padding: .1rem 1rem; border-left: 3px solid var(--rule); color: var(--muted); }
img { max-width: 100%; height: auto; }
hr { border: 0; border-top: 1px solid var(--rule); margin: 2rem 0; }
footer { margin-top: 4rem; padding-top: 1rem; border-top: 1px solid var(--rule);
         font-size: .8rem; color: var(--muted); }
ul.contents { list-style: none; padding-left: 0; }
ul.contents li { padding: .2rem 0; }
"""

PAGE = """<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1">
<title>{title}</title>
<style>{style}</style>
</head>
<body>
<div class="wrap">
{breadcrumb}
{body}
<footer>{repository} &middot; built from <code>{source_ref}</code></footer>
</div>
</body>
</html>
"""


def tracked() -> list[str]:
    # splitlines(), never split(): a tracked path may contain a space.
    names = subprocess.run(
        ["git", "ls-files"], capture_output=True, text=True, check=True
    ).stdout.splitlines()
    names = [n for n in names if not EXCLUDED.search(n)]
    # A path can be in the index and not on disk -- a working tree mid-edit,
    # a sparse checkout. CI checks out everything, so this is a courtesy to
    # whoever runs the builder locally; it is reported rather than swallowed,
    # because silently publishing fewer documents than the repository tracks
    # is the failure this whole workflow exists to catch.
    present = [n for n in names if pathlib.Path(n).is_file()]
    missing = len(names) - len(present)
    if missing:
        print(f"note: {missing} tracked path(s) absent from disk, skipped", file=sys.stderr)
    return present


def published_path(name: str) -> str:
    """Where a tracked document is served from."""
    if name == "README.md":
        return "index.html"
    base = name[: -len(pathlib.PurePosixPath(name).suffix)]
    # A directory's README becomes that directory's index.
    if posixpath.basename(base) == "README":
        parent = posixpath.dirname(base)
        return posixpath.join(parent, "index.html") if parent else "index.html"
    return base + ".html"


def rewrite_links(body: str, here: str, documents: dict[str, str]) -> str:
    """Point markdown links at where their targets are actually published."""

    def fix(match: re.Match) -> str:
        target = match.group(2)
        if re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", target) or target.startswith("#"):
            return match.group(0)
        path, _, fragment = target.partition("#")
        path = urllib.parse.unquote(path)
        if not path:
            return match.group(0)
        resolved = posixpath.normpath(posixpath.join(posixpath.dirname(here), path))
        if resolved not in documents:
            return match.group(0)
        relative = posixpath.relpath(
            documents[resolved], posixpath.dirname(published_path(here)) or "."
        )
        return f"{match.group(1)}({relative}{'#' + fragment if fragment else ''})"

    return re.sub(r"(\[[^\]]*\])\(\s*([^)\s]+)\s*\)", fix, body)


def render(text: str) -> str:
    import markdown  # provided by the workflow, pinned there

    return markdown.markdown(
        text,
        extensions=["extra", "sane_lists", "toc", "admonition"],
        output_format="html5",
    )


def breadcrumb_for(published: str, contents_at: str) -> str:
    if published == contents_at:
        return ""
    depth = published.count("/")
    up = "../" * depth if depth else ""
    return f'<nav class="breadcrumb"><a href="{up}{contents_at}">&#8592; Contents</a></nav>'


def link_into_landing(landing: pathlib.Path, contents_at: str, emitted: dict) -> None:
    """Add one link to the contents page into a landing page someone else built.

    Four of these repositories generate their own `index.html` -- a landing
    page and a family explorer, built from `docs/family/family-graph.json`.
    That page is kept, so the rendered documents need a way in from it, or
    they are published and unreachable.

    Idempotent by marker, and it restructures nothing: a landing page with no
    `</body>` is left untouched rather than guessed at.
    """
    marker = "<!-- rendered-documents-link -->"
    try:
        text = landing.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError):
        return
    if marker in text or "</body>" not in text:
        return
    block = (
        f'{marker}\n'
        '<p style="max-width:46rem;margin:2rem auto;padding:0 1rem;'
        'font:16px/1.65 -apple-system,BlinkMacSystemFont,\'Segoe UI\',Helvetica,Arial,sans-serif">'
        f'<a href="{contents_at}">Browse every document in this repository &#8594;</a>'
        "</p>\n"
    )
    text = text.replace("</body>", block + "</body>", 1)
    data = text.encode("utf-8")
    landing.write_bytes(data)
    emitted["index.html"] = hashlib.sha256(data).hexdigest()


def title_for(text: str, fallback: str) -> str:
    for line in text.split("\n"):
        if line.startswith("# "):
            return line[2:].strip()
    return fallback


def contents_page(documents: dict[str, str]) -> str:
    by_directory: dict[str, list[tuple[str, str]]] = {}
    for source, published in sorted(documents.items()):
        if published == "index.html":
            continue
        by_directory.setdefault(posixpath.dirname(source) or ".", []).append(
            (source, published)
        )
    parts = ["<h1>Contents</h1>"]
    for directory in sorted(by_directory):
        parts.append(f"<h2>{html.escape(directory)}</h2>")
        parts.append('<ul class="contents">')
        for source, published in by_directory[directory]:
            label = posixpath.basename(source)
            parts.append(f'<li><a href="{published}">{html.escape(label)}</a></li>')
        parts.append("</ul>")
    return "\n".join(parts)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="_site")
    parser.add_argument("--source-ref", required=True)
    parser.add_argument("--repository", default="")
    parser.add_argument(
        "--keep-existing",
        action="store_true",
        help=(
            "Never overwrite a file already in the output directory. Set when "
            "running after a repository's own scripts/build_pages.py, which "
            "generates a landing page and the family explorer -- a different "
            "artifact from rendered documents, not a worse one. Both belong "
            "in the site, so this renderer fills in around it."
        ),
    )
    options = parser.parse_args()

    out = pathlib.Path(options.output)
    names = tracked()
    documents = {
        n: published_path(n) for n in names if n.endswith(DOCUMENT_SUFFIXES)
    }
    if not documents:
        print("no tracked markdown document: nothing to publish", file=sys.stderr)
        return 1

    # Where the generated table of contents goes depends on whether another
    # builder already owns the landing page. Decided before anything is
    # rendered, because every document's breadcrumb points at it.
    contents_at = "contents.html" if (out / "index.html").exists() else "index.html"

    emitted: dict[str, str] = {}

    def write(relative: str, data: bytes) -> None:
        destination = out / relative
        if options.keep_existing and destination.exists():
            return
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(data)
        emitted[relative] = hashlib.sha256(data).hexdigest()

    for source, published in sorted(documents.items()):
        text = pathlib.Path(source).read_text(encoding="utf-8", errors="replace")
        page = PAGE.format(
            title=html.escape(title_for(text, posixpath.basename(source))),
            style=STYLE,
            breadcrumb=breadcrumb_for(published, contents_at),
            body=render(rewrite_links(text, source, documents)),
            repository=html.escape(options.repository),
            source_ref=html.escape(options.source_ref),
        )
        write(published, page.encode("utf-8"))

    landing = out / "index.html"
    page = PAGE.format(
        title=html.escape(options.repository or "Contents"),
        style=STYLE,
        breadcrumb="",
        body=contents_page(documents),
        repository=html.escape(options.repository),
        source_ref=html.escape(options.source_ref),
    )
    if contents_at == "index.html":
        if "index.html" not in emitted:
            write("index.html", page.encode("utf-8"))
    else:
        # Written unconditionally: --keep-existing protects the OTHER builder's
        # files, not a stale copy of this one's.
        destination = out / contents_at
        destination.write_bytes(page.encode("utf-8"))
        emitted[contents_at] = hashlib.sha256(page.encode("utf-8")).hexdigest()
        link_into_landing(landing, contents_at, emitted)

    # Publish exactly the non-document files the documents point at -- images,
    # data, the scaffold scripts a chapter links to. Not a suffix allowlist,
    # which guesses at layout, and not the whole tree: a documentation site is
    # not a file server. Measured: hypergrammar's chapters link to their
    # `NN_*_scaffold.py`, which no reasonable asset suffix list would include.
    tracked_set = set(names)
    referenced: set[str] = set()
    for source in documents:
        text = pathlib.Path(source).read_text(encoding="utf-8", errors="replace")
        for target in LINK.findall(text):
            if re.match(r"[a-zA-Z][a-zA-Z0-9+.-]*:", target) or target.startswith("#"):
                continue
            path = urllib.parse.unquote(target.split("#", 1)[0]).strip()
            if not path or path.endswith("/"):
                continue
            resolved = posixpath.normpath(
                posixpath.join(posixpath.dirname(source), path)
            )
            if resolved in tracked_set and resolved not in documents:
                referenced.add(resolved)
    for name in sorted(referenced):
        write(name, pathlib.Path(name).read_bytes())

    # Jekyll would otherwise drop every path beginning with an underscore.
    write(".nojekyll", b"")

    # No manifest is written here on purpose. `.github/pages_manifest.py` walks
    # the built directory afterwards, so one receipt covers whatever a
    # repository's own builder contributed to this directory as well. Writing
    # a second one here would leave two manifests, free to disagree.
    print(f"built {len(emitted)} file(s) from {len(documents)} document(s)")
    print(f"contents page at {contents_at}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
