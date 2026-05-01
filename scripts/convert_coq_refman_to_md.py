#!/usr/bin/env python3
"""Convert a published Coq/Rocq Sphinx reference manual to one Markdown file.

The Coq 8.x reference manual is published as Sphinx HTML.  This script
downloads the rendered pages in the table-of-contents order, strips the
ReadTheDocs chrome, normalizes Coq-specific literal/grammar markup, and then
uses Pandoc to emit GitHub-Flavored Markdown.

Example:

    uv run --with beautifulsoup4 -- python scripts/convert_coq_refman_to_md.py \
      --version V8.19.0 \
      --output docs/coq-8.19.0-reference-manual.md
"""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tempfile
from dataclasses import dataclass
from html import escape
from pathlib import Path
from typing import Iterable
from urllib.parse import urldefrag, urljoin, urlparse
from urllib.request import Request, urlopen

try:
    from bs4 import BeautifulSoup
    from bs4.element import Tag
except ImportError as import_error:  # pragma: no cover - exercised by humans
    raise SystemExit(
        "Missing dependency: beautifulsoup4. Run with:\n"
        "  uv run --with beautifulsoup4 -- python "
        "scripts/convert_coq_refman_to_md.py ..."
    ) from import_error


USER_AGENT = "name-the-biggest-number-doc-converter/1.0"
DEFAULT_BASE_TEMPLATE = "https://rocq-prover.org/doc/{version}/refman/"
SKIP_CLASSES = {
    "coqtop-hidden",
    "math-preamble",
    "headerlink",
    "search",
}


@dataclass(frozen=True)
class ManualPage:
    href: str
    title: str


def fetch_text(url: str) -> str:
    request = Request(url, headers={"User-Agent": USER_AGENT})
    with urlopen(request, timeout=60) as response:
        encoding = response.headers.get_content_charset() or "utf-8"
        return response.read().decode(encoding, errors="replace")


def normalize_inline(text: str) -> str:
    return (
        text.replace("\xa0", " ")
        .replace("\u200b", "")
        .replace("¶", "")
        .strip()
    )


def normalize_code(text: str) -> str:
    lines = [line.rstrip() for line in text.replace("\xa0", " ").splitlines()]
    while lines and not lines[0].strip():
        lines.pop(0)
    while lines and not lines[-1].strip():
        lines.pop()
    compacted: list[str] = []
    blank_seen = False
    for line in lines:
        if line.strip():
            compacted.append(line)
            blank_seen = False
        elif not blank_seen:
            compacted.append("")
            blank_seen = True
    return "\n".join(compacted)


def tag_text(tag: Tag | None, separator: str = " ") -> str:
    if tag is None:
        return ""
    return normalize_inline(tag.get_text(separator, strip=True))


def make_pre(soup: BeautifulSoup, text: str, language: str | None = None) -> Tag:
    pre_tag = soup.new_tag("pre")
    code_tag = soup.new_tag("code")
    if language:
        code_tag["class"] = f"language-{language}"
    code_tag.string = normalize_code(text)
    pre_tag.append(code_tag)
    return pre_tag


def iter_unique_pages(index_soup: BeautifulSoup) -> list[ManualPage]:
    article_body = index_soup.select_one('[itemprop="articleBody"]')
    if article_body is None:
        raise RuntimeError("Could not find Sphinx article body in index.html")

    pages: list[ManualPage] = [ManualPage("index.html", "Introduction and Contents")]
    seen = {"index.html"}
    for link_tag in article_body.select(".toctree-wrapper a.reference.internal"):
        raw_href = link_tag.get("href", "")
        href_without_fragment, _ = urldefrag(raw_href)
        if raw_href.startswith("#") or not href_without_fragment:
            href_without_fragment = "index.html"
        if not href_without_fragment.endswith(".html"):
            continue
        if href_without_fragment in seen:
            continue
        seen.add(href_without_fragment)
        pages.append(ManualPage(href_without_fragment, tag_text(link_tag)))
    return pages


def remove_unwanted_tags(article_body: Tag) -> None:
    for unwanted in article_body.find_all(
        class_=lambda classes: classes
        and any(class_name in SKIP_CLASSES for class_name in as_class_list(classes))
    ):
        unwanted.decompose()
    for unwanted in article_body.find_all(["script", "style"]):
        unwanted.decompose()
    for target_span in article_body.select("span.target"):
        if not target_span.get_text(strip=True):
            target_span.decompose()


def as_class_list(classes: object) -> list[str]:
    if isinstance(classes, str):
        return classes.split()
    if isinstance(classes, Iterable):
        return [str(class_name) for class_name in classes]
    return []


def convert_literal_blocks(soup: BeautifulSoup, article_body: Tag) -> None:
    for literal_block in list(article_body.select(".literal-block")):
        if literal_block.find("pre"):
            continue

        block_classes = set(as_class_list(literal_block.get("class", [])))
        language = "coq" if {"coqtop", "coqdoc"} & block_classes else None
        fragments: list[str] = []

        definition_lists = literal_block.find_all("dl", recursive=False)
        if definition_lists:
            for definition_list in definition_lists:
                command_tag = definition_list.find("dt", recursive=False)
                output_tags = definition_list.find_all("dd", recursive=False)
                command_text = (
                    normalize_code(command_tag.get_text("", strip=False))
                    if command_tag
                    else ""
                )
                if command_text:
                    fragments.append(command_text)
                for output_tag in output_tags:
                    output_classes = set(as_class_list(output_tag.get("class", [])))
                    if "coqtop-hidden" in output_classes:
                        continue
                    output_text = normalize_code(output_tag.get_text("", strip=False))
                    if output_text:
                        fragments.append(output_text)
                fragments.append("")
        else:
            block_text = normalize_code(literal_block.get_text("", strip=False))
            if block_text:
                fragments.append(block_text)

        replacement = make_pre(soup, "\n".join(fragments), language)
        literal_block.replace_with(replacement)


def convert_grammar_blocks(soup: BeautifulSoup, article_body: Tag) -> None:
    for production_block in list(article_body.select(".prodn-table, .productionlist")):
        rows: list[str] = []
        for row_tag in production_block.select(".prodn-row"):
            nonterminal = tag_text(row_tag.select_one(".prodn-cell-nonterminal"))
            operator = tag_text(row_tag.select_one(".prodn-cell-op"))
            production = tag_text(row_tag.select_one(".prodn-cell-production"))
            row_note = tag_text(row_tag.select_one(".prodn-cell-tag"))
            if nonterminal or operator or production:
                left = f"{nonterminal:<24} {operator}".rstrip()
                row = f"{left:<32} {production}".rstrip()
                if row_note:
                    row = f"{row}  {row_note}"
                rows.append(row)

        if not rows:
            rows = [normalize_inline(production_block.get_text(" ", strip=True))]
        production_block.replace_with(make_pre(soup, "\n".join(rows), "ebnf"))


def simplify_inline_markup(soup: BeautifulSoup, article_body: Tag) -> None:
    inline_selectors = (
        "span.notation",
        "span.inline-grammar-production",
        "span.smallcaps",
    )
    for inline_tag in list(article_body.select(", ".join(inline_selectors))):
        if inline_tag.find_parent(["pre", "code"]):
            continue
        text = normalize_inline(inline_tag.get_text("", strip=False))
        if not text:
            inline_tag.decompose()
            continue
        if "smallcaps" in as_class_list(inline_tag.get("class", [])):
            inline_tag.replace_with(text)
        else:
            code_tag = soup.new_tag("code")
            code_tag.string = text
            inline_tag.replace_with(code_tag)

    for remaining_span in list(article_body.find_all("span")):
        if remaining_span.find_parent(["pre", "code"]):
            continue
        remaining_span.unwrap()


def rewrite_links(article_body: Tag, page_url: str) -> None:
    for link_tag in article_body.find_all("a", href=True):
        href = str(link_tag["href"])
        parsed = urlparse(href)
        if parsed.scheme or href.startswith("mailto:"):
            continue
        link_tag["href"] = urljoin(page_url, href)


def strip_rendering_attributes(article_body: Tag) -> None:
    """Drop Sphinx/CSS attributes that make Pandoc preserve raw HTML."""
    for html_tag in article_body.find_all(True):
        if html_tag.name == "a":
            href = html_tag.get("href")
            html_tag.attrs = {"href": href} if href else {}
            continue
        if html_tag.name == "img":
            kept = {
                name: html_tag.get(name)
                for name in ("src", "alt")
                if html_tag.get(name) is not None
            }
            html_tag.attrs = kept
            continue
        if html_tag.name == "code" and html_tag.find_parent("pre"):
            classes = as_class_list(html_tag.get("class", []))
            language_classes = [
                class_name for class_name in classes if class_name.startswith("language-")
            ]
            html_tag.attrs = {"class": language_classes} if language_classes else {}
            continue
        html_tag.attrs = {}


def sanitize_page(html: str, page: ManualPage, page_url: str) -> str:
    soup = BeautifulSoup(html, "html.parser")
    article_body = soup.select_one('[itemprop="articleBody"]')
    if article_body is None:
        raise RuntimeError(f"Could not find Sphinx article body in {page.href}")

    remove_unwanted_tags(article_body)
    convert_literal_blocks(soup, article_body)
    convert_grammar_blocks(soup, article_body)
    simplify_inline_markup(soup, article_body)
    rewrite_links(article_body, page_url)
    strip_rendering_attributes(article_body)

    page_container = soup.new_tag("section")
    page_container["data-source"] = page.href
    for child in list(article_body.children):
        page_container.append(child.extract())
    return str(page_container)


def display_version(version: str) -> str:
    return version[1:] if version.startswith("V") else version


def build_combined_html(base_url: str, pages: list[ManualPage], version: str) -> str:
    release = display_version(version)
    chunks: list[str] = [
        "<!doctype html>",
        '<html><head><meta charset="utf-8">',
        f"<title>The Coq Reference Manual, Release {escape(release)}</title>",
        "</head><body>",
        f"<h1>The Coq Reference Manual, Release {escape(release)}</h1>",
        "<p><em>Converted from the published Sphinx HTML manual at "
        f'<a href="{escape(base_url)}">{escape(base_url)}</a>.</em></p>',
    ]
    for page in pages:
        page_url = urljoin(base_url, page.href)
        print(f"[fetch] {page.href}", file=sys.stderr)
        chunks.append(sanitize_page(fetch_text(page_url), page, page_url))
    chunks.append("</body></html>")
    return "\n".join(chunks)


def run_pandoc(pandoc: str, html_path: Path, markdown_path: Path) -> None:
    command = [
        pandoc,
        "--from=html-native_divs-native_spans",
        "--to=gfm+tex_math_dollars",
        "--wrap=none",
        "--markdown-headings=atx",
        str(html_path),
        "-o",
        str(markdown_path),
    ]
    subprocess.run(command, check=True)


def write_markdown_header(markdown_path: Path, version: str, base_url: str) -> None:
    original = markdown_path.read_text(encoding="utf-8").replace("\u200b", "")
    header = (
        "<!--\n"
        f"Generated by scripts/convert_coq_refman_to_md.py from {base_url}\n"
        f"Version: {version}\n"
        "The source manual states that it is distributed under the Open "
        "Publication License, v1.0 or later, with Options A and B not elected.\n"
        "-->\n\n"
    )
    markdown_path.write_text(header + original, encoding="utf-8", newline="\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--version",
        default="V8.19.0",
        help="Manual version path component, e.g. V8.19.0.",
    )
    parser.add_argument(
        "--base-url",
        help="Override the published refman base URL.",
    )
    parser.add_argument(
        "--output",
        required=True,
        type=Path,
        help="Markdown file to write.",
    )
    parser.add_argument(
        "--work-dir",
        type=Path,
        help="Directory for the intermediate combined HTML.",
    )
    parser.add_argument(
        "--pandoc",
        default="pandoc",
        help="Pandoc executable to use.",
    )
    return parser.parse_args()


def main() -> None:
    args = parse_args()
    pandoc_path = shutil.which(args.pandoc)
    if pandoc_path is None:
        raise SystemExit("pandoc is required but was not found on PATH")

    base_url = args.base_url or DEFAULT_BASE_TEMPLATE.format(version=args.version)
    if not base_url.endswith("/"):
        base_url += "/"

    print(f"[index] {urljoin(base_url, 'index.html')}", file=sys.stderr)
    index_soup = BeautifulSoup(
        fetch_text(urljoin(base_url, "index.html")),
        "html.parser",
    )
    pages = iter_unique_pages(index_soup)
    print(f"[pages] {len(pages)} pages", file=sys.stderr)

    args.output.parent.mkdir(parents=True, exist_ok=True)
    if args.work_dir:
        args.work_dir.mkdir(parents=True, exist_ok=True)
        work_dir_context = None
        work_dir = args.work_dir
    else:
        work_dir_context = tempfile.TemporaryDirectory(prefix="coq-refman-md-")
        work_dir = Path(work_dir_context.name)

    try:
        combined_html_path = work_dir / "coq-refman-combined.html"
        combined_html_path.write_text(
            build_combined_html(base_url, pages, args.version),
            encoding="utf-8",
        )
        run_pandoc(pandoc_path, combined_html_path, args.output)
        write_markdown_header(args.output, args.version, base_url)
        print(f"[write] {args.output}", file=sys.stderr)
    finally:
        if work_dir_context is not None:
            work_dir_context.cleanup()


if __name__ == "__main__":
    main()
