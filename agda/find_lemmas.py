#!/usr/bin/env python3
import os
import re
import argparse
from rich.console import Console
from rich.table import Table
from rich import box

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("search_substr", help="Substring to match in the entire lemma type signature.")
    parser.add_argument("--root", default=".", help="Root directory to search.")
    return parser.parse_args()

def collect_lemma_signatures(root_dir="."):
    """
    A lemma signature must match:
        LemmaName : ...
    on a line that does NOT contain ' = '.
    The statement extends until:
      - A new lemma signature line appears,
      - Or a line contains ' = ' (start of proof),
      - Or end of file.

    We also skip:
      - data definitions ('data ' or 'data ... where'),
      - lines starting with '--' (comments).
    """
    lemma_pattern = re.compile(r'^\s*(\S+)\s*:\s*(.*)$')
    data_where_pattern = re.compile(r'^\s*data\b.*\bwhere\b')
    lemmas_dict = {}

    for root, _, files in os.walk(root_dir):
        for filename in files:
            if filename.endswith(".agda"):
                file_path = os.path.join(root, filename)
                with open(file_path, "r", encoding="utf-8") as f:
                    lines = f.readlines()

                reading_lemma = False
                start_line = None
                current_lemma_lines = []
                data_block = False

                for i, line in enumerate(lines, start=1):
                    stripped_line = line.strip()

                    if stripped_line.startswith("--"):
                        continue

                    if not data_block:
                        if data_where_pattern.search(line):
                            data_block = True
                            if reading_lemma and current_lemma_lines:
                                lemma_text = "\n".join(current_lemma_lines).strip()
                                lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))
                            reading_lemma = False
                            current_lemma_lines = []
                            continue
                        if stripped_line.startswith("data "):
                            if reading_lemma and current_lemma_lines:
                                lemma_text = "\n".join(current_lemma_lines).strip()
                                lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))
                            reading_lemma = False
                            current_lemma_lines = []
                            continue
                    else:
                        if len(line) - len(line.lstrip()) < 2:
                            data_block = False
                        else:
                            if reading_lemma and current_lemma_lines:
                                lemma_text = "\n".join(current_lemma_lines).strip()
                                lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))
                            reading_lemma = False
                            current_lemma_lines = []
                            continue

                    # Lines with ' = ' mark the start of a proof => finalize
                    if " = " in line:
                        if reading_lemma and current_lemma_lines:
                            lemma_text = "\n".join(current_lemma_lines).strip()
                            lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))
                        reading_lemma = False
                        current_lemma_lines = []
                        continue

                    if reading_lemma:
                        if lemma_pattern.match(line):
                            # finalize old
                            lemma_text = "\n".join(current_lemma_lines).strip()
                            lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))
                            # start new
                            reading_lemma = True
                            start_line = i
                            current_lemma_lines = [line.rstrip("\n")]
                        else:
                            current_lemma_lines.append(line.rstrip("\n"))
                    else:
                        if lemma_pattern.match(line):
                            reading_lemma = True
                            start_line = i
                            current_lemma_lines = [line.rstrip("\n")]

                if reading_lemma and current_lemma_lines:
                    lemma_text = "\n".join(current_lemma_lines).strip()
                    lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))

    return lemmas_dict

def parse_lemma_text(lemma_text):
    lines = lemma_text.splitlines()
    if not lines:
        return lemma_text
    first_line = lines[0]
    m = re.match(r'^\s*(\S+)\s*:\s*(.*)$', first_line)
    if m:
        name = m.group(1)
        remainder = m.group(2)
        if len(lines) > 1:
            return f"[bold]{name}[/bold] : {remainder}\n" + "\n".join(lines[1:])
        else:
            return f"[bold]{name}[/bold] : {remainder}"
    return lemma_text

def print_lemmas(lemmas_dict, search_substr):
    console = Console()

    filtered = {
        stmt: occs
        for stmt, occs in lemmas_dict.items()
        if search_substr in stmt
    }

    if not filtered:
        console.print("[bold red]No lemmas found matching your criteria.[/bold red]")
        return

    # Sort lemmas based on the first occurrence's file (and line number)
    sorted_lemmas = sorted(
        filtered.items(),
        key=lambda item: min(item[1], key=lambda occ: (occ[0], occ[1]))
    )

    table = Table(box=box.SQUARE, show_header=True, show_lines=True)
    table.add_column("No.", style="dim", no_wrap=True, justify="right")
    table.add_column("Lemma Statement", style="white")
    table.add_column("Occurrences", style="green")

    # Prefix to cut from the file path
    path_prefix = "/Users/xuxue/Dropbox/research/contextual-polymorphic/agda/Implicit/"
    idx = 1
    for stmt, occs in sorted_lemmas:
        styled = parse_lemma_text(stmt)
        occ_str = "\n".join(
            f"{p[len(path_prefix):] if p.startswith(path_prefix) else p}:{ln}"
            for p, ln in occs
        )
        table.add_row(str(idx), styled, occ_str)
        idx += 1

    console.print(table)

def main():
    args = parse_args()
    all_lemmas = collect_lemma_signatures(args.root)
    print_lemmas(all_lemmas, args.search_substr)

if __name__ == "__main__":
    main()