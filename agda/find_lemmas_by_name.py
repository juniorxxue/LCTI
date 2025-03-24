#!/usr/bin/env python3
import os
import re
import argparse
from rich.console import Console
from rich.table import Table
from rich import box

def parse_args():
    parser = argparse.ArgumentParser()
    parser.add_argument("search_substr", help="Substring to match in the lemma name.")
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

                    # Skip comment lines
                    if stripped_line.startswith("--"):
                        continue

                    # Handle data blocks
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

                    # If we encounter a line with ' = ', treat it as proof => finalize any current lemma
                    if " = " in line:
                        if reading_lemma and current_lemma_lines:
                            lemma_text = "\n".join(current_lemma_lines).strip()
                            lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))
                        reading_lemma = False
                        current_lemma_lines = []
                        continue

                    if reading_lemma:
                        # Check if this line starts a new lemma (and doesn't contain ' = ')
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
                        # Check if this line starts a lemma (and doesn't contain ' = ')
                        if lemma_pattern.match(line):
                            reading_lemma = True
                            start_line = i
                            current_lemma_lines = [line.rstrip("\n")]

                # End of file
                if reading_lemma and current_lemma_lines:
                    lemma_text = "\n".join(current_lemma_lines).strip()
                    lemmas_dict.setdefault(lemma_text, []).append((file_path, start_line))

    return lemmas_dict

def parse_lemma_text(lemma_text):
    lines = lemma_text.splitlines()
    if not lines:
        return "", lemma_text
    first_line = lines[0]
    m = re.match(r'^\s*(\S+)\s*:\s*(.*)$', first_line)
    if m:
        return m.group(1), lemma_text
    return "", lemma_text

def print_lemmas(lemmas_dict, search_substr):
    console = Console()
    filtered = {}

    for stmt, occs in lemmas_dict.items():
        name, _full = parse_lemma_text(stmt)
        if search_substr in name:
            filtered[stmt] = occs

    if not filtered:
        console.print("[bold red]No lemmas found matching your criteria.[/bold red]")
        return

    # Sort lemmas based on the first occurrence's file and line number
    sorted_lemmas = sorted(
        filtered.items(),
        key=lambda item: min(item[1], key=lambda occ: (occ[0], occ[1]))
    )

    table = Table(box=box.SQUARE, show_header=True, show_lines=True)
    table.add_column("No.", style="dim", no_wrap=True, justify="right")
    table.add_column("Lemma Statement", style="white")
    table.add_column("Occurrences", style="green")

    # Prefix to remove from the file path in the occurrences
    path_prefix = "/Users/xuxue/Dropbox/research/contextual-polymorphic/agda/Implicit/"
    idx = 1
    for stmt, occs in sorted_lemmas:
        name, _ = parse_lemma_text(stmt)
        if name:
            styled_name = f"[bold]{name}[/bold]"
            stmt_lines = stmt.splitlines()
            if stmt_lines:
                first_line = re.sub(r'^\s*\S+\s*:\s*', f"{styled_name} : ", stmt_lines[0], 1)
                full_stmt = "\n".join([first_line] + stmt_lines[1:])
            else:
                full_stmt = stmt
        else:
            full_stmt = stmt

        occ_str = "\n".join(
            f"{p[len(path_prefix):] if p.startswith(path_prefix) else p}:{ln}"
            for p, ln in occs
        )
        table.add_row(str(idx), full_stmt, occ_str)
        idx += 1

    console.print(table)

def main():
    args = parse_args()
    lemmas = collect_lemma_signatures(args.root)
    print_lemmas(lemmas, args.search_substr)

if __name__ == "__main__":
    main()