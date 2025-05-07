#!/usr/bin/env python3
"""
strip_proofs.py

Strip out all proof clauses for *new* top‑level lemmas in one or more Agda files,
turning each lemma’s type signature into a `postulate` block, but leaving
any existing `postulate` declarations and other definitions untouched.

For each input `XXX.agda`, writes `PXXX.agda` alongside it, and
updates the module declaration from `module A.B.C.XXX where` to
`module A.B.C.PXXX where`.

Usage:
  python3 strip_proofs.py file1.agda file2.agda ...
"""

import argparse
import os
import re
import sys

# Patterns to identify parts of the file
SIG_RE = re.compile(r'^([^ \t(][^:]*?)\s*:\s')      # lemma signature
CONT_RE = re.compile(r'^\s+→')                      # continuation arrows for signature
TOP_LEVEL_KW_RE = re.compile(
    r'^\s*(?:module\b|open import\b|postulate\b|data\b|record\b|infix[lr]?\b)'
)
MODULE_RE = re.compile(r'^(module\s+)([A-Za-z0-9_.]+)(\s+where.*)$')

# Patterns to detect data/infix definitions to preserve
INFIX_RE = re.compile(r'^infix\s+\d+')
DATA_RE  = re.compile(r'^data\s+.*\s+where')


def process(lines):
    out = []
    i = 0
    n = len(lines)

    while i < n:
        line = lines[i]

        # 0) Preserve data/infix blocks verbatim
        if INFIX_RE.match(line) or DATA_RE.match(line):
            # copy the header
            out.append(line.rstrip('\n'))
            i += 1
            # copy all indented constructor lines
            while i < n and (lines[i].startswith(' ') or lines[i].startswith('\t')):
                out.append(lines[i].rstrip('\n'))
                i += 1
            out.append('')
            continue

        # 1) Preserve existing postulate blocks verbatim
        if line.lstrip().startswith('postulate') and not SIG_RE.match(line):
            out.append(line.rstrip('\n'))
            i += 1
            while i < n and lines[i].startswith(' '):
                out.append(lines[i].rstrip('\n'))
                i += 1
            out.append('')
            continue

        # 2) Strip proofs for top‑level lemma signatures
        m = SIG_RE.match(line)
        if m and not line.startswith(' '):
            sig_block = [line.rstrip('\n')]
            i += 1
            # collect continuation lines
            while i < n and CONT_RE.match(lines[i]):
                sig_block.append(lines[i].rstrip('\n'))
                i += 1

            # skip proof clauses until next top‑level marker or signature
            while i < n:
                if SIG_RE.match(lines[i]) and not lines[i].startswith(' '):
                    break
                if TOP_LEVEL_KW_RE.match(lines[i]):
                    break
                i += 1

            # emit one postulate block
            out.append('postulate')
            for s in sig_block:
                out.append('  ' + s)
            out.append('')
            continue

        # 3) Otherwise copy line verbatim
        out.append(line.rstrip('\n'))
        i += 1

    return out


def rename_module(line, prefix='P'):
    """
    Rename module declaration by prefixing the last component.
    """
    m = MODULE_RE.match(line)
    if not m:
        return line
    pre, full_mod, post = m.groups()
    parts = full_mod.split('.')
    parts[-1] = prefix + parts[-1]
    return f"{pre}{'.'.join(parts)}{post}"


def main():
    parser = argparse.ArgumentParser(
        description="Strip proof bodies from Agda files and postulate their signatures."
    )
    parser.add_argument('infiles', nargs='+', help="One or more Agda source files")
    args = parser.parse_args()

    for infile in args.infiles:
        if not os.path.isfile(infile):
            print(f"Warning: '{infile}' not found, skipping.", file=sys.stderr)
            continue

        with open(infile, encoding='utf-8') as f:
            lines = f.readlines()

        # Process and rename module
        out_lines = process(lines)
        for idx, l in enumerate(out_lines):
            if l.strip():
                out_lines[idx] = rename_module(l, prefix='P')
                break

        # Determine output file path: P<basename>.agda next to input
        input_dir = os.path.dirname(infile) or '.'
        base, ext = os.path.splitext(os.path.basename(infile))
        ext = ext or '.agda'
        out_name = f"P{base}{ext}"
        out_path = os.path.join(input_dir, out_name)

        with open(out_path, 'w', encoding='utf-8') as f:
            f.write('\n'.join(out_lines) + '\n')

        print(f"Written postulated file to: {out_path}")

if __name__ == '__main__':
    main()
