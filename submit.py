import os
import shutil
import tempfile
import zipfile
from pathlib import Path

REPO_DIR = Path.cwd()
ARCHIVE_NAME = "submission.zip"
SCRIPT_NAME = "submit.py"

def read_gitignore():
    patterns = []
    gitignore = REPO_DIR / ".gitignore"
    if gitignore.exists():
        with open(gitignore) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#"):
                    patterns.append(line)
    return patterns

def remove_patterns(base_dir, patterns):
    for pattern in patterns:
        # Use rglob for recursive matching
        for path in base_dir.rglob(pattern):
            if path.exists():
                if path.is_dir():
                    shutil.rmtree(path, ignore_errors=True)
                else:
                    path.unlink(missing_ok=True)

def main():
    with tempfile.TemporaryDirectory() as tmpdir:
        tmp_path = Path(tmpdir)
        # Copy all files except .git and .gitmodules
        for item in REPO_DIR.iterdir():
            if item.name in [".git", ".gitmodules"]:
                continue
            dest = tmp_path / item.name
            if item.is_dir():
                shutil.copytree(item, dest, ignore=shutil.ignore_patterns('.git', '.gitmodules'))
            else:
                shutil.copy2(item, dest)

        # Remove files from .gitignore
        patterns = read_gitignore()
        remove_patterns(tmp_path, patterns)

        # Remove git-related files
        for name in [".git", ".gitmodules", ".gitignore"]:
            target = tmp_path / name
            if target.exists():
                if target.is_dir():
                    shutil.rmtree(target, ignore_errors=True)
                else:
                    target.unlink(missing_ok=True)

        # Remove other unwanted files (add patterns as needed)
        remove_patterns(tmp_path, ["*.swp", "*.bak"])

        # Remove this script from the archive
        script_in_tmp = tmp_path / SCRIPT_NAME
        if script_in_tmp.exists():
            script_in_tmp.unlink()

        # Create zip archive
        archive_path = REPO_DIR / ARCHIVE_NAME
        with zipfile.ZipFile(archive_path, 'w', zipfile.ZIP_DEFLATED) as zipf:
            for root, dirs, files in os.walk(tmp_path):
                for file in files:
                    file_path = Path(root) / file
                    zipf.write(file_path, file_path.relative_to(tmp_path))

    print(f"Archive created at {archive_path}")

if __name__ == "__main__":
    main()