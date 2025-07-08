import os
import shutil
import subprocess
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
                # Skip html directories that we want to preserve
                if path.name == "html" and path.is_dir():
                    # Check if this is one of our documentation html directories
                    if ("proof_core/main_agda" in str(path) or 
                        "proof_core/decidability_coq" in str(path)):
                        continue
                
                if path.is_dir():
                    shutil.rmtree(path, ignore_errors=True)
                else:
                    path.unlink(missing_ok=True)

def clean_build_artifacts(base_dir):
    """Clean build artifacts while preserving HTML documentation."""
    print("Cleaning build artifacts...")
    
    # Define patterns for build artifacts that should be cleaned
    # (from .gitignore, but we want to keep html folders)
    build_patterns = [
        "*.agdai",
        "*.vo", "*.vos", "*.vok", "*.glob",
        "dist-newstyle",
        ".lia.cache",
        "*.aux", "*.log", "*.toc", "*.xdv", "*.fls",
        "*.fdb_latexmk", "*.synctex.gz",
        "*.snm", "*.vrb", "*.nav", "*.out",
        "*.bbl", "*.blg"
    ]
    
    # Clean build artifacts but preserve html directories
    for pattern in build_patterns:
        for path in base_dir.rglob(pattern):
            if path.exists():
                # Skip if this is an html directory we want to keep
                if path.name == "html" and path.is_dir():
                    continue
                    
                if path.is_dir():
                    shutil.rmtree(path, ignore_errors=True)
                    print(f"Removed directory: {path.relative_to(base_dir)}")
                else:
                    path.unlink(missing_ok=True)
                    print(f"Removed file: {path.relative_to(base_dir)}")

def run_make_commands():
    """Run make commands to generate HTML documentation."""
    print("Generating HTML documentation...")
    
    # Run build_agda_html.sh for Agda HTML generation
    build_script = REPO_DIR / "build_agda_html.sh"
    if build_script.exists():
        print(f"Running {build_script}")
        try:
            subprocess.run(["sh", str(build_script)], cwd=REPO_DIR, check=True)
            print("Agda HTML generation completed")
        except subprocess.CalledProcessError as e:
            print(f"Warning: build_agda_html.sh failed: {e}")
    
    # Run make in proof_core/decidability_coq/Dec/
    coq_dec_dir = REPO_DIR / "proof_core" / "decidability_coq" / "Dec"
    coq_parent_dir = REPO_DIR / "proof_core" / "decidability_coq"
    if coq_dec_dir.exists():
        print(f"Running make in {coq_dec_dir}")
        try:
            subprocess.run(["make"], cwd=coq_dec_dir, check=True)
            print("Coq HTML generation completed")
            
            # Move html folder from Dec/ to its parent directory
            html_source = coq_dec_dir / "html"
            html_dest = coq_parent_dir / "html"
            
            if html_source.exists():
                # Remove existing html folder in parent if it exists
                if html_dest.exists():
                    shutil.rmtree(html_dest)
                # Move the html folder
                shutil.move(str(html_source), str(html_dest))
                print(f"Moved HTML from {html_source} to {html_dest}")
            
        except subprocess.CalledProcessError as e:
            print(f"Warning: make failed in {coq_dec_dir}: {e}")

def main():
    # First, run make commands to generate HTML documentation
    run_make_commands()
    
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

        # Clean build artifacts (but preserve html directories)
        clean_build_artifacts(tmp_path)
        
        # Remove files from .gitignore (but preserve html directories)
        patterns = read_gitignore()
        # Filter out html pattern if it exists, since we want to keep html dirs
        patterns = [p for p in patterns if p.strip() != "html/"]
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

        # Remove build_agda_html.sh from the archive
        build_script = tmp_path / "build_agda_html.sh"
        if build_script.exists():
            build_script.unlink()

        # Remove html_generator directory from the archive
        html_generator_dir = tmp_path / "html_generator"
        if html_generator_dir.exists():
            shutil.rmtree(html_generator_dir, ignore_errors=True)

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