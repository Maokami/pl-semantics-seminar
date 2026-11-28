"""Compile the checked-in gh-aw sources in isolation and compare all outputs."""
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def generated(root):
    github = root / '.github'
    return {p.relative_to(github): p.read_bytes() for p in
            [github / 'aw/actions-lock.json', *(github / 'workflows').glob('*.lock.yml')]}


def main():
    version = subprocess.check_output(['gh', 'aw', 'version'], text=True).strip()
    if version != 'gh aw version v1.2.2':
        raise SystemExit(f'Expected gh-aw v1.2.2, found {version}')
    before = generated(ROOT)
    with tempfile.TemporaryDirectory() as work:
        root = Path(work)
        shutil.copytree(ROOT / '.github', root / '.github')
        subprocess.run(['git', 'init', '-q'], cwd=root, check=True)
        subprocess.run(['git', 'remote', 'add', 'origin', 'https://github.com/Maokami/pl-semantics-seminar'], cwd=root, check=True)
        subprocess.run(['gh', 'aw', 'compile', '--no-check-update'], cwd=root, check=True)
        after = generated(root)
        expected = {p.name.replace('.md', '.lock.yml') for p in (root/'.github/workflows').glob('*.md')}
        if expected != {p.name for p in after if p.suffix == '.yml'} or before != after:
            raise SystemExit('Workflow locks differ from the Markdown sources. Run gh aw compile.')


if __name__ == '__main__':
    main()
