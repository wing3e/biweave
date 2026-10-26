#!/usr/bin/env python3
"""Fetch pinned external sources without redistributing their contents."""
import argparse
import hashlib
import io
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import urllib.request
import zipfile

ROOT = Path(__file__).resolve().parents[1]
EXTERNAL = ROOT / 'external'
SOURCES = {
    'biwes': ('https://github.com/Glaviano/biwes.git', '3a22fe9fc348935bdb2fa225f993cf7c48035211'),
    'cgsampr': ('https://github.com/jscott6/cgsampr.git', '9d68a1c23fb6da7c05ea1c7f1adec7415f1e0650'),
}
EXACT_URL = 'https://jwmi.github.io/software/exact_v0.3.zip'
EXACT_SHA256 = '00f95cc76b2b70af2e39cb25091db39b11c571db18f315c3418b2b26c40d9eee'


def fetch(name):
    target = EXTERNAL / name
    if target.exists():
        raise ValueError('destination already exists: ' + str(target.relative_to(ROOT)))
    EXTERNAL.mkdir(exist_ok=True)
    with tempfile.TemporaryDirectory(dir=EXTERNAL, prefix='download_') as temporary:
        work = Path(temporary)
        if name in SOURCES:
            url, commit = SOURCES[name]
            source = work / 'source'
            subprocess.run(['git', 'init', '-q', str(source)], check=True)
            subprocess.run(['git', '-C', str(source), 'fetch', '-q', '--depth', '1', url, commit], check=True)
            subprocess.run(['git', '-C', str(source), 'checkout', '-q', '--detach', 'FETCH_HEAD'], check=True)
            actual = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
            if actual != commit:
                raise ValueError('source commit mismatch')
            shutil.rmtree(source / '.git')
        else:
            with urllib.request.urlopen(EXACT_URL, timeout=120) as response:
                payload = response.read()
            if hashlib.sha256(payload).hexdigest() != EXACT_SHA256:
                raise ValueError('EXACT archive checksum mismatch')
            source = work / 'source'
            source.mkdir()
            with zipfile.ZipFile(io.BytesIO(payload)) as archive:
                for info in archive.infolist():
                    path = Path(info.filename)
                    if path.is_absolute() or '..' in path.parts:
                        raise ValueError('unsafe external archive path')
                archive.extractall(source)
            if not (source / 'code').is_dir():
                children = list(source.iterdir())
                if len(children) != 1 or not children[0].is_dir():
                    raise ValueError('unexpected EXACT archive layout')
                source = children[0]
        shutil.move(str(source), str(target))
        if name == 'cgsampr':
            (target / 'src' / 'weighted_directed_DG_graph.h').write_text(
                '#pragma once\n#include \"weighted_graph.h\"\n'
                'int sampleDelta(const Weighted::DeltaRange&,std::default_random_engine&);\n')
    print('Fetched ' + name + ' into external/' + name)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('sources', nargs='+', choices=('biwes', 'cgsampr', 'exact', 'all'))
    args = parser.parse_args()
    names = ('biwes', 'cgsampr', 'exact') if 'all' in args.sources else args.sources
    for name in names:
        fetch(name)


if __name__ == '__main__':
    main()
