#!/usr/bin/env python3
"""Losslessly compact old recursive cache JSON, with streaming round-trip verification.

One-off tool; requires ijson (the build wrapper itself remains standard-library only).
No Lean source, artifact, or provenance value is changed. Every JSON parse event
is compared against the expanded compact representation before atomic replacement.
"""
import argparse
import itertools
import json
import os
from pathlib import Path
import sys
import time
import uuid

# Optional project-local installation for this one-off maintenance tool.
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'logs/cache_migration_tools'))
import ijson


def compact_stream(stream):
    nodes, intern, stack = [], {}, []
    root = None

    def signature(v):
        return ('ref', v['ref']) if isinstance(v, dict) else (type(v).__name__, v)

    def accept(v):
        nonlocal root
        if not stack:
            root = v
        elif stack[-1][0] == 'list':
            stack[-1][1].append(v)
        else:
            frame = stack[-1]
            if frame[2] is None:
                raise ValueError('Missing object key')
            frame[1].append([frame[2], v])
            frame[2] = None

    for event, value in ijson.basic_parse(stream, use_float=True):
        if event in ('start_map', 'start_array'):
            stack.append(['dict' if event == 'start_map' else 'list', [], None])
        elif event == 'map_key':
            stack[-1][2] = value
        elif event in ('end_map', 'end_array'):
            kind, items, key = stack.pop()
            if kind == 'dict':
                if key is not None or len({k for k, _ in items}) != len(items):
                    raise ValueError('Malformed or duplicate object keys')
                sig = (kind, tuple((k, signature(v)) for k, v in items))
            else:
                sig = (kind, tuple(signature(v) for v in items))
            index = intern.get(sig)
            if index is None:
                index = len(nodes)
                intern[sig] = index
                nodes.append([kind, items])
            accept({'ref': index})
        else:
            accept(value)
    if stack:
        raise ValueError('Unterminated JSON')
    return {'record_encoding': 'shared-json-v1', 'root': root, 'nodes': nodes}


def expanded_events(packed):
    def visit(value):
        if isinstance(value, dict):
            kind, items = packed['nodes'][value['ref']]
            yield ('start_map' if kind == 'dict' else 'start_array', None)
            if kind == 'dict':
                for key, child in items:
                    yield ('map_key', key)
                    yield from visit(child)
            else:
                for child in items:
                    yield from visit(child)
            yield ('end_map' if kind == 'dict' else 'end_array', None)
        else:
            event = ('null' if value is None else 'boolean' if isinstance(value, bool)
                     else 'string' if isinstance(value, str) else 'number')
            yield event, value
    yield from visit(packed['root'])


def verify_stream(stream, packed):
    missing = object()
    for index, (a, b) in enumerate(itertools.zip_longest(
            ijson.basic_parse(stream, use_float=True), expanded_events(packed), fillvalue=missing)):
        if a is missing or b is missing or a != b or type(a[1]) is not type(b[1]):
            raise ValueError(f'Round-trip mismatch at JSON event {index}')


def convert(path):
    with path.open('rb') as f:
        first_key = next(value for event, value in ijson.basic_parse(f) if event == 'map_key')
    if first_key == 'record_encoding':
        return None
    if first_key != 'schema':
        raise ValueError(f'Unexpected legacy record layout: {path}')
    start = time.monotonic()
    before = path.stat()
    with path.open('rb') as f:
        packed = compact_stream(f)
    # Check serialized output too, not only its in-memory representation.
    text = json.dumps(packed, indent=2) + '\n'
    packed = json.loads(text)
    with path.open('rb') as f:
        verify_stream(f, packed)
    current = path.stat()
    if (before.st_ino, before.st_size, before.st_mtime_ns) != (
            current.st_ino, current.st_size, current.st_mtime_ns):
        raise RuntimeError(f'Record changed during conversion: {path}')
    temporary = path.with_name(path.name + '.' + uuid.uuid4().hex + '.tmp')
    temporary.write_text(text)
    os.replace(temporary, path)
    return dict(path=str(path), before_bytes=before.st_size, after_bytes=path.stat().st_size,
                seconds=time.monotonic()-start, exact_event_roundtrip=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    parser.add_argument('--min-bytes', type=int, default=1_000_000)
    parser.add_argument('--report', type=Path, required=True)
    args = parser.parse_args()
    for path in sorted(args.directory.glob('*.json'), key=lambda p: p.stat().st_size):
        if path.stat().st_size < args.min_bytes:
            continue
        result = convert(path)
        if result:
            line = json.dumps(result)
            with args.report.open('a') as f:
                f.write(line + '\n')
            print(line, flush=True)


if __name__ == '__main__':
    main()
