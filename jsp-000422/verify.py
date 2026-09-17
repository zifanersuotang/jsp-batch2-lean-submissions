#!/usr/bin/env python3
"""Check published metadata/logs by default; --execute performs a fresh complete replay.

Python 3.10+. No installation, Lake build, cache download or shared-cache writes.
Supply Lean 4.33.0 and an already cached Mathlib checkout at the recorded commit.
--plan displays the fresh commands without running a subprocess or downloading.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import time
import urllib.parse
import urllib.request

HERE = Path(__file__).resolve().parent
UPSTREAM_SHA256 = 'e50d722260caebe03beb35a738baa45486c812ac313739c5ee63d2eda610e019'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
NAME = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*')
HASH = re.compile(r'[0-9a-f]{64}')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def save(path, value):
    path.write_bytes((json.dumps(value, ensure_ascii=False, indent=2) + '\n').encode('utf-8'))


def under(root, relative):
    require(isinstance(relative, str) and bool(relative), 'Missing relative path')
    pure = PurePosixPath(relative)
    require(not pure.is_absolute() and str(pure) == relative and
            all(x not in ('.', '..') for x in pure.parts) and
            not any(x in relative for x in ('\\', ':', '\0')), 'Unsafe relative path')
    path = root / relative
    require(path.resolve().is_relative_to(root.resolve()), 'Path escapes its root')
    return path


def parse_axioms(text, names):
    parsed, raw = {}, {}
    for match in re.finditer(r"'([^']+)' (?:depends on axioms:\s*\[([^]]*)\]|does not depend on any axioms)", text, re.S):
        if match[1] not in names:
            continue
        atoms = []
        for token in re.split(r',\s*(?![^{}]*\})', match[2] or ''):
            if not token.strip():
                continue
            atom = re.fullmatch(r'([A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*)(?:\.\{[^{}]+\})?', token.strip())
            require(atom is not None, 'Malformed printed axiom')
            atoms.append(atom[1])
        require(len(set(atoms)) == len(atoms) and set(atoms) <= ALLOWED, 'Nonstandard or repeated axiom')
        require(match[1] not in parsed or parsed[match[1]] == atoms, 'Conflicting axiom reports')
        parsed[match[1]], raw[match[1]] = atoms, match[0]
    require(set(parsed) == set(names), 'Missing requested axiom report')
    return {n: parsed[n] for n in names}, {n: raw[n] for n in names}


def selection(text, expected):
    actual = re.findall(r'(?m)^replaying ([A-Za-z_0-9.]+)\s*$', text)
    require(len(actual) == len(set(actual)) and set(actual) == set(expected), 'Actual checker selection differs')
    return actual


def strip_comments_strings(text):
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        if depth:
            if text.startswith('/-', i): depth += 1; i += 2; out.append('  ')
            elif text.startswith('-/', i): depth -= 1; i += 2; out.append('  ')
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif quoted:
            if text[i] == '\\': out.append('  '); i += 2
            else: quoted = text[i] != '"'; out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end == -1: out.append(' ' * (len(text) - i)); break
            out.append(' ' * (end - i)); i = end
        elif text.startswith('/-', i): depth = 1; i += 2; out.append('  ')
        elif text[i] == '"': quoted = True; i += 1; out.append(' ')
        else: out.append(text[i]); i += 1
    require(depth == 0 and not quoted, 'Unclosed source comment or string')
    return ''.join(out)


def validate(metadata, evidence, base=HERE):
    """Read local included sources and logs only; no subprocess or network."""
    require(metadata['schema_version'] == evidence['schema_version'] == 1, 'Unsupported schema')
    require(metadata['jsp'] == evidence['jsp'] == 'JSP-000422', 'Wrong catalog item')
    require(evidence['status'] == 'verified' and evidence['observed_wrapper_exit_code'] == 0, 'Unverified record')
    sources = metadata['sources']
    order = [s['module'] for s in sources]
    require(len(order) == len(set(order)) == 7 and order == metadata['build_order'], 'Incomplete build order')
    require(all(NAME.fullmatch(n) for n in order), 'Unsafe module name')
    included, downloaded = [], []
    for row in sources:
        require(HASH.fullmatch(row['sha256']) and type(row['bytes']) is int and row['bytes'] > 0, 'Bad source digest/size')
        require(row['relative_file'] == row['module'].replace('.', '/') + '.lean', 'Module/file mismatch')
        path = under(base, row['relative_file'])
        if row['kind'] == 'included_bridge':
            data = path.read_bytes()
            require(sha(data) == row['sha256'] and len(data) == row['bytes'], 'Included bridge bytes changed')
            require(evidence['candidate_sha256'][row['module']] == row['sha256'], 'Bridge evidence hash mismatch')
            included.append(row['module'])
        else:
            require(row['kind'] == 'download' and not path.exists(), 'Upstream source must not be vendored')
            tail = 'plby/lean-proofs/' + metadata['source_commit'] + '/src/latest/' + row['relative_file']
            require(row['raw_url'] == 'https://raw.githubusercontent.com/' + tail, 'Unpinned or mismatched raw URL')
            require(row['source_url'] == 'https://github.com/plby/lean-proofs/blob/' + metadata['source_commit'] + '/src/latest/' + row['relative_file'], 'Unpinned view URL')
            require(re.fullmatch(r'[0-9a-f]{40}', row['git_blob_sha1']) is not None, 'Bad upstream blob ID')
            downloaded.append(row['module'])
    require(included == ['FiniteHeadBridge', 'StrictOnceCriterion', 'LargeArcBridge'] and len(downloaded) == 4, 'Wrong source partition')
    audit = metadata['audit']
    audit_bytes = under(base, audit['file']).read_bytes()
    require(sha(audit_bytes) == audit['sha256'] == evidence['audit_sha256'], 'Audit bytes changed')
    names = audit['declarations']
    require(len(names) == len(set(names)) == 17 and metadata['main_theorem'] in names, 'Incomplete declaration audit')
    require(all(NAME.fullmatch(n) for n in names), 'Unsafe theorem name')
    require(set(metadata['axiom_whitelist']) == ALLOWED, 'Changed axiom whitelist')
    for rel, log in evidence['logs'].items():
        data = under(base, rel).read_bytes()
        require(sha(data) == log['published_sha256'] and len(data) == log['published_bytes'], 'Published log digest/size mismatch')
        require(HASH.fullmatch(log['original_sha256']) is not None, 'Missing original log hash')
        if log['bytes_unchanged']:
            require(not log['redactions'] and log['original_sha256'] == log['published_sha256'] and
                    log['original_bytes'] == log['published_bytes'], 'Incorrect unchanged-log claim')
        else:
            require(bool(log['redactions']), 'Unexplained changed log bytes')
    events = evidence['events']
    require(len(events) == 12 and all(e['exit_code'] == 0 for e in events), 'Incomplete successful events')
    require([e['stage'] for e in events] == ['compile'] * 7 + ['audit'] + ['leanchecker'] * 4, 'Wrong actual event sequence')
    require([e['module'] for e in events[:7]] == order, 'Compilation coverage mismatch')
    require([e['origin_attempt'] for e in events] == ['v4'] * 6 + ['v5'] * 6, 'Misstated compilation reuse')
    require(evidence['new_v5_process_count'] == evidence['reused_v4_compilation_event_count'] == 6, 'Wrong reuse counts')
    for event in events + evidence['failed_attempts']:
        require(event['log_sha256'] == evidence['logs'][event['log']]['published_sha256'], 'Event log mismatch')
    for event in events[:8]:
        command = event['recorded_command_with_paths_redacted']
        require(command[1:4] == ['-j1', '-M8192', '-o'], 'Recorded compile flags differ')
    actual, raw = parse_axioms(under(base, events[7]['log']).read_text(encoding='utf-8'), names)
    require(actual == evidence['actual_axioms'] and raw == evidence['actual_axiom_reports_raw'], 'Published axiom summary differs from log')
    roots = metadata['checker_targets']
    require([x['module'] for x in roots] == ['ErdosProblems.Erdos526', 'FiniteHeadBridge', 'StrictOnceCriterion', 'LargeArcBridge'], 'Wrong replay roots')
    for target, event in zip(roots, events[8:], strict=True):
        root = target['module']
        expected = [m for m in order if m == root or m.startswith(root + '.')]
        require(set(expected) == set(target['expected_selected_modules']) and event['module'] == root, 'Wrong structural Name scope')
        require(event['recorded_command_with_paths_redacted'][1:] == ['--verbose', root], 'Unexpected checker flags')
        selected = selection(under(base, event['log']).read_text(encoding='utf-8'), expected)
        require(selected == evidence['actual_checker_modules'][root], 'Recorded selection differs from actual log')
    require(not re.search(r'(?i)(?:[a-z]:[\\/]|/Users/|/home/)', json.dumps(evidence)), 'Private path in public evidence')
    return {'status': 'metadata_and_published_logs_passed', 'source_compile_events': 7,
            'included_bridges': 3, 'downloaded_upstream_modules_on_execute': 4,
            'audited_declarations': 17, 'actual_replay_counts': [4, 1, 1, 1],
            'lean_started': False, 'network_used': False}


def load(base=HERE):
    raw = (base / 'upstream.json').read_bytes()
    require(sha(raw) == UPSTREAM_SHA256, 'Pinned upstream metadata changed')
    metadata = json.loads(raw)
    evidence = json.loads((base / 'verification.json').read_text(encoding='utf-8'))
    require(evidence['upstream_json_sha256'] == sha(raw), 'Evidence/metadata mismatch')
    return metadata, evidence


def tool_path(directory, name):
    return directory / (name + '.exe' if (directory / (name + '.exe')).is_file() else name)


def command_plan(metadata, lean_bin, output):
    src, build = output / 'src', output / 'build'
    stages = []
    for row in metadata['sources']:
        stages.append({'stage': 'compile', 'module': row['module'], 'command': [str(tool_path(lean_bin, 'lean')), '-j1', '-M8192', '-o', str(build / Path(row['relative_file']).with_suffix('.olean')), row['relative_file']]})
    audit = metadata['audit']
    stages.append({'stage': 'audit', 'module': audit['module'], 'command': [str(tool_path(lean_bin, 'lean')), '-j1', '-M8192', '-o', str(build / (audit['module'] + '.olean')), audit['file']]})
    stages += [{'stage': 'leanchecker', 'module': t['module'], 'command': [str(tool_path(lean_bin, 'leanchecker')), '--verbose', t['module']], 'expected_selected_modules': t['expected_selected_modules']} for t in metadata['checker_targets']]
    return src, build, stages


class RejectRedirects(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None


def download(row):
    opener = urllib.request.build_opener(RejectRedirects())
    with opener.open(row['raw_url'], timeout=60) as response:
        require(response.status == 200, 'Source download did not return HTTP 200')
        require(response.geturl() == row['raw_url'], 'Source response URL differs from its pinned URL')
        return response.read(row['bytes'] + 1)


def materialize(metadata, source_root, package=HERE, fetch=download):
    """Write only fixed source bytes into a fresh isolated directory; refuse conflicts."""
    seen = set()
    for row in metadata['sources']:
        data = fetch(row) if row['kind'] == 'download' else under(package, row['relative_file']).read_bytes()
        require(len(data) == row['bytes'] and sha(data) == row['sha256'], 'Downloaded/included source mismatch')
        if row['kind'] == 'download':
            require(hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == row['git_blob_sha1'], 'Git blob mismatch')
        clean = strip_comments_strings(data.decode('utf-8'))
        require(not re.search(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by)\b', clean), 'Untrusted proof marker')
        imports = re.findall(r'(?m)^\s*(?:public\s+)?import\s+([\w.]+)', clean)
        require(imports == row['imports'], 'Source imports changed')
        require(all(m in seen or m == 'Mathlib' or m.startswith('Mathlib.') for m in imports), 'Incomplete/topologically invalid custom closure')
        target = under(source_root, row['relative_file'])
        target.parent.mkdir(parents=True, exist_ok=True)
        with target.open('xb') as out: out.write(data)
        seen.add(row['module'])
    audit = metadata['audit']
    data = under(package, audit['file']).read_bytes()
    require(sha(data) == audit['sha256'], 'Audit changed')
    with under(source_root, audit['file']).open('xb') as out: out.write(data)


def execute(metadata, mathlib, lean_bin, output, package=HERE, fetch=download):
    require(not output.exists(), 'Output already exists; choose a fresh dedicated directory')
    require(not output.is_relative_to(mathlib) and not output.is_relative_to(package), 'Output must be outside Mathlib and this package')
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    env['PATH'] = str(lean_bin) + os.pathsep + env.get('PATH', '')
    head = subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True, env=env).strip()
    require(head == metadata['mathlib_commit'], 'Wrong Mathlib commit')
    require((mathlib / 'lean-toolchain').read_text().strip() == metadata['lean_toolchain'], 'Wrong toolchain file')
    lean, checker = tool_path(lean_bin, 'lean'), tool_path(lean_bin, 'leanchecker')
    require(lean.is_file() and checker.is_file(), 'Missing explicit Lean/checker executable')
    version = subprocess.check_output([str(lean), '--version'], text=True, env=env).strip()
    require(re.search(r'\bversion\s+4\.33\.0(?:[,\s]|$)', version) is not None, 'Actual Lean is not 4.33.0')
    caches = [mathlib / '.lake/build/lib/lean']
    require((caches[0] / 'Mathlib.olean').is_file(), 'Mathlib cache is not installed')
    packages = mathlib / '.lake/packages'
    if packages.is_dir():
        caches += sorted(p / '.lake/build/lib/lean' for p in packages.iterdir() if (p / '.lake/build/lib/lean').is_dir())
    src, build, stages = command_plan(metadata, lean_bin, output)
    output.mkdir(parents=True, exist_ok=False)
    src.mkdir(); build.mkdir(); logs = output / 'logs'; logs.mkdir()
    result = {'status': 'running', 'fresh_custom_compilation': True, 'private_object_reuse': False,
        'lean_version': version, 'mathlib_commit': head, 'toolchain': metadata['lean_toolchain'],
        'LEAN_NUM_THREADS': '1', 'runtime_binary_sha256': {p.name: sha(p.read_bytes()) for p in (lean, checker)},
        'sources': [{'module': s['module'], 'sha256': s['sha256']} for s in metadata['sources']],
        'events': [], 'actual_axioms': None, 'actual_checker_modules': {}}
    save(output / 'result.json', result)
    try:
        materialize(metadata, src, package, fetch)
        env['LEAN_PATH'] = os.pathsep.join(map(str, [build, src, *caches]))
        compiled = set()
        for i, stage in enumerate(stages):
            command = stage['command']
            if stage['stage'] != 'leanchecker':
                Path(command[4]).parent.mkdir(parents=True, exist_ok=True)
            if stage['stage'] == 'compile':
                row = metadata['sources'][i]
                require(all(m in compiled or m == 'Mathlib' or m.startswith('Mathlib.') for m in row['imports']), 'Refuse cached custom-import fallback')
            log = logs / f'{i:02d}-{stage["stage"]}-{stage["module"]}.log'
            event = {'stage': stage['stage'], 'module': stage['module'], 'command': command,
                'start_utc': datetime.now(timezone.utc).isoformat(), 'exit_code': None, 'log': log.relative_to(output).as_posix()}
            result['events'].append(event); save(output / 'result.json', result)
            started = time.monotonic()
            with log.open('xb') as stream:
                child = subprocess.run(command, cwd=src, env=env, stdout=stream, stderr=subprocess.STDOUT)
            event.update(exit_code=child.returncode, seconds=round(time.monotonic() - started, 3),
                end_utc=datetime.now(timezone.utc).isoformat(), log_sha256=sha(log.read_bytes()))
            save(output / 'result.json', result)
            require(child.returncode == 0, f'{stage["stage"]} failed: {stage["module"]}; see {log}')
            text = log.read_text(encoding='utf-8')
            if stage['stage'] == 'compile':
                require(Path(command[4]).is_file(), 'Compiler did not produce the expected local object')
                compiled.add(stage['module'])
            elif stage['stage'] == 'audit':
                result['actual_axioms'], result['actual_axiom_reports_raw'] = parse_axioms(text, metadata['audit']['declarations'])
            else:
                result['actual_checker_modules'][stage['module']] = selection(text, stage['expected_selected_modules'])
            save(output / 'result.json', result)
        for row in metadata['sources']:
            require(sha(under(src, row['relative_file']).read_bytes()) == row['sha256'], 'Source changed during execution')
        require(sha(under(src, metadata['audit']['file']).read_bytes()) == metadata['audit']['sha256'], 'Audit changed during execution')
        require(subprocess.check_output(['git', '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True, env=env).strip() == head, 'Mathlib changed during execution')
        for tool in (lean, checker):
            require(sha(tool.read_bytes()) == result['runtime_binary_sha256'][tool.name], 'Runtime binary changed')
        result['status'] = 'verified_fresh_custom_compilation'
        save(output / 'result.json', result)
        return result
    except Exception as error:
        result.update(status='failed', error=f'{type(error).__name__}: {error}')
        save(output / 'result.json', result)
        raise


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--execute', action='store_true')
    mode.add_argument('--plan', action='store_true')
    parser.add_argument('--mathlib', type=Path, help='Already cached, pinned Mathlib checkout; read-only')
    parser.add_argument('--lean-bin', type=Path, help='Directory containing Lean 4.33.0 and leanchecker')
    parser.add_argument('--output', type=Path, help='New dedicated directory outside Mathlib and this package')
    args = parser.parse_args()
    metadata, evidence = load()
    summary = validate(metadata, evidence)
    if not args.execute and not args.plan:
        print(json.dumps(summary, indent=2)); return
    require(args.mathlib is not None and args.lean_bin is not None and args.output is not None,
            '--plan/--execute requires --mathlib, --lean-bin and --output')
    mathlib, lean_bin, output = (p.resolve() for p in (args.mathlib, args.lean_bin, args.output))
    if args.plan:
        src, build, stages = command_plan(metadata, lean_bin, output)
        print(json.dumps({'status': 'plan_only_not_executed', 'cwd': str(src), 'build': str(build),
            'LEAN_NUM_THREADS': '1', 'fresh_custom_compile_count': 7, 'stage_count': 12,
            'stages': stages, 'network_used': False, 'lean_started': False}, indent=2))
        return
    result = execute(metadata, mathlib, lean_bin, output)
    print(json.dumps({'status': result['status'], 'event_count': len(result['events']),
        'result_file': str(output / 'result.json')}, indent=2))


if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
