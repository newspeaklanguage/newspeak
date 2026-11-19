"""Refuse a build when two sources declare the same top-level class.

The Newspeak builds glob *.ns from a staging directory, so if two files declare
the same top-level class one silently REPLACES the other -- glob order decides
the winner and the loser leaves no trace. The resulting image reports the current
commit while running code from whichever file happened to sort last.

That is not hypothetical. NewspeakTypechecker.recovered.ns, a copy rescued from a
wedged image, sat in the repository root from 2026-09-21 to 2026-09-22 and
shadowed NewspeakTypechecker.ns in every build in between: changesets appeared to
apply, BuildInfo reported the right commit, and three sessions' measurements were
taken against a stale typechecker. defective.ns was shadowing
VCSIsomorphicGitBackendProvider the same way, for far longer.

Every source in this tree declares the class its filename names, so within a
colliding group the stray is identifiable: it is the file whose name does not
match the class.

Platform namespaces (PLATFORM_NAMESPACES_DESIGN_2026-11-18.md): the modules of
platform P live in DIR/platform/P/ and are compiled as P/Name, so a class there
may share its name with one in DIR or in another platform's directory. Each
platform directory is checked as a namespace of its own, and each of its files
must name P as its category (line 2): the directory is the authority, and the
category must agree with it.

Usage: check-duplicate-modules.py DIR [DIR ...]
Exits 1 and reports every directory containing a collision.
"""
import collections
import glob
import os
import re
import sys


def duplicates_in(directory):
    declared = collections.defaultdict(list)
    for path in sorted(glob.glob(os.path.join(directory, '*.ns'))):
        text = open(path, encoding='utf-8', errors='replace').read(4000)
        match = re.search(r'^\s*class\s+(\w+)', text, re.M)
        if match:
            declared[match.group(1)].append(os.path.basename(path))
    return {cls: files for cls, files in declared.items() if len(files) > 1}


def misfiled_in(directory, platform):
    """Files in a platform directory whose category is not the platform."""
    wrong = []
    for path in sorted(glob.glob(os.path.join(directory, '*.ns'))):
        lines = open(path, encoding='utf-8', errors='replace').read(4000).splitlines()
        category = lines[1].strip().strip("'") if len(lines) > 1 else ''
        if category != platform:
            wrong.append((os.path.basename(path), category))
    return wrong


def namespaces_of(directory):
    """DIR itself, then each DIR/platform/P, with its platform name."""
    yield directory, None
    for sub in sorted(glob.glob(os.path.join(directory, 'platform', '*'))):
        if os.path.isdir(sub):
            yield sub, os.path.basename(sub)


def main(roots):
    failed = False
    directories = []
    for root in roots:
        for directory, platform in namespaces_of(root):
            directories.append(directory)
            if platform is None:
                continue
            for name, category in misfiled_in(directory, platform):
                failed = True
                print("error: %s/%s is in platform %s's directory but its category is '%s'."
                      % (directory, name, platform, category), file=sys.stderr)
    for directory in directories:
        dups = duplicates_in(directory)
        if not dups:
            continue
        failed = True
        print('error: more than one source in %s declares the same top-level class.'
              % directory, file=sys.stderr)
        print('       The compile globs *.ns, so one silently replaces the other.',
              file=sys.stderr)
        for cls, files in sorted(dups.items()):
            print('       %s <- %s' % (cls, ', '.join(files)), file=sys.stderr)
            for stray in [f for f in files if f != cls + '.ns']:
                print('         remove %s from the source directory AND from the '
                      'staging directory' % stray, file=sys.stderr)
    return 1 if failed else 0


if __name__ == '__main__':
    if len(sys.argv) < 2:
        print('usage: check-duplicate-modules.py DIR [DIR ...]', file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
