#!/usr/bin/env bash
# the release, again or for the first time: tested, written to target/pages-maven, put on gh-pages, the tag moved —
# while nobody else uses it, one version is republished (the user's rule)
set -euo pipefail
cd "$(dirname "$0")/.."
version=$(sed -n 's/^ThisBuild \/ version := "\(.*\)"/\1/p' build.sbt)
rm -rf target/pages-maven
sbt -batch proofJVM/test proofJS/test policyJVM/test policyJS/test \
  proofJVM/publish proofJS/publish policyJVM/publish policyJS/publish
pages=$(mktemp -d)/pages
git fetch -q origin gh-pages
git worktree add -q "$pages" origin/gh-pages
rsync -a target/pages-maven/ "$pages/maven/"
(cd "$pages" && git add -A && (git commit -qm "release $version" || true) && git push -q origin HEAD:gh-pages)
git worktree remove --force "$pages"
git tag -f "v$version" && git push -q origin master && git push -qf origin "v$version"
rm -rf ~/Library/Caches/Coursier/v1/https/okay-effects.github.io/okay-proof
echo "released $version"
