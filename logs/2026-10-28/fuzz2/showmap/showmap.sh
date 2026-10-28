#!/usr/bin/env bash
# Runs in the AFL++ image (fuzz/run.sh), at the tree's root, after fuzz/build.sh: afl-showmap over
# four seeds; prints each seed's edge count, edges one has and another lacks, and the map size.
rm -rf out/showmap && mkdir --parents out/showmap || exit 1
/py/bin/python3 -I fuzz/seeds.py out/showmap/seeds > /dev/null || exit 1
bin=.lake/fuzz/plain/lean-http-fuzz
for s in hand-content-length hand-chunked-ext-trailers hand-empty-eof hand-gzip-chunked; do
  afl-showmap -q -o "out/showmap/$s.map" -- "$bin" < "out/showmap/seeds/$s"
  echo "$s: $(wc -l < "out/showmap/$s.map") edges"
done
cut -d: -f1 out/showmap/hand-content-length.map | sort > out/showmap/a
cut -d: -f1 out/showmap/hand-chunked-ext-trailers.map | sort > out/showmap/b
cut -d: -f1 out/showmap/hand-gzip-chunked.map | sort > out/showmap/c
echo "edges in chunked but not content-length: $(comm -13 out/showmap/a out/showmap/b | wc -l)"
echo "edges in content-length but not chunked: $(comm -23 out/showmap/a out/showmap/b | wc -l)"
echo "edges in gzip-chunked but not chunked: $(comm -13 out/showmap/b out/showmap/c | wc -l)"
AFL_DEBUG=1 afl-showmap -q -o /dev/null -- "$bin" < out/showmap/seeds/hand-empty-eof 2>&1 | grep 'after guard init' | head -n 1
