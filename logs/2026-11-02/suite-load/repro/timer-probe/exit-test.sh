for k in none dedicated pool timer; do
  t0=${EPOCHREALTIME/[.,]/}
  .lake/build/bin/exitprobe $k 3000 > /dev/null
  t1=${EPOCHREALTIME/[.,]/}
  echo "$k: $(( (t1 - t0) / 1000 )) ms (t0=$t0)"
done
