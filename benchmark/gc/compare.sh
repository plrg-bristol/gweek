#!/usr/bin/env bash
# Join results-main.csv and results-gc.csv into a side-by-side peak-memory table.
# Uses the median peak across repeats per (program, strategy).
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

awk -F, '
  FNR==1 { next }                         # skip headers
  {
    key=$2" "$3; kind[key]=$4
    n=++cnt[$1,key]; peak[$1,key,n]=$8    # peak_mb per repeat
    seen[key]=1
  }
  function median(label, key,   m,i,vals,t,j) {
    m=cnt[label,key]; if(m==0) return -1
    for(i=1;i<=m;i++) vals[i]=peak[label,key,i]
    for(i=1;i<=m;i++) for(j=i+1;j<=m;j++) if(vals[j]<vals[i]){t=vals[i];vals[i]=vals[j];vals[j]=t}
    return vals[int((m+1)/2)]
  }
  END {
    fmt="%-13s %-5s %-9s %10s %10s %9s\n"
    printf fmt, "program","strat","kind","main MB","gc MB","change"
    printf fmt, "-------","-----","----","-------","-----","------"
    order="perm bfs|perm fair|perm dfs|nqueens bfs|nqueens fair|nqueens dfs|coins bfs|coins fair|coins dfs|pythagorean bfs|pythagorean fair|pythagorean dfs"
    n=split(order,ks,"|")
    for(i=1;i<=n;i++){
      key=ks[i]; if(!seen[key]) continue
      split(key,p," ")
      mm=median("main",key); gg=median("gc",key)
      ch=(mm>0)? sprintf("%+.0f%%",(gg-mm)/mm*100) : "n/a"
      printf fmt, p[1],p[2],kind[key], sprintf("%.1f",mm), sprintf("%.1f",gg), ch
    }
  }
' "$HERE/results-main.csv" "$HERE/results-gc.csv"
