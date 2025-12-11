#!/usr/bin/env sh

DIR="$(readlink -f "$(dirname "$0")")"
cd "$DIR" || exit 1

case "$1" in
  ''|*[!0-9]*) DAYN="$(date +%d)" ;;
  *) DAYN="$1"; shift ;;
esac
DAY="$(echo "$DAYN" | sed 's/^0*//')"
DAYP="$(printf "%02d" "$DAY")"

export AOC_INPUT
case "$1" in
 --) AOC_INPUT="/dev/stdin"; shift ;;
 -e | --example) AOC_INPUT="$DIR/inputs/example$DAYP.txt"; shift ;;
 -e* | --example=*)
     EXAMPLENO="$(echo "$1" | sed -E 's/-e|--example//')"
     AOC_INPUT="$DIR/inputs/example$DAYP.$EXAMPLENO.txt"; shift ;;
 -i | --input) AOC_INPUT="$2"; shift; shift ;;
 "")
     AOC_INPUT="$DIR/inputs/day$DAYP.txt"
     if ! [ -f "$AOC_INPUT" ]
     then raco aoc -y 2025 -d "$DAY" > "$AOC_INPUT" || exit 1
     fi ;;
esac

./build.sh "$DAY" || exit 1
time ".lake/build/bin/Day$DAYP" "$@" < "$AOC_INPUT"
