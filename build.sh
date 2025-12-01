#!/usr/bin/env sh

DIR="$(readlink -f "$(dirname "$0")")"
cd "$DIR" || exit 1

case "$1" in
  ''|*[!0-9]*) DAYN="$(date +%d)" ;;
  *) DAYN="$1"; shift ;;
esac
DAY="$(echo "$DAYN" | sed 's/^0*//')"
DAYP="$(printf "%02d" "$DAY")"

lake build --no-ansi "Day$DAYP:exe" "$@"
