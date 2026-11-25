#!/bin/sh
# Chrome's ProcessSingleton uses a Unix socket below TMPDIR. Preserve all browser
# arguments, but avoid the deep archive/evidence path for its temporary socket.
set -eu
: "${E6_SHORT_TMPDIR:?Coordinator must pass an existing private short directory}"
[ -d "$E6_SHORT_TMPDIR" ]
export TMPDIR="$E6_SHORT_TMPDIR"
exec /usr/bin/chromium "$@"
