#!/usr/bin/env bash
# Render the deck to render/slide-NN.jpg for a visual check (LibreOffice + Poppler).
# The deck uses Calibri/Cambria; for faithful line breaks without them, install the
# metric-compatible Carlito/Caladea (Debian/Ubuntu: fonts-crosextra-carlito,
# fonts-crosextra-caladea), which LibreOffice substitutes automatically.
set -euo pipefail
cd "$(dirname "$0")/.."
mkdir -p render && rm -f render/slide-*.jpg render/QueryLTLEquiv.pdf
soffice --headless --convert-to pdf --outdir render QueryLTLEquiv.pptx >/dev/null
pdftoppm -jpeg -r "${DPI:-100}" render/QueryLTLEquiv.pdf render/slide
ls render/slide-*.jpg | wc -l | xargs echo "slides rendered:"
