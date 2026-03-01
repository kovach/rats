chromium \
  --headless \
  --disable-gpu \
  --no-pdf-header-footer \
  --print-to-pdf=$1.pdf \
  $1.svg
pdfcrop $1.pdf $1.pdf
