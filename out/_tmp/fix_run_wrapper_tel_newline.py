import re
from pathlib import Path

p = Path("tools/telemetry/run_wrapper.py")
txt = p.read_text(encoding="utf-8").replace("\r\n", "\n").replace("\r", "\n")

# Extract TEL block
m = re.search(r"(?s)(# --- TEL post-run emission ---.*?# --- /TEL post-run emission ---)", txt)
if not m:
    raise SystemExit("TEL markers not found in run_wrapper.py")

block = m.group(1)
orig = block

# Fix the classic broken pattern: + " \n " (multiline accidental)
block = re.sub(r'\+\s*"\s*\n\s*"\s*,', r'+ "\\n",', block)
block = re.sub(r'\+\s*"\s*\n\s*"\s*', r'+ "\\n"', block)
block = re.sub(r'\+\s*"\s*\n', r'+ "\\n"\n', block)

# Sanity: ensure no dangling + " newline remains inside TEL block
if re.search(r'\+\s*"\s*\n', block):
    # show a small excerpt to help if it still fails
    bad = re.search(r'(.{0,80}\+\s*"\s*\n.{0,80})', block, re.S)
    raise SystemExit("TEL block still contains a broken string literal near: " + (bad.group(1) if bad else "<unknown>"))

if block == orig:
    print("No newline-literal repair needed (TEL block unchanged).")
else:
    txt = txt[:m.start(1)] + block + txt[m.end(1):]
    p.write_text(txt, encoding="utf-8", newline="\n")
    print("OK: repaired TEL block newline literal(s).")
