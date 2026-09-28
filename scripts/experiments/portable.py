"""Remove local installation paths from persisted runner records, not execution."""
from pathlib import Path
import sys


def portable_text(text, root):
    root = str(Path(root).resolve())
    text = text.replace(root + "/", "./")
    text = text.replace('"' + root + '"', '"."')
    text = text.replace(sys.executable, Path(sys.executable).name)
    home = str(Path.home())
    if home != "/":
        text = text.replace(home + "/", "<home>/")
    return text
