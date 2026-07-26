# Locating a clause in the PDF

`~/LRM.pdf` is IEEE 1800-2023, 1354 PDF pages. The printed page number is
the physical page minus one: §10.1 General is physical page 248, printed
247.

`pdftotext`, `pdfgrep`, `pdftohtml`, `pdftoppm` and `mutool` are blocked by
the Bash deny hook. `pdfinfo` and `python3` with `pypdf` are allowed.
Resolving a clause to a page from the bookmarks reads metadata only, so it
costs nothing against the content-filter budget:

```python
import pypdf
r = pypdf.PdfReader('/Users/jdrowne/LRM.pdf')
def walk(o):
    for it in o:
        if isinstance(it, list):
            walk(it)
            continue
        print(it.title.strip(), '->', r.get_destination_page_number(it) + 1)
walk(r.outline)
```

Then Read the resolved physical pages. Section 10, "Assignment
statements", spans physical pages 248 to 269 and ends at §10.11, "Net
aliasing"; section 11 starts at physical page 270. There is no §10.12,
§10.13 or §10.14.
