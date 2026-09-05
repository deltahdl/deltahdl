# Filing what a session finds

File the issue when the session finds the defect. Do not describe it in a reply and ask whether to file it.

A reply is not a record. The next session reads the repository and the issue tracker, and a defect that lives in a transcript is one nobody will meet again. Asking first also puts the finding at the end of a queue of its own: the answer arrives after the session that found it has moved on, and the reading that made the finding possible has to be done a second time to write it up.

Most findings arrive while working on something else. Reading `SynthLower::LowerIncDecStmt` into place under #3007 is what showed that `SynthLower::LowerBinaryBit` answers `AigGraph::kConstFalse` for every operator it has no arm for, which became #3028, #3029 and #3030. Finish the work in hand first, then file, so the issue is written from what the reading established rather than from what the fix happened to touch.

## What does not get filed

A defect the commit in hand fixes. The commit message states it and the issue would close on the same push.

A defect an open issue already covers. Cite that issue. A second issue over one defect gives one piece of work two entries, and closing either leaves the other claiming there is something left.

## Splitting what one reading found

One reading often turns up more than one scope. `LowerBinaryBit`'s `default` arm answers a constant for the arithmetic operators, for the comparisons and for the shifts, and those became three issues rather than one, because each closes by finishing and the third does not wait on the first two to be worth reading. Deciding this is the work of filing, and an issue that would only close when a whole family did is the shape to avoid.
