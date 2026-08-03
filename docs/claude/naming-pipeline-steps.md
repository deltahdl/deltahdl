# Naming pipeline steps

Never name a step "Step 0" when adding one to a numbered sequence of steps, such as the list `build_steps` returns. It is an off-by-one tell: it signals retrofitting rather than redesign, and it makes the sequence look as though it always had an unnamed preamble. It also ages badly, since every later reader has to work out which step really runs first.

When inserting a step — into `build_steps` in `scripts/satisfy_subclause/mutators.py`, for instance — either renumber so the new step takes a real position and the rest shift, or give it a descriptive name with no number at all.
