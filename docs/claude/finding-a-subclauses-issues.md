# Finding every issue a subclause has

Take the issue `next_subclause` names and then look for its neighbours by
number, because a subclause with subclauses of its own has an issue for each
and they are not all findable by searching.

`PYTHONPATH=.:scripts python3 -m next_subclause` prints one subclause and one
issue. Where that subclause has a Syntax and a Description beneath it, two more
issues exist and the printed one is the parent: §34.5.28 is #2066, §34.5.28.1 is
#2068 and §34.5.28.2 is #2070. The parent sorts first in
`docs/dependency_graph.json`, which is why it is the one printed, and it has no
prose of its own to satisfy -- what it states is the two subclauses beneath it.

`gh issue list --search "34.5.29 in:title"` returned only the parent while
#2073 and #2075 stood open. Whatever the reason, the search is not what to trust
here. `gh issue view <n>` on the numbers around the parent answers directly, and
the numbers run in the order the subclauses do.

The cost of missing them is two issues left open behind work that closed them.
Commit `6e7e93166` covered §34.5.29.1 and §34.5.29.2 and named neither, because
the search had said neither existed; both had to be closed afterwards against a
commit that did not mention them. A `Closes` line in the commit is what ties the
work to the issue for whoever reads `git log`, and closing an issue by hand
leaves that tie in a comment instead.

Close the parent alongside its children in the one commit. `b97f191f6` closed
§34.5.26's parent and §34.5.9's together with the work that satisfied them, and
`334d33406` closed §34.5.28's three the same way.
