# The blocked-by sequence

Every open issue numbered above #2939 sits in one linear sequence, ordered by GitHub's blocked-by relation. Exactly one issue in it is blocked by nothing open, and that issue is what gets worked next. Everything else waits behind it in a single file.

A new issue joins the sequence at the moment it is created. Prepend it, append it, or interpose it between two links. Creating one with no blocked-by edge is the failure this note exists to prevent: two issues then claim to be next, and nothing in the repository says which.

The order has to make sense. Placement is a claim that the work above the new issue comes first and the work below it comes after, so read the neighbours before inserting rather than appending because appending is easiest.

## An issue owns one scope and indexes nothing

Give each issue a scope it can close by finishing. An issue that lists other issues is not a work item, and it cannot leave the sequence, because whatever it tracks always has something left.

That mistake was made in #2961 and undone. #2961 was rewritten to enumerate the batches converting 3,179 assertions, with #3016 and #3017 attached as sub-issues. It then closed only when all of them did, so the ten issues behind it in the sequence waited on the whole programme. It now owns one component's assertions, the tree-wide count stays in it as the statement of the defect, and the other components are separate issues placed in the sequence.

Reference another issue freely. `#2961 settles what a converted assertion asserts` is a citation, and citations are how an issue stays self-contained without repeating what another one established. A list of children is what is barred.

## Reading and editing the sequence

The relation lives behind `gh api`, not `gh issue`. Read one issue's blockers with

```bash
gh api repos/deltahdl/deltahdl/issues/<N>/dependencies/blocked_by \
  -q '[.[] | "\(.number)(\(.state))"] | join(",")'
```

Add and remove edges by the blocker's `id`, which is the GitHub object id and not the issue number:

```bash
id=$(gh api repos/deltahdl/deltahdl/issues/<BLOCKER> -q .id)
gh api -X POST   repos/deltahdl/deltahdl/issues/<N>/dependencies/blocked_by -F issue_id=$id
gh api -X DELETE repos/deltahdl/deltahdl/issues/<N>/dependencies/blocked_by/$id
```

Use `-F` and not `-f`. `-f` sends the id as a string and the request fails with `422 Invalid property /issue_id: "5135762695" is not of type integer`.

Interposing takes two edits, not one. To put `<NEW>` between `<BEFORE>` and `<AFTER>`, add `<NEW>` blocked by `<BEFORE>`, then delete `<AFTER>` blocked by `<BEFORE>` and add `<AFTER>` blocked by `<NEW>`. Leaving the old edge in place is harmless to the ordering but hides where the sequence was cut.

## Mending the cut when an issue closes out of order

Closing an issue that is not the head leaves two heads. Block the orphaned successor on the nearest predecessor still open:

```bash
id=$(gh api repos/deltahdl/deltahdl/issues/<NEAREST-OPEN-PREDECESSOR> -q .id)
gh api -X POST repos/deltahdl/deltahdl/issues/<ORPHANED-SUCCESSOR>/dependencies/blocked_by -F issue_id=$id
```

That is expected rather than a breach. Closing the head promotes its successor and needs no edit, because a head whose only blockers are closed is the head. Closing anything else promotes a second one alongside it, and the sequence has two heads until the cut is mended.

It happens whenever a session solves a defect it filed while working the head. `.claude/skills/autopilot/SKILL.md` calls for exactly that -- "Where a defect you file while solving that issue stops it from closing, solve what you filed first" -- so two issues close and each promotes a successor. One session closed #3392 and #3397 together and left `heads: [3393, 3398]`; blocking #3398 on #3396 restored it.

## Checking it after an edit

The check that matters is the head count. Walk the whole sequence and confirm one head, no branch and no orphan:

```bash
python3 - <<'PY'
import subprocess
nums=[int(x) for x in subprocess.run(["gh","issue","list","--state","open","--limit","200",
  "--json","number","-q",".[].number"],capture_output=True,text=True).stdout.split()]
nums=sorted(n for n in nums if n>2939)
blocked={n:[int(x) for x in subprocess.run(["gh","api",
  f"repos/deltahdl/deltahdl/issues/{n}/dependencies/blocked_by","-q",
  '[.[]|select(.state=="open").number]|join(",")'],capture_output=True,text=True
  ).stdout.strip().split(",") if x] for n in nums}
heads=[n for n in nums if not blocked[n]]
succ={}
for n,bs in blocked.items():
    for b in bs: succ.setdefault(b,[]).append(n)
print("heads:", heads)
seen=[]; cur=heads[0] if len(heads)==1 else None
while cur:
    seen.append(cur); nxt=succ.get(cur,[])
    if len(nxt)>1: print(f"branches at {cur}: {nxt}"); break
    cur=nxt[0] if nxt else None
print("chain:", " -> ".join(map(str,seen)))
print("off the chain:", sorted(set(nums)-set(seen)) or "none")
PY
```

`heads` holding anything but one number wants one of two answers. An issue created with no blocked-by edge is the breach this check exists to catch, and the fix is to place it. An issue orphaned by a predecessor closing out of order is the case above, and the fix is to mend the cut. A closed issue still carries its edges, so filter on `state == "open"`: a head whose only blockers are closed is the head.
