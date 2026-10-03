---
name: fetching-an-sv-tests-file
description: Fetch a failing sv-tests file from chipsalliance/sv-tests with gh api and base64 -d.
metadata:
  type: reference
---

# Fetching an sv-tests file

The suite lives in `chipsalliance/sv-tests`, and a failing file named by a CI run is fetched from it with:

```sh
gh api repos/chipsalliance/sv-tests/contents/tests/chapter-N/<path>.sv \
  --jq .content | base64 -d
```

Related: [reading-the-sv-tests-log-first](reading-the-sv-tests-log-first.md) for when fetching it is unnecessary. The file is read, not run locally; per [verifying-through-ci](verifying-through-ci.md), running it is CI's.
