---
name: fetching-an-sv-tests-file
description: Fetch a failing sv-tests file from chipsalliance/sv-tests with gh api and base64 -d.
metadata:
  type: reference
---

# Fetching an sv-tests file

The corpus lives in `chipsalliance/sv-tests`, and a failing file named by a CI run is fetched from it with:

```sh
gh api repos/chipsalliance/sv-tests/contents/tests/chapter-N/<path>.sv \
  --jq .content | base64 -d
```

Related: [the-sv-tests-build-exception](the-sv-tests-build-exception.md) for what to do with the file once it is here, and [reading-the-sv-tests-log-first](reading-the-sv-tests-log-first.md) for when fetching it is unnecessary.
