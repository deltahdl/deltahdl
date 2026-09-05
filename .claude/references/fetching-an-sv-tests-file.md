# Fetching an sv-tests file

The corpus lives in `chipsalliance/sv-tests`, and a failing file named by a CI run is fetched from it with:

```sh
gh api repos/chipsalliance/sv-tests/contents/tests/chapter-N/<path>.sv \
  --jq .content | base64 -d
```

Related: [diagnosing-sv-tests-failures](../rules/diagnosing-sv-tests-failures.md) for what to do with the file once it is here.
