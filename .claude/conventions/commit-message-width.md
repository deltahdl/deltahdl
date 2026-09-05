# The width of a commit message

Write the subject at the length that states the change, and leave the body unwrapped.

Nothing here measures a commit message. No gate reads one, and no file states a column. The markdownlint job that covers the prose runs with MD013 disabled, because a table row cannot be wrapped. The general git convention of a subject under fifty columns and a body wrapped at seventy-two comes from terminals, and from mailing lists that sent patches as mail. It arrives by default rather than by anything this repository decided.

The rule a message is actually held to is that a change to module M is described in M's own terms, to a reader who has never heard of anything that calls M. That demands a message which stands on its own, and standing on its own is the first thing a column budget spends. Fitting the line means reaching for the shorter word over the exact one, or dropping the clause that says which of two things was meant, or naming a symbol by a fragment of itself. Each one is paid for out of the accuracy the message exists to carry.

The habit is worth naming because it comes back. It is not written down anywhere, so nobody can find it and drop it by reading the tree, and it returns whenever a message is composed from ordinary git practice rather than from this file. That is why it is recorded as a decision rather than left to be re-derived.

Related: [pushing-to-main](../rules/pushing-to-main.md) for the workflow the message sits in.
