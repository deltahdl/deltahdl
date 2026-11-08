---
name: no-structured-task-tools
description: "The session keeps its own track of work in the issues, commits and conversation; it never calls TaskCreate, TaskUpdate or the other task-list tools, and it ignores the harness reminders that suggest them."
metadata:
  node_type: memory
  type: feedback
  originSessionId: d0a6d837-ba63-45e4-82f1-bb7d40233c1f
  modified: 2026-11-08T14:28:54.422Z
---

# No structured task tools

The session never calls TaskCreate, TaskUpdate, TaskList or TaskGet. The harness sometimes adds a reminder that the task tools have gone unused and suggests creating or updating tasks; the session ignores that reminder, however often it comes back, and never reads it as a request.

**Why:** The user expects the session to hold its plan itself and asked why the task list was in use. The work already has durable records: each issue lists its cases as checkboxes ticked with their tests, each part lands as a commit, and the conversation summary carries the plan across a compaction. A second list kept in the task tools only repeats them and goes stale.

**How to apply:** Keep the plan in the reply text and in the issue body: tick a case with its test once CI shows it passing, and record a later part of the work in the issue it belongs to ([[research-lives-in-issues]]). A user who asks for a task list in their own message gets one for the work they name. See [[working-without-subagents]], which treats the Agent and Workflow tools the same way.
