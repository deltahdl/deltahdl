// §20.15.6 Status codes — every stochastic-analysis queue management task and
// function ($q_initialize, $q_add, $q_remove, $q_full, $q_exam) returns an
// output status code, and Table 20-11 fixes the meaning of each value. The
// status a call reports depends on runtime queue state that earlier calls
// build up (an entry was added, the queue was drained, a q_id was already
// taken) and on how the arguments are produced (a negative max_length is only
// distinguishable from a huge positive one once the literal is parsed as
// signed). These tests therefore declare real integral variables, invoke the
// queue tasks from procedural source, and drive the module through the full
// pipeline (parse → elaborate → lower → run), reading each status back through
// $display, rather than hand-building a system-call node and calling the
// evaluator in isolation.
#include <sstream>
#include <string>
#include <vector>

#include "fixture_simulator.h"

using namespace delta;

namespace {

// Runs a single-module source through elaboration and simulation while
// capturing everything the run writes to stdout.
std::string RunCapture(const std::string& src, SimFixture& f) {
  std::ostringstream captured;
  std::streambuf* old_buf = std::cout.rdbuf(captured.rdbuf());
  auto* design = ElaborateSrc(src, f);
  if (design != nullptr) LowerAndRun(design, f);
  std::cout.rdbuf(old_buf);
  return captured.str();
}

// Splits captured stdout into its non-empty lines, one per $display.
std::vector<std::string> Lines(const std::string& out) {
  std::vector<std::string> lines;
  std::istringstream in(out);
  std::string line;
  while (std::getline(in, line)) {
    if (!line.empty()) lines.push_back(line);
  }
  return lines;
}

// Wraps a procedural body in a module `t` that declares the status/output
// variables the queue tasks write into, runs it through the full pipeline, and
// returns the lines printed. `q_id`, `st`, `job`, and `inf` are always
// available for the body to use.
std::vector<std::string> RunBody(const std::string& body) {
  SimFixture f;
  std::string src =
      "module t;\n"
      "  integer st;\n"
      "  integer job;\n"
      "  integer inf;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  return Lines(RunCapture(src, f));
}

// §20.15.6 Table 20-11, value 0: a well-formed $q_initialize reports OK. The
// status output variable is declared and driven from real source.
TEST(StochasticQueueStatus, InitializeSucceedsWithOk) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

// §20.15.6 Table 20-11, value 4: an unsupported q_type (only 1 and 2 are
// defined per Table 20-9) fails creation with "unsupported queue type".
TEST(StochasticQueueStatus, UnsupportedQueueType) {
  auto out = RunBody(
      "    $q_initialize(1, 3, 4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "4");
}

// §20.15.6 Table 20-11, value 5: a zero max_length fails creation, exercising
// the boundary of the "length <= 0" condition.
TEST(StochasticQueueStatus, ZeroLength) {
  auto out = RunBody(
      "    $q_initialize(1, 2, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "5");
}

// §20.15.6 Table 20-11, value 5: a negative max_length also fails creation.
// Driving the literal -4 from real source is what makes this meaningful: the
// signed value must survive parsing so the "length <= 0" test recognizes it
// rather than seeing a large positive capacity.
TEST(StochasticQueueStatus, NegativeLength) {
  auto out = RunBody(
      "    $q_initialize(1, 1, -4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "5");
}

// §20.15.6 Table 20-11, value 6: re-using a live q_id fails creation with
// "duplicate q_id". The first creation must have succeeded (value 0) for the
// second to see the collision, so both statuses are observed in sequence.
TEST(StochasticQueueStatus, DuplicateQueueId) {
  auto out = RunBody(
      "    $q_initialize(5, 1, 4, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(5, 1, 4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "6");
}

// §20.15.6 Table 20-11, value 2: adding to a q_id that was never created
// reports "undefined q_id".
TEST(StochasticQueueStatus, AddToUndefinedQueue) {
  auto out = RunBody(
      "    $q_add(99, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

// §20.15.6 Table 20-11, value 1: adding past the queue's capacity reports
// "queue full, cannot add". The successful add first reports OK; the state it
// leaves behind is what turns the second add into a full-queue error.
TEST(StochasticQueueStatus, AddToFullQueue) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 1, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 2, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");  // creation
  EXPECT_EQ(out[1], "0");  // first add fills the one slot
  EXPECT_EQ(out[2], "1");  // second add finds it full
}

// §20.15.6 Table 20-11, value 3: removing from an empty queue reports "queue
// empty, cannot remove". The queue is created, then drained across calls so the
// empty state is reached through real runtime activity, not a hand-built state.
TEST(StochasticQueueStatus, RemoveFromEmptyQueue) {
  auto out = RunBody(
      "    $q_initialize(2, 1, 4, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"  // never added to
      "    $display(\"%0d\", st);\n"
      "    $q_add(2, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"  // drains the single entry
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"  // now empty again
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 5u);
  EXPECT_EQ(out[0], "0");  // creation
  EXPECT_EQ(out[1], "3");  // empty
  EXPECT_EQ(out[2], "0");  // add
  EXPECT_EQ(out[3], "0");  // successful remove
  EXPECT_EQ(out[4], "3");  // empty again
}

// §20.15.6 Table 20-11, value 2: $q_remove on an undefined q_id also reports
// "undefined q_id".
TEST(StochasticQueueStatus, RemoveFromUndefinedQueue) {
  auto out = RunBody(
      "    $q_remove(42, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

// §20.15.6: $q_full is a function that returns 0/1 fullness but also reports a
// status code through its trailing output. An undefined q_id reports value 2;
// once the queue is live the status is OK. Reading the status back confirms the
// function participates in the "every task and function returns a status code"
// requirement.
TEST(StochasticQueueStatus, FullReportsStatus) {
  auto out = RunBody(
      "    if ($q_full(3, st)) ;\n"  // undefined
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(3, 1, 4, st);\n"
      "    if ($q_full(3, st)) ;\n"  // live queue
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");
  EXPECT_EQ(out[1], "0");
}

// §20.15.6: $q_exam reports a status code through its trailing output. An
// undefined q_id reports value 2; once the queue is live the status is OK.
TEST(StochasticQueueStatus, ExamReportsStatus) {
  auto out = RunBody(
      "    $q_exam(8, 1, job, st);\n"  // undefined
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(8, 2, 4, st);\n"
      "    $q_exam(8, 1, job, st);\n"  // live queue
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");
  EXPECT_EQ(out[1], "0");
}

}  // namespace
