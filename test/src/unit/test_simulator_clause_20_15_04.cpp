// §20.15.4 $q_full — the stochastic-analysis system *function* that checks
// whether a queue has room for another entry. Unlike the queue tasks, $q_full
// yields a value: it returns 0 when the queue is not full and 1 when it is
// full. Its q_id argument is an integer input naming the queue to test; a
// trailing `status` output reports the outcome (its Table 20-11 codes owned by
// §20.15.6).
//
// The rule is a runtime rule whose 0/1 result depends on how its input is
// produced: a queue only has a notion of "full" because §20.15.1 $q_initialize
// fixed its capacity (max_length), and whether that capacity is reached depends
// on how many entries §20.15.2 $q_add placed and §20.15.3 $q_remove took off.
// These tests therefore build the queue and its occupancy from real procedural
// source, drive each module through the full pipeline (parse → elaborate →
// lower → run), and read $q_full's return value back by assigning it into a
// declared integer variable and printing it — rather than hand-building a
// system-call node and calling the evaluator in isolation.
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

// Wraps a procedural body in a module `t` that declares the status variable the
// queue tasks write into (`st`), an integer `r` to receive $q_full's returned
// fullness result, throwaway job/inform outputs for $q_remove (`job`, `inf`),
// and an integer `qv` a body may load to supply a q_id as a variable operand
// rather than a literal. Runs the module through the full pipeline and returns
// the lines printed.
std::vector<std::string> RunBody(const std::string& body) {
  SimFixture f;
  std::string src =
      "module t;\n"
      "  integer st;\n"
      "  integer r;\n"
      "  integer job;\n"
      "  integer inf;\n"
      "  integer qv;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  return Lines(RunCapture(src, f));
}

// §20.15.4: a freshly created queue holds no entries, so it has room for
// another and $q_full returns 0 (not full).
TEST(QFull, EmptyQueueIsNotFull) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 2, st);\n"
      "    r = $q_full(1, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");  // empty queue still has room
}

// §20.15.4: a queue holding fewer entries than its capacity still has room, so
// $q_full returns 0. The occupancy is produced by real §20.15.2 $q_add source.
TEST(QFull, PartiallyFilledQueueIsNotFull) {
  auto out = RunBody(
      "    $q_initialize(2, 1, 3, st);\n"
      "    $q_add(2, 10, 0, st);\n"
      "    r = $q_full(2, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");  // one of three slots used — room remains
}

// §20.15.4: once the queue holds as many entries as the capacity fixed at
// §20.15.1 $q_initialize allows, there is no room for another entry, so $q_full
// returns 1 (full).
TEST(QFull, FullQueueReturnsOne) {
  auto out = RunBody(
      "    $q_initialize(3, 1, 2, st);\n"
      "    $q_add(3, 10, 0, st);\n"
      "    $q_add(3, 20, 0, st);\n"
      "    r = $q_full(3, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "1");  // capacity reached — no room
}

// §20.15.4: fullness tracks the queue's capacity, not a fixed threshold. A
// single-slot queue has room while empty (0) and is full as soon as its one
// slot is occupied (1).
TEST(QFull, SingleEntryQueueIsFullAfterOneAdd) {
  auto out = RunBody(
      "    $q_initialize(4, 1, 1, st);\n"
      "    r = $q_full(4, st);\n"
      "    $display(\"%0d\", r);\n"  // empty: has room
      "    $q_add(4, 7, 0, st);\n"
      "    r = $q_full(4, st);\n"
      "    $display(\"%0d\", r);\n");  // one slot filled: full
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "1");
}

// §20.15.4: fullness reflects current occupancy, not a one-way latch. A queue
// filled to capacity reports full (1); after §20.15.3 $q_remove takes an entry
// off it has room again, so $q_full reports not full (0).
TEST(QFull, ReportsNotFullAfterEntryRemoved) {
  auto out = RunBody(
      "    $q_initialize(5, 1, 2, st);\n"
      "    $q_add(5, 1, 0, st);\n"
      "    $q_add(5, 2, 0, st);\n"
      "    r = $q_full(5, st);\n"
      "    $display(\"%0d\", r);\n"  // at capacity
      "    $q_remove(5, job, inf, st);\n"
      "    r = $q_full(5, st);\n"
      "    $display(\"%0d\", r);\n");  // a slot has freed up
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "1");
  EXPECT_EQ(out[1], "0");
}

// §20.15.4 input form: q_id is an integer input, so it may be supplied as a
// declared integer variable rather than a literal. Loading the variable from
// source and passing it to $q_full still tests that queue's fullness.
TEST(QFull, AcceptsIntegerVariableQidOperand) {
  auto out = RunBody(
      "    $q_initialize(8, 1, 1, st);\n"
      "    $q_add(8, 55, 0, st);\n"
      "    qv = 8;\n"
      "    r = $q_full(qv, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "1");  // the variable q_id selected the full queue
}

// §20.15.4: a $q_full on a live queue completes successfully, so the trailing
// status reports success (the Table 20-11 codes are §20.15.6's rule).
TEST(QFull, ReportsSuccessStatusOnLiveQueue) {
  auto out = RunBody(
      "    $q_initialize(9, 1, 2, st);\n"
      "    r = $q_full(9, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");  // success
}

// §20.15.4 negative form: the q_id input must indicate a queue that exists.
// Aimed at an id that no $q_initialize ever created, $q_full has no queue to
// test and reports a non-success status rather than a valid fullness result.
TEST(QFull, UndefinedQueueReportsErrorStatus) {
  auto out = RunBody(
      "    r = $q_full(99, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");  // no such queue
}

}  // namespace
