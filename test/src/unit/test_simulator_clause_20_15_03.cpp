// §20.15.3 $q_remove — the stochastic-analysis task that receives (removes) an
// entry from a queue. Its q_id argument is an integer input naming which queue
// to remove from; the job_id and inform_id arguments are integer *outputs* that
// carry the removed entry's identifiers back to the caller — job_id identifies
// the entry, and inform_id returns whatever value the queue manager stored when
// §20.15.2 $q_add placed it (its meaning is user-defined). A trailing `status`
// output reports the outcome (its codes owned by §20.15.6).
//
// Every rule here is a runtime rule whose behavior depends on how its inputs
// are produced: the entry $q_remove returns is the one §20.15.2 $q_add stored,
// which entry comes off follows the FIFO/LIFO discipline of the q_type fixed at
// §20.15.1 $q_initialize, and the job_id/inform_id outputs are only observable
// once they are written back into declared integer variables. These tests
// therefore declare real integral variables, build the queue and its contents
// from procedural $q_initialize/$q_add source, and drive each module through
// the full pipeline (parse → elaborate → lower → run), reading the outputs back
// through $display — rather than hand-building a system-call node and calling
// the evaluator in isolation.
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

// Wraps a procedural body in a module `t` that declares the status variable and
// the job_id/inform_id output variables the queue tasks write into (`st`,
// `job`, `inf`), plus an integer variable (`qv`) a body may load to supply
// $q_remove's q_id as a variable operand rather than a literal. Runs the module
// through the full pipeline and returns the lines printed.
std::vector<std::string> RunBody(const std::string& body) {
  SimFixture f;
  std::string src =
      "module t;\n"
      "  integer st;\n"
      "  integer job;\n"
      "  integer inf;\n"
      "  integer qv;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  return Lines(RunCapture(src, f));
}

// §20.15.3: $q_remove receives an entry from the queue named by q_id and
// returns the value the queue manager stored during §20.15.2 $q_add through the
// inform_id output. Its meaning is user-defined, so an arbitrary value placed
// at add time comes back unchanged through the output at remove time, alongside
// a success status.
TEST(QRemove, ReturnsInformIdStoredAtAdd) {
  auto out = RunBody(
      "    $q_initialize(3, 1, 4, st);\n"
      "    $q_add(3, 5, 9001, st);\n"
      "    $q_remove(3, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"   // remove reported success
      "    $display(\"%0d\", inf);\n"  // the stored inform_id came back
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");     // success status
  EXPECT_EQ(out[1], "9001");  // user-defined inform_id round-trips unchanged
  EXPECT_EQ(out[2], "5");     // the job_id output identifies the entry
}

// §20.15.3: q_id selects which queue the entry is removed from. With two
// independent queues holding distinct entries, removing from each yields that
// queue's own entry through the job_id output.
TEST(QRemove, RemovesFromQueueSelectedByQid) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 2, st);\n"
      "    $q_initialize(2, 1, 2, st);\n"
      "    $q_add(1, 11, 0, st);\n"
      "    $q_add(2, 22, 0, st);\n"
      "    $q_remove(2, job, inf, st);\n"
      "    $display(\"%0d\", job);\n"
      "    $q_remove(1, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "22");  // queue 2's entry
  EXPECT_EQ(out[1], "11");  // queue 1's entry
}

// §20.15.3 input form: q_id is an integer input, so it may be supplied as a
// declared integer variable rather than a literal. Loading the variable from
// source and passing it to $q_remove still selects the queue and returns its
// entry through the job_id output.
TEST(QRemove, AcceptsIntegerVariableQidOperand) {
  auto out = RunBody(
      "    $q_initialize(7, 1, 2, st);\n"
      "    $q_add(7, 55, 0, st);\n"
      "    qv = 7;\n"
      "    $q_remove(qv, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");   // the variable q_id selected the live queue
  EXPECT_EQ(out[1], "55");  // and its entry came back
}

// §20.15.3: which entry is removed follows the queue discipline set by the
// q_type $q_initialize fixed (§20.15.1). A FIFO queue (q_type 1) returns the
// oldest entry first, each remove handing back through the job_id output the
// distinct identifier that add stored for that entry.
TEST(QRemove, FifoQueueReturnsOldestEntryFirst) {
  auto out = RunBody(
      "    $q_initialize(4, 1, 4, st);\n"
      "    $q_add(4, 100, 0, st);\n"
      "    $q_add(4, 200, 0, st);\n"
      "    $q_remove(4, job, inf, st);\n"
      "    $display(\"%0d\", job);\n"
      "    $q_remove(4, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "100");  // first in, first out
  EXPECT_EQ(out[1], "200");
}

// §20.15.3: a LIFO queue (q_type 2) returns the most recently added entry first
// through the job_id output, showing the removed entry is chosen by the queue
// type.
TEST(QRemove, LifoQueueReturnsNewestEntryFirst) {
  auto out = RunBody(
      "    $q_initialize(5, 2, 4, st);\n"
      "    $q_add(5, 100, 0, st);\n"
      "    $q_add(5, 200, 0, st);\n"
      "    $q_remove(5, job, inf, st);\n"
      "    $display(\"%0d\", job);\n"
      "    $q_remove(5, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "200");  // last in, first out
  EXPECT_EQ(out[1], "100");
}

// §20.15.3 negative form: removing from a queue that holds no entry cannot
// return one, so the status reports an error (the Table 20-11 codes are
// §20.15.6's rule) rather than success.
TEST(QRemove, RemoveFromEmptyQueueReportsError) {
  auto out = RunBody(
      "    $q_initialize(6, 1, 2, st);\n"
      "    $q_remove(6, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");  // nothing to remove
}

// §20.15.3 negative form: the q_id input must indicate a queue that exists.
// Aimed at an id that no $q_initialize ever created, $q_remove finds no queue
// to take an entry from and reports a non-success status.
TEST(QRemove, RemoveFromUndefinedQueueReportsError) {
  auto out = RunBody(
      "    $q_remove(99, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");  // no such queue
}

// §20.15.3: a successful $q_remove actually takes the entry off the queue.
// After the single stored entry is removed with success, the queue is empty, so
// an immediate second remove can no longer return an entry and reports an error
// — confirming the first remove consumed the entry rather than leaving it.
TEST(QRemove, SuccessfulRemoveConsumesTheEntry) {
  auto out = RunBody(
      "    $q_initialize(8, 1, 2, st);\n"
      "    $q_add(8, 77, 0, st);\n"
      "    $q_remove(8, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"   // first remove succeeds
      "    $display(\"%0d\", job);\n"  // and returns the stored entry
      "    $q_remove(8, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");  // nothing left to remove
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");  // consumed one entry
  EXPECT_EQ(out[1], "77");
  EXPECT_NE(out[2], "0");  // queue now empty
}

}  // namespace
