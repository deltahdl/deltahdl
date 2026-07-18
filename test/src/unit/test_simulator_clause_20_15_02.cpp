// §20.15.2 $q_add — the stochastic-analysis task that places an entry onto a
// queue. Its q_id argument (an integer input) names which queue receives the
// entry; the job_id and inform_id arguments (also integer inputs) describe the
// entry, the inform_id carrying a user-defined value; and a trailing `status`
// output reports the outcome (its codes owned by §20.15.6).
//
// Every rule here is a runtime rule whose behavior depends on how its inputs
// are produced: the queue $q_add fills is the one built by §20.15.1
// $q_initialize, an entry is only observably "placed" once §20.15.3 $q_remove
// hands its job_id/inform_id back, and the q_id/job_id/inform_id operands may
// arrive as either literals or declared integer variables. These tests
// therefore declare real integral variables, invoke $q_add (and the sibling
// §20.15.1/.3 tasks that build and witness the queue) from procedural source,
// and drive each module through the full pipeline (parse → elaborate → lower →
// run), reading results back through $display — rather than hand-building a
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

// Wraps a procedural body in a module `t` that declares the status/output
// variables the queue tasks write into (`st`, `job`, `inf`) and a trio of
// integer variables (`qv`, `jv`, `nv`) a body may load to supply $q_add's
// arguments as variable operands rather than literals. Runs the module through
// the full pipeline and returns the lines printed.
std::vector<std::string> RunBody(const std::string& body) {
  SimFixture f;
  std::string src =
      "module t;\n"
      "  integer st;\n"
      "  integer job;\n"
      "  integer inf;\n"
      "  integer qv;\n"
      "  integer jv;\n"
      "  integer nv;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  return Lines(RunCapture(src, f));
}

// §20.15.2: $q_add places an entry on the named queue. The placement is only
// observable through the entry it makes available to a later $q_remove — so a
// well-formed add against a live queue (built by §20.15.1) is confirmed by the
// remove that returns the very job that was added, with a success status.
TEST(QAdd, PlacesEntryOnQueue) {
  auto out = RunBody(
      "    $q_initialize(7, 1, 4, st);\n"
      "    $q_add(7, 11, 0, st);\n"
      "    $display(\"%0d\", st);\n"  // add succeeded
      "    $q_remove(7, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"     // remove found the entry
      "    $display(\"%0d\", job);\n");  // and it is the one added
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");   // placement reported success
  EXPECT_EQ(out[1], "0");   // an entry was there to remove
  EXPECT_EQ(out[2], "11");  // the entry $q_add placed
}

// §20.15.2 negative form of placement: with no queue at the q_id there is
// nowhere to place the entry, so the add reports a non-success status and
// leaves nothing behind — a following $q_remove on the same id also fails.
TEST(QAdd, AddToUndefinedQueuePlacesNothing) {
  auto out = RunBody(
      "    $q_add(99, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"  // nothing placed
      "    $q_remove(99, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");  // still nothing to remove
  ASSERT_EQ(out.size(), 2u);
  EXPECT_NE(out[0], "0");  // add could not place an entry
  EXPECT_NE(out[1], "0");  // and left none behind
}

// §20.15.2: the q_id argument indicates which queue receives the entry.
// Two independent queues share the same capacity of one; filling queue 1 does
// not affect queue 2, so an add routed to 2 still succeeds after 1 is full —
// witnessing that q_id, not global state, selects the target.
TEST(QAdd, QidSelectsTargetQueue) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 1, st);\n"
      "    $q_initialize(2, 1, 1, st);\n"
      "    $q_add(1, 1, 0, st);\n"  // queue 1 now full
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 2, 0, st);\n"  // rejected: queue 1 is full
      "    $display(\"%0d\", st);\n"
      "    $q_add(2, 3, 0, st);\n"  // queue 2 untouched, accepts one
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");  // placed in queue 1
  EXPECT_NE(out[1], "0");  // queue 1 full, cannot add
  EXPECT_EQ(out[2], "0");  // queue 2 still had room
}

// §20.15.2: the job_id argument is an integer input that identifies the job.
// It is carried with the entry and handed back by $q_remove, per entry: two
// adds with distinct job_ids come back as those same identifiers in FIFO order.
TEST(QAdd, JobIdIdentifiesEntry) {
  auto out = RunBody(
      "    $q_initialize(3, 1, 4, st);\n"
      "    $q_add(3, 42, 0, st);\n"
      "    $q_add(3, 84, 0, st);\n"
      "    $q_remove(3, job, inf, st);\n"
      "    $display(\"%0d\", job);\n"
      "    $q_remove(3, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "42");  // first job identifier preserved
  EXPECT_EQ(out[1], "84");  // second job identifier preserved
}

// §20.15.2: the inform_id argument is an integer input associated with the
// entry, and its meaning is user-defined — so $q_add accepts an arbitrary
// integer and carries it with the entry. $q_remove returns the same value.
TEST(QAdd, InformIdCarriedWithEntry) {
  auto out = RunBody(
      "    $q_initialize(5, 1, 4, st);\n"
      "    $q_add(5, 1, 314, st);\n"
      "    $q_remove(5, job, inf, st);\n"
      "    $display(\"%0d\", inf);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "314");  // the user-defined inform_id came back unchanged
}

// §20.15.2 input form: q_id, job_id and inform_id are integer inputs, so they
// may be supplied as declared integer variables rather than literals. Loading
// the variables from source and passing them to $q_add still selects the queue
// and stamps the entry — $q_remove returns the job and inform values that the
// variables held.
TEST(QAdd, AcceptsIntegerVariableOperands) {
  auto out = RunBody(
      "    $q_initialize(6, 1, 4, st);\n"
      "    qv = 6;\n"
      "    jv = 77;\n"
      "    nv = 555;\n"
      "    $q_add(qv, jv, nv, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(6, job, inf, st);\n"
      "    $display(\"%0d\", job);\n"
      "    $display(\"%0d\", inf);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");    // variable q_id selected the live queue
  EXPECT_EQ(out[1], "77");   // variable job_id carried through
  EXPECT_EQ(out[2], "555");  // variable inform_id carried through
}

// §20.15.2 input form: the q_id/job_id integer inputs may also be supplied by a
// parameter, whose value is resolved during elaboration rather than read from
// runtime storage — a distinct operand path from a plain variable. Declaring
// real parameters and passing them to $q_add still selects the queue and stamps
// the entry, witnessed by the $q_remove that returns the parameter-valued job.
TEST(QAdd, AcceptsParameterOperands) {
  SimFixture f;
  std::string src =
      "module t;\n"
      "  parameter QID = 6;\n"
      "  parameter JOB = 88;\n"
      "  integer st;\n"
      "  integer job;\n"
      "  integer inf;\n"
      "  initial begin\n"
      "    $q_initialize(QID, 1, 4, st);\n"
      "    $q_add(QID, JOB, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(QID, job, inf, st);\n"
      "    $display(\"%0d\", job);\n"
      "  end\n"
      "endmodule\n";
  auto out = Lines(RunCapture(src, f));
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");   // parameter q_id selected the live queue
  EXPECT_EQ(out[1], "88");  // parameter job_id stamped the entry
}

// §20.15.2: the status output reports the outcome of the operation. $q_add
// writes success (0) when it places the entry and a non-success value when it
// cannot; the exact codes and their meanings belong to §20.15.6 Table 20-11, so
// this test only observes that $q_add itself records the outcome into status.
TEST(QAdd, ReportsOutcomeInStatus) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"  // well-formed placement
      "    $display(\"%0d\", st);\n"
      "    $q_add(2, 1, 0, st);\n"  // no such queue, cannot place
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");  // success recorded
  EXPECT_NE(out[1], "0");  // failure recorded
}

// §20.15.2 edge: an add rejected because the queue is full must not place an
// entry. After one accepted add fills a capacity-one queue, the rejected add
// leaves occupancy at one: exactly one remove succeeds and the next finds the
// queue empty — the rejected add contributed nothing.
TEST(QAdd, RejectedAddDoesNotPlaceEntry) {
  auto out = RunBody(
      "    $q_initialize(4, 1, 1, st);\n"
      "    $q_add(4, 1, 0, st);\n"  // single allowed entry
      "    $display(\"%0d\", st);\n"
      "    $q_add(4, 2, 0, st);\n"  // rejected: queue full
      "    $display(\"%0d\", st);\n"
      "    $q_remove(4, job, inf, st);\n"  // the one real entry
      "    $display(\"%0d\", st);\n"
      "    $q_remove(4, job, inf, st);\n"  // nothing left behind
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 4u);
  EXPECT_EQ(out[0], "0");  // accepted
  EXPECT_NE(out[1], "0");  // full, cannot add
  EXPECT_EQ(out[2], "0");  // the single entry comes back
  EXPECT_NE(out[3], "0");  // empty: the rejected add placed nothing
}

}  // namespace
