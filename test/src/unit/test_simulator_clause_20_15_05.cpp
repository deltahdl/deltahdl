// §20.15.5 $q_exam — the stochastic-analysis task that reports statistical
// information about activity on the queue named by q_id. The q_stat_code
// argument is an integer input selecting which statistic to report; the chosen
// value is delivered through the q_stat_value integer output. Table 20-10 fixes
// the mapping of q_stat_code to statistic: 1 current queue length, 2 mean
// interarrival time, 3 maximum queue length, 4 shortest wait ever, 5 longest
// wait among jobs still queued, and 6 average wait in the queue. A trailing
// `status` output reports the outcome (its codes owned by §20.15.6).
//
// Every rule here is a runtime rule whose behavior depends on how its inputs
// are produced: the statistics summarize a queue built by §20.15.1
// $q_initialize and filled/drained by §20.15.2 $q_add / §20.15.3 $q_remove, and
// several of them (mean interarrival, the wait times) depend on the simulation
// time at which those adds and removes happen. These tests therefore declare
// real integral variables, build the queue and its history from procedural
// source with real
// `#` delays advancing simulation time, and drive each module through the full
// pipeline (parse → elaborate → lower → run), reading the q_stat_value output
// back through $display — rather than hand-building a system-call node and
// invoking the evaluator against a stubbed scheduler.
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

// Wraps a procedural body in a module `t` that declares the status variable
// (`st`), the q_stat_value output variable $q_exam writes its statistic into
// (`sv`), the job_id/inform_id output variables $q_remove needs (`job`, `inf`),
// and an integer (`qv`) a body may load to supply q_id as a variable operand
// rather than a literal. A 1 ns time unit and precision make every `#N` delay
// advance the simulation exactly N ticks, so the times the queue tasks stamp on
// arrivals and measure waits against read straight out of the delays. Runs the
// module through the full pipeline and returns the lines printed.
std::vector<std::string> RunBody(const std::string& body) {
  SimFixture f;
  std::string src =
      "module t;\n"
      "  timeunit 1ns;\n"
      "  timeprecision 1ns;\n"
      "  integer st;\n"
      "  integer sv;\n"
      "  integer job;\n"
      "  integer inf;\n"
      "  integer qv;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  return Lines(RunCapture(src, f));
}

// §20.15.5 Table 20-10, code 1: the current queue length tracks live occupancy,
// rising with each $q_add and falling with each $q_remove.
TEST(QExam, CurrentQueueLength) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"
      "    #1 $q_exam(1, 1, sv, st);\n"  // two entries live
      "    $display(\"%0d\", sv);\n"
      "    #1 $q_remove(1, job, inf, st);\n"
      "    #1 $q_exam(1, 1, sv, st);\n"  // one entry left
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");
  EXPECT_EQ(out[1], "1");
}

// §20.15.5 Table 20-10, code 3: the maximum queue length is the peak occupancy
// ever reached, retained even after entries drain back out.
TEST(QExam, MaximumQueueLength) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"  // occupancy peaks at 3 here
      "    #1 $q_remove(1, job, inf, st);\n"
      "    #1 $q_remove(1, job, inf, st);\n"
      "    #1 $q_exam(1, 3, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "3");  // peak survives the drain
}

// §20.15.5 Table 20-10, code 2: the mean interarrival time is the average gap
// between successive arrivals. Arrivals at t=0, 4 and 10 give (10-0)/2 = 5.
TEST(QExam, MeanInterarrivalTime) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #4 $q_add(1, 1, 0, st);\n"
      "    #6 $q_add(1, 1, 0, st);\n"
      "    #1 $q_exam(1, 2, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "5");
}

// §20.15.5 Table 20-10, code 4: the shortest wait time ever is the smallest
// residence time across removed entries. FIFO removal drains the oldest first,
// so entry A waits 5 (0->5) and B waits 4 (2->6); the minimum is 4. Making the
// second removal the shorter one keeps a true minimum distinct from "most
// recent wait".
TEST(QExam, ShortestWaitEver) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"            // entry A
      "    #2 $q_add(1, 1, 0, st);\n"         // entry B
      "    #3 $q_remove(1, job, inf, st);\n"  // t=5, removes A, wait 5
      "    #1 $q_remove(1, job, inf, st);\n"  // t=6, removes B, wait 4
      "    #1 $q_exam(1, 4, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "4");
}

// §20.15.5 Table 20-10, code 6: the average wait time over removed entries. A
// waits 4 (0->4) and B waits 6 (4->10), averaging 5. B is added at the same
// tick as A's removal, after it, exercising same-time procedural ordering.
TEST(QExam, AverageWaitTime) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"            // entry A
      "    #4 $q_remove(1, job, inf, st);\n"  // t=4, A waits 4
      "    $q_add(1, 1, 0, st);\n"  // entry B, same tick, after remove
      "    #6 $q_remove(1, job, inf, st);\n"  // t=10, B waits 6
      "    #1 $q_exam(1, 6, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "5");
}

// §20.15.5 Table 20-10, code 5: the longest wait among entries still in the
// queue is measured against the current time; the oldest still-present entry
// has waited the longest. Once it is removed the next-oldest takes over, so the
// reported longest wait drops.
TEST(QExam, LongestWaitStillQueued) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"       // entry A, oldest
      "    #3 $q_add(1, 1, 0, st);\n"    // t=3, entry B
      "    #7 $q_exam(1, 5, sv, st);\n"  // t=10, A has waited 10
      "    $display(\"%0d\", sv);\n"
      "    $q_remove(1, job, inf, st);\n"  // remove A (FIFO), same tick
      "    $q_exam(1, 5, sv, st);\n"       // now B, has waited 7
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "10");
  EXPECT_EQ(out[1], "7");
}

// §20.15.5: a successful $q_exam reports the OK status through the trailing
// output alongside the statistic it delivers.
TEST(QExam, ReportsSuccessStatus) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $q_exam(1, 1, sv, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");  // OK
}

// §20.15.5 negative form: q_id must name a queue that exists. Aimed at an id no
// $q_initialize ever created, $q_exam has no queue to examine and reports a
// non-success status (the Table 20-11 codes are §20.15.6's rule).
TEST(QExam, ExamUndefinedQueueReportsError) {
  auto out = RunBody(
      "    $q_exam(99, 1, sv, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");  // no such queue
}

// §20.15.5 input form: q_stat_code is an integer input, so it may be supplied
// as a declared integer variable rather than a literal. Loading the code from
// source and passing it to $q_exam selects the same Table 20-10 statistic.
TEST(QExam, AcceptsVariableStatCodeOperand) {
  auto out = RunBody(
      "    integer code;\n"
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"
      "    code = 1;\n"  // request current queue length
      "    $q_exam(1, code, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

// §20.15.5: a q_stat_code outside the Table 20-10 range requests no defined
// statistic, so q_stat_value comes back as zero.
TEST(QExam, UnknownStatCodeYieldsZero) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_exam(1, 99, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

// §20.15.5 Table 20-10, edge case: querying a queue that has never held an
// entry yields zero for occupancy-based statistics. Code 1 (current length)
// reports the empty count and code 5 (longest wait still queued) has no entry
// to measure, so both come back as zero.
TEST(QExam, StatisticsOnEmptyQueueAreZero) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    #5 $q_exam(1, 1, sv, st);\n"
      "    $display(\"%0d\", sv);\n"
      "    $q_exam(1, 5, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");  // current length
  EXPECT_EQ(out[1], "0");  // longest wait still queued
}

// §20.15.5 Table 20-10, edge case: the completed-wait statistics depend on
// entries having left the queue. With entries added but none yet removed, both
// the shortest wait ever (code 4) and the average wait (code 6) are zero.
TEST(QExam, WaitStatisticsBeforeAnyRemovalAreZero) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #4 $q_add(1, 1, 0, st);\n"
      "    #5 $q_exam(1, 4, sv, st);\n"
      "    $display(\"%0d\", sv);\n"
      "    $q_exam(1, 6, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");  // shortest wait ever
  EXPECT_EQ(out[1], "0");  // average wait
}

// §20.15.5 Table 20-10, edge case: the mean interarrival time (code 2) needs at
// least two arrivals to span a gap. A single arrival leaves no interval to
// average, so the result is zero.
TEST(QExam, MeanInterarrivalWithSingleArrivalIsZero) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    #3 $q_add(1, 1, 0, st);\n"
      "    #4 $q_exam(1, 2, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

// §20.15.5 input form: q_id is an integer input, so it may be supplied as a
// declared integer variable rather than a literal. Loading the id from source
// and passing it to $q_exam still selects the named queue and returns its
// requested statistic through q_stat_value.
TEST(QExam, AcceptsVariableQidOperand) {
  auto out = RunBody(
      "    $q_initialize(7, 1, 8, st);\n"
      "    $q_add(7, 1, 0, st);\n"
      "    #1 $q_add(7, 1, 0, st);\n"
      "    qv = 7;\n"  // q_id delivered via a variable
      "    $q_exam(qv, 1, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");  // the variable q_id reached the live queue
}

// §20.15.5 dependency end-to-end (§20.15.1 q_type 2 + §20.15.3 LIFO removal):
// the wait statistics summarize entries as the queue discipline actually drains
// them, so the answer depends on how the queue was produced. On a LIFO queue
// the most recently added entry leaves first, so removing at t=5 then t=6 takes
// B (waited 3) then A (waited 6); the shortest wait ever (code 4) is 3. A FIFO
// queue built the same way would report 4, confirming $q_exam reads the wait of
// the entry the LIFO $q_remove chose rather than a discipline-independent
// value.
TEST(QExam, ShortestWaitReflectsLifoQueueDiscipline) {
  auto out = RunBody(
      "    $q_initialize(8, 2, 8, st);\n"     // q_type 2 = LIFO
      "    $q_add(8, 1, 0, st);\n"            // entry A @ t=0
      "    #2 $q_add(8, 1, 0, st);\n"         // entry B @ t=2
      "    #3 $q_remove(8, job, inf, st);\n"  // t=5, LIFO pops B, wait 3
      "    #1 $q_remove(8, job, inf, st);\n"  // t=6, pops A, wait 6
      "    #1 $q_exam(8, 4, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "3");  // min wait under LIFO drainage (FIFO would give 4)
}

}  // namespace
