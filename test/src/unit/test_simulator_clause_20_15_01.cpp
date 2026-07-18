// §20.15.1 $q_initialize — the stochastic-analysis task that creates a queue
// from a q_id, a q_type drawn from Table 20-9 (1 = first-in-first-out,
// 2 = last-in-first-out), and a max_length capacity, reporting the creation
// outcome through a trailing `status` output (its codes owned by §20.15.6).
//
// Every rule here is a runtime rule, and its behavior depends on how the
// arguments are produced: the status/output variables are declared integrals,
// a negative max_length is only distinguishable from a large positive one once
// the literal is parsed as signed, and creation is only observable through the
// later queue calls it enables. These tests therefore declare real variables,
// invoke $q_initialize (and the sibling §20.15.2/.3/.4 tasks that witness what
// it built) from procedural source, and drive each module through the full
// pipeline (parse → elaborate → lower → run), reading results back through
// $display — rather than hand-building a system-call node and calling the
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

// Wraps a procedural body in a module that declares the status/output variables
// the queue tasks write into (`st`, `job`, `inf`), runs it through the full
// pipeline, and returns the lines printed.
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

// §20.15.1: $q_initialize creates a new queue. Before the call the q_id names
// nothing — adding to it reports the undefined-q_id status (2). After a
// well-formed q_type 1 creation the same id is a live queue and the add
// succeeds (0), so the creation is what turned the id from undefined into a
// working queue.
TEST(QInitialize, CreatesNewQueue) {
  auto out = RunBody(
      "    $q_add(7, 1, 0, st);\n"  // no queue yet
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(7, 1, 4, st);\n"
      "    $q_add(7, 1, 0, st);\n"  // now a live queue
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");  // undefined before creation
  EXPECT_EQ(out[1], "0");  // add accepted after creation
}

// §20.15.1: the success or failure of the creation is returned as an integer
// value in the status output. A well-formed call reports success (0); a call
// that cannot create the queue (here an unsupported q_type) reports a non-zero
// failure. The exact failure code and its meaning belong to §20.15.6 Table
// 20-11; this test only observes that $q_initialize itself writes the outcome
// into status.
TEST(QInitialize, ReturnsCreationOutcomeInStatus) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"  // well-formed
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(2, 3, 4, st);\n"  // unsupported type, cannot create
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");  // success
  EXPECT_NE(out[1], "0");  // failure reported in status
}

// §20.15.1 Table 20-9, row 1: q_type 1 creates a first-in-first-out queue. Two
// entries are added in order (job 11 then 22); a remove returns the oldest,
// witnessing that the value 1 selected the FIFO discipline at creation.
TEST(QInitialize, FifoTypeReturnsOldestEntry) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $q_add(1, 11, 0, st);\n"
      "    $q_add(1, 22, 0, st);\n"
      "    $q_remove(1, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "11");  // first in, first out
}

// §20.15.1 Table 20-9, row 2: q_type 2 creates a last-in-first-out queue. With
// the same two adds, a remove returns the most recent entry, witnessing that
// value 2 selected the LIFO discipline.
TEST(QInitialize, LifoTypeReturnsNewestEntry) {
  auto out = RunBody(
      "    $q_initialize(1, 2, 4, st);\n"
      "    $q_add(1, 11, 0, st);\n"
      "    $q_add(1, 22, 0, st);\n"
      "    $q_remove(1, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "22");  // last in, first out
}

// §20.15.1: q_type selects from Table 20-9, which defines only values 1 and 2.
// A value above that range names no queue type, so no queue is created — a
// subsequent add to that id still reports undefined (2).
TEST(QInitialize, TypeAboveTableCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 3, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");  // no queue was registered
}

// §20.15.1 lower boundary of Table 20-9: q_type 0 sits just below the first
// defined type, so like any out-of-table value it registers no queue.
TEST(QInitialize, TypeBelowTableCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 0, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");  // no queue was registered
}

// §20.15.1 negative q_type input form: a negative literal is also outside
// Table 20-9's {1, 2}. Driving -1 from real source exercises the signed path —
// the value must survive parsing as negative rather than as a large unsigned
// type — and like any out-of-table value it registers no queue.
TEST(QInitialize, NegativeTypeCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, -1, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");  // no queue was registered
}

// §20.15.1: max_length is the maximum number of entries allowed on the queue.
// A queue created with capacity 2 accepts exactly two entries; the third add
// finds it full (status 1), pinning the capacity to the supplied max_length.
TEST(QInitialize, MaxLengthBoundsTheEntryCount) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 2, st);\n"
      "    $q_add(1, 1, 0, st);\n"  // entry 1 of 2
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 2, 0, st);\n"  // entry 2 of 2 fills the queue
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 3, 0, st);\n"  // capacity reached
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");  // accepted
  EXPECT_EQ(out[1], "0");  // accepted, now full
  EXPECT_EQ(out[2], "1");  // full, cannot add
}

// §20.15.1 negative max_length input form, zero boundary: a max_length of 0
// specifies no room for any entry, so no queue is created — a subsequent add
// reports undefined (2).
TEST(QInitialize, ZeroLengthCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 0, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");  // no queue was registered
}

// §20.15.1 negative max_length input form, signed literal: a negative capacity
// cannot bound an entry count. Driving -4 from real source is what makes this
// meaningful — the value must survive parsing as signed rather than as a huge
// positive capacity — and creation registers no queue.
TEST(QInitialize, NegativeLengthCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 1, -4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");  // no queue was registered
}

// §20.15.1: the q_id shall uniquely identify the new queue, so a second
// $q_initialize re-using a live q_id cannot create another queue over it. The
// original queue must survive the duplicate call: an entry added before it is
// still removable afterward (job 7 comes back with status 0), proving the id
// still names the same queue rather than a freshly reset one.
TEST(QInitialize, QidMustBeUnique) {
  auto out = RunBody(
      "    $q_initialize(5, 1, 4, st);\n"
      "    $q_add(5, 7, 0, st);\n"
      "    $q_initialize(5, 1, 4, st);\n"  // duplicate id, no new queue
      "    $q_remove(5, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");  // original queue still has its entry
  EXPECT_EQ(out[1], "7");  // and it is the entry added before the duplicate
}

// §20.15.1: because the q_id identifies the queue, distinct q_ids name
// independent queues. An entry added under one id leaves the other empty — a
// remove from the untouched queue reports empty (status 3).
TEST(QInitialize, DistinctQidsAreIndependentQueues) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $q_initialize(2, 1, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"         // populate queue 1 only
      "    $q_remove(1, job, inf, st);\n"  // queue 1 yields its entry
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"  // queue 2 is still empty
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");  // queue 1 had the entry
  EXPECT_EQ(out[1], "3");  // queue 2 empty, cannot remove
}

}  // namespace
