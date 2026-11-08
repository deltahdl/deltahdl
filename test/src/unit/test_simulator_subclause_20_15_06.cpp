#include <gtest/gtest.h>

#include <string>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_text_lines.h"

using namespace delta;

namespace {

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

TEST(StochasticQueueStatus, InitializeSucceedsWithOk) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

TEST(StochasticQueueStatus, UnsupportedQueueType) {
  auto out = RunBody(
      "    $q_initialize(1, 3, 4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "4");
}

TEST(StochasticQueueStatus, ZeroLength) {
  auto out = RunBody(
      "    $q_initialize(1, 2, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "5");
}

TEST(StochasticQueueStatus, NegativeLength) {
  auto out = RunBody(
      "    $q_initialize(1, 1, -4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "5");
}

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

TEST(StochasticQueueStatus, AddToUndefinedQueue) {
  auto out = RunBody(
      "    $q_add(99, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(StochasticQueueStatus, AddToFullQueue) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 1, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 2, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "0");
  EXPECT_EQ(out[2], "1");
}

TEST(StochasticQueueStatus, RemoveFromEmptyQueue) {
  auto out = RunBody(
      "    $q_initialize(2, 1, 4, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(2, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 5u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "3");
  EXPECT_EQ(out[2], "0");
  EXPECT_EQ(out[3], "0");
  EXPECT_EQ(out[4], "3");
}

TEST(StochasticQueueStatus, RemoveFromUndefinedQueue) {
  auto out = RunBody(
      "    $q_remove(42, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(StochasticQueueStatus, FullReportsStatus) {
  auto out = RunBody(
      "    if ($q_full(3, st)) ;\n"
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(3, 1, 4, st);\n"
      "    if ($q_full(3, st)) ;\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");
  EXPECT_EQ(out[1], "0");
}

TEST(StochasticQueueStatus, ExamReportsStatus) {
  auto out = RunBody(
      "    $q_exam(8, 1, job, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(8, 2, 4, st);\n"
      "    $q_exam(8, 1, job, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");
  EXPECT_EQ(out[1], "0");
}

}  // namespace
