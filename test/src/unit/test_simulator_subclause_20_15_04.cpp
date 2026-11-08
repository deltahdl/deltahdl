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

TEST(QFull, EmptyQueueIsNotFull) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 2, st);\n"
      "    r = $q_full(1, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

TEST(QFull, PartiallyFilledQueueIsNotFull) {
  auto out = RunBody(
      "    $q_initialize(2, 1, 3, st);\n"
      "    $q_add(2, 10, 0, st);\n"
      "    r = $q_full(2, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

TEST(QFull, FullQueueReturnsOne) {
  auto out = RunBody(
      "    $q_initialize(3, 1, 2, st);\n"
      "    $q_add(3, 10, 0, st);\n"
      "    $q_add(3, 20, 0, st);\n"
      "    r = $q_full(3, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "1");
}

TEST(QFull, SingleEntryQueueIsFullAfterOneAdd) {
  auto out = RunBody(
      "    $q_initialize(4, 1, 1, st);\n"
      "    r = $q_full(4, st);\n"
      "    $display(\"%0d\", r);\n"
      "    $q_add(4, 7, 0, st);\n"
      "    r = $q_full(4, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "1");
}

TEST(QFull, ReportsNotFullAfterEntryRemoved) {
  auto out = RunBody(
      "    $q_initialize(5, 1, 2, st);\n"
      "    $q_add(5, 1, 0, st);\n"
      "    $q_add(5, 2, 0, st);\n"
      "    r = $q_full(5, st);\n"
      "    $display(\"%0d\", r);\n"
      "    $q_remove(5, job, inf, st);\n"
      "    r = $q_full(5, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "1");
  EXPECT_EQ(out[1], "0");
}

TEST(QFull, AcceptsIntegerVariableQidOperand) {
  auto out = RunBody(
      "    $q_initialize(8, 1, 1, st);\n"
      "    $q_add(8, 55, 0, st);\n"
      "    qv = 8;\n"
      "    r = $q_full(qv, st);\n"
      "    $display(\"%0d\", r);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "1");
}

TEST(QFull, ReportsSuccessStatusOnLiveQueue) {
  auto out = RunBody(
      "    $q_initialize(9, 1, 2, st);\n"
      "    r = $q_full(9, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

TEST(QFull, UndefinedQueueReportsErrorStatus) {
  auto out = RunBody(
      "    r = $q_full(99, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");
}

}  // namespace
