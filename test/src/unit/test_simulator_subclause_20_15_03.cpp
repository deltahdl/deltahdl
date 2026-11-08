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
      "  integer qv;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  return Lines(RunCapture(src, f));
}

TEST(QRemove, ReturnsInformIdStoredAtAdd) {
  auto out = RunBody(
      "    $q_initialize(3, 1, 4, st);\n"
      "    $q_add(3, 5, 9001, st);\n"
      "    $q_remove(3, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $display(\"%0d\", inf);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "9001");
  EXPECT_EQ(out[2], "5");
}

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
  EXPECT_EQ(out[0], "22");
  EXPECT_EQ(out[1], "11");
}

TEST(QRemove, AcceptsIntegerVariableQidOperand) {
  auto out = RunBody(
      "    $q_initialize(7, 1, 2, st);\n"
      "    $q_add(7, 55, 0, st);\n"
      "    qv = 7;\n"
      "    $q_remove(qv, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "55");
}

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
  EXPECT_EQ(out[0], "100");
  EXPECT_EQ(out[1], "200");
}

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
  EXPECT_EQ(out[0], "200");
  EXPECT_EQ(out[1], "100");
}

TEST(QRemove, RemoveFromEmptyQueueReportsError) {
  auto out = RunBody(
      "    $q_initialize(6, 1, 2, st);\n"
      "    $q_remove(6, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");
}

TEST(QRemove, RemoveFromUndefinedQueueReportsError) {
  auto out = RunBody(
      "    $q_remove(99, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");
}

TEST(QRemove, SuccessfulRemoveConsumesTheEntry) {
  auto out = RunBody(
      "    $q_initialize(8, 1, 2, st);\n"
      "    $q_add(8, 77, 0, st);\n"
      "    $q_remove(8, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $display(\"%0d\", job);\n"
      "    $q_remove(8, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "77");
  EXPECT_NE(out[2], "0");
}

}  // namespace
