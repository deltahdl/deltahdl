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
      "  integer jv;\n"
      "  integer nv;\n"
      "  initial begin\n" +
      body +
      "  end\n"
      "endmodule\n";
  return Lines(RunCapture(src, f));
}

TEST(QAdd, PlacesEntryOnQueue) {
  auto out = RunBody(
      "    $q_initialize(7, 1, 4, st);\n"
      "    $q_add(7, 11, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(7, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "0");
  EXPECT_EQ(out[2], "11");
}

TEST(QAdd, AddToUndefinedQueuePlacesNothing) {
  auto out = RunBody(
      "    $q_add(99, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(99, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_NE(out[0], "0");
  EXPECT_NE(out[1], "0");
}

TEST(QAdd, QidSelectsTargetQueue) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 1, st);\n"
      "    $q_initialize(2, 1, 1, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 2, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(2, 3, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");
  EXPECT_NE(out[1], "0");
  EXPECT_EQ(out[2], "0");
}

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
  EXPECT_EQ(out[0], "42");
  EXPECT_EQ(out[1], "84");
}

TEST(QAdd, InformIdCarriedWithEntry) {
  auto out = RunBody(
      "    $q_initialize(5, 1, 4, st);\n"
      "    $q_add(5, 1, 314, st);\n"
      "    $q_remove(5, job, inf, st);\n"
      "    $display(\"%0d\", inf);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "314");
}

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
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "77");
  EXPECT_EQ(out[2], "555");
}

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
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "88");
}

TEST(QAdd, ReportsOutcomeInStatus) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(2, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_NE(out[1], "0");
}

TEST(QAdd, RejectedAddDoesNotPlaceEntry) {
  auto out = RunBody(
      "    $q_initialize(4, 1, 1, st);\n"
      "    $q_add(4, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(4, 2, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(4, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(4, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 4u);
  EXPECT_EQ(out[0], "0");
  EXPECT_NE(out[1], "0");
  EXPECT_EQ(out[2], "0");
  EXPECT_NE(out[3], "0");
}

TEST(QAdd, StatusOutputWakesAnEventControlOnIt) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  integer st;\n"
      "  integer hits;\n"
      "  always @(st) hits = hits + 1;\n"
      "  initial begin\n"
      "    hits = 0;\n"
      "    #1 $q_add(99, 1, 0, st);\n"
      "    #1 $finish;\n"
      "  end\n"
      "endmodule\n",
      f, "hits");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 1u);
}

}  // namespace
