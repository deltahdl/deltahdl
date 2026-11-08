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

TEST(QExam, CurrentQueueLength) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"
      "    #1 $q_exam(1, 1, sv, st);\n"
      "    $display(\"%0d\", sv);\n"
      "    #1 $q_remove(1, job, inf, st);\n"
      "    #1 $q_exam(1, 1, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");
  EXPECT_EQ(out[1], "1");
}

TEST(QExam, MaximumQueueLength) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"
      "    #1 $q_remove(1, job, inf, st);\n"
      "    #1 $q_remove(1, job, inf, st);\n"
      "    #1 $q_exam(1, 3, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "3");
}

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

TEST(QExam, ShortestWaitEver) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #2 $q_add(1, 1, 0, st);\n"
      "    #3 $q_remove(1, job, inf, st);\n"
      "    #1 $q_remove(1, job, inf, st);\n"
      "    #1 $q_exam(1, 4, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "4");
}

TEST(QExam, AverageWaitTime) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #4 $q_remove(1, job, inf, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #6 $q_remove(1, job, inf, st);\n"
      "    #1 $q_exam(1, 6, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "5");
}

TEST(QExam, LongestWaitStillQueued) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #3 $q_add(1, 1, 0, st);\n"
      "    #7 $q_exam(1, 5, sv, st);\n"
      "    $display(\"%0d\", sv);\n"
      "    $q_remove(1, job, inf, st);\n"
      "    $q_exam(1, 5, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "10");
  EXPECT_EQ(out[1], "7");
}

TEST(QExam, ReportsSuccessStatus) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $q_exam(1, 1, sv, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

TEST(QExam, ExamUndefinedQueueReportsError) {
  auto out = RunBody(
      "    $q_exam(99, 1, sv, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_NE(out[0], "0");
}

TEST(QExam, AcceptsVariableStatCodeOperand) {
  auto out = RunBody(
      "    integer code;\n"
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_add(1, 1, 0, st);\n"
      "    code = 1;\n"
      "    $q_exam(1, code, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(QExam, UnknownStatCodeYieldsZero) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    #1 $q_exam(1, 99, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

TEST(QExam, StatisticsOnEmptyQueueAreZero) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    #5 $q_exam(1, 1, sv, st);\n"
      "    $display(\"%0d\", sv);\n"
      "    $q_exam(1, 5, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "0");
}

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
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "0");
}

TEST(QExam, MeanInterarrivalWithSingleArrivalIsZero) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 8, st);\n"
      "    #3 $q_add(1, 1, 0, st);\n"
      "    #4 $q_exam(1, 2, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "0");
}

TEST(QExam, AcceptsVariableQidOperand) {
  auto out = RunBody(
      "    $q_initialize(7, 1, 8, st);\n"
      "    $q_add(7, 1, 0, st);\n"
      "    #1 $q_add(7, 1, 0, st);\n"
      "    qv = 7;\n"
      "    $q_exam(qv, 1, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(QExam, ShortestWaitReflectsLifoQueueDiscipline) {
  auto out = RunBody(
      "    $q_initialize(8, 2, 8, st);\n"
      "    $q_add(8, 1, 0, st);\n"
      "    #2 $q_add(8, 1, 0, st);\n"
      "    #3 $q_remove(8, job, inf, st);\n"
      "    #1 $q_remove(8, job, inf, st);\n"
      "    #1 $q_exam(8, 4, sv, st);\n"
      "    $display(\"%0d\", sv);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "3");
}

}  // namespace
