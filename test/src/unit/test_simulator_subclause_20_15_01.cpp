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

TEST(QInitialize, CreatesNewQueue) {
  auto out = RunBody(
      "    $q_add(7, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(7, 1, 4, st);\n"
      "    $q_add(7, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "2");
  EXPECT_EQ(out[1], "0");
}

TEST(QInitialize, ReturnsCreationOutcomeInStatus) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_initialize(2, 3, 4, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_NE(out[1], "0");
}

TEST(QInitialize, FifoTypeReturnsOldestEntry) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $q_add(1, 11, 0, st);\n"
      "    $q_add(1, 22, 0, st);\n"
      "    $q_remove(1, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "11");
}

TEST(QInitialize, LifoTypeReturnsNewestEntry) {
  auto out = RunBody(
      "    $q_initialize(1, 2, 4, st);\n"
      "    $q_add(1, 11, 0, st);\n"
      "    $q_add(1, 22, 0, st);\n"
      "    $q_remove(1, job, inf, st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "22");
}

TEST(QInitialize, TypeAboveTableCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 3, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(QInitialize, TypeBelowTableCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 0, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(QInitialize, NegativeTypeCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, -1, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(QInitialize, MaxLengthBoundsTheEntryCount) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 2, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 2, 0, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_add(1, 3, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 3u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "0");
  EXPECT_EQ(out[2], "1");
}

TEST(QInitialize, ZeroLengthCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 0, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(QInitialize, NegativeLengthCreatesNothing) {
  auto out = RunBody(
      "    $q_initialize(1, 1, -4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 1u);
  EXPECT_EQ(out[0], "2");
}

TEST(QInitialize, QidMustBeUnique) {
  auto out = RunBody(
      "    $q_initialize(5, 1, 4, st);\n"
      "    $q_add(5, 7, 0, st);\n"
      "    $q_initialize(5, 1, 4, st);\n"
      "    $q_remove(5, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $display(\"%0d\", job);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "7");
}

TEST(QInitialize, DistinctQidsAreIndependentQueues) {
  auto out = RunBody(
      "    $q_initialize(1, 1, 4, st);\n"
      "    $q_initialize(2, 1, 4, st);\n"
      "    $q_add(1, 1, 0, st);\n"
      "    $q_remove(1, job, inf, st);\n"
      "    $display(\"%0d\", st);\n"
      "    $q_remove(2, job, inf, st);\n"
      "    $display(\"%0d\", st);\n");
  ASSERT_EQ(out.size(), 2u);
  EXPECT_EQ(out[0], "0");
  EXPECT_EQ(out[1], "3");
}

}  // namespace
