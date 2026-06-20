#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(TimeLiteralSimulation, IntegerNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 10ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

TEST(TimeLiteralSimulation, FixedPointNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

TEST(TimeLiteralSimulation, ScalePs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

TEST(TimeLiteralSimulation, ScaleFs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 100fs;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.0001);
}

TEST(TimeLiteralSimulation, ScaleUs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1000.0);
}

TEST(TimeLiteralSimulation, ScaleMs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1ms;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e6);
}

TEST(TimeLiteralSimulation, ScaleS) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1s;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e9);
}

TEST(TimeLiteralSimulation, ScaledToExplicitTimeunitPs) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  timeunit 1ps;\n"
      "  realtime r;\n"
      "  initial r = 40ps;\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 40.0);
}

TEST(TimeLiteralSimulation, ScaledToExplicitTimeunitUs) {
  auto v = RunAndGetReal(
      "module t;\n"
      "  timeunit 1us;\n"
      "  realtime r;\n"
      "  initial r = 500ns;\n"
      "endmodule\n",
      "r");
  EXPECT_DOUBLE_EQ(v, 0.5);
}

}  // namespace
