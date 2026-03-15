#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(LexicalConventionSim, IntegerNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 10ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

TEST(LexicalConventionSim, FixedPointNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

TEST(LexicalConventionSim, ScalePs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

TEST(LexicalConventionSim, ScaleFs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 100fs;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.0001);
}

TEST(LexicalConventionSim, ScaleUs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1000.0);
}

TEST(LexicalConventionSim, ScaleMs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1ms;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e6);
}

TEST(LexicalConventionSim, ScaleS) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1s;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e9);
}

TEST(LexicalConventionSim, FixedPointUs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.5us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2500.0);
}

TEST(LexicalConventionSim, FixedPointMs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1.5ms;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1.5e6);
}

TEST(LexicalConventionSim, FixedPointS) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 0.5s;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.5e9);
}

TEST(LexicalConventionSim, FixedPointFs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 500.0fs;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.5);
}

TEST(LexicalConventionSim, FixedPointPs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 3.5ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.0035);
}

}  // namespace
