#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(SimClause05, Cl5_8_IntegerNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 10ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

TEST(SimClause05, Cl5_8_FixedPointNs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

TEST(SimClause05, Cl5_8_Ps) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

TEST(SimClause05, Cl5_8_Fs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 100fs;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.0001);
}

TEST(SimClause05, Cl5_8_Us) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1000.0);
}

TEST(SimClause05, Cl5_8_Ms) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1ms;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e6);
}

TEST(SimClause05, Cl5_8_S) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1s;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e9);
}

TEST(SimClause05, Cl5_8_FixedPointUs) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.5us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2500.0);
}

TEST(SimClause05, Cl5_8_LrmExample2p1ns) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

TEST(SimClause05, Cl5_8_LrmExample40ps) {
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

}  // namespace
