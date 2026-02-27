
#include <cstring>

#include "simulation/lowerer.h"
#include "simulation/variable.h"

#include "fixture_simulator.h"

using namespace delta;

static double RunAndGetReal(const std::string& src, const char* var_name) {
  SimFixture f;
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  if (!design) return 0.0;
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable(var_name);
  EXPECT_NE(var, nullptr);
  if (!var) return 0.0;
  double d = 0.0;
  uint64_t bits = var->value.ToUint64();
  std::memcpy(&d, &bits, sizeof(double));
  return d;
}

// ===========================================================================
// §5.8 Time literals
// ===========================================================================

// ---------------------------------------------------------------------------
// 1. Integer format with ns unit (default time unit)
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitIntegerNs) {
  // §5.8: Integer time literal with ns unit (default).
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 10ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 10.0);
}

// ---------------------------------------------------------------------------
// 2. Fixed-point format with ns unit
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitFixedPointNs) {
  // §5.8: Fixed-point time literal with ns unit.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

// ---------------------------------------------------------------------------
// 3. ps unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitPs) {
  // §5.8 example: 40ps.  With default timeunit 1ns: 40ps = 0.04 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}

// ---------------------------------------------------------------------------
// 4. fs unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitFs) {
  // §5.8 unit: fs.  100fs = 0.0001 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 100fs;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.0001);
}

// ---------------------------------------------------------------------------
// 5. us unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitUs) {
  // §5.8 unit: us.  1us = 1000.0 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1000.0);
}

// ---------------------------------------------------------------------------
// 6. ms unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitMs) {
  // §5.8 unit: ms.  1ms = 1e6 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1ms;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e6);
}

// ---------------------------------------------------------------------------
// 7. s unit — scaled to default time unit (ns)
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitS) {
  // §5.8 unit: s.  1s = 1e9 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 1s;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 1e9);
}

// ---------------------------------------------------------------------------
// 8. Fixed-point format with non-ns unit
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitFixedPointUs) {
  // §5.8: fixed-point format with us unit.  2.5us = 2500.0 ns.
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.5us;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2500.0);
}

// ---------------------------------------------------------------------------
// 9. LRM example: 2.1ns
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitLrmExample2p1ns) {
  // §5.8 example verbatim: "2.1ns"
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 2.1ns;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 2.1);
}

// ---------------------------------------------------------------------------
// 10. LRM example: 40ps
// ---------------------------------------------------------------------------
TEST(SimCh508, TimeLitLrmExample40ps) {
  // §5.8 example verbatim: "40ps"
  auto v = RunAndGetReal(
      "module t;\n  realtime r;\n  initial r = 40ps;\nendmodule\n", "r");
  EXPECT_DOUBLE_EQ(v, 0.04);
}
