#include <gtest/gtest.h>

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiValueChanges, TheSimulatorHandlesChangesOfOutputsAndInouts) {
  EXPECT_TRUE(DpiSimulatorDetectsChangesOf(Direction::kOutput));
  EXPECT_TRUE(DpiSimulatorDetectsChangesOf(Direction::kInout));
  EXPECT_FALSE(DpiSimulatorDetectsChangesOf(Direction::kInput));
}

TEST(DpiValueChanges, AChangeIsDetectedAfterControlReturns) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_set";
  func.sv_name = "set";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"o", DataTypeKind::kInt, Direction::kOutput},
               DpiArg{"i", DataTypeKind::kInt, Direction::kInput}};
  std::vector<DpiArgValueChange> changes;
  std::size_t detected_while_running = 99;
  func.arg_impl = [&](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(42);
    a[1] = DpiArgValue::FromInt(-1);
    detected_while_running = changes.size();
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(7),
                                      DpiArgValue::FromInt(3)};
  rt.CallImportDetectingChanges("set", actuals, changes);

  EXPECT_EQ(detected_while_running, 0U);
  ASSERT_EQ(changes.size(), 1U);
  EXPECT_EQ(changes[0].index, 0U);
  EXPECT_EQ(changes[0].old_value.AsInt(), 7);
  EXPECT_EQ(changes[0].new_value.AsInt(), 42);
  EXPECT_EQ(actuals[0].AsInt(), 42);
  EXPECT_EQ(actuals[1].AsInt(), 3);
}

int WriteThenPeek(int* v) {
  auto peek = NamedExport<int (*)()>("sv_peek");
  *v = 9;
  return peek == nullptr ? -1 : peek();
}

void RunPeekDuring(const std::string& direction, SimFixture& f) {
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" context function int during(" +
          direction +
          " int v);\n"
          "  export \"DPI-C\" function sv_peek;\n"
          "  int a = 5;\n"
          "  int events, woken, seen;\n"
          "  function int sv_peek();\n"
          "    return a * 100 + events * 10 + woken;\n"
          "  endfunction\n"
          "  always @(a) events++;\n"
          "  initial begin wait (a == 9); woken = 1; end\n"
          "  initial #1 seen = during(a);\n"
          "endmodule\n",
      f, {{"during", reinterpret_cast<void*>(&WriteThenPeek)}},
      "annex_h_06_04_during");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
}

TEST(DpiValueChanges, ADesignsInoutChangesOnceAfterTheImportReturns) {
  SimFixture f;
  RunPeekDuring("inout", f);
  EXPECT_EQ(DesignValue(f, "seen"), 500U);
  EXPECT_EQ(DesignValue(f, "a"), 9U);
  EXPECT_EQ(DesignValue(f, "events"), 1U);
  EXPECT_EQ(DesignValue(f, "woken"), 1U);
}

TEST(DpiValueChanges, ADesignsOutputChangesOnceAfterTheImportReturns) {
  SimFixture f;
  RunPeekDuring("output", f);
  EXPECT_EQ(DesignValue(f, "seen"), 500U);
  EXPECT_EQ(DesignValue(f, "a"), 9U);
  EXPECT_EQ(DesignValue(f, "events"), 1U);
  EXPECT_EQ(DesignValue(f, "woken"), 1U);
}

void LeaveInout(int* v) { *v += 0; }

TEST(DpiValueChanges, AnInoutLeftAsItWasRaisesNoChangeInADesign) {
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" function void leave(inout int v);\n"
      "  int a = 5;\n"
      "  int events;\n"
      "  always @(a) events++;\n"
      "  initial #1 leave(a);\n"
      "endmodule\n",
      f, {{"leave", reinterpret_cast<void*>(&LeaveInout)}},
      "annex_h_06_04_leave");
  EXPECT_EQ(DesignValue(f, "a"), 5U);
  EXPECT_EQ(DesignValue(f, "events"), 0U);
}

}  // namespace
