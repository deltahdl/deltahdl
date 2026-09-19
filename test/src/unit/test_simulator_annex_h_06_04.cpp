#include <gtest/gtest.h>

#include <cstddef>
#include <utility>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_c_type.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

// Annex H.6.4 (Value changes for output and inout arguments): the
// SystemVerilog simulator is responsible for handling value changes for
// output and inout arguments, and such changes shall be detected and
// handled after control returns from C code to SystemVerilog code. The
// cases check which directions the simulator watches for a change, and
// that a change an imported function makes to an output is not yet
// detected while the C code runs and is once control has returned, the C
// code having nothing to do to raise it.

namespace {

// §H.6.4: the simulator watches an output and an inout for a change, and
// an input, which the foreign code may not modify (§H.6.2), not at all.
TEST(DpiValueChanges, TheSimulatorHandlesChangesOfOutputsAndInouts) {
  EXPECT_TRUE(DpiSimulatorDetectsChangesOf(Direction::kOutput));
  EXPECT_TRUE(DpiSimulatorDetectsChangesOf(Direction::kInout));
  EXPECT_FALSE(DpiSimulatorDetectsChangesOf(Direction::kInput));
}

// §H.6.4: while the C code runs no change has been detected -- the
// imported function sees none recorded even after it has written its
// output -- and once control returns the change is there to handle.
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
  // The input the function wrote to raised nothing and holds what it held.
  EXPECT_EQ(actuals[1].AsInt(), 3);
}

}  // namespace
