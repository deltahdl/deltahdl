#include <gtest/gtest.h>

#include <cstddef>
#include <utility>
#include <vector>

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

}  // namespace
