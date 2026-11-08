#include <gtest/gtest.h>

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"

using namespace delta;

namespace {

TEST(DpiForeignLayer, RuntimeProvidesArgPassingForInoutFormalAccess) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_accumulate";
  func.sv_name = "sv_accumulate";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{}};
  func.args[0].direction = Direction::kInout;
  func.args[0].type = DataTypeKind::kInt;
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    const int32_t kSeen = args[0].AsInt();
    args[0] = DpiArgValue::FromInt(kSeen + 100);
    return DpiArgValue::FromInt(kSeen);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5)};
  const DpiArgValue kResult = rt.CallImportWithArgs("sv_accumulate", actuals);

  EXPECT_EQ(kResult.AsInt(), 5);
  EXPECT_EQ(actuals[0].AsInt(), 105);
}

TEST(DpiForeignLayer, RuntimeProvidesArgPassingForOutputFormalAccess) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce";
  func.sv_name = "sv_produce";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{}};
  func.args[0].direction = Direction::kOutput;
  func.args[0].type = DataTypeKind::kInt;
  auto seen_seed = std::make_shared<int32_t>(-1);
  func.arg_impl = [seen_seed](std::vector<DpiArgValue>& args) -> DpiArgValue {
    *seen_seed = args[0].AsInt();
    args[0] = DpiArgValue::FromInt(77);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(func);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(12345)};
  rt.CallImportWithArgs("sv_produce", actuals);

  EXPECT_NE(*seen_seed, 12345);
  EXPECT_EQ(actuals[0].AsInt(), 77);
}

TEST(DpiForeignLayer, SameSvCodeUsableWithDifferentForeignDataAccessMethods) {
  DpiRuntime rt_input_layer;
  DpiRtFunction input_layer;
  input_layer.c_name = "c_triple_input";
  input_layer.sv_name = "sv_triple";
  input_layer.return_type = DataTypeKind::kInt;
  input_layer.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 3);
  };
  rt_input_layer.RegisterImport(input_layer);

  DpiRuntime rt_argpass_layer;
  DpiRtFunction argpass_layer;
  argpass_layer.c_name = "c_triple_argpass";
  argpass_layer.sv_name = "sv_triple";
  argpass_layer.return_type = DataTypeKind::kInt;
  argpass_layer.args = {DpiArg{}};
  argpass_layer.args[0].direction = Direction::kInput;
  argpass_layer.args[0].type = DataTypeKind::kInt;
  argpass_layer.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 3);
  };
  rt_argpass_layer.RegisterImport(argpass_layer);

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(14)};
  const int32_t kViaInput =
      rt_input_layer.CallImport("sv_triple", actuals).AsInt();
  const int32_t kViaArgpass =
      rt_argpass_layer.CallImportWithArgs("sv_triple", actuals).AsInt();

  EXPECT_EQ(kViaInput, 42);
  EXPECT_EQ(kViaInput, kViaArgpass);
}

TEST(DpiForeignLayer, SameSvCodeUsableAcrossForeignLayersOnWriteBackPath) {
  const auto kMakeWriter = [](int32_t produced) {
    DpiRtFunction func;
    func.sv_name = "sv_emit";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{}};
    func.args[0].direction = Direction::kOutput;
    func.args[0].type = DataTypeKind::kInt;
    func.arg_impl = [produced](std::vector<DpiArgValue>& args) -> DpiArgValue {
      args[0] = DpiArgValue::FromInt(produced);
      return DpiArgValue::FromInt(0);
    };
    return func;
  };

  DpiRuntime rt_layer_a;
  DpiRtFunction layer_a = kMakeWriter(8);
  layer_a.c_name = "c_emit_const";
  rt_layer_a.RegisterImport(layer_a);

  DpiRuntime rt_layer_b;
  DpiRtFunction layer_b = kMakeWriter(8);
  layer_b.c_name = "c_emit_other";
  rt_layer_b.RegisterImport(layer_b);

  std::vector<DpiArgValue> actuals_a = {DpiArgValue::FromInt(0)};
  std::vector<DpiArgValue> actuals_b = {DpiArgValue::FromInt(0)};
  rt_layer_a.CallImportWithArgs("sv_emit", actuals_a);
  rt_layer_b.CallImportWithArgs("sv_emit", actuals_b);

  EXPECT_EQ(actuals_a[0].AsInt(), 8);
  EXPECT_EQ(actuals_a[0].AsInt(), actuals_b[0].AsInt());
}

TEST(DpiForeignLayer, MixedDirectionCallExercisesFullArgPassingMechanism) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_combine";
  func.sv_name = "sv_combine";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{}, DpiArg{}, DpiArg{}};
  func.args[0].direction = Direction::kInput;
  func.args[0].type = DataTypeKind::kInt;
  func.args[1].direction = Direction::kOutput;
  func.args[1].type = DataTypeKind::kInt;
  func.args[2].direction = Direction::kInout;
  func.args[2].type = DataTypeKind::kInt;
  auto seen_output_seed = std::make_shared<int32_t>(-1);
  func.arg_impl =
      [seen_output_seed](std::vector<DpiArgValue>& args) -> DpiArgValue {
    const int32_t kIn = args[0].AsInt();
    const int32_t kInoutInitial = args[2].AsInt();
    *seen_output_seed = args[1].AsInt();
    args[1] = DpiArgValue::FromInt(kIn * kInoutInitial);
    args[2] = DpiArgValue::FromInt(kInoutInitial + 1);
    return DpiArgValue::FromInt(kIn + kInoutInitial);
  };
  rt.RegisterImport(func);

  const int32_t kOutputSentinel = 999;
  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(6),
                                      DpiArgValue::FromInt(kOutputSentinel),
                                      DpiArgValue::FromInt(10)};
  const DpiArgValue kResult = rt.CallImportWithArgs("sv_combine", actuals);

  EXPECT_EQ(kResult.AsInt(), 16);
  EXPECT_NE(*seen_output_seed, kOutputSentinel);
  EXPECT_EQ(actuals[1].AsInt(), 60);
  EXPECT_EQ(actuals[2].AsInt(), 11);
  EXPECT_EQ(actuals[0].AsInt(), 6);
}

}  // namespace
