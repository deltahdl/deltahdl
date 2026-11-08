#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_touch_import.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(DpiArgumentDirections, InputActualUnchangedAfterForeignModification) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_consume";
  func.sv_name = "consume";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    int32_t seen = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(-1);
    return DpiArgValue::FromInt(seen);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(7)};
  DpiArgValue result = rt.CallImportWithArgs("consume", actuals);

  EXPECT_EQ(result.AsInt(), 7);
  EXPECT_EQ(actuals[0].AsInt(), 7);
}

TEST(DpiArgumentDirections, OutputInitialUndeterminedAndWritebackVisible) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce";
  func.sv_name = "produce";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"y", DataTypeKind::kInt, Direction::kOutput}};
  int32_t observed_initial = 12345;
  func.arg_impl = [&observed_initial](std::vector<DpiArgValue>& a) {
    observed_initial = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(42);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(999)};
  rt.CallImportWithArgs("produce", actuals);

  EXPECT_NE(observed_initial, 999);
  EXPECT_EQ(observed_initial, 0);
  EXPECT_EQ(actuals[0].AsInt(), 42);
}

TEST(DpiArgumentDirections, InoutInitialReadableAndWritebackVisible) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_bump";
  func.sv_name = "bump";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"z", DataTypeKind::kInt, Direction::kInout}};
  int32_t observed_initial = -1;
  func.arg_impl = [&observed_initial](std::vector<DpiArgValue>& a) {
    observed_initial = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(a[0].AsInt() + 1);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(7)};
  rt.CallImportWithArgs("bump", actuals);

  EXPECT_EQ(observed_initial, 7);
  EXPECT_EQ(actuals[0].AsInt(), 8);
}

TEST(DpiArgumentDirections, MixedDirectionArgumentsHandledInOneCall) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_mix";
  func.sv_name = "mix";
  func.return_type = DataTypeKind::kVoid;
  func.args = {
      DpiArg{"a", DataTypeKind::kInt, Direction::kInput},
      DpiArg{"b", DataTypeKind::kInt, Direction::kOutput},
      DpiArg{"c", DataTypeKind::kInt, Direction::kInout},
  };
  int32_t seen_in = -1;
  int32_t seen_out = -1;
  int32_t seen_io = -1;
  func.arg_impl = [&](std::vector<DpiArgValue>& a) {
    seen_in = a[0].AsInt();
    seen_out = a[1].AsInt();
    seen_io = a[2].AsInt();
    a[0] = DpiArgValue::FromInt(111);
    a[1] = DpiArgValue::FromInt(222);
    a[2] = DpiArgValue::FromInt(seen_io + 1);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5),
                                      DpiArgValue::FromInt(900),
                                      DpiArgValue::FromInt(7)};
  rt.CallImportWithArgs("mix", actuals);

  EXPECT_EQ(seen_in, 5);
  EXPECT_EQ(actuals[0].AsInt(), 5);
  EXPECT_NE(seen_out, 900);
  EXPECT_EQ(seen_out, 0);
  EXPECT_EQ(actuals[1].AsInt(), 222);
  EXPECT_EQ(seen_io, 7);
  EXPECT_EQ(actuals[2].AsInt(), 8);
}

TEST(DpiArgumentDirections, OutputUndeterminedSeedMatchesNonIntFormalType) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_rout";
  func.sv_name = "rout";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"r", DataTypeKind::kReal, Direction::kOutput}};
  double seen = 1.0;
  func.arg_impl = [&seen](std::vector<DpiArgValue>& a) {
    seen = a[0].AsReal();
    a[0] = DpiArgValue::FromReal(2.5);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromReal(99.0)};
  rt.CallImportWithArgs("rout", actuals);

  EXPECT_NE(seen, 99.0);
  EXPECT_DOUBLE_EQ(seen, 0.0);
  EXPECT_DOUBLE_EQ(actuals[0].AsReal(), 2.5);
}

TEST(DpiArgumentDirections, OutputUndeterminedSeedForStringFormalIsNotActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_sout";
  func.sv_name = "sout";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"s", DataTypeKind::kString, Direction::kOutput}};
  std::string seen = "sentinel";
  func.arg_impl = [&seen](std::vector<DpiArgValue>& a) {
    seen = a[0].AsString();
    a[0] = DpiArgValue::FromString("written");
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromString("caller")};
  rt.CallImportWithArgs("sout", actuals);

  EXPECT_NE(seen, "caller");
  EXPECT_EQ(seen, "");
  EXPECT_EQ(actuals[0].AsString(), "written");
}

TEST(DpiArgumentDirections, OutputUndeterminedSeedForLongintFormalIsNotActual) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_lout";
  func.sv_name = "lout";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"l", DataTypeKind::kLongint, Direction::kOutput}};
  int64_t seen = 0x7fffffffffffffffLL;
  func.arg_impl = [&seen](std::vector<DpiArgValue>& a) {
    seen = a[0].AsLongint();
    a[0] = DpiArgValue::FromLongint(0x0123456789abcdefLL);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {
      DpiArgValue::FromLongint(0x1111222233334444LL)};
  rt.CallImportWithArgs("lout", actuals);

  EXPECT_NE(seen, 0x1111222233334444LL);
  EXPECT_EQ(seen, 0);
  EXPECT_EQ(actuals[0].AsLongint(), 0x0123456789abcdefLL);
}

TEST(DpiArgumentDirections, LegacyInputOnlyCallbackLeavesActualUnchanged) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_legacy";
  func.sv_name = "legacy";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.impl = [](const std::vector<DpiArgValue>& a) {
    return DpiArgValue::FromInt(a[0].AsInt() * 2);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(6)};
  DpiArgValue result = rt.CallImportWithArgs("legacy", actuals);

  EXPECT_EQ(result.AsInt(), 12);
  EXPECT_EQ(actuals[0].AsInt(), 6);
}

struct TouchingAnActual {
  DpiRuntime dpi;
  SimFixture f;
  uint64_t seen = 0;

  TouchingAnActual(Direction direction, uint64_t wrote, uint64_t actual) {
    RegisterTouchImport(dpi, direction, wrote, &seen);
    f.ctx.SetDpiRuntime(&dpi);
    auto* var = f.ctx.CreateVariable("a", 32);
    var->value = MakeLogic4VecVal(f.arena, 32, actual);
    EvalFunctionCall(ParseExprFrom("touch(a)", f), f.ctx, f.arena);
  }

  uint64_t Actual() { return f.ctx.FindVariable("a")->value.ToUint64(); }
};

TEST(DpiArgumentDirectionsInADesign, AnInputActualIsNotChangedByTheCall) {
  TouchingAnActual run(Direction::kInput, 111, 5);
  EXPECT_EQ(run.Actual(), 5U);
}

TEST(DpiArgumentDirectionsInADesign, AnInputActualReachesTheImport) {
  TouchingAnActual run(Direction::kInput, 111, 5);
  EXPECT_EQ(run.seen, 5U);
}

TEST(DpiArgumentDirectionsInADesign, AnOutputActualTakesWhatTheImportWrote) {
  TouchingAnActual run(Direction::kOutput, 42, 900);
  EXPECT_EQ(run.Actual(), 42U);
}

TEST(DpiArgumentDirectionsInADesign, AnOutputFormalIsNotHandedTheActual) {
  TouchingAnActual run(Direction::kOutput, 42, 900);
  EXPECT_NE(run.seen, 900U);
}

TEST(DpiArgumentDirectionsInADesign, AnInoutFormalIsHandedTheActual) {
  TouchingAnActual run(Direction::kInout, 8, 7);
  EXPECT_EQ(run.seen, 7U);
}

TEST(DpiArgumentDirectionsInADesign, AnInoutActualTakesWhatTheImportWrote) {
  TouchingAnActual run(Direction::kInout, 8, 7);
  EXPECT_EQ(run.Actual(), 8U);
}

TEST(DpiArgumentDirectionsInADesign, ANamedActualTakesItsOwnFormalsValue) {
  DpiRuntime dpi;
  SimFixture f;
  DpiRtFunction func;
  func.c_name = "c_pair";
  func.sv_name = "pair";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"first", DataTypeKind::kInt, Direction::kOutput},
               DpiArg{"second", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& args) -> DpiArgValue {
    args[0] = DpiArgValue::FromInt(11);
    args[1] = DpiArgValue::FromInt(22);
    return DpiArgValue::FromInt(0);
  };
  dpi.RegisterImport(std::move(func));
  f.ctx.SetDpiRuntime(&dpi);
  f.ctx.CreateVariable("one", 32)->value = MakeLogic4VecVal(f.arena, 32, 0);
  f.ctx.CreateVariable("two", 32)->value = MakeLogic4VecVal(f.arena, 32, 0);

  EvalFunctionCall(ParseExprFrom("pair(.second(two), .first(one))", f), f.ctx,
                   f.arena);

  EXPECT_EQ(f.ctx.FindVariable("two")->value.ToUint64(), 22U);
}

TEST(DpiArgumentDirectionsInADesign, AnImportWritingNothingYieldsItsResult) {
  DpiRuntime dpi;
  SimFixture f;
  DpiRtFunction func;
  func.c_name = "c_double";
  func.sv_name = "twice";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"a", DataTypeKind::kInt, Direction::kInput}};
  func.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 2);
  };
  dpi.RegisterImport(std::move(func));
  f.ctx.SetDpiRuntime(&dpi);
  f.ctx.CreateVariable("a", 32)->value = MakeLogic4VecVal(f.arena, 32, 6);

  auto result =
      EvalFunctionCall(ParseExprFrom("twice(a)", f), f.ctx, f.arena).ToUint64();

  EXPECT_EQ(result, 12U);
}

}  // namespace
