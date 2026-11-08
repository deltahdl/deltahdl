#include <gtest/gtest.h>

#include <cstdint>
#include <utility>
#include <vector>

#include "common/types.h"
#include "fixture_simulator.h"
#include "helpers_dpi_take_int.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(DpiArgumentPassing, InputActualCoercedToFormalTypeOnCopyIn) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_take_int";
  func.sv_name = "take_int";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    bool is_int = a[0].type == DataTypeKind::kInt;
    return DpiArgValue::FromInt(is_int ? a[0].AsInt() : -1);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(42)};
  DpiArgValue result = rt.CallImportWithArgs("take_int", actuals);

  EXPECT_EQ(result.AsInt(), 42);
}

TEST(DpiArgumentPassing, RealInputCoercedToIntegerFormalRoundsLikeAssignment) {
  DpiRuntime rt;
  DpiArgValue result =
      CallTakeIntReportingFormal(rt, DpiArgValue::FromReal(3.7));

  EXPECT_EQ(result.AsInt(), 4);
}

TEST(DpiArgumentPassing, OutputValueCoercedToActualTypeOnCopyOut) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce_int";
  func.sv_name = "produce_int";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"y", DataTypeKind::kInt, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromInt(7);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(0)};
  rt.CallImportWithArgs("produce_int", actuals);

  EXPECT_EQ(actuals[0].type, DataTypeKind::kLongint);
  EXPECT_EQ(actuals[0].AsLongint(), 7);
}

TEST(DpiArgumentPassing, InoutCoercedBothDirections) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_bump";
  func.sv_name = "bump";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"z", DataTypeKind::kInt, Direction::kInout}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    int32_t seen = a[0].type == DataTypeKind::kInt ? a[0].AsInt() : -1;
    a[0] = DpiArgValue::FromInt(seen + 1);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(10)};
  rt.CallImportWithArgs("bump", actuals);

  EXPECT_EQ(actuals[0].type, DataTypeKind::kLongint);
  EXPECT_EQ(actuals[0].AsLongint(), 11);
}

TEST(DpiArgumentPassing, InputCopyInLeavesActualUnaffected) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_clobber";
  func.sv_name = "clobber";
  func.return_type = DataTypeKind::kInt;
  func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    int32_t seen = a[0].AsInt();
    a[0] = DpiArgValue::FromInt(-999);
    return DpiArgValue::FromInt(seen);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(5)};
  DpiArgValue result = rt.CallImportWithArgs("clobber", actuals);

  EXPECT_EQ(result.AsInt(), 5);
  EXPECT_EQ(actuals[0].AsInt(), 5);
}

TEST(DpiArgumentPassing, MatchingTypeArgumentPassesWithoutCoercion) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_echo";
  func.sv_name = "echo";
  func.return_type = DataTypeKind::kLongint;
  func.args = {DpiArg{"x", DataTypeKind::kLongint, Direction::kInput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    bool is_longint = a[0].type == DataTypeKind::kLongint;
    return DpiArgValue::FromLongint(is_longint ? a[0].AsLongint() : -1);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromLongint(123456789012)};
  DpiArgValue result = rt.CallImportWithArgs("echo", actuals);

  EXPECT_EQ(result.AsLongint(), 123456789012);
}

TEST(DpiArgumentPassing, NarrowingInputCoercionTruncatesLikeAssignment) {
  DpiRuntime rt;
  DpiArgValue result =
      CallTakeIntReportingFormal(rt, DpiArgValue::FromLongint(0x100000007LL));

  EXPECT_EQ(result.AsInt(), 7);
}

TEST(DpiArgumentPassing, OutputRealRoundedToIntegerActualOnCopyOut) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_produce_real";
  func.sv_name = "produce_real";
  func.return_type = DataTypeKind::kVoid;
  func.args = {DpiArg{"y", DataTypeKind::kReal, Direction::kOutput}};
  func.arg_impl = [](std::vector<DpiArgValue>& a) {
    a[0] = DpiArgValue::FromReal(2.9);
    return DpiArgValue::FromInt(0);
  };
  rt.RegisterImport(std::move(func));

  std::vector<DpiArgValue> actuals = {DpiArgValue::FromInt(0)};
  rt.CallImportWithArgs("produce_real", actuals);

  EXPECT_EQ(actuals[0].type, DataTypeKind::kInt);
  EXPECT_EQ(actuals[0].AsInt(), 3);
}

struct FourStateActual {
  DpiRuntime dpi;
  SimFixture f;
  SvLogicVecVal seen = {};

  FourStateActual(Direction direction, SvLogicVecVal actual,
                  SvLogicVecVal wrote) {
    DpiRtFunction func;
    func.c_name = "c_touch_4state";
    func.sv_name = "touch4";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"a", DataTypeKind::kInteger, direction}};
    SvLogicVecVal* seen_slot = &seen;
    func.arg_impl = [seen_slot,
                     wrote](std::vector<DpiArgValue>& args) -> DpiArgValue {
      *seen_slot = args[0].AsLogicVec();
      args[0] = DpiArgValue::FromLogicVec(wrote);
      return DpiArgValue::FromInt(0);
    };
    dpi.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&dpi);
    auto* var = f.ctx.CreateVariable("a", 4);
    var->value = MakeLogic4Vec(f.arena, 4);
    var->value.words[0] = Logic4Word{actual.aval, actual.bval};
    EvalFunctionCall(ParseExprFrom("touch4(a)", f), f.ctx, f.arena);
  }

  Logic4Word Actual() { return f.ctx.FindVariable("a")->value.words[0]; }
};

struct PackedFormal {
  DataTypeKind kind = DataTypeKind::kBit;
  uint32_t width = 128;
  Direction direction = Direction::kInput;
};

struct WideActual {
  DpiRuntime dpi;
  SimFixture f;
  std::vector<SvLogicVecVal> seen;

  WideActual(PackedFormal decl, Logic4Word lo, Logic4Word hi,
             const std::vector<SvLogicVecVal>& wrote) {
    DpiRtFunction func;
    func.c_name = "c_touch_wide";
    func.sv_name = "touch_wide";
    func.return_type = DataTypeKind::kInt;
    DpiArg formal;
    formal.name = "k";
    formal.type = decl.kind;
    formal.direction = decl.direction;
    formal.width = decl.width;
    func.args = {formal};
    auto* seen_slot = &seen;
    func.arg_impl = [seen_slot, wrote,
                     decl](std::vector<DpiArgValue>& args) -> DpiArgValue {
      *seen_slot = args[0].AsLogicVecWords();
      if (!wrote.empty()) {
        args[0] = DpiArgValue::FromLogicVecWords(wrote, decl.width, decl.kind);
      }
      return DpiArgValue::FromInt(0);
    };
    dpi.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&dpi);
    auto* var = f.ctx.CreateVariable("k", decl.width);
    var->value = MakeLogic4Vec(f.arena, decl.width);
    var->value.words[0] = lo;
    if (var->value.nwords > 1) var->value.words[1] = hi;
    EvalFunctionCall(ParseExprFrom("touch_wide(k)", f), f.ctx, f.arena);
  }

  const Logic4Vec& Actual() { return f.ctx.FindVariable("k")->value; }
};

TEST(DpiArgumentPassingInADesign, AFormalWiderThanOneWordArrivesWhole) {
  WideActual run(PackedFormal{}, Logic4Word{0x1234567855667788ULL, 0},
                 Logic4Word{0x99AABBCCDDEEFF00ULL, 0}, {});

  ASSERT_EQ(run.seen.size(), 4u);
  EXPECT_EQ(run.seen[0].aval, 0x55667788U);
  EXPECT_EQ(run.seen[1].aval, 0x12345678U);
  EXPECT_EQ(run.seen[2].aval, 0xDDEEFF00U);
  EXPECT_EQ(run.seen[3].aval, 0x99AABBCCU);
}

TEST(DpiArgumentPassingInADesign, AnUnknownBitAboveTheFirstWordSurvives) {
  WideActual run(PackedFormal{}, Logic4Word{1, 0},
                 Logic4Word{0x0000000100000000ULL, 0x0000000100000000ULL}, {});

  ASSERT_EQ(run.seen.size(), 4u);
  EXPECT_EQ(run.seen[0].aval, 1U);
  EXPECT_EQ(run.seen[0].bval, 0U);
  EXPECT_EQ(run.seen[3].aval, 1U);
  EXPECT_EQ(run.seen[3].bval, 1U);
}

TEST(DpiArgumentPassingInADesign, AWideOutputFormalIsWrittenBackWhole) {
  WideActual run(
      PackedFormal{DataTypeKind::kBit, 128, Direction::kOutput}, Logic4Word{},
      Logic4Word{},
      {SvLogicVecVal{0x0A0B0C0DU, 0}, SvLogicVecVal{0x1A1B1C1DU, 0},
       SvLogicVecVal{0x2A2B2C2DU, 0}, SvLogicVecVal{0x3A3B3C3DU, 0}});

  const Logic4Vec& got = run.Actual();
  ASSERT_EQ(got.width, 128U);
  ASSERT_GE(got.nwords, 2U);
  EXPECT_EQ(got.words[0].aval, 0x1A1B1C1D0A0B0C0DULL);
  EXPECT_EQ(got.words[1].aval, 0x3A3B3C3D2A2B2C2DULL);
}

TEST(DpiArgumentPassingInADesign,
     APackedFormalNarrowerThanOneWordArrivesWhole) {
  WideActual run(PackedFormal{DataTypeKind::kBit, 8, Direction::kInput},
                 Logic4Word{0xA5, 0}, Logic4Word{}, {});

  ASSERT_EQ(run.seen.size(), 1u);
  EXPECT_EQ(run.seen[0].aval, 0xA5U);
}

TEST(DpiArgumentPassingInADesign, AnUnknownBitOfAPackedLogicFormalSurvives) {
  WideActual run(PackedFormal{DataTypeKind::kLogic, 8, Direction::kInput},
                 Logic4Word{0x13, 0x10}, Logic4Word{}, {});

  ASSERT_EQ(run.seen.size(), 1u);
  EXPECT_EQ(run.seen[0].aval, 0x13U);
  EXPECT_EQ(run.seen[0].bval, 0x10U);
}

TEST(DpiArgumentPassingInADesign,
     APackedOutputFormalNarrowerThanOneWordIsWrittenBackWhole) {
  WideActual run(PackedFormal{DataTypeKind::kBit, 8, Direction::kOutput},
                 Logic4Word{}, Logic4Word{}, {SvLogicVecVal{0x3C, 0}});

  const Logic4Vec& got = run.Actual();
  ASSERT_EQ(got.width, 8U);
  ASSERT_GE(got.nwords, 1U);
  EXPECT_EQ(got.words[0].aval, 0x3CU);
}

TEST(DpiArgumentPassingInADesign, AnInputActualsUnknownBitReachesTheImport) {
  FourStateActual run(Direction::kInput, SvLogicVecVal{0b1011, 0b0010},
                      SvLogicVecVal{});

  EXPECT_EQ(run.seen.aval, 0b1011U);
  EXPECT_EQ(run.seen.bval, 0b0010U);
}

TEST(DpiArgumentPassingInADesign, AnInputActualsHighImpedanceBitIsNotAnX) {
  FourStateActual run(Direction::kInput, SvLogicVecVal{0b1001, 0b0010},
                      SvLogicVecVal{});

  EXPECT_EQ(run.seen.bval, 0b0010U);
  EXPECT_EQ(run.seen.aval, 0b1001U);
}

TEST(DpiArgumentPassingInADesign, AnOutputFormalsUnknownBitReachesTheActual) {
  FourStateActual run(Direction::kOutput, SvLogicVecVal{},
                      SvLogicVecVal{0b0110, 0b0100});

  EXPECT_EQ(run.Actual().aval, 0b0110U);
  EXPECT_EQ(run.Actual().bval, 0b0100U);
}

struct TwoStateFormal {
  DpiRuntime dpi;
  SimFixture f;
  DpiArgValue seen;

  TwoStateFormal(DataTypeKind formal, SvLogicVecVal actual) {
    DpiRtFunction func;
    func.c_name = "c_take_two_state";
    func.sv_name = "take2";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"a", formal, Direction::kInput}};
    auto* seen_slot = &seen;
    func.arg_impl = [seen_slot](std::vector<DpiArgValue>& args) -> DpiArgValue {
      *seen_slot = args[0];
      return DpiArgValue::FromInt(0);
    };
    dpi.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&dpi);
    auto* var = f.ctx.CreateVariable("a", 4);
    var->value = MakeLogic4Vec(f.arena, 4);
    var->value.words[0] = Logic4Word{actual.aval, actual.bval};
    EvalFunctionCall(ParseExprFrom("take2(a)", f), f.ctx, f.arena);
  }
};

TEST(DpiArgumentPassingInADesign, AnUnknownBitOfATwoStateFormalArrivesAsZero) {
  TwoStateFormal run(DataTypeKind::kInt, SvLogicVecVal{0b1011, 0b0010});

  EXPECT_EQ(run.seen.AsInt(), 9);
}

TEST(DpiArgumentPassingInADesign, AnUnknownBitOfARealFormalArrivesAsZero) {
  TwoStateFormal run(DataTypeKind::kReal, SvLogicVecVal{0b1101, 0b0100});

  EXPECT_DOUBLE_EQ(run.seen.AsReal(), 9.0);
}

TEST(DpiArgumentPassingInADesign, AnUnknownBitOfABitFormalArrivesAsZero) {
  TwoStateFormal run(DataTypeKind::kBit, SvLogicVecVal{1, 1});

  EXPECT_EQ(run.seen.AsBit(), 0);
}

TEST(DpiArgumentPassingInADesign,
     TheKnownBitsOfAFourStateActualArriveUntouched) {
  TwoStateFormal run(DataTypeKind::kInt, SvLogicVecVal{0b1101, 0});

  EXPECT_EQ(run.seen.AsInt(), 13);
}

}  // namespace
