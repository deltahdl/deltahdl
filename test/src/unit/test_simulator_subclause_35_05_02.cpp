#include <gtest/gtest.h>

#include <cstdint>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"
#include "simulator/sim_context.h"

using namespace delta;

namespace {

TEST(PureDpiImportRegistry, PureFlagSurvivesRegistration) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_p";
  func.sv_name = "sv_p";
  func.return_type = DataTypeKind::kInt;
  func.is_pure = true;
  rt.RegisterImport(std::move(func));

  const auto* found = rt.FindImport("sv_p");
  ASSERT_NE(found, nullptr);
  EXPECT_TRUE(found->is_pure);
}

TEST(PureDpiImportRegistry, NonPureImportDistinguishable) {
  DpiRuntime rt;
  DpiRtFunction func;
  func.c_name = "c_n";
  func.sv_name = "sv_n";
  func.return_type = DataTypeKind::kInt;
  rt.RegisterImport(std::move(func));

  const auto* found = rt.FindImport("sv_n");
  ASSERT_NE(found, nullptr);
  EXPECT_FALSE(found->is_pure);
}

struct CountingPureEntries {
  DpiRuntime rt;
  int entries = 0;

  explicit CountingPureEntries(bool is_pure) {
    DpiRtFunction func;
    func.c_name = "c_square";
    func.sv_name = "square";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"x", DataTypeKind::kInt, Direction::kInput}};
    func.is_pure = is_pure;
    func.impl = [this](const std::vector<DpiArgValue>& a) {
      ++entries;
      return DpiArgValue::FromInt(a[0].AsInt() * a[0].AsInt());
    };
    rt.RegisterImport(std::move(func));
  }

  int Squaring(int x) {
    return rt.CallImportReusingPureResult("square", {DpiArgValue::FromInt(x)})
        .AsInt();
  }
};

TEST(PureDpiCallRemoval, APureImportsCallIsRemovable) {
  CountingPureEntries declared(true);
  EXPECT_TRUE(declared.rt.ImportCallIsRemovable("square"));
}

TEST(PureDpiCallRemoval, AnImportWithoutThePropertyIsNotRemovable) {
  CountingPureEntries declared(false);
  EXPECT_FALSE(declared.rt.ImportCallIsRemovable("square"));
}

TEST(PureDpiCallRemoval, AnUndeclaredNamesCallIsNotRemovable) {
  CountingPureEntries declared(true);
  EXPECT_FALSE(declared.rt.ImportCallIsRemovable("cube"));
}

TEST(PureDpiCallRemoval, TheSecondPureCallOnOneValueIsNotComputed) {
  CountingPureEntries declared(true);
  declared.Squaring(7);
  declared.Squaring(7);
  EXPECT_EQ(declared.entries, 1);
}

TEST(PureDpiCallRemoval, TheReusedValueIsWhatTheFirstCallComputed) {
  CountingPureEntries declared(true);
  EXPECT_EQ(declared.Squaring(7), declared.Squaring(7));
}

TEST(PureDpiCallRemoval, ADifferentValueIsComputedAfresh) {
  CountingPureEntries declared(true);
  declared.Squaring(7);
  EXPECT_EQ(declared.Squaring(8), 64);
}

TEST(PureDpiCallRemoval, AValueSeenBeforeIsStillReusedAfterAnother) {
  CountingPureEntries declared(true);
  declared.Squaring(7);
  declared.Squaring(8);
  declared.Squaring(7);
  EXPECT_EQ(declared.entries, 2);
}

TEST(PureDpiCallRemoval, AnImportWithoutThePropertyIsEnteredEveryTime) {
  CountingPureEntries declared(false);
  declared.Squaring(7);
  declared.Squaring(7);
  EXPECT_EQ(declared.entries, 2);
}

TEST(PureDpiCallRemoval, AnOrdinaryCallIsMadeAfterAReusableOneWasAnswered) {
  CountingPureEntries declared(true);
  declared.Squaring(7);
  declared.rt.CallImport("square", {DpiArgValue::FromInt(7)});
  EXPECT_EQ(declared.entries, 2);
}

struct CallingASquaringImportTwice {
  DpiRuntime rt;
  SimFixture f;
  int entries = 0;
  uint64_t first = 0;
  uint64_t second = 0;

  CallingASquaringImportTwice(bool is_pure, int actual) {
    DpiRtFunction func;
    func.c_name = "c_square";
    func.sv_name = "square";
    func.return_type = DataTypeKind::kInt;
    func.args = {DpiArg{"v", DataTypeKind::kInt, Direction::kInput}};
    func.is_pure = is_pure;
    int* entries_slot = &entries;
    func.impl = [entries_slot](const std::vector<DpiArgValue>& a) {
      ++*entries_slot;
      return DpiArgValue::FromInt(a[0].AsInt() * a[0].AsInt());
    };
    rt.RegisterImport(std::move(func));
    f.ctx.SetDpiRuntime(&rt);
    const Expr* call =
        ParseExprFrom("square(" + std::to_string(actual) + ")", f);
    first = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
    second = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  }
};

TEST(DpiPureCallInADesign, ASecondCallOnEqualInputsReusesTheFirstResult) {
  CallingASquaringImportTwice run(true, 6);
  EXPECT_EQ(run.entries, 1);
}

TEST(DpiPureCallInADesign, TheReusedResultIsTheValueTheCallWouldCompute) {
  CallingASquaringImportTwice run(true, 6);
  EXPECT_EQ(run.second, 36U);
  EXPECT_EQ(run.first, 36U);
}

TEST(DpiPureCallInADesign, AnImportWithoutThePropertyIsEnteredOnEveryCall) {
  CallingASquaringImportTwice run(false, 6);
  EXPECT_EQ(run.entries, 2);
}

int cube_calls = 0;
int Cube(int a) {
  ++cube_calls;
  return a * a * a;
}

TEST(PureDpiCallRemoval, APureImportBoundToCIsEnteredOncePerInputValue) {
  cube_calls = 0;
  SimFixture f;
  RunWithImportsBound(
      "module t;\n"
      "  import \"DPI-C\" pure function int cube(input int a);\n"
      "  int r;\n"
      "  int s;\n"
      "  int u;\n"
      "  initial begin\n"
      "    r = cube(3);\n"
      "    s = cube(4);\n"
      "    u = cube(3);\n"
      "  end\n"
      "endmodule\n",
      f, {{"cube", reinterpret_cast<void*>(&Cube)}}, "subclause_35_05_02_pure");
  EXPECT_TRUE(f.diag.Diagnostics().empty());
  auto* r = f.ctx.FindVariable("r");
  auto* s = f.ctx.FindVariable("s");
  auto* u = f.ctx.FindVariable("u");
  ASSERT_NE(r, nullptr);
  ASSERT_NE(s, nullptr);
  ASSERT_NE(u, nullptr);
  EXPECT_EQ(r->value.ToUint64(), 27U);
  EXPECT_EQ(s->value.ToUint64(), 64U);
  EXPECT_EQ(u->value.ToUint64(), 27U);
  EXPECT_EQ(cube_calls, 2);
}

}  // namespace
