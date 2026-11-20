#include <gtest/gtest.h>

#include <cstdint>
#include <map>
#include <string>
#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "helpers_dpi_c_binding.h"
#include "parser/ast_type.h"
#include "simulator/dpi_arg_value.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

static void RegisterProbe(DpiRuntime& dpi, SimFixture& f) {
  DpiRtFunction fn;
  fn.c_name = "c_probe";
  fn.sv_name = "sv_probe";
  fn.return_type = DataTypeKind::kInt;

  DpiArg a;
  a.name = "a";
  DpiArg b;
  b.name = "b";
  b.default_value = ParseExprFrom("99", f);
  fn.args = {a, b};

  fn.impl = [](const std::vector<DpiArgValue>& v) -> DpiArgValue {
    return DpiArgValue::FromInt(v[0].AsInt() * 1000 + v[1].AsInt());
  };
  dpi.RegisterImport(std::move(fn));
}

TEST(DpiCallArgumentBinding, PositionalCallBindsInOrder) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(2, 8)", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 2008u);
}

TEST(DpiCallArgumentBinding, NamedArgumentsBindToMatchingFormals) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(.b(7), .a(3))", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 3007u);
}

TEST(DpiCallArgumentBinding, OmittedArgumentUsesDefault) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(5)", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 5099u);
}

TEST(DpiCallArgumentBinding, MixedPositionalAndNamedBinding) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(4, .b(6))", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 4006u);
}

TEST(DpiCallArgumentBinding, NamedBindingOmittingDefaultedFormal) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(.a(3))", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 3099u);
}

int Combine(int a, int b) { return a * 1000 + b; }

int32_t CombineResult(const char* decl_tail, const char* body) {
  return IntVariableAfterRun(
      std::string("module top;\n"
                  "  import \"DPI-C\" function int c_combine("
                  "input int a, input int b") +
          decl_tail +
          ");\n"
          "  int v = 3;\n"
          "  int r;\n" +
          body + "endmodule\n",
      {{"c_combine", reinterpret_cast<void*>(&Combine)}},
      "subclause_35_06_calls", "r");
}

TEST(DpiImportCallInADesign, AnOmittedDefaultedArgumentReachesTheImport) {
  EXPECT_EQ(CombineResult(" = 99", "  initial r = c_combine(4);\n"), 4099);
}

TEST(DpiImportCallInADesign, NamedArgumentsBindOutOfOrder) {
  EXPECT_EQ(CombineResult("", "  initial r = c_combine(.b(2), .a(7));\n"),
            7002);
}

TEST(DpiImportCallInADesign, ANamedCallMayOmitADefaultedArgument) {
  EXPECT_EQ(CombineResult(" = 99", "  initial r = c_combine(.a(5));\n"), 5099);
}

TEST(DpiImportCallInADesign, AnImportServesInAContinuousAssignment) {
  EXPECT_EQ(CombineResult("",
                          "  wire integer w;\n"
                          "  assign w = c_combine(v, 1);\n"
                          "  initial #1 r = w;\n"),
            3001);
}

TEST(DpiImportCallInADesign, TwoCallsServeAsOperandsOfOneExpression) {
  EXPECT_EQ(
      CombineResult("", "  initial r = c_combine(1, 2) + c_combine(v, 4);\n"),
      4006);
}

int32_t CombineThroughAnInstance(const std::string& keyword) {
  return IntVariableAfterRun(
      keyword +
          " holder;\n"
          "  import \"DPI-C\" function int c_combine(input int a, "
          "input int b);\n"
          "end" +
          keyword +
          "\n"
          "module top;\n"
          "  holder u();\n"
          "  int r;\n"
          "  initial r = u.c_combine(6, 7);\n"
          "endmodule\n",
      {{"c_combine", reinterpret_cast<void*>(&Combine)}},
      "subclause_35_06_hierarchical_" + keyword, "r");
}

TEST(DpiImportCallInADesign,
     DISABLED_AnInterfaceInstancesImportIsCalledThroughItsName) {
  EXPECT_EQ(CombineThroughAnInstance("interface"), 6007);
}

TEST(DpiImportCallInADesign,
     DISABLED_AModuleInstancesImportIsCalledThroughItsName) {
  EXPECT_EQ(CombineThroughAnInstance("module"), 6007);
}

}  // namespace
