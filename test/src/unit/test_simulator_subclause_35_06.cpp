#include <gtest/gtest.h>

#include <utility>
#include <vector>

#include "fixture_simulator.h"
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

}  // namespace
