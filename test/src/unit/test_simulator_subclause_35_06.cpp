#include <utility>
#include <vector>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §35.6 — Calling imported functions: the usage and syntax for calling an
// imported function is identical to a native SystemVerilog function call.
// In particular, arguments backed by defaults can be omitted and arguments can
// be bound by name. The simulator resolves a DPI call's actuals against the
// import's declared formals so these mechanisms behave as they do natively.

// Registers an imported function `sv_probe(a, b = 99)` whose body encodes the
// values it received in formal order: a * 1000 + b.
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

// C1/C2: a plain positional call binds actuals to formals in order, just like a
// native call.
TEST(DpiCallArgumentBinding, PositionalCallBindsInOrder) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(2, 8)", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 2008u);  // a == 2, b == 8
}

// C4: when every actual is bound by name, the simulator routes each to the
// matching formal regardless of the written order.
TEST(DpiCallArgumentBinding, NamedArgumentsBindToMatchingFormals) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(.b(7), .a(3))", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 3007u);  // a == 3, b == 7 despite reversed call order
}

// C3: an argument with a default value can be omitted from the call; the
// declared default is supplied for the missing formal.
TEST(DpiCallArgumentBinding, OmittedArgumentUsesDefault) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(5)", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 5099u);  // a == 5, b defaults to 99
}

// C3 + C4 together: a leading positional actual followed by a trailing named
// actual binds correctly (edge case mixing both forms).
TEST(DpiCallArgumentBinding, MixedPositionalAndNamedBinding) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(4, .b(6))", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 4006u);  // a == 4 positional, b == 6 by name
}

// C3 + C4 edge: a named-only call that binds one formal by name and omits the
// other entirely; the omitted formal has a default, so the default is supplied.
TEST(DpiCallArgumentBinding, NamedBindingOmittingDefaultedFormal) {
  SimFixture f;
  DpiRuntime dpi;
  RegisterProbe(dpi, f);
  f.ctx.SetDpiRuntime(&dpi);

  auto* call = ParseExprFrom("sv_probe(.a(3))", f);
  auto result = EvalFunctionCall(call, f.ctx, f.arena).ToUint64();
  EXPECT_EQ(result, 3099u);  // a == 3 by name, b omitted -> default 99
}

}  // namespace
