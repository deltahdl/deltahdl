#include <cstdint>
#include <vector>

#include "fixture_simulator.h"
#include "parser/ast.h"
#include "simulator/dpi_runtime.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

// §35.7: the exports a registry answers for are the ones some declaration
// gave it. DpiRuntime.RegisterExportAndCall below makes the positive claim --
// a registered name is found and its body runs; this one makes the negative,
// which no other case states: a name no export declaration gave is not an
// export of the design, however many others were registered.
TEST(DpiRuntime, HasExportIsFalseForAnUndeclaredName) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  rt.RegisterExport(exp);

  EXPECT_FALSE(rt.HasExport("missing"));
}

TEST(DpiRuntime, RegisterExportAndCall) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  exp.impl = [](const std::vector<DpiArgValue>& args) -> DpiArgValue {
    return DpiArgValue::FromInt(args[0].AsInt() * 2);
  };
  rt.RegisterExport(exp);

  EXPECT_EQ(rt.ExportCount(), 1u);
  EXPECT_TRUE(rt.HasExport("sv_callback"));

  auto result = rt.CallExport("sv_callback", {DpiArgValue::FromInt(21)});
  EXPECT_EQ(result.AsInt(), 42);
}

TEST(DpiRuntime, CallMissingExportReturnsZero) {
  DpiRuntime rt;
  auto result = rt.CallExport("nonexistent", {});
  EXPECT_EQ(result.AsInt(), 0);
}

// §35.7: every export declaration designates a context function. The runtime
// records that property unconditionally at registration, so a caller that
// passes is_context=false still ends up with a context export.
TEST(DpiRuntime, RegisteredExportIsAlwaysContext) {
  DpiRuntime rt;
  DpiRtExport exp;
  exp.c_name = "c_callback";
  exp.sv_name = "sv_callback";
  exp.is_context = false;
  rt.RegisterExport(exp);

  const auto* stored = rt.FindExport("sv_callback");
  ASSERT_NE(stored, nullptr);
  EXPECT_TRUE(stored->is_context);
}

// §35.7: "Declaring a SystemVerilog function to be exported does not change its
// semantics or behavior from the SystemVerilog perspective; there is no effect
// on SystemVerilog usage other than making it possible for foreign language
// tasks and functions in a DPI call-chain to call the exported function." So a
// SystemVerilog call to an exported function returns what the function returns,
// exactly as it would without the export declaration.
TEST(DpiExportedFunctionInADesign, ACallToAnExportedFunctionReturnsItsResult) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function int five();\n"
      "    return 5;\n"
      "  endfunction\n"
      "  export \"DPI-C\" function five;\n"
      "  initial x = five();\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 5u);
}

// The same rule holds of the arguments a call passes: exporting the function
// leaves the actual reaching the formal and the result computed from it. Five
// is what the case above returns from a body that reads nothing, so this one
// varies the actual to keep the answer out of the body.
TEST(DpiExportedFunctionInADesign, AnExportedFunctionStillReadsItsArguments) {
  SimFixture f;
  auto* var = RunAndFindVar(
      "module t;\n"
      "  int x;\n"
      "  function int twice(input int v);\n"
      "    return v + v;\n"
      "  endfunction\n"
      "  export \"DPI-C\" function twice;\n"
      "  initial x = twice(21);\n"
      "endmodule\n",
      f, "x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 42u);
}

}  // namespace
