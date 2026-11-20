#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "fixture_simulator.h"
#include "helpers_reported_error.h"
#include "simulator/vpi_context.h"
#include "simulator/vpi_globals.h"
#include "simulator/vpi_internal.h"
#include "simulator/vpi_user.h"

namespace delta {
namespace {

class SystemFunctionPlaces : public ::testing::Test {
 protected:
  void SetUp() override { SetGlobalVpiContext(&vpi_ctx_); }
  void TearDown() override { SetGlobalVpiContext(nullptr); }

  VpiContext vpi_ctx_;
};

int g_function_calls = 0;

PLI_INT32 ReturnThirtySeven(PLI_BYTE8*) {
  ++g_function_calls;
  s_vpi_value value = {};
  value.format = vpiIntVal;
  value.value.integer = 37;
  vpi_put_value(vpi_handle(vpiSysTfCall, nullptr), &value, nullptr, vpiNoDelay);
  return 0;
}

void RunWithTheFunction(const std::string& src, SimFixture& f) {
  g_function_calls = 0;
  s_vpi_systf_data func = {};
  func.type = vpiSysFunc;
  func.sysfunctype = vpiIntFunc;
  func.tfname = VpiText("$f");
  func.calltf = ReturnThirtySeven;
  ASSERT_NE(vpi_register_systf(&func), nullptr);
  auto* design = ElaborateSrc(src, f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_FALSE(f.diag.HasErrors());
}

uint64_t ROf(const std::string& src) {
  SimFixture f;
  RunWithTheFunction(src, f);
  auto* var = f.ctx.FindVariable("r");
  return var == nullptr ? ~uint64_t{0} : var->value.ToUint64();
}

std::string Module(const std::string& body) {
  return "module m;\n  int r;\n" + body + "endmodule\n";
}

TEST_F(SystemFunctionPlaces, AContinuousAssignmentDrivesTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  wire [31:0] w;\n"
                       "  assign w = $f();\n"
                       "  initial #1 r = w;\n")),
            37U);
}

TEST_F(SystemFunctionPlaces, APortConnectionCarriesTheReturnedValue) {
  EXPECT_EQ(ROf("module sub(input logic [31:0] a); int seen; assign seen = a; "
                "endmodule\n"
                "module m; int r; sub u (.a($f())); initial #1 r = u.seen; "
                "endmodule\n"),
            37U);
}

TEST_F(SystemFunctionPlaces, APrimitiveTerminalTakesTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  wire z;\n"
                       "  and g (z, $f(), 1'b1);\n"
                       "  initial #1 r = z;\n")),
            1U);
}

TEST_F(SystemFunctionPlaces, DISABLED_AClockingEventRunsTheFunction) {
  SimFixture f;
  RunWithTheFunction(Module("  clocking cb @(posedge $f()); endclocking\n"
                            "  initial #1 r = 1;\n"),
                     f);
  EXPECT_GE(g_function_calls, 1);
}

TEST_F(SystemFunctionPlaces, AConstraintUsesTheReturnedValue) {
  EXPECT_EQ(
      ROf(Module("  class C; rand int x; constraint c { x == $f(); } endclass\n"
                 "  C o;\n"
                 "  initial begin o = new; void'(o.randomize()); r = o.x; "
                 "end\n")),
      37U);
}

TEST_F(SystemFunctionPlaces, APackagePropertyUsesTheReturnedValue) {
  EXPECT_EQ(ROf("package pk;\n"
                "  property q(x); x == $f(); endproperty\n"
                "endpackage\n"
                "module m;\n"
                "  int r = 0, k = 37;\n"
                "  logic clk = 0;\n"
                "  assert property (@(posedge clk) pk::q(k)) r = r + 1;\n"
                "  initial #1 clk = 1;\n"
                "endmodule\n"),
            1U);
}

TEST_F(SystemFunctionPlaces, AModportPortExpressionCarriesTheReturnedValue) {
  EXPECT_EQ(ROf("interface ifc;\n"
                "  modport mp (input .i($f()));\n"
                "endinterface\n"
                "module sub(ifc.mp p); int seen; initial seen = p.i; "
                "endmodule\n"
                "module m; int r; ifc u (); sub s (u.mp);\n"
                "  initial #1 r = s.seen;\n"
                "endmodule\n"),
            37U);
}

TEST_F(SystemFunctionPlaces, AnExtendsClauseArgumentIsTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  class B; int n; function new(int v); n = v; "
                       "endfunction endclass\n"
                       "  class E extends B($f()); endclass\n"
                       "  E o;\n"
                       "  initial begin o = new; r = o.n; end\n")),
            37U);
}

TEST_F(SystemFunctionPlaces, AnOperandOfALargerExpressionUsesTheValue) {
  EXPECT_EQ(ROf(Module("  initial r = $f() + 1;\n")), 38U);
}

TEST_F(SystemFunctionPlaces, AnIfConditionUsesTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  initial if ($f() == 37) r = 1; else r = 2;\n")), 1U);
}

TEST_F(SystemFunctionPlaces, AWhileConditionUsesTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  initial while (r < $f()) r = r + 1;\n")), 37U);
}

TEST_F(SystemFunctionPlaces, AForConditionUsesTheReturnedValue) {
  EXPECT_EQ(
      ROf(Module("  initial for (int i = 0; i < $f(); i++) r = r + 1;\n")),
      37U);
}

TEST_F(SystemFunctionPlaces, ARepeatCountUsesTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  initial repeat ($f()) r = r + 1;\n")), 37U);
}

TEST_F(SystemFunctionPlaces, ACaseExpressionUsesTheReturnedValue) {
  EXPECT_EQ(
      ROf(Module("  initial case ($f()) 37: r = 1; default: r = 2; endcase\n")),
      1U);
}

TEST_F(SystemFunctionPlaces, ACaseItemUsesTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  initial case (37) $f(): r = 1; default: r = 2; "
                       "endcase\n")),
            1U);
}

TEST_F(SystemFunctionPlaces, AnArgumentOfASubroutineCallIsTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  function int g(int v); return v * 2; endfunction\n"
                       "  initial r = g($f());\n")),
            74U);
}

TEST_F(SystemFunctionPlaces, AnArgumentOfASystemCallIsTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  initial r = $clog2($f());\n")), 6U);
}

TEST_F(SystemFunctionPlaces, AReturnExpressionInAModuleFunctionIsTheValue) {
  EXPECT_EQ(ROf(Module("  function int g(); return $f(); endfunction\n"
                       "  initial r = g();\n")),
            37U);
}

TEST_F(SystemFunctionPlaces, AClassMethodUsesTheReturnedValue) {
  EXPECT_EQ(
      ROf(Module("  class C; function int k(); return $f() + 1; endfunction\n"
                 "  endclass\n"
                 "  C o;\n"
                 "  initial begin o = new; r = o.k(); end\n")),
      38U);
}

TEST_F(SystemFunctionPlaces, AProgramUsesTheReturnedValue) {
  EXPECT_EQ(ROf("program m;\n"
                "  int r;\n"
                "  initial r = $f();\n"
                "endprogram\n"),
            37U);
}

TEST_F(SystemFunctionPlaces, AnInterfaceUsesTheReturnedValue) {
  EXPECT_EQ(ROf("interface ifc; int v; initial v = $f(); endinterface\n"
                "module m; int r; ifc u (); initial #1 r = u.v; endmodule\n"),
            37U);
}

TEST_F(SystemFunctionPlaces, AGenerateBlocksProcedureUsesTheReturnedValue) {
  EXPECT_EQ(ROf(Module("  if (1) begin : g\n"
                       "    initial r = $f();\n"
                       "  end\n")),
            37U);
}

TEST_F(SystemFunctionPlaces,
       DISABLED_AStatementCallWarnsThatItsValueIsDiscarded) {
  SimFixture f;
  const std::string kSrc = Module("  initial $f();\n");
  RunWithTheFunction(kSrc, f);
  EXPECT_EQ(g_function_calls, 1);
  EXPECT_TRUE(ReportedWarning(f.diag.Diagnostics(),
                              "return value of nonvoid function '$f' is "
                              "discarded",
                              LineHolding(kSrc, "$f"), "13.4.1"));
}

TEST_F(SystemFunctionPlaces, AVoidCastCallIsNotWarnedAbout) {
  SimFixture f;
  RunWithTheFunction(Module("  initial void'($f());\n"), f);
  EXPECT_EQ(g_function_calls, 1);
  for (const auto& diag : f.diag.Diagnostics()) {
    EXPECT_NE(diag.severity, DiagSeverity::kWarning) << diag.message;
  }
}

}  // namespace
}  // namespace delta
