#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

TEST(PackageImportSim, WildcardImportParameter) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 99;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  logic [7:0] x;\n"
      "  initial x = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 99u);
}

TEST(PackageScopeReferenceSim, PackageScopeParamResolves) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int WIDTH = 16;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial y = pkg::WIDTH;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 16u);
}

// §26.3: a wildcard import brings a package's enumeration literals into the
// importing scope. Drive one through the full pipeline and observe that the
// unqualified literal reference evaluates to its ordinal value at run time.
TEST(PackageImportSim, WildcardImportEnumLiteralEvaluates) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  typedef enum { LOW, MID, HIGH } level_t;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::*;\n"
      "  level_t sel;\n"
      "  logic [31:0] y;\n"
      "  initial begin\n"
      "    sel = HIGH;\n"
      "    y = sel;\n"
      "  end\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 2u);
}

TEST(PackageImportSim, ExplicitImportParameter) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  parameter int VAL = 77;\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::VAL;\n"
      "  logic [31:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 77u);
}

// §26.3: the package scope resolution operator resolves a package localparam at
// run time, just as it does a parameter. A localparam takes a different
// constant form (§11.2.1) than a parameter, so observe its value end to end.
TEST(PackageScopeReferenceSim, PackageScopeLocalparamResolves) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  localparam int W = 24;\n"
      "endpackage\n"
      "module t;\n"
      "  logic [31:0] y;\n"
      "  initial y = pkg::W;\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 24u);
}

// §26.3: an explicit import brings a package function into the importing scope
// so it can be called with an unqualified name. Drive the imported call through
// the full pipeline and observe its returned value at run time.
TEST(PackageImportSim, ExplicitImportFunctionCalledUnqualified) {
  auto val = RunAndGet(
      "package pkg;\n"
      "  function automatic int scale(int a);\n"
      "    return a * 5;\n"
      "  endfunction\n"
      "endpackage\n"
      "module t;\n"
      "  import pkg::scale;\n"
      "  logic [31:0] y;\n"
      "  initial y = scale(4);\n"
      "endmodule\n",
      "y");
  EXPECT_EQ(val, 20u);
}

}  // namespace
