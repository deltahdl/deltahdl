#include "fixture_simulator.h"

using namespace delta;

namespace {

TEST(PackageImportInHeaderSim, ConstantFromHeaderImportSetsValue) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 42;\n"
      "endpackage\n"
      "module t import pkg::VAL; ();\n"
      "  logic [7:0] x;\n"
      "  initial x = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("x")->value.ToUint64(), 42u);
}

TEST(PackageImportInHeaderSim, WildcardConstantFromHeaderImport) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "package pkg;\n"
      "  parameter int VAL = 7;\n"
      "endpackage\n"
      "module t import pkg::*; ();\n"
      "  logic [7:0] y;\n"
      "  initial y = VAL;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  LowerAndRun(design, f);
  EXPECT_EQ(f.ctx.FindVariable("y")->value.ToUint64(), 7u);
}

}  // namespace
