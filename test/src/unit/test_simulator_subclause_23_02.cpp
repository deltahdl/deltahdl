

#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"
#include "helpers_preprocess_and_get.h"
#include "simulator/lowerer.h"

using namespace delta;

namespace {

TEST(ModuleDefinitions, MinimalModuleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc("module m; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

TEST(ModuleDefinitions, MacromoduleSimulates) {
  SimFixture f;
  auto* design = ElaborateSrc("macromodule m; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  EXPECT_FALSE(f.has_errors);
}

std::string RunMacromodule(const std::string& src) {
  SimFixture f;
  return PreprocessAndCapture(src, f);
}

TEST(MacromoduleDefinitions, TakesEveryHeaderAndBodyFormAModuleTakes) {
  EXPECT_EQ(RunMacromodule("macromodule m #(parameter int W = 3)"
                           "(output logic [W-1:0] o);\n"
                           "  assign o = 5;\nendmodule\n"
                           "module t;\n  wire [2:0] y;\n  m u(y);\n"
                           "  initial #1 $display(\"%b\", y);\nendmodule\n"),
            "101\n");
  EXPECT_EQ(RunMacromodule("package pk;\n  localparam int V = 6;\nendpackage\n"
                           "macromodule m import pk::*; (output int o);\n"
                           "  assign o = V;\nendmodule\n"
                           "module t;\n  int y;\n  m u(y);\n"
                           "  initial #1 $display(\"%0d\", y);\nendmodule\n"),
            "6\n");
  EXPECT_EQ(
      RunMacromodule("macromodule m(.*);\n  output int o;\n  assign o = 7;\n"
                     "endmodule\n"
                     "module t;\n  int y;\n  m u(y);\n"
                     "  initial #1 $display(\"%0d\", y);\nendmodule\n"),
      "7\n");
  EXPECT_EQ(RunMacromodule(
                "(* keep *) macromodule m(output int o);\n  assign o = 8;\n"
                "endmodule : m\n"
                "module t;\n  int y;\n  m u(y);\n"
                "  initial #1 $display(\"%0d\", y);\nendmodule\n"),
            "8\n");
  EXPECT_EQ(
      RunMacromodule("macromodule leaf(output int o);\n  assign o = 4;\n"
                     "endmodule\n"
                     "macromodule m(output int o);\n  leaf l(o);\nendmodule\n"
                     "module t;\n  int y;\n  m u(y);\n"
                     "  initial #1 $display(\"%0d\", y);\nendmodule\n"),
      "4\n");
  EXPECT_EQ(RunMacromodule("module t;\n"
                           "  macromodule n(output int o);\n    assign o = 2;\n"
                           "  endmodule\n"
                           "  int y;\n  n u(y);\n"
                           "  initial #1 $display(\"%0d\", y);\nendmodule\n"),
            "2\n");
}

}  // namespace
