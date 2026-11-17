#include <gtest/gtest.h>

#include <cstdint>
#include <filesystem>
#include <string>
#include <string_view>
#include <system_error>

#include "fixture_simulator.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

uint64_t RunAndRead(SimFixture& f, const std::string& src,
                    std::string_view var) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* v = f.ctx.FindVariable(var);
  EXPECT_NE(v, nullptr);
  return v ? v->value.ToUint64() : 0;
}

void RunSrc(SimFixture& f, const std::string& src) {
  auto* design = ElaborateSrc(src, f);
  EXPECT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
}

TEST(SystemTask, FunctionReportsCommandFailure) {
  SimFixture f;
  uint64_t r = RunAndRead(f,
                          "module t;\n"
                          "  int r;\n"
                          "  initial r = $system(\"exit 1\");\n"
                          "endmodule\n",
                          "r");
  EXPECT_NE(r, 0u);
}

TEST(SystemTask, SuccessReturnsZeroAsExpressionOperand) {
  SimFixture f;
  uint64_t r = RunAndRead(f,
                          "module t;\n"
                          "  int r;\n"
                          "  initial begin\n"
                          "    if ($system(\"exit 0\") == 0) r = 42;\n"
                          "    else r = 7;\n"
                          "  end\n"
                          "endmodule\n",
                          "r");
  EXPECT_EQ(r, 42u);
}

TEST(SystemTask, TaskExecutesCommandFromTerminal) {
  namespace fs = std::filesystem;
  fs::path marker =
      fs::temp_directory_path() / "deltahdl_subclause_20_17_01.marker";
  std::error_code ec;
  fs::remove(marker, ec);

  SimFixture f;
  RunSrc(f,
         "module t;\n"
         "  initial $system(\"touch '" +
             marker.string() +
             "'\");\n"
             "endmodule\n");

  EXPECT_TRUE(fs::exists(marker));
  fs::remove(marker, ec);
}

TEST(SystemTask, NoArgumentInvokesSystemWithNullString) {
  SimFixture f;
  uint64_t r = RunAndRead(f,
                          "module t;\n"
                          "  int r;\n"
                          "  initial r = $system();\n"
                          "endmodule\n",
                          "r");
  EXPECT_NE(r, 0u);
}

TEST(SystemTask, ExitOneYieldsTheRawWaitStatus) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial $display(\"%0d\", $system(\"exit 1\"));\n"
                       "endmodule\n",
                       f),
            "256\n");
}

TEST(SystemTask, TheResultIs32BitsWide) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  initial $display(\"%0d\", $bits($system(\"true\")));\n"
                 "endmodule\n",
                 f),
      "32\n");
}

TEST(SystemTask, TheResultIsSigned) {
  SimFixture f;
  EXPECT_EQ(RunCapture(
                "module t;\n"
                "  initial $display(\"%0d\", $system(\"exit 1\") - 1000 < 0);\n"
                "endmodule\n",
                f),
            "1\n");
}

TEST(SystemTask, DISABLED_TheResultTypeIsInt) {
  SimFixture f;
  EXPECT_EQ(
      RunCapture("module t;\n"
                 "  initial $display(\"%s\", $typename($system(\"true\")));\n"
                 "endmodule\n",
                 f),
      "int\n");
}

TEST(SystemTask, TheTaskFormWithNoArgumentRuns) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  initial begin\n"
                       "    $system();\n"
                       "    $display(\"after\");\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "after\n");
}

TEST(SystemTask, BothFormsRunInAClassMethod) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    static function int run(string s);\n"
                       "      $system(\"exit 0\");\n"
                       "      return $system(\"exit 2\");\n"
                       "    endfunction\n"
                       "  endclass\n"
                       "  initial $display(\"%0d\", C::run(\"\"));\n"
                       "endmodule\n",
                       f),
            "512\n");
}

TEST(SystemTask, BothFormsRunInAPackageFunction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package pk;\n"
                       "  function int run();\n"
                       "    $system(\"exit 0\");\n"
                       "    return $system(\"exit 2\");\n"
                       "  endfunction\n"
                       "endpackage\n"
                       "module t;\n"
                       "  initial $display(\"%0d\", pk::run());\n"
                       "endmodule\n",
                       f),
            "512\n");
}

TEST(SystemTask, BothFormsRunInAProgramBlock) {
  SimFixture f;
  EXPECT_EQ(RunCapture("program p;\n"
                       "  initial begin\n"
                       "    $system(\"exit 0\");\n"
                       "    $display(\"%0d\", $system(\"exit 2\"));\n"
                       "  end\n"
                       "endprogram\n"
                       "module t;\n"
                       "  p u();\n"
                       "endmodule\n",
                       f),
            "512\n");
}

TEST(SystemTask, BothFormsRunInAnInterfaceFunction) {
  SimFixture f;
  EXPECT_EQ(RunCapture("interface i;\n"
                       "  function int run();\n"
                       "    $system(\"exit 0\");\n"
                       "    return $system(\"exit 2\");\n"
                       "  endfunction\n"
                       "endinterface\n"
                       "module t;\n"
                       "  i u();\n"
                       "  initial $display(\"%0d\", u.run());\n"
                       "endmodule\n",
                       f),
            "512\n");
}

}  // namespace
