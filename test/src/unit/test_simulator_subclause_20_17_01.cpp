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

}  // namespace
