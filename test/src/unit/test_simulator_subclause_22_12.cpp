#include <gtest/gtest.h>

#include <string>

#include "common/source_mgr.h"
#include "elaborator/elaborator.h"
#include "elaborator/rtlir.h"
#include "fixture_simulator.h"
#include "fixture_vpi_run.h"
#include "helpers_preprocess_and_get.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"
#include "simulator/vpi_user.h"

TEST(LineDirectiveSimulation, OverriddenLineNumberReachesSimulatedValue) {
  auto result = PreprocessAndGet(
      "module t;\n"
      "  int result;\n"
      "  `line 800 \"renamed.sv\" 0\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 800u);
}

TEST(LineDirectiveSimulation, OverrideBetweenModulesRenumbersFollowingLines) {
  auto result = PreprocessAndGet(
      "module m1;\n"
      "  int unused;\n"
      "  initial unused = 8'd10;\n"
      "endmodule\n"
      "`line 500 \"switched.sv\" 0\n"
      "module t;\n"
      "  int result;\n"
      "  initial result = `__LINE__;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(result, 502u);
}

namespace delta {
namespace {

class LineDirectiveVpi : public VpiDesignRun {
 protected:
  void RunPreprocessed(const std::string& src) {
    Preprocessor pp(f_.mgr, f_.diag, {});
    auto out = pp.Preprocess(f_.mgr.AddFile("real.sv", src));
    auto fid =
        f_.mgr.AddPreprocessedFile("<preprocessed>", out, pp.LineOrigins());
    Lexer lexer(f_.mgr.FileContent(fid), fid, f_.diag,
                TextOrigin::kPreprocessorOutput);
    Parser parser(lexer, f_.arena, f_.diag);
    Elaborator elab(f_.arena, f_.diag, parser.Parse());
    RtlirDesign* design = elab.Elaborate("t");
    ASSERT_NE(design, nullptr);
    ASSERT_FALSE(f_.diag.HasErrors());
    LowerAndRun(design, f_);
  }
};

constexpr const char* kDeclarationsBelowALine =
    "module t;\n"
    "`line 40 \"named.sv\" 0\n"
    "  wire w;\n"
    "  logic r;\n"
    "endmodule\n";

TEST_F(LineDirectiveVpi, ADeclarationReportsTheLineTheDirectiveSet) {
  RunPreprocessed(kDeclarationsBelowALine);
  EXPECT_EQ(vpi_get(vpiLineNo, By("t.w")), 40);
  EXPECT_EQ(vpi_get(vpiLineNo, By("t.r")), 41);
}

TEST_F(LineDirectiveVpi, ADeclarationReportsTheFileTheDirectiveSet) {
  RunPreprocessed(kDeclarationsBelowALine);
  const char* net_file = vpi_get_str(vpiFile, By("t.w"));
  ASSERT_NE(net_file, nullptr);
  EXPECT_STREQ(net_file, "named.sv");
  const char* var_file = vpi_get_str(vpiFile, By("t.r"));
  ASSERT_NE(var_file, nullptr);
  EXPECT_STREQ(var_file, "named.sv");
}

constexpr const char* kDefinitionBelowALine =
    "module t;\n"
    "  sub s();\n"
    "endmodule\n"
    "`line 60 \"defs.sv\" 0\n"
    "\n"
    "module sub;\n"
    "endmodule\n";

TEST_F(LineDirectiveVpi, AnInstanceReportsTheDefinitionLineTheDirectiveSet) {
  RunPreprocessed(kDefinitionBelowALine);
  EXPECT_EQ(vpi_get(vpiDefLineNo, By("t.s")), 61);
}

TEST_F(LineDirectiveVpi, AnInstanceReportsTheDefinitionFileTheDirectiveSet) {
  RunPreprocessed(kDefinitionBelowALine);
  const char* file = vpi_get_str(vpiDefFile, By("t.s"));
  ASSERT_NE(file, nullptr);
  EXPECT_STREQ(file, "defs.sv");
}

}  // namespace
}  // namespace delta
