#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

} // namespace

// =============================================================================
// §10.3 Continuous assignments — elaboration
// =============================================================================

TEST(ElabClause1003, MultipleContAssigns) {
  ElabFixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  wire a, b, c, d;\n"
                              "  assign a = b, c = d;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 2u);
}

TEST(ElabClause1003, ContAssignDelayPreserved) {
  ElabFixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  wire a, b;\n"
                              "  assign #10 a = b;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].delay, nullptr);
}

TEST(ElabClause1003, ContAssignDelayRiseFall) {
  ElabFixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  wire a, b;\n"
                              "  assign #(5, 10) a = b;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_EQ(mod->assigns[0].delay_decay, nullptr);
}

TEST(ElabClause1003, ContAssignDelayThreeValues) {
  ElabFixture f;
  auto *design = ElaborateSrc("module m;\n"
                              "  wire a, b;\n"
                              "  assign #(5, 10, 15) a = b;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->assigns.size(), 1u);
  EXPECT_NE(mod->assigns[0].delay, nullptr);
  EXPECT_NE(mod->assigns[0].delay_fall, nullptr);
  EXPECT_NE(mod->assigns[0].delay_decay, nullptr);
}

// =============================================================================
// §10.3.4 Drive strength — validation
// =============================================================================

TEST(ElabClause1003, Validate_IllegalDriveStrengthHighz0Highz1) {
  ElabFixture f;
  ElaborateSrc("module m;\n"
               "  wire w;\n"
               "  assign (highz0, highz1) w = 1'b0;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1003, Validate_IllegalDriveStrengthHighz1Highz0) {
  ElabFixture f;
  ElaborateSrc("module m;\n"
               "  wire w;\n"
               "  assign (highz1, highz0) w = 1'b0;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabClause1003, Validate_LegalDriveStrengthHighz0Strong1) {
  ElabFixture f;
  ElaborateSrc("module m;\n"
               "  wire w;\n"
               "  assign (highz0, strong1) w = 1'b0;\n"
               "endmodule\n",
               f);
  EXPECT_FALSE(f.diag.HasErrors());
}
