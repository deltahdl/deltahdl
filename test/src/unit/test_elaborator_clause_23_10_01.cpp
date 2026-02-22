// §23.10.1: defparam statement

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "elaboration/sensitivity.h"
#include "elaboration/type_eval.h"
#include "lexer/lexer.h"
#include "lexer/token.h"
#include "parser/parser.h"
#include <gtest/gtest.h>

using namespace delta;

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

namespace {

// --- Defparam tests ---
TEST(Elaboration, Defparam_OverridesDefault) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child #(parameter WIDTH = 4)();\n"
                              "endmodule\n"
                              "module top;\n"
                              "  child u0();\n"
                              "  defparam u0.WIDTH = 16;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1);
  auto *child = mod->children[0].resolved;
  ASSERT_NE(child, nullptr);
  ASSERT_EQ(child->params.size(), 1);
}

TEST(Elaboration, Defparam_OverridesDefault_Value) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child #(parameter WIDTH = 4)();\n"
                              "endmodule\n"
                              "module top;\n"
                              "  child u0();\n"
                              "  defparam u0.WIDTH = 16;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  auto *child = design->top_modules[0]->children[0].resolved;
  EXPECT_EQ(child->params[0].resolved_value, 16);
  EXPECT_TRUE(child->params[0].is_resolved);
}

TEST(Elaboration, Defparam_NotFoundWarns) {
  ElabFixture f;
  auto *design = ElaborateSrc("module child #(parameter WIDTH = 4)();\n"
                              "endmodule\n"
                              "module top;\n"
                              "  child u0();\n"
                              "  defparam u0.BOGUS = 99;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

} // namespace
