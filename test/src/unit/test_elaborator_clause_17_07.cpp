// §17.7: Checker variables

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

struct CheckerElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSource(const std::string& src,
                                    CheckerElabFixture& f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

namespace {

TEST(CheckerElab, ElaborateCheckerWithVars) {
  CheckerElabFixture f;
  auto* design = ElaborateSource(
      "checker my_chk;\n"
      "  logic [7:0] count;\n"
      "  assign count = 8'hFF;\n"
      "endchecker\n",
      f, "my_chk");
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  EXPECT_EQ(mod->name, "my_chk");
  EXPECT_FALSE(mod->variables.empty());
  EXPECT_FALSE(mod->assigns.empty());
}

}  // namespace
