// §17.3: Checker instantiation

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

static RtlirDesign *ElaborateSource(const std::string &src,
                                    CheckerElabFixture &f,
                                    std::string_view top_name) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(top_name);
}

namespace {

TEST(CheckerElab, CheckerInstantiatedFromModule) {
  CheckerElabFixture f;
  auto *design = ElaborateSource(
      "checker sub_chk(input logic a);\n"
      "endchecker\n"
      "module top;\n"
      "  logic sig;\n"
      "  sub_chk u0(.a(sig));\n"
      "endmodule\n",
      f, "top");
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->children.size(), 1u);
  EXPECT_NE(mod->children[0].resolved, nullptr);
  EXPECT_EQ(mod->children[0].resolved->name, "sub_chk");
}

}  // namespace
