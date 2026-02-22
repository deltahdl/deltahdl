// §17.2: Checker declaration

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"
#include <gtest/gtest.h>
#include <string>

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

TEST(CheckerElab, ElaborateCheckerWithPorts) {
  CheckerElabFixture f;
  auto *design =
      ElaborateSource("checker chk_ports(input logic clk, input logic rst);\n"
                      "endchecker\n",
                      f, "chk_ports");
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->ports.size(), 2u);
  EXPECT_EQ(mod->ports[0].name, "clk");
  EXPECT_EQ(mod->ports[1].name, "rst");
}

} // namespace
