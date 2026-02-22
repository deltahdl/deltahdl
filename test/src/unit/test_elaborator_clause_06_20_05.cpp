// §6.20.5: Specify parameters

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

// --- §6.20.5: Specparam restriction ---
TEST(Elaboration, SpecparamInParam_Error) {
  ElabFixture f;
  ElaborateSrc("module top();\n"
               "  specparam delay = 50;\n"
               "  parameter p = delay + 2;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

} // namespace
