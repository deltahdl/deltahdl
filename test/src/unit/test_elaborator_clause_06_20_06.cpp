// §6.20.6: Const constants

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

// --- §6.20.6: Const constants ---
TEST(Elaboration, ConstVarNoInit_Error) {
  // const variable without initializer is an error.
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  const int x;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ConstVarWithInit_OK) {
  // const variable with initializer is fine.
  ElabFixture f;
  auto *design = ElaborateSrc("module top;\n"
                              "  const int x = 42;\n"
                              "endmodule\n",
                              f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, ConstVarReassign_Error) {
  // Assignment to const variable is an error.
  ElabFixture f;
  ElaborateSrc("module top;\n"
               "  const int x = 5;\n"
               "  initial x = 10;\n"
               "endmodule\n",
               f);
  EXPECT_TRUE(f.diag.HasErrors());
}

} // namespace
