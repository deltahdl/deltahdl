// §6.14: Chandle data type

#include <gtest/gtest.h>
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

using namespace delta;

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

static RtlirDesign* ElaborateSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// --- §6.14 Chandle restriction tests ---
TEST(Elaboration, ChandlePort_Error) {
  // §6.14: chandle cannot be used as a port.
  ElabFixture f;
  ElaborateSrc(
      "module top(input chandle ch);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleContAssign_Error) {
  // §6.14: chandle cannot be used in continuous assignment.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleSensitivity_Error) {
  // §6.14: chandle cannot appear in event expression.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "  always @(ch) begin end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, ChandleVarDecl_OK) {
  // §6.14: chandle variable declaration is legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  chandle ch;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
