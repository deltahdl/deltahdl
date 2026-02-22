// §6.6.8: Generic interconnect

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

// --- §6.6.8 Interconnect restriction tests ---
TEST(Elaboration, InterconnectContAssign_Error) {
  // §6.6.8: interconnect nets cannot be used in continuous assignments.
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  interconnect sig;\n"
      "  assign sig = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, InterconnectDecl_OK) {
  // §6.6.8: interconnect declaration is legal.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  interconnect bus;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  // Check that bus is created as a net.
  ASSERT_FALSE(design->top_modules.empty());
  auto* mod = design->top_modules[0];
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "bus") found = true;
  }
  EXPECT_TRUE(found);
}

}  // namespace
