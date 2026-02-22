// §6.10: Implicit declarations

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

// --- §6.10: Implicit declarations ---
TEST(Elaboration, ImplicitNetOnAssignLhs) {
  // Undeclared identifier on continuous assign LHS creates implicit wire.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  assign w = 1'b1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  // The implicit net 'w' should appear in nets.
  bool found = false;
  for (const auto& n : mod->nets) {
    if (n.name == "w") {
      found = true;
      EXPECT_EQ(n.width, 1) << "implicit net should be scalar";
    }
  }
  EXPECT_TRUE(found) << "implicit net 'w' not created";
}

TEST(Elaboration, ImplicitNetOnInstancePort) {
  // Undeclared identifier in instance port connection creates implicit wire.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module child(input logic a, output logic b);\n"
      "  assign b = a;\n"
      "endmodule\n"
      "module top;\n"
      "  child u0(.a(x), .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  bool found_x = false;
  bool found_y = false;
  for (const auto& n : mod->nets) {
    if (n.name == "x") found_x = true;
    if (n.name == "y") found_y = true;
  }
  EXPECT_TRUE(found_x) << "implicit net 'x' not created";
  EXPECT_TRUE(found_y) << "implicit net 'y' not created";
}

}  // namespace
