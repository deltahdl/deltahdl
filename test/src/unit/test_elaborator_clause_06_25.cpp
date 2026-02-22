// §6.25: Parameterized data types

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

static RtlirDesign *ElaborateSrc(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

namespace {

// --- §6.25: Parameterized data types ---
TEST(Elaboration, ParameterizedType_Basic) {
  // §6.25: C#(logic)::my_type resolves to logic (width 1).
  ElabFixture f;
  auto *design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic)::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 1);
}

TEST(Elaboration, ParameterizedType_Vector) {
  // §6.25: C#(logic [7:0])::my_type resolves to logic [7:0] (width 8).
  ElabFixture f;
  auto *design = ElaborateSrc(
      "class C #(type T = int);\n"
      "  typedef T my_type;\n"
      "endclass\n"
      "module top;\n"
      "  C#(logic [7:0])::my_type x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto *mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8);
}

}  // namespace
