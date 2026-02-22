// §7.7: Arrays as arguments to subroutines

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

// §7.9.8: Assoc array index width propagated to RtlirVariable.
TEST(Elaboration, AssocArrayByteIndexWidth) {
  ElabFixture f;
  auto *design = ElaborateSrc(
      "module top;\n"
      "  int map[byte];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto &vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 8u);
}

TEST(Elaboration, AssocArrayIntIndexWidth) {
  ElabFixture f;
  auto *design = ElaborateSrc(
      "module top;\n"
      "  int map[int];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(design->top_modules.empty());
  auto &vars = design->top_modules[0]->variables;
  ASSERT_FALSE(vars.empty());
  EXPECT_TRUE(vars[0].is_assoc);
  EXPECT_EQ(vars[0].assoc_index_width, 32u);
}

}  // namespace
