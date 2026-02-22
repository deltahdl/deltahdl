#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

struct ElabA608Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA608Fixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto *design = elab.Elaborate(cu->modules.back()->name);
  f.has_errors = f.diag.HasErrors();
  return design;
}

}  // namespace

// =============================================================================
// A.6.8 Looping statements — Elaboration
// =============================================================================

// §12.7.1: for loop with typed init elaborates without error
TEST(ElabA608, ForLoopTypedInit) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 10; i++) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.1: for loop without typed init elaborates without error
TEST(ElabA608, ForLoopUntypedInit) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  integer i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 10; i = i + 1) x = i[7:0];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.3: foreach loop elaborates without error
TEST(ElabA608, ForeachLoop) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] arr [4];\n"
      "  logic [7:0] total;\n"
      "  initial begin\n"
      "    foreach (arr[i]) total = total + arr[i];\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.4: while loop elaborates without error
TEST(ElabA608, WhileLoop) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    while (x > 0) x = x - 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.5: do-while loop elaborates without error
TEST(ElabA608, DoWhileLoop) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    do x = x + 8'd1; while (x < 8'd10);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.6: repeat loop elaborates without error
TEST(ElabA608, RepeatLoop) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    repeat (10) x = x + 8'd1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §12.7.7: forever loop elaborates without error
TEST(ElabA608, ForeverLoop) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    forever begin\n"
      "      if (x == 8'd10) break;\n"
      "      x = x + 8'd1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// Nested loops elaborate without error
TEST(ElabA608, NestedLoops) {
  ElabA608Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    for (int i = 0; i < 4; i++) begin\n"
      "      for (int j = 0; j < 4; j++) begin\n"
      "        x = i[7:0] + j[7:0];\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
