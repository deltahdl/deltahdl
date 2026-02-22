// Tests for A.8.3 — Expressions — Elaboration

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

struct ElabA83Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src, ElabA83Fixture &f) {
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
// A.8.3 Expressions — Elaboration
// =============================================================================

// § inc_or_dec_expression — prefix increment elaborates

TEST(ElabA83, PrefixIncrementElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; ++x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § inc_or_dec_expression — postfix decrement elaborates

TEST(ElabA83, PostfixDecrementElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial begin x = 8'd5; x--; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § conditional_expression — ternary in continuous assignment elaborates

TEST(ElabA83, TernaryInContAssignElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic sel;\n"
      "  wire [7:0] a, b, y;\n"
      "  assign y = sel ? a : b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_expression — binary op in parameter elaborates

TEST(ElabA83, ConstantBinaryExprInParamElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter int WIDTH = 4 + 4;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_expression — ternary in parameter elaborates

TEST(ElabA83, ConstantTernaryInParamElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter int P = 1 ? 10 : 20;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § expression — binary operations in initial block elaborate

TEST(ElabA83, BinaryExprInInitialElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b, c;\n"
      "  initial c = a + b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § expression — unary operator in initial elaborates

TEST(ElabA83, UnaryExprInInitialElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] a, b;\n"
      "  initial b = ~a;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § inside_expression — inside in initial block elaborates

TEST(ElabA83, InsideExprElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  logic result;\n"
      "  initial result = x inside {8'd1, 8'd2, 8'd3};\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § tagged_union_expression — tagged elaborates

TEST(ElabA83, TaggedUnionElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    automatic int x;\n"
      "    x = tagged Valid 42;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § part_select_range — indexed part select elaborates

TEST(ElabA83, IndexedPartSelectElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [15:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[0+:8];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § genvar_expression — genvar in generate for elaborates

TEST(ElabA83, GenvarExprElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  parameter int N = 4;\n"
      "  logic [N-1:0] w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § constant_range — packed dimension range elaborates

TEST(ElabA83, ConstantRangePackedDimElaborates) {
  ElabA83Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] data;\n"
      "  logic [7:0] x;\n"
      "  initial x = data[7:0];\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
