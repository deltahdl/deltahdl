// Tests for A.8.5 — Expression left-side values — Elaboration

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

struct ElabA85Fixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
  bool has_errors = false;
};

static RtlirDesign *ElaborateSrc(const std::string &src,
                                 ElabA85Fixture &f) {
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
// A.8.5 Expression left-side values — Elaboration
// =============================================================================

// § net_lvalue — simple net in continuous assignment elaborates

TEST(ElabA85, NetLvalueSimpleContAssign) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  wire a, b;\n"
      "  assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § net_lvalue — bit select in continuous assignment elaborates

TEST(ElabA85, NetLvalueBitSelectContAssign) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  wire [7:0] a;\n"
      "  wire b;\n"
      "  assign a[3] = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § net_lvalue — concatenation in continuous assignment elaborates

TEST(ElabA85, NetLvalueConcatContAssign) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  wire [3:0] a, b;\n"
      "  wire [7:0] c;\n"
      "  assign {a, b} = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — simple variable in procedural assignment elaborates

TEST(ElabA85, VarLvalueSimpleProceduralAssign) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — bit select in procedural assignment elaborates

TEST(ElabA85, VarLvalueBitSelectProcedural) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x[3] = 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — part select in procedural assignment elaborates

TEST(ElabA85, VarLvaluePartSelectProcedural) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "  initial x[7:4] = 4'hF;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — concatenation in procedural assignment elaborates

TEST(ElabA85, VarLvalueConcatProcedural) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [3:0] a, b;\n"
      "  logic [7:0] c;\n"
      "  initial {a, b} = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — member access in procedural assignment elaborates

TEST(ElabA85, VarLvalueMemberAccessProcedural) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [7:0] hi; logic [7:0] lo; } pair_t;\n"
      "  pair_t p;\n"
      "  initial p.hi = 8'hAB;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — nonblocking assignment elaborates

TEST(ElabA85, VarLvalueNonblockingElaborates) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial x <= 1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — force/release elaborates

TEST(ElabA85, VarLvalueForceReleaseElaborates) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic x;\n"
      "  initial begin force x = 1; release x; end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § variable_lvalue — streaming concatenation LHS elaborates

TEST(ElabA85, VarLvalueStreamingConcatElaborates) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  logic [31:0] a, b;\n"
      "  initial {>> {a}} = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// § nonrange_variable_lvalue — simple variable elaborates

TEST(ElabA85, NonrangeVarLvalueElaborates) {
  ElabA85Fixture f;
  auto *design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  initial x = 42;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}
