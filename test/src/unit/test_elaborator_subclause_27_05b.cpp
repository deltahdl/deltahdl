#include <gtest/gtest.h>

#include "elaborator/rtlir.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §27.5: a generate block holding nothing but another conditional generate
// construct, with no begin-end around it, is no scope of its own, and the inner
// construct's blocks count as the outer construct's. They are held to the
// outer construct's naming rules, so the name dup below conflicts with logic
// dup as it would written directly in the outer if-generate.
TEST(GenerateElaboration, DirectlyNestedIfBlockCollidesWithDeclaration) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  logic dup;\n"
      "  if (P) if (Q) begin : dup end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'dup' conflicts with another declaration in the same "
      "scope",
      3, "27.5"));
}

// The same holds of a case-generate directly nested in the else branch of an
// if-generate: its item block w conflicts with wire w.
TEST(GenerateElaboration, DirectlyNestedCaseBlockCollidesWithDeclaration) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  wire w;\n"
      "  if (P) begin end else case (Q) 0: begin : w end\n"
      "    default: begin end endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'w' conflicts with another declaration in the same "
      "scope",
      3, "27.5"));
}

// A block of a directly nested construct may not share its name with a block of
// another construct in the scope either: s on line 3 is a block of the
// construct on line 3, and s on line 2 one of the construct on line 2.
TEST(GenerateElaboration, DirectlyNestedBlockCollidesAcrossConstructs) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  if (P) begin : s end\n"
      "  if (Q) if (P) begin : s end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 's' has the same name as a "
                            "generate block in another generate construct",
                            3, "27.5"));
}

// §27.5's Example 1 writes a case-generate directly nested in the else branch
// of an if-generate and names every block of both u1. The inner blocks are the
// outer construct's own alternatives, so sharing the name with its then-block
// breaks no rule and the source elaborates with no report.
TEST(GenerateElaboration, DirectlyNestedBlocksMayShareTheOuterBlocksName) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0, Q = 0) ();\n"
      "  if (P) begin : u1 logic a; end\n"
      "  else case (Q)\n"
      "    0: begin : u1 logic b; end\n"
      "    default: begin : u1 logic c; end\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §27.5's naming rules hold in every scope that holds a conditional generate
// construct, and a generate block is one: inside outer, the block dup conflicts
// with outer's logic dup, and the block s of the case-generate with the block s
// of the if-generate beside it. The parameter P is 0, so neither inner
// construct selects a block, which §27.5 rules makes no difference.
TEST(GenerateElaboration, BlockNameRulesHoldInsideAGenerateBlock) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0) ();\n"
      "  if (1) begin : outer\n"
      "    logic dup;\n"
      "    if (P) begin : dup end\n"
      "    if (P) begin : s end\n"
      "    case (P) 1: begin : s end\n"
      "             default: begin end endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'dup' conflicts with another declaration in the same "
      "scope",
      4, "27.5"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "generate block 's' has the same name as a "
                            "generate block in another generate construct",
                            6, "27.5"));
}

// The rules reach a block the elaboration never instantiates and a loop
// generate block as well: the then-block of if (0) is not selected, and the
// conflict inside it is reported all the same, as is the one in each block of
// the loop.
TEST(GenerateElaboration, BlockNameRulesHoldInUnselectedAndLoopBlocks) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0) ();\n"
      "  if (0) begin : never\n"
      "    wire d;\n"
      "    if (P) begin : d end\n"
      "  end\n"
      "  for (genvar i = 0; i < 2; i++) begin : loop\n"
      "    logic e;\n"
      "    if (P) begin : e end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'd' conflicts with another declaration in the same "
      "scope",
      4, "27.5"));
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "generate block 'e' conflicts with another declaration in the same "
      "scope",
      8, "27.5"));
}

// Each generate block is a scope of its own, so a name one block declares is no
// conflict for a construct in another block, nor for the module's: the blocks
// named x in a and in b, and the logic x of the module, are three scopes'
// names.
TEST(GenerateElaboration, BlockNameRulesStayWithinOneScope) {
  ElabFixture f;
  Elaborate(
      "module top #(parameter P = 0) ();\n"
      "  logic x;\n"
      "  if (1) begin : a\n"
      "    if (P) begin : x end\n"
      "  end\n"
      "  if (1) begin : b\n"
      "    if (P) begin : x end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §27.5 lets a module instantiate itself through a conditional generate
// construct, the recursion ending where the condition folds false, and rules
// that such a module is not a top-level module. Module r here instantiates
// itself while N is above zero, so the one top is top, and its instance of r
// with N = 2 heads a chain of three instances of r: N = 2, 1 and 0, the last
// instantiating nothing.
TEST(GenerateElaboration, SelfInstantiationEndsWhereTheConditionFails) {
  ElabFixture f;
  auto* design = ElaborateWithPreprocessor(
      "module r #(parameter N = 3) ();\n"
      "  if (N > 0) begin : sub\n"
      "    r #(.N(N - 1)) u ();\n"
      "  end\n"
      "endmodule\n"
      "module top;\n"
      "  r #(.N(2)) u ();\n"
      "endmodule\n",
      f, "", true);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  ASSERT_EQ(design->top_modules.size(), 1u);
  EXPECT_EQ(design->top_modules[0]->name, "top");
  int depth = 0;
  const RtlirModule* mod = design->top_modules[0];
  while (!mod->children.empty()) {
    ASSERT_EQ(mod->children.size(), 1u);
    EXPECT_EQ(mod->children[0].module_name, "r");
    mod = mod->children[0].resolved;
    ASSERT_NE(mod, nullptr);
    ++depth;
  }
  EXPECT_EQ(depth, 3);
}

}  // namespace
