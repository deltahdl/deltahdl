#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(GenerateInstantiationGrammar, ForGenerateNamedBlockWithWire) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i;\n"
              "  for (i = 0; i < 4; i = i + 1) begin : gen\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, GenerateItemAlwaysBlock) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    always @(posedge clk) q[i] <= d[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kAlwaysBlock);
}

TEST(GenerateInstantiationGrammar, GenerateItemModuleInst) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin : blk\n"
      "    sub u(.a(in[i]), .b(out[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(GenerateInstantiationGrammar, GenerateItemInInterface) {
  auto r = Parse(
      "interface my_if;\n"
      "  if (W > 0)\n"
      "    wire a;\n"
      "endinterface\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->interfaces.size(), 1u);
  bool found_if = false;
  for (auto* item : r.cu->interfaces[0]->items) {
    if (item->kind == ModuleItemKind::kGenerateIf) found_if = true;
  }
  EXPECT_TRUE(found_if);
}

TEST(GenerateInstantiationGrammar, GenerateForInstantiation) {
  auto r = Parse(
      "module top;\n"
      "  for (genvar i = 0; i < 4; i++) begin : gen_blk\n"
      "    sub u(.a(w[i]));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules[0];
  ASSERT_EQ(mod->items.size(), 1u);
  EXPECT_EQ(mod->items[0]->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(mod->items[0]->gen_body.size(), 1u);
  EXPECT_EQ(mod->items[0]->gen_body[0]->kind, ModuleItemKind::kModuleInst);
}

TEST(GenerateInstantiationGrammar, GenvarIterationPreIncrement) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; ++i) begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  ASSERT_NE(gen->gen_step, nullptr);
}

TEST(GenerateInstantiationGrammar, GenvarInitNonZeroStart) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 3; i >= 0; i--) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu->modules[0]->items[0]->gen_init, nullptr);
}

TEST(GenerateInstantiationGrammar, GenvarInitConstantExpression) {
  auto r = Parse(
      "module m #(parameter N = 4) ();\n"
      "  for (genvar i = N - 1; i >= 0; i--) begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_NE(r.cu->modules[0]->items[0]->gen_init, nullptr);
}

TEST(GenerateInstantiationGrammar, CaseGenerateDefaultNoColon) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: assign out = in8;\n"
      "    default assign out = in_def;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_TRUE(gen->gen_case_items[1].is_default);
}

TEST(GenerateInstantiationGrammar, GenerateBlockEmptyBeginEnd) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_TRUE(gen->gen_body.empty());
}

TEST(GenerateInstantiationGrammar, GenerateForEmptyBody) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  EXPECT_TRUE(gen->gen_body.empty());
}

TEST(GenerateInstantiationGrammar, CaseGenerateEmptyItem) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8: begin end\n"
      "    default: begin end\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 2u);
  EXPECT_TRUE(gen->gen_case_items[0].body.empty());
  EXPECT_TRUE(gen->gen_case_items[1].body.empty());
}

TEST(GenerateInstantiationGrammar, GenerateBlockLabelBeginOnly) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  for (genvar i = 0; i < 4; i++) begin : blk\n"
              "    wire w;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, GenerateBlockLabelAfterBegin) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  for (genvar i = 0; i < 4; i++) begin : blk\n"
              "    wire w;\n"
              "  end : blk\n"
              "endmodule\n"));
}

TEST(GenerateInstantiationGrammar, NestedGenerateRegion) {
  auto r = Parse(
      "module m;\n"
      "  generate\n"
      "    generate\n"
      "      wire a;\n"
      "    endgenerate\n"
      "  endgenerate\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(GenerateInstantiationGrammar, GenerateIfInChecker) {
  auto r = Parse(
      "checker my_chk;\n"
      "  if (1) begin\n"
      "    wire w;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(GenerateInstantiationGrammar, GenerateForInChecker) {
  auto r = Parse(
      "checker my_chk;\n"
      "  for (genvar i = 0; i < 4; i++) begin\n"
      "    wire w;\n"
      "  end\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(GenerateInstantiationGrammar, GenerateItemWithParamDecl) {
  auto r = Parse(
      "module m;\n"
      "  if (W > 0) begin : blk\n"
      "    localparam int X = 5;\n"
      "    wire [X-1:0] data;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_GE(gen->gen_body.size(), 2u);
}

TEST(GenerateInstantiationGrammar, GenerateItemWithInitialBlock) {
  auto r = Parse(
      "module m;\n"
      "  if (SIM) begin\n"
      "    initial $display(\"sim\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_GE(gen->gen_body.size(), 1u);
  EXPECT_EQ(gen->gen_body[0]->kind, ModuleItemKind::kInitialBlock);
}

TEST(GenerateInstantiationGrammar, GenerateItemWithFunction) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) begin : blk\n"
      "    function automatic int add(int a, int b);\n"
      "      return a + b;\n"
      "    endfunction\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(GenerateInstantiationGrammar, CaseGenerateSingleItem) {
  auto r = Parse(
      "module m;\n"
      "  case (MODE)\n"
      "    0: assign out = in;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_EQ(gen->gen_case_items.size(), 1u);
}

TEST(GenerateInstantiationGrammar, CaseGenerateOnlyDefault) {
  auto r = Parse(
      "module m;\n"
      "  case (MODE)\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  ASSERT_EQ(gen->gen_case_items.size(), 1u);
  EXPECT_TRUE(gen->gen_case_items[0].is_default);
}

TEST(GenerateInstantiationGrammar, CaseGenerateNested) {
  auto r = Parse(
      "module m;\n"
      "  case (A)\n"
      "    0: case (B)\n"
      "         0: assign out = 0;\n"
      "         default: assign out = 1;\n"
      "       endcase\n"
      "    default: assign out = 2;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_GE(gen->gen_case_items.size(), 2u);
}

TEST(GenerateInstantiationGrammar, IfGenerateInsideCaseGenerate) {
  auto r = Parse(
      "module m;\n"
      "  case (MODE)\n"
      "    0: if (EN) assign out = in;\n"
      "    default: assign out = 0;\n"
      "  endcase\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateCase);
  ASSERT_GE(gen->gen_case_items[0].body.size(), 1u);
  EXPECT_EQ(gen->gen_case_items[0].body[0]->kind, ModuleItemKind::kGenerateIf);
}

// generate_block ::= ... | [ generate_block_identifier : ] begin ...
// The label may precede `begin` (first optional position in the production),
// distinct from the post-`begin` `: label` form exercised elsewhere.
TEST(GenerateInstantiationGrammar, GenerateBlockLabelBeforeBegin) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 4; i++) blk : begin\n"
      "    assign out[i] = in[i];\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateFor);
  EXPECT_EQ(gen->name, "blk");
  ASSERT_EQ(gen->gen_body.size(), 1u);
}

TEST(GenerateInstantiationGrammar, IfGenerateBlockLabelBeforeBegin) {
  auto r = Parse(
      "module m;\n"
      "  if (EN) g : begin\n"
      "    wire w;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* gen = r.cu->modules[0]->items[0];
  EXPECT_EQ(gen->kind, ModuleItemKind::kGenerateIf);
  EXPECT_EQ(gen->name, "g");
}

TEST(GenerateInstantiationGrammar, DeeplyNestedGenerateFor) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin : l1\n"
      "    for (genvar j = 0; j < 2; j++) begin : l2\n"
      "      for (genvar k = 0; k < 2; k++) begin : l3\n"
      "        assign out[i][j][k] = in[i][j][k];\n"
      "      end\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* l1 = r.cu->modules[0]->items[0];
  EXPECT_EQ(l1->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(l1->gen_body.size(), 1u);
  auto* l2 = l1->gen_body[0];
  EXPECT_EQ(l2->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(l2->gen_body.size(), 1u);
  auto* l3 = l2->gen_body[0];
  EXPECT_EQ(l3->kind, ModuleItemKind::kGenerateFor);
  ASSERT_EQ(l3->gen_body.size(), 1u);
}

// --- error conditions ---

// case_generate_item ::= constant_expression { , constant_expression }
//   : generate_block | default [ : ] generate_block
// The colon is mandatory for the non-default form (only the `default` form may
// omit it), so a pattern item with no colon before its body is rejected.
TEST(GenerateInstantiationGrammar, CaseGenerateItemMissingColonRejected) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "    8 assign out = in;\n"
      "  endcase\n"
      "endmodule\n");
  // §27.5 owns the case generate construct; A.4.2 only states its production.
  EXPECT_TRUE(ReportedError(r.diags, "expected ':', got 'assign'", 3, "27.5"));
}

// if_generate_construct ::= if ( constant_expression ) generate_block
//   [ else generate_block ]
// The parentheses around the condition are required by the production.
TEST(GenerateInstantiationGrammar, IfGenerateMissingParenRejected) {
  auto r = Parse(
      "module m;\n"
      "  if EN\n"
      "    assign out = in;\n"
      "endmodule\n");
  // §27.5 owns the conditional generate construct; A.4.2 only states its
  // production.
  EXPECT_TRUE(
      ReportedError(r.diags, "expected '(', got identifier", 2, "27.5"));
}

// genvar_initialization ::= [ genvar ] genvar_identifier = constant_expression
// The first header position holds that assignment and nothing else. The
// parser read it as any assignment or expression statement, so an increment,
// a compound assignment and a select on the genvar were each accepted
// silently.
TEST(GenerateInstantiationGrammar, LoopGenerateInitIncrementRejected) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i++; i < 4; i++) begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a loop generate's initialization is written", 3, "A.4.2"));
}

TEST(GenerateInstantiationGrammar, LoopGenerateInitCompoundAssignRejected) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i += 1; i < 4; i++) begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a loop generate's initialization is written", 3, "A.4.2"));
}

TEST(GenerateInstantiationGrammar, LoopGenerateInitSelectRejected) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i[0] = 0; i < 4; i++) begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a loop generate's initialization is written", 3, "A.4.2"));
}

// The `genvar` keyword is the production's one option, and what follows it is
// the same assignment; the genvar and its bound are recorded as the elaborator
// reads them.
TEST(GenerateInstantiationGrammar, LoopGenerateInitRecordsGenvarAndBound) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 2; i < 4; i++) begin end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item =
      FindItemByKind(r.cu->modules[0]->items, ModuleItemKind::kGenerateFor);
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->gen_init, nullptr);
  EXPECT_EQ(item->gen_init->kind, StmtKind::kBlockingAssign);
  ASSERT_NE(item->gen_init->lhs, nullptr);
  EXPECT_EQ(item->gen_init->lhs->kind, ExprKind::kIdentifier);
  EXPECT_EQ(item->gen_init->lhs->text, "i");
  ASSERT_NE(item->gen_init->rhs, nullptr);
  EXPECT_EQ(item->gen_init->rhs->kind, ExprKind::kIntegerLiteral);
}

// genvar_iteration ::= genvar_identifier assignment_operator genvar_expression
//   | inc_or_dec_operator genvar_identifier
//   | genvar_identifier inc_or_dec_operator
// The third header position holds one of those three; a bare genvar, a call
// and a nonblocking assignment were each accepted silently.
TEST(GenerateInstantiationGrammar, LoopGenerateIterationBareGenvarRejected) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i) begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a loop generate's iteration is written",
                            3, "A.4.2"));
}

TEST(GenerateInstantiationGrammar, LoopGenerateIterationCallRejected) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; next(i)) begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a loop generate's iteration is written",
                            3, "A.4.2"));
}

TEST(GenerateInstantiationGrammar, LoopGenerateIterationNonblockingRejected) {
  auto r = Parse(
      "module m;\n"
      "  genvar i;\n"
      "  for (i = 0; i < 4; i <= i + 1) begin end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(r.diags, "a loop generate's iteration is written",
                            3, "A.4.2"));
}

// The two forms the tests above do not already observe: a compound
// assignment_operator other than `+=`, and a prefix decrement.
TEST(GenerateInstantiationGrammar, LoopGenerateIterationOtherForms) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  genvar i, j;\n"
              "  for (i = 1; i < 16; i *= 2) begin end\n"
              "  for (j = 4; j > 0; --j) begin end\n"
              "endmodule\n"));
}

// case_generate_construct ::= case ( constant_expression ) case_generate_item
//   { case_generate_item } endcase
// One item at least; a construct with none was accepted silently.
TEST(GenerateInstantiationGrammar, CaseGenerateWithoutItemsRejected) {
  auto r = Parse(
      "module m;\n"
      "  case (WIDTH)\n"
      "  endcase\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a case generate construct has at least one case_generate_item",
      3, "A.4.2"));
}

// generate_block ::= ... begin [ : generate_block_identifier ] { generate_item
// }
//   end [ : generate_block_identifier ]
// The identifier after `end` is the one the block opened with: §9.3.4 has "it
// shall be an error if the name at the end is different from the block name
// at the beginning", and a block with no name has none for it to match. The
// parser skipped whatever identifier stood there.
TEST(GenerateInstantiationGrammar, GenerateBlockEndLabelMismatchRejected) {
  auto r = Parse(
      "module m;\n"
      "  if (1) begin : g\n"
      "    assign a = b;\n"
      "  end : h\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'h' does not match block name 'g'", 4, "9.3.4"));
}

TEST(GenerateInstantiationGrammar, GenerateBlockEndLabelOnUnnamedRejected) {
  auto r = Parse(
      "module m;\n"
      "  for (genvar i = 0; i < 2; i++) begin\n"
      "    assign a[i] = b[i];\n"
      "  end : g\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "end label 'g' specified for unnamed block", 4, "9.3.4"));
}

// The label before `begin` names the block as the one after it does, so the
// end label matches either.
TEST(GenerateInstantiationGrammar, GenerateBlockEndLabelMatchesPrefixLabel) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  if (1) g : begin\n"
              "    assign a = b;\n"
              "  end : g\n"
              "endmodule\n"));
}

}  // namespace
