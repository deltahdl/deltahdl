#include <cstdint>

#include "common/types.h"
#include "fixture_elaborator.h"
#include "fixture_simulator.h"
#include "parser/ast.h"

using namespace delta;

namespace {

static CompilationUnit* ParseSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

TEST(ElabA91, LexerRecognizesAttrStartEnd) {

  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "(* foo *)");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  auto tokens = lexer.LexAll();
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(ElabA91, LexerDisambiguatesAttrFromMul) {

  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "(a * b)");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  auto tokens = lexer.LexAll();
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

TEST(ElabA91, ParserSingleAttrNoValue) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  (* full_case *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  ASSERT_FALSE(cu->modules.empty());
  auto* item = cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[0].value, nullptr);
}

TEST(ElabA91, ParserAttrWithConstExpr) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  (* depth = 4 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* item = cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "depth");
  ASSERT_NE(item->attrs[0].value, nullptr);
}

TEST(ElabA91, ParserMultipleAttrSpecs) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  (* full_case, parallel_case *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* item = cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[1].name, "parallel_case");
}

TEST(ElabA91, ParserMultipleSeparateInstances) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  (* first *)\n"
      "  (* second *)\n"
      "  logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* item = cu->modules[0]->items[0];
  ASSERT_GE(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "first");
  EXPECT_EQ(item->attrs[1].name, "second");
}

TEST(ElabA91, AttrNameIsIdentifier) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  (* my_tool_attr123 = 42 *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* item = cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "my_tool_attr123");
}

TEST(ElabA91, NestedAttributeDisallowed) {

  ElabFixture f;
  ParseSrc(
      "module m;\n"
      "  (* foo = 1 + (* bar *) 2 *) logic x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabA91, NonNestedConstExprOk) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  (* foo = 3 + 4 *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabA91, DefaultValueBitOne) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* full_case *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());

  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());

  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "full_case");
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 1);
}

static void VerifyFirstAttrResolved(RtlirDesign* design, ElabFixture& f,
                                    int64_t expected) {
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN),
            expected);
}

TEST(ElabA91, AttributeValueFromExpression) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "depth");
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 8);
}

TEST(ElabA91, AttributeValueConstExpr) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 3 + 5 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  VerifyFirstAttrResolved(design, f, 8);
}

TEST(ElabA91, AttributeValueString) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* tool_purpose = \"synthesis\" *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "tool_purpose");

  EXPECT_EQ(mod->variables[0].attrs[0].string_value, "synthesis");
}

TEST(ElabA91, DuplicateAttrLastWins) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 4, depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());

  auto& attrs = mod->variables[0].attrs;
  int depth_count = 0;
  for (auto& a : attrs) {
    if (a.name == "depth") {
      ++depth_count;
      ASSERT_NE(a.resolved_value, std::nullopt);
      EXPECT_EQ(a.resolved_value.value_or(INT64_MIN), 8);
    }
  }
  EXPECT_EQ(depth_count, 1);
}

TEST(ElabA91, DuplicateAttrWarning) {

  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  (* depth = 4, depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(ElabA91, DuplicateAttrAcrossInstances) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 2 *)\n"
      "  (* depth = 16 *)\n"
      "  logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  auto& attrs = mod->variables[0].attrs;
  int depth_count = 0;
  for (auto& a : attrs) {
    if (a.name == "depth") {
      ++depth_count;
      ASSERT_NE(a.resolved_value, std::nullopt);
      EXPECT_EQ(a.resolved_value.value_or(INT64_MIN), 16);
    }
  }
  EXPECT_EQ(depth_count, 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(ElabA91, AttrOnVarDecl) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state *) logic [7:0] state;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "fsm_state");
}

TEST(ElabA91, AttrOnNetDecl) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* mark *) wire w;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->nets.empty());
  ASSERT_FALSE(mod->nets[0].attrs.empty());
  EXPECT_EQ(mod->nets[0].attrs[0].name, "mark");
}

TEST(ElabA91, AttrOnContAssign) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic a, b;\n"
      "  (* synthesis_on *) assign a = b;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->assigns.empty());
  ASSERT_FALSE(mod->assigns[0].attrs.empty());
  EXPECT_EQ(mod->assigns[0].attrs[0].name, "synthesis_on");
}

TEST(ElabA91, AttrOnModuleInst) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module sub(input a);\n"
      "endmodule\n"
      "module m;\n"
      "  logic x;\n"
      "  (* optimize_power = 0 *) sub u1(.a(x));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->children.empty());
  ASSERT_FALSE(mod->children[0].attrs.empty());
  EXPECT_EQ(mod->children[0].attrs[0].name, "optimize_power");
}

TEST(ElabA91, AttrOnModuleDefinition) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "(* optimize_power *)\n"
      "module m;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->attrs.empty());
  EXPECT_EQ(mod->attrs[0].name, "optimize_power");
}

TEST(ElabA91, AttrOnCaseStmt) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (a)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* initial = cu->modules[0]->items[0];
  auto* block = initial->body;
  ASSERT_NE(block, nullptr);
  ASSERT_FALSE(block->stmts.empty());
  auto* case_stmt = block->stmts[0];
  EXPECT_EQ(case_stmt->kind, StmtKind::kCase);
  ASSERT_EQ(case_stmt->attrs.size(), 2u);
  EXPECT_EQ(case_stmt->attrs[0].name, "full_case");
  EXPECT_EQ(case_stmt->attrs[1].name, "parallel_case");
}

TEST(ElabA91, AttrOnIfStmt) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin\n"
      "    (* synthesis_off *) if (a) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* block = cu->modules[0]->items[0]->body;
  ASSERT_NE(block, nullptr);
  auto* if_stmt = block->stmts[0];
  EXPECT_EQ(if_stmt->kind, StmtKind::kIf);
  ASSERT_EQ(if_stmt->attrs.size(), 1u);
  EXPECT_EQ(if_stmt->attrs[0].name, "synthesis_off");
}

TEST(ElabA91, AttrOnForLoop) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin\n"
      "    (* unroll *) for (int i = 0; i < 4; i++) x = i;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* block = cu->modules[0]->items[0]->body;
  auto* for_stmt = block->stmts[0];
  EXPECT_EQ(for_stmt->kind, StmtKind::kFor);
  ASSERT_EQ(for_stmt->attrs.size(), 1u);
  EXPECT_EQ(for_stmt->attrs[0].name, "unroll");
}

TEST(ElabA91, AttrOnAssignStmt) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  initial begin\n"
      "    (* mark *) x = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  auto* block = cu->modules[0]->items[0]->body;
  auto* assign_stmt = block->stmts[0];
  ASSERT_EQ(assign_stmt->attrs.size(), 1u);
  EXPECT_EQ(assign_stmt->attrs[0].name, "mark");
}

TEST(ElabA91, AttrOnPortConnection) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  sub u1(.a(x), (* no_connect *) .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabA91, AttrOnBinaryOperator) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  assign a = b + (* mode = \"cla\" *) c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabA91, AttrOnTernaryOperator) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic a, b, c, d;\n"
      "  assign a = b ? (* no_glitch *) c : d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabA91, AttrOnFunctionCall) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic a, b, c;\n"
      "  initial a = add (* mode = \"cla\" *) (b, c);\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabA91, AttrOnFunctionCallNoArgs) {

  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  logic a;\n"
      "  initial a = foo (* bar *) ();\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(ElabA91, AttrPropagatedToRtlirProcess) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic clk, q, d;\n"
      "  (* synthesis = \"on\" *)\n"
      "  always_ff @(posedge clk) q <= d;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->processes.empty());
  ASSERT_FALSE(mod->processes[0].attrs.empty());
  EXPECT_EQ(mod->processes[0].attrs[0].name, "synthesis");
}

TEST(ElabA91, AttrValueZero) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state = 0 *) logic [3:0] reg2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(mod->variables[0].attrs[0].resolved_value.value_or(INT64_MIN), 0);
}

TEST(ElabA91, AttrValueLargeInt) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* weight = 255 *) logic x;\n"
      "endmodule\n",
      f);
  VerifyFirstAttrResolved(design, f, 255);
}

TEST(ElabA91, MultipleDistinctAttrsPreserved) {

  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* fsm_state, optimize = 1 *) logic [7:0] state;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_GE(mod->variables[0].attrs.size(), 2u);
  EXPECT_EQ(mod->variables[0].attrs[0].name, "fsm_state");
  EXPECT_EQ(mod->variables[0].attrs[1].name, "optimize");
}

TEST(SimA604, AttributedStatementExecutes) {
  SimA604Fixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [7:0] x;\n"
      "  initial begin\n"
      "    (* synthesis *) x = 8'd99;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* var = f.ctx.FindVariable("x");
  ASSERT_NE(var, nullptr);
  EXPECT_EQ(var->value.ToUint64(), 99u);
}

}
