// §5.12 Attributes — elaboration-level semantics (A.9.1 BNF)

#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "common/types.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/ast.h"
#include "parser/parser.h"

using namespace delta;

namespace {

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
  if (!cu || cu->modules.empty()) return nullptr;
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

// Helper: parse without elaboration, return CompilationUnit.
static CompilationUnit* ParseSrc(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  return parser.Parse();
}

// =========================================================================
// A.9.1 BNF production: attribute_instance ::= (* attr_spec { , attr_spec } *)
// =========================================================================

// --- Lexer level: (* and *) token recognition ---

TEST(ElabA91, LexerRecognizesAttrStartEnd) {
  // §A.9.1: (* and *) are the delimiters for attribute_instance.
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "(* foo *)");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  auto tokens = lexer.LexAll();
  ASSERT_GE(tokens.size(), 3u);
  EXPECT_EQ(tokens[0].kind, TokenKind::kAttrStart);
  EXPECT_EQ(tokens[2].kind, TokenKind::kAttrEnd);
}

TEST(ElabA91, LexerDisambiguatesAttrFromMul) {
  // §A.9.1: (a * b) should NOT produce kAttrStart.
  ElabFixture f;
  auto fid = f.mgr.AddFile("<test>", "(a * b)");
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  auto tokens = lexer.LexAll();
  EXPECT_EQ(tokens[0].kind, TokenKind::kLParen);
  EXPECT_EQ(tokens[2].kind, TokenKind::kStar);
}

// --- Parser level: single attr_spec ---

TEST(ElabA91, ParserSingleAttrNoValue) {
  // §A.9.1: attr_spec with just attr_name, no value.
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

// --- Parser level: attr_spec with value ---

TEST(ElabA91, ParserAttrWithConstExpr) {
  // §A.9.1: attr_spec ::= attr_name [ = constant_expression ]
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

// --- Parser level: multiple attr_spec in one attribute_instance ---

TEST(ElabA91, ParserMultipleAttrSpecs) {
  // §A.9.1: attribute_instance ::= (* attr_spec { , attr_spec } *)
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

// --- Parser level: multiple separate attribute_instance blocks ---

TEST(ElabA91, ParserMultipleSeparateInstances) {
  // §5.12: Multiple attribute_instance blocks are merged.
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

// --- Parser level: attr_name ::= identifier ---

TEST(ElabA91, AttrNameIsIdentifier) {
  // §A.9.1: attr_name ::= identifier — any valid identifier can be an attr
  // name.
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

// =========================================================================
// §5.12 Semantic: Nesting of attribute instances is disallowed
// =========================================================================

TEST(ElabA91, NestedAttributeDisallowed) {
  // §5.12: It shall be illegal to specify the value of an attribute
  // with a constant expression that contains an attribute instance.
  ElabFixture f;
  ParseSrc(
      "module m;\n"
      "  (* foo = 1 + (* bar *) 2 *) logic x;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(ElabA91, NonNestedConstExprOk) {
  // §5.12: A constant expression without nesting is fine.
  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  (* foo = 3 + 4 *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// =========================================================================
// §5.12 Semantic: Default value — attribute with no value is bit with value 1
// =========================================================================

TEST(ElabA91, DefaultValueBitOne) {
  // §5.12: The default type of an attribute with no value is bit, with
  // a value of 1.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* full_case *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  // After elaboration, the attribute with no value should have been
  // assigned a default value of 1'b1.
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  // Verify the attribute is propagated to the RTLIR variable.
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  EXPECT_EQ(mod->variables[0].attrs[0].name, "full_case");
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(*mod->variables[0].attrs[0].resolved_value, 1);
}

// =========================================================================
// §5.12 Semantic: Attribute takes type of expression when value assigned
// =========================================================================

TEST(ElabA91, AttributeValueFromExpression) {
  // §5.12: Otherwise, the attribute takes the type of the expression.
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
  EXPECT_EQ(*mod->variables[0].attrs[0].resolved_value, 8);
}

TEST(ElabA91, AttributeValueConstExpr) {
  // §5.12: Value is a constant expression — evaluated at elaboration time.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 3 + 5 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(*mod->variables[0].attrs[0].resolved_value, 8);
}

TEST(ElabA91, AttributeValueString) {
  // §5.12 Example 6: mode = "cla" — string-valued attribute.
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
  // String values: resolved_value may be nullopt (not integer-evaluable).
  // The string_value should be preserved.
  EXPECT_EQ(mod->variables[0].attrs[0].string_value, "synthesis");
}

// =========================================================================
// §5.12 Semantic: Duplicate attribute — last value wins + warning
// =========================================================================

TEST(ElabA91, DuplicateAttrLastWins) {
  // §5.12: If the same attribute name is defined more than once for the
  // same language element, the last attribute value shall be used.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* depth = 4, depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  // After dedup, only one 'depth' attribute should remain with the last value.
  auto& attrs = mod->variables[0].attrs;
  int depth_count = 0;
  for (auto& a : attrs) {
    if (a.name == "depth") {
      ++depth_count;
      ASSERT_NE(a.resolved_value, std::nullopt);
      EXPECT_EQ(*a.resolved_value, 8);
    }
  }
  EXPECT_EQ(depth_count, 1);
}

TEST(ElabA91, DuplicateAttrWarning) {
  // §5.12: A tool can issue a warning that a duplicate attribute
  // specification has occurred.
  ElabFixture f;
  ElaborateSrc(
      "module m;\n"
      "  (* depth = 4, depth = 8 *) logic [7:0] mem;\n"
      "endmodule\n",
      f);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

TEST(ElabA91, DuplicateAttrAcrossInstances) {
  // §5.12: Duplicate across separate attribute_instance blocks.
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
      EXPECT_EQ(*a.resolved_value, 16);
    }
  }
  EXPECT_EQ(depth_count, 1);
  EXPECT_GT(f.diag.WarningCount(), 0u);
}

// =========================================================================
// §5.12 Prefix attachment: declarations
// =========================================================================

TEST(ElabA91, AttrOnVarDecl) {
  // §5.12: attribute_instance as prefix on a declaration.
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
  // §5.12: attribute on a net declaration.
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

// =========================================================================
// §5.12 Prefix attachment: module items
// =========================================================================

TEST(ElabA91, AttrOnContAssign) {
  // §5.12: attribute on a continuous assignment (module item).
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
  // §5.12 Example 4: attribute on a module instantiation.
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
  // §5.12 Example 3: attribute on a module definition.
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

// =========================================================================
// §5.12 Prefix attachment: statements
// =========================================================================

TEST(ElabA91, AttrOnCaseStmt) {
  // §5.12 Example 1: full_case, parallel_case on a case statement.
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
  // §5.12: attribute as prefix on an if statement.
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
  // §5.12: attribute on a for loop statement.
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
  // §5.12: attribute on an assignment statement.
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

// =========================================================================
// §5.12 Prefix attachment: port connections
// =========================================================================

TEST(ElabA91, AttrOnPortConnection) {
  // §5.12: attribute_instance as prefix on a port connection.
  ElabFixture f;
  auto* cu = ParseSrc(
      "module m;\n"
      "  sub u1(.a(x), (* no_connect *) .b(y));\n"
      "endmodule\n",
      f);
  ASSERT_NE(cu, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// =========================================================================
// §5.12 Suffix attachment: operators
// =========================================================================

TEST(ElabA91, AttrOnBinaryOperator) {
  // §5.12 Example 6: a = b + (* mode = "cla" *) c;
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
  // §5.12 Example 8: a = b ? (* no_glitch *) c : d;
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

// =========================================================================
// §5.12 Suffix attachment: function name in expression
// =========================================================================

TEST(ElabA91, AttrOnFunctionCall) {
  // §5.12 Example 7: a = add (* mode = "cla" *) (b, c);
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
  // §5.12: attribute on function call with no arguments.
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

// =========================================================================
// Elaboration: attribute propagation to RTLIR
// =========================================================================

TEST(ElabA91, AttrPropagatedToRtlirProcess) {
  // Attributes on always block should propagate to RtlirProcess.
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

// =========================================================================
// Mixed: attribute with various constant expression types
// =========================================================================

TEST(ElabA91, AttrValueZero) {
  // §5.12 Example 2: parallel_case = 0 explicitly disables.
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
  EXPECT_EQ(*mod->variables[0].attrs[0].resolved_value, 0);
}

TEST(ElabA91, AttrValueLargeInt) {
  // Constant expression with a larger integer value.
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  (* weight = 255 *) logic x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
  auto* mod = design->top_modules[0];
  ASSERT_FALSE(mod->variables.empty());
  ASSERT_FALSE(mod->variables[0].attrs.empty());
  ASSERT_NE(mod->variables[0].attrs[0].resolved_value, std::nullopt);
  EXPECT_EQ(*mod->variables[0].attrs[0].resolved_value, 255);
}

// =========================================================================
// §5.12: Multiple attributes on same declaration, different names
// =========================================================================

TEST(ElabA91, MultipleDistinctAttrsPreserved) {
  // Multiple distinct attributes should all be preserved.
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

}  // namespace
