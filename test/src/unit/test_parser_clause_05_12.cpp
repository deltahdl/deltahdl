#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

// --- §5.12: attribute on module definition ---

TEST(ParserClause05, Cl5_12_AttrOnModuleDefinition) {
  auto r = Parse(
      "(* optimize_power *)\n"
      "module m;\n"
      "  wire a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

TEST(ParserClause05, Cl5_12_AttrWithValueOnModuleDefinition) {
  EXPECT_TRUE(ParseOk("(* optimize_power = 1 *) module m; endmodule"));
}

// --- §5.12: attribute on module instantiation ---

TEST(ParserClause05, Cl5_12_AttrOnModuleInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  (* dont_touch *)\n"
      "  sub u1(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kModuleInst);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "dont_touch");
}

TEST(ParserClause05, Cl5_12_AttrWithValueOnInstantiation) {
  auto r = Parse(
      "module m;\n"
      "  (* optimize_power = 0 *)\n"
      "  sub u1(.a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "optimize_power");
  EXPECT_NE(items[0]->attrs[0].value, nullptr);
}

// --- §5.12: attribute on variable declaration ---

TEST(ParserClause05, Cl5_12_AttrOnVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  (* fsm_state *)\n"
      "  logic [7:0] state1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "fsm_state");
  EXPECT_EQ(item->attrs[0].value, nullptr);
}

TEST(ParserClause05, Cl5_12_AttrWithValueOnVarDecl) {
  auto r = Parse(
      "module m;\n"
      "  (* fsm_state = 1 *)\n"
      "  logic [3:0] state2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_NE(item->attrs[0].value, nullptr);
}

// --- §5.12: attribute on continuous assignment ---

TEST(ParserClause05, Cl5_12_AttrOnContAssign) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b;\n"
      "  (* synthesis_on *)\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 3u);
  auto* item = r.cu->modules[0]->items[2];
  EXPECT_EQ(item->kind, ModuleItemKind::kContAssign);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "synthesis_on");
}

// --- §5.12: multiple attr_specs in one instance ---

TEST(ParserClause05, Cl5_12_MultipleAttrSpecs) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case, parallel_case *)\n"
      "  wire a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[1].name, "parallel_case");
}

TEST(ParserClause05, Cl5_12_MixedAttrWithAndWithoutValue) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case, parallel_case = 1 *)\n"
      "  wire a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_GE(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].value, nullptr);
  EXPECT_NE(item->attrs[1].value, nullptr);
}

// --- §5.12: multiple separate attribute instances ---

TEST(ParserClause05, Cl5_12_MultipleSeparateInstances) {
  auto r = Parse(
      "module m;\n"
      "  (* full_case = 1 *)\n"
      "  (* parallel_case = 1 *)\n"
      "  logic x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_GE(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[1].name, "parallel_case");
}

// --- §5.12: attribute on case statement ---

TEST(ParserClause05, Cl5_12_AttrOnCaseStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (a)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->attrs.size(), 2u);
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
  EXPECT_EQ(stmt->attrs[1].name, "parallel_case");
}

// --- §5.12: attribute on if statement ---

TEST(ParserClause05, Cl5_12_AttrOnIfStatement) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* synthesis_off *)\n"
      "    if (a) x = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kIf);
  ASSERT_EQ(stmt->attrs.size(), 1u);
  EXPECT_EQ(stmt->attrs[0].name, "synthesis_off");
}

// --- §5.12: attribute on for loop ---

TEST(ParserClause05, Cl5_12_AttrOnForLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* unroll *)\n"
              "    for (int i = 0; i < 4; i++) x = i;\n"
              "  end\n"
              "endmodule\n"));
}

// --- §5.12: attribute on assignment statement ---

TEST(ParserClause05, Cl5_12_AttrOnAssignment) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* weight = 10 *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "weight");
  EXPECT_NE(stmt->attrs[0].value, nullptr);
}

// --- §5.12: attribute as suffix on operator ---

TEST(ParserClause05, Cl5_12_AttrOnBinaryOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b + (* mode = \"cla\" *) c;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_12_AttrOnTernaryOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c, d;\n"
              "  assign a = b ? (* no_glitch *) c : d;\n"
              "endmodule\n"));
}

// --- §5.12: attribute as suffix on function call ---

TEST(ParserClause05, Cl5_12_AttrOnFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  initial a = add (* mode = \"cla\" *) (b, c);\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_12_AttrOnFunctionCallNoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a;\n"
              "  initial a = foo (* bar *) ();\n"
              "endmodule\n"));
}

// --- §5.12: attribute value is constant expression ---

TEST(ParserClause05, Cl5_12_AttrValueConstExpr) {
  auto r = Parse(
      "module m;\n"
      "  (* depth = 3 + 1 *)\n"
      "  logic [7:0] mem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_NE(item->attrs[0].value, nullptr);
  EXPECT_EQ(item->attrs[0].value->kind, ExprKind::kBinary);
}

TEST(ParserClause05, Cl5_12_AttrValueString) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* tool_purpose = \"synthesis\" *)\n"
              "  logic x;\n"
              "endmodule\n"));
}

// --- §5.12: nested attributes disallowed ---

TEST(ParserClause05, Cl5_12_NestedAttributeError) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  (* foo = 1 + (* bar *) 2 *) logic x;\n"
              "endmodule\n"));
}

TEST(ParserClause05, Cl5_12_NonNestedConstExprOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* foo = 1 + 2 *) logic x;\n"
              "endmodule\n"));
}

}  // namespace
