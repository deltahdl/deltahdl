#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;

namespace {

TEST(LexicalConventionParsing, AttrOnModuleInstantiation) {
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

TEST(LexicalConventionParsing, AttrWithValueOnInstantiation) {
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

TEST(LexicalConventionParsing, AttrOnVarDecl) {
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

TEST(LexicalConventionParsing, AttrWithValueOnVarDecl) {
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

TEST(LexicalConventionParsing, AttrOnContAssign) {
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

TEST(LexicalConventionParsing, MultipleSeparateInstances) {
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

TEST(LexicalConventionParsing, AttrOnCaseStatement) {
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

TEST(LexicalConventionParsing, AttrOnIfStatement) {
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

TEST(LexicalConventionParsing, AttrOnForLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    (* unroll *)\n"
              "    for (int i = 0; i < 4; i++) x = i;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, AttrOnAssignment) {
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

TEST(LexicalConventionParsing, AttrOnBinaryOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b + (* mode = \"cla\" *) c;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, AttrOnTernaryOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c, d;\n"
              "  assign a = b ? (* no_glitch *) c : d;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, AttrOnFunctionCall) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  initial a = add (* mode = \"cla\" *) (b, c);\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, AttrOnFunctionCallNoArgs) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a;\n"
              "  initial a = foo (* bar *) ();\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, NestedAttributeError) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  (* foo = 1 + (* bar *) 2 *) logic x;\n"
              "endmodule\n"));
}

TEST(LexicalConventionParsing, NonNestedConstExprOk) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* foo = 1 + 2 *) logic x;\n"
              "endmodule\n"));
}

// Syntax 5-4: attr_name is an identifier. A non-identifier token (here a
// number literal) in the attr_name position is rejected by the parser.
TEST(LexicalConventionParsing, AttrNameMustBeIdentifier) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  (* 7 *) logic x;\n"
              "endmodule\n"));
}

// Syntax 5-4: an attribute_instance contains one or more attr_spec, so an
// empty (* *) with no attr_spec is rejected.
TEST(LexicalConventionParsing, EmptyAttributeInstanceRejected) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  (* *) logic x;\n"
              "endmodule\n"));
}

// §5.12 Example 5: an attribute prefix binds only to the declaration it
// immediately precedes. A single prefix is shared by every name declared in
// that declaration, while a declaration with no prefix carries no attributes.
TEST(LexicalConventionParsing, PrefixBindsOnlyToItsDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  (* fsm_state *) logic [7:0] state1;\n"
      "  (* fsm_state = 1 *) logic [3:0] state2, state3;\n"
      "  logic [3:0] reg1;\n"
      "  (* fsm_state = 0 *) logic [3:0] reg2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);

  auto has_fsm_state = [](const ModuleItem* item) {
    for (const auto& a : item->attrs) {
      if (a.name == "fsm_state") return true;
    }
    return false;
  };
  auto find = [&](std::string_view name) -> ModuleItem* {
    for (auto* item : r.cu->modules[0]->items) {
      if (item->name == name) return item;
    }
    return nullptr;
  };

  ASSERT_NE(find("state1"), nullptr);
  ASSERT_NE(find("state2"), nullptr);
  ASSERT_NE(find("state3"), nullptr);
  ASSERT_NE(find("reg1"), nullptr);
  ASSERT_NE(find("reg2"), nullptr);

  // The single prefix is distributed to both names of the multi-name
  // declaration.
  EXPECT_TRUE(has_fsm_state(find("state1")));
  EXPECT_TRUE(has_fsm_state(find("state2")));
  EXPECT_TRUE(has_fsm_state(find("state3")));

  // The unprefixed declaration does not inherit the preceding prefix.
  EXPECT_FALSE(has_fsm_state(find("reg1")));

  // A later prefixed declaration is attributed independently.
  EXPECT_TRUE(has_fsm_state(find("reg2")));
}

TEST(LexicalConventionParsing, AttrOnPortConnection) {
  auto r = Parse(
      "module m;\n"
      "  sub u1((* mark *) .a(x));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(LexicalConventionParsing, AttributeOnModuleParses) {
  auto r = Parse(
      "(* synthesis *) module t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->attrs.empty());
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "synthesis");
}

TEST(LexicalConventionParsing, AttributeWithValueParses) {
  auto r = Parse(
      "(* full_case = 1 *) module t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_FALSE(r.cu->modules[0]->attrs.empty());
  EXPECT_EQ(r.cu->modules[0]->attrs[0].name, "full_case");
  EXPECT_NE(r.cu->modules[0]->attrs[0].value, nullptr);
}

TEST(LexicalConventionParsing, MultipleAttributesOnModule) {
  auto r = Parse(
      "(* synthesis, full_case *) module t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->attrs.size(), 2u);
}

}  // namespace
