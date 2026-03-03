// §5.12: Attributes

#include "fixture_program.h"
#include "fixture_simulator.h"

using namespace delta;

using DpiParseTest = ProgramTestParse;

using ApiParseTest = ProgramTestParse;

struct ParseResult40 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult40 Parse(const std::string& src) {
  ParseResult40 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// =============================================================================
// §35.2.1 Attributes on modules/instances
// =============================================================================
TEST_F(DpiParseTest, AttributeOnModuleDefinition) {
  auto* unit = Parse(R"(
    (* optimize_power *)
    module m;
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_EQ(unit->modules[0]->name, "m");
}

TEST_F(DpiParseTest, AttributeOnModuleInstantiation) {
  auto* unit = Parse(R"(
    module m;
      (* dont_touch *)
      sub u1(.a(x));
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kModuleInst);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "dont_touch");
}

TEST_F(DpiParseTest, AttributeWithValueOnInstance) {
  auto* unit = Parse(R"(
    module m;
      (* optimize_power = 0 *)
      sub u1(.a(x));
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_FALSE(items[0]->attrs.empty());
  EXPECT_EQ(items[0]->attrs[0].name, "optimize_power");
  EXPECT_NE(items[0]->attrs[0].value, nullptr);
}

// =============================================================================
// A.9 -- General (attributes, identifiers)
// =============================================================================
TEST(ParserAnnexA, A9AttributeOnContAssign) {
  auto r = Parse("module m; wire y; (* synthesis *) assign y = 1; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// =============================================================================
// §35.5 Attribute compatibility (multiple attributes)
// =============================================================================
TEST_F(DpiParseTest, MultipleAttributesOnDecl) {
  auto* unit = Parse(R"(
    module m;
      (* full_case, parallel_case *)
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_EQ(items.size(), 1u);
  ASSERT_GE(items[0]->attrs.size(), 2u);
  EXPECT_EQ(items[0]->attrs[0].name, "full_case");
  EXPECT_EQ(items[0]->attrs[1].name, "parallel_case");
}

TEST(ParserAnnexA, A9AttributeWithValue) {
  auto r = Parse("module m; (* max_fanout = 8 *) wire w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST_F(DpiParseTest, AttributeWithAndWithoutValue) {
  auto* unit = Parse(R"(
    module m;
      (* full_case, parallel_case = 1 *)
      wire a;
    endmodule
  )");
  ASSERT_EQ(unit->modules.size(), 1u);
  auto& items = unit->modules[0]->items;
  ASSERT_GE(items[0]->attrs.size(), 2u);
  EXPECT_EQ(items[0]->attrs[0].value, nullptr);
  EXPECT_NE(items[0]->attrs[1].value, nullptr);
}

// §12.3: statement with attribute having value
TEST(ParserA604, StatementWithAttributeValue) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* weight = 10 *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_FALSE(stmt->attrs.empty());
  EXPECT_EQ(stmt->attrs[0].name, "weight");
  EXPECT_NE(stmt->attrs[0].value, nullptr);
}

// §12.3: statement with multiple attributes
TEST(ParserA604, StatementWithMultipleAttributes) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* foo, bar *) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->attrs.size(), 2u);
  EXPECT_EQ(stmt->attrs[0].name, "foo");
  EXPECT_EQ(stmt->attrs[1].name, "bar");
}

// --- §5.12 Attributes ---
struct ParseResult512 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult512 Parse(const std::string& src) {
  ParseResult512 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// From test_parser_clause_05.cpp
TEST(ParserCh512, AttributeOnModuleItem) {
  auto r = Parse(
      "module t;\n"
      "  (* full_case *)\n"
      "  logic [7:0] x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 1u);
  EXPECT_EQ(item->attrs[0].name, "full_case");
  EXPECT_EQ(item->attrs[0].value, nullptr);
}

static void VerifyAttrNames(const ModuleItem* item,
                            const std::string expected_names[], size_t count) {
  ASSERT_EQ(item->attrs.size(), count);
  for (size_t i = 0; i < count; ++i) {
    EXPECT_EQ(item->attrs[i].name, expected_names[i]) << "attr " << i;
  }
}

TEST(ParserCh512, AttributeWithValue_Names) {
  auto r = Parse(
      "module t;\n"
      "  (* synthesis, optimize_power = 1 *)\n"
      "  logic y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  std::string expected_names[] = {"synthesis", "optimize_power"};
  VerifyAttrNames(r.cu->modules[0]->items[0], expected_names,
                  std::size(expected_names));
}

TEST(ParserCh512, AttributeWithValue_Values) {
  auto r = Parse(
      "module t;\n"
      "  (* synthesis, optimize_power = 1 *)\n"
      "  logic y;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->attrs.size(), 2u);
  EXPECT_EQ(item->attrs[0].value, nullptr);
  ASSERT_NE(item->attrs[1].value, nullptr);
}

TEST(ParserCh512, TopLevel_AttributeBeforeModule) {
  EXPECT_TRUE(ParseOk("(* optimize_power *) module m; endmodule"));
}

TEST(ParserCh512, Expr_AttributeOnOperator) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c;\n"
              "  assign a = b + (* mode = \"cla\" *) c;\n"
              "endmodule"));
}

TEST(ParserCh512, Expr_AttributeOnTernary) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  logic a, b, c, d;\n"
              "  assign a = b ? (* no_glitch *) c : d;\n"
              "endmodule"));
}

TEST(ParserCh512, PostfixFunctionAttribute) {
  // §5.12 Example 7: a = add (* mode = "cla" *) (b, c);
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a, b, c;\n"
              "  initial a = add (* mode = \"cla\" *) (b, c);\n"
              "endmodule\n"));
}

TEST(ParserCh512, PostfixFunctionAttribute_NoArgs) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  logic a;\n"
              "  initial a = foo (* bar *) ();\n"
              "endmodule\n"));
}

TEST(ParserCh512, NestedAttribute_Error) {
  // §5.12: Nesting of attribute instances is disallowed.
  EXPECT_FALSE(
      ParseOk("module t;\n"
              "  (* foo = 1 + (* bar *) 2 *) logic x;\n"
              "endmodule\n"));
}

TEST(ParserCh512, AttributeValue_NoNesting_Ok) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  (* foo = 1 + 2 *) logic x;\n"
              "endmodule\n"));
}

static Stmt* FirstInitialStmt(ParseResult512& r) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kInitialBlock) {
      if (item->body && item->body->kind == StmtKind::kBlock) {
        return item->body->stmts.empty() ? nullptr : item->body->stmts[0];
      }
      return item->body;
    }
  }
  return nullptr;
}

// From test_parser_clause_05b.cpp
TEST(ParserCh512, Attribute_OnCaseStatement) {
  // Section 5.12 Example 1: full_case, parallel_case on a case statement.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    (* full_case, parallel_case *)\n"
      "    case (a)\n"
      "      default: x = 0;\n"
      "    endcase\n"
      "  end\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kCase);
  ASSERT_EQ(stmt->attrs.size(), 2u);
  EXPECT_EQ(stmt->attrs[0].name, "full_case");
  EXPECT_EQ(stmt->attrs[1].name, "parallel_case");
}

TEST(ParserCh512, Attribute_MultipleInstances) {
  // Multiple separate attribute instances before the same item.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* full_case=1 *)\n"
              "  (* parallel_case=1 *)\n"
              "  logic x;\n"
              "endmodule"));
}

TEST(ParserCh512, Attribute_OnModuleInstantiation) {
  // Section 5.12 Example 4: attribute on a module instantiation.
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  (* optimize_power=0 *)\n"
              "  sub u1(.a(x));\n"
              "endmodule"));
}

}  // namespace
