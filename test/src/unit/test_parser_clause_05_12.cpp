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

}  // namespace
