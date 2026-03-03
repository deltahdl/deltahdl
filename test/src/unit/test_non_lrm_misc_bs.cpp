// Non-LRM tests

#include "fixture_parser.h"

using namespace delta;

struct ParseResult8b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult8b Parse(const std::string& src) {
  ParseResult8b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

// Static cast with type apostrophe syntax: type'(expr).
TEST(ParserSection8, StaticCastTypeSyntax) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    int a;\n"
              "    real r;\n"
              "    r = 3.14;\n"
              "    a = int'(r);\n"
              "  end\n"
              "endmodule\n"));
}

// =============================================================================
// Section 8.18 -- User-defined types (typedef)
// =============================================================================
// Simple typedef of built-in type.
TEST(ParserSection8, TypedefSimpleBuiltin) {
  auto r = Parse(
      "module m;\n"
      "  typedef int my_int;\n"
      "  my_int x;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->name, "my_int");
}

// Forward typedef declaration for enum.
TEST(ParserSection8, TypedefForwardEnum) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef enum my_enum;\n"
              "  typedef enum {A, B, C} my_enum;\n"
              "endmodule\n"));
}

// Typedef of enum with named type for reuse.
TEST(ParserSection8, TypedefEnumWithMembers) {
  auto r = Parse(
      "module m;\n"
      "  typedef enum {RED, GREEN, BLUE} color_t;\n"
      "  color_t c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(items[0]->typedef_type.kind, DataTypeKind::kEnum);
}

}  // namespace
