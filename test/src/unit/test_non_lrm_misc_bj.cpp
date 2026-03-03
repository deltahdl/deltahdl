// Non-LRM tests

#include "fixture_parser.h"
#include "elaborator/type_eval.h"

using namespace delta;

struct ParseResult6b {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult6b Parse(const std::string& src) {
  ParseResult6b result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

namespace {

TEST(ParserSection6, ModuleLifetimeAutomatic) {
  auto r = Parse("module automatic t; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "t");
}

// =========================================================================
// §6.22.1 -- Matching types
// =========================================================================
TEST(ParserSection6, MatchingTypesBuiltinTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit node;\n"
      "  node n1;\n"
      "  bit n2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesAnonymousStruct) {
  auto r = Parse(
      "module m;\n"
      "  struct packed {int A; int B;} AB1, AB2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 1u);
}

TEST(ParserSection6, MatchingTypesNamedTypedefStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {int A; int B;} AB_t;\n"
      "  AB_t x1;\n"
      "  AB_t x2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesSignedBitVector) {
  auto r = Parse(
      "module m;\n"
      "  typedef bit signed [7:0] BYTE;\n"
      "  BYTE b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

TEST(ParserSection6, MatchingTypesArrayTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef byte MEM_BYTES [256];\n"
      "  MEM_BYTES mem;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->modules[0]->items.size(), 2u);
}

// =========================================================================
// §6.22: Type compatibility — additional tests
// =========================================================================
TEST(ParserSection6, TypesMatchNamedSame) {
  // Two named types with the same name should match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "mytype";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "mytype";
  EXPECT_TRUE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesMatchNamedDifferent) {
  // Two named types with different names should not match.
  DataType a;
  a.kind = DataTypeKind::kNamed;
  a.type_name = "type_a";
  DataType b;
  b.kind = DataTypeKind::kNamed;
  b.type_name = "type_b";
  EXPECT_FALSE(TypesMatch(a, b));
}

TEST(ParserSection6, TypesEquivalentSameKind) {
  // §6.22.2: Same kind, same signedness, same state-ness -> equivalent.
  DataType a;
  a.kind = DataTypeKind::kInt;
  a.is_signed = true;
  DataType b;
  b.kind = DataTypeKind::kInt;
  b.is_signed = true;
  EXPECT_TRUE(TypesEquivalent(a, b));
}

}  // namespace
