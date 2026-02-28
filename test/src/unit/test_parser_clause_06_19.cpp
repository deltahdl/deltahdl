// §6.19: Enumerations

#include "fixture_parser.h"

using namespace delta;

namespace {

// --- enum_base_type ---
// integer_atom_type [signing] | integer_vector_type [signing] [packed_dim]
// | type_identifier [packed_dimension]
TEST(ParserA221, EnumBaseAtomType) {
  auto r = Parse("module m; enum int {A, B} x; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
}

// --- enum_name_declaration ---
// enum_id [ [ integral_number [ : integral_number ] ] ] [ = const_expr ]
TEST(ParserA221, EnumNameBasic) {
  auto r = Parse("module m; enum {RED, GREEN, BLUE} color; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->data_type.enum_members.size(), 3u);
}

struct ParseResult90301 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
};

static ParseResult90301 Parse(const std::string& src) {
  ParseResult90301 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  return result;
}

// =============================================================================
// Section 8.25 -- Enums
// =============================================================================
// Anonymous enum variable declaration with member inspection.
TEST(ParserSection8, EnumAnonymousDeclMembers) {
  auto r = Parse(
      "module m;\n"
      "  enum {IDLE, RUNNING, DONE} state;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kEnum);
  EXPECT_EQ(item->name, "state");
  ASSERT_EQ(item->data_type.enum_members.size(), 3u);
  EXPECT_EQ(item->data_type.enum_members[0].name, "IDLE");
  EXPECT_EQ(item->data_type.enum_members[1].name, "RUNNING");
  EXPECT_EQ(item->data_type.enum_members[2].name, "DONE");
}

// Enum with explicit base type and value assignments.
TEST(ParserSection8, EnumExplicitBaseTypeValues) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  enum bit [3:0] {BRONZE = 4'h3, SILVER, GOLD = 4'h5}"
              " medal;\n"
              "endmodule\n"));
}

}  // namespace
