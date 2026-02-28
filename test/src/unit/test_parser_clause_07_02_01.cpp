// §7.2.1: Packed structures

#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(ParserAnnexA, A2TypedefStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct packed {\n"
      "    logic [7:0] addr;\n"
      "    logic [31:0] data;\n"
      "  } req_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kTypedef);
}

// struct_union [packed [signing]] { ... } {packed_dimension}
TEST(ParserA221, DataTypeStructPacked) {
  auto r = Parse(
      "module m;\n"
      "  struct packed signed { logic [7:0] a; logic [7:0] b; } pair;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_TRUE(item->data_type.is_signed);
}

struct ParseResult7e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult7e Parse(const std::string& src) {
  ParseResult7e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static ModuleItem* FirstItem(ParseResult7e& r) {
  if (!r.cu || r.cu->modules.empty() || r.cu->modules[0]->items.empty())
    return nullptr;
  return r.cu->modules[0]->items[0];
}

// =========================================================================
// LRM section 7.2.1 -- Packed structures
// =========================================================================
// --- Packed struct typedef with logic members of various widths ---
TEST(ParserSection7, Sec7_2_1_PackedTypedefLogicWidths) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    logic [15:0] addr;\n"
      "    logic [7:0] data;\n"
      "    logic valid;\n"
      "  } bus_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_FALSE(item->typedef_type.is_signed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 3u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "addr");
  EXPECT_EQ(item->typedef_type.struct_members[1].name, "data");
  EXPECT_EQ(item->typedef_type.struct_members[2].name, "valid");
}

// --- Packed struct typedef with bit members and packed dim checks ---
TEST(ParserSection7, Sec7_2_1_PackedTypedefBitMembers) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    bit [3:0] nibble_hi;\n"
      "    bit [3:0] nibble_lo;\n"
      "  } byte_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind, DataTypeKind::kBit);
  EXPECT_EQ(item->typedef_type.struct_members[1].type_kind, DataTypeKind::kBit);
  EXPECT_NE(item->typedef_type.struct_members[0].packed_dim_left, nullptr);
  EXPECT_NE(item->typedef_type.struct_members[0].packed_dim_right, nullptr);
}

// --- Packed struct with integer type members (byte, shortint, int, longint)
// ---
TEST(ParserSection7, Sec7_2_1_PackedIntegerTypes) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed {\n"
      "    byte a;\n"
      "    shortint b;\n"
      "    int c;\n"
      "    longint d;\n"
      "  } wide_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 4u);
  EXPECT_EQ(item->typedef_type.struct_members[0].type_kind,
            DataTypeKind::kByte);
  EXPECT_EQ(item->typedef_type.struct_members[1].type_kind,
            DataTypeKind::kShortint);
  EXPECT_EQ(item->typedef_type.struct_members[2].type_kind, DataTypeKind::kInt);
  EXPECT_EQ(item->typedef_type.struct_members[3].type_kind,
            DataTypeKind::kLongint);
}

// --- Packed struct signed typedef with member name verification ---
TEST(ParserSection7, Sec7_2_1_PackedSignedTypedef) {
  auto r = Parse(
      "module t;\n"
      "  typedef struct packed signed {\n"
      "    logic [15:0] real_part;\n"
      "    logic [15:0] imag_part;\n"
      "  } complex_t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_TRUE(item->typedef_type.is_packed);
  EXPECT_TRUE(item->typedef_type.is_signed);
  ASSERT_EQ(item->typedef_type.struct_members.size(), 2u);
  EXPECT_EQ(item->typedef_type.struct_members[0].name, "real_part");
  EXPECT_EQ(item->typedef_type.struct_members[1].name, "imag_part");
}

// --- Packed struct variable declaration (non-typedef, inline) ---
TEST(ParserSection7, Sec7_2_1_PackedVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  struct packed {\n"
      "    logic [7:0] tag;\n"
      "    logic [23:0] payload;\n"
      "  } pkt;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kStruct);
  EXPECT_TRUE(item->data_type.is_packed);
  EXPECT_EQ(item->name, "pkt");
  EXPECT_EQ(item->data_type.struct_members.size(), 2u);
}

}  // namespace
