// §6.18: User-defined types

#include <gtest/gtest.h>
#include <string>
#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string &src) {
  ParseResult result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// --- type_declaration ---
// Form 1: typedef data_type type_identifier { variable_dimension } ;
// Form 2: typedef ifc_port[sel].type_id type_id ; (not implemented)
// Form 3: typedef [ forward_type ] type_identifier ;
TEST(ParserA213, TypedefBasic) {
  auto r = Parse("module m; typedef logic [7:0] byte_t; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "byte_t");
}

// --- forward_type ---
// enum | struct | union | class | interface class
TEST(ParserA213, ForwardTypedefClass) {
  auto r = Parse("module m; typedef class my_class; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_class");
}

TEST(ParserA213, ForwardTypedefInterfaceClass) {
  auto r = Parse("module m; typedef interface class my_ifc; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->name, "my_ifc");
}

TEST(ParserA213, ForwardTypedefEnum) {
  // forward_type: enum
  auto r = Parse("module m; typedef enum color_e; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "color_e");
}

TEST(ParserA213, ForwardTypedefStruct) {
  // forward_type: struct
  auto r = Parse("module m; typedef struct my_struct; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_struct");
}

TEST(ParserA213, ForwardTypedefUnion) {
  // forward_type: union
  auto r = Parse("module m; typedef union my_union; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kTypedef);
  EXPECT_EQ(item->name, "my_union");
}

static bool ParseOk(const std::string &src) {
  SourceManager mgr;
  Arena arena;
  auto fid = mgr.AddFile("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

// data_declaration alternative: type_declaration (typedef)
TEST(ParserA28, TypedefInBlock) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    typedef int my_int_t;\n"
              "    my_int_t x = 5;\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
