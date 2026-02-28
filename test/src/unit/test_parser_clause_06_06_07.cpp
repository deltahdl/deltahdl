// §6.6.7: User-defined nettypes

#include "fixture_parser.h"
#include "elaborator/type_eval.h"
#include "helpers_parser_verify.h"

using namespace delta;

struct ParseResult6e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ModuleItem* FindNettypeDecl(ParseResult6e& r,
                                   std::string_view name = "") {
  if (!r.cu) return nullptr;
  for (auto* mod : r.cu->modules) {
    for (auto* item : mod->items) {
      if (item->kind == ModuleItemKind::kNettypeDecl) {
        if (name.empty() || item->name == name) return item;
      }
    }
  }
  return nullptr;
}

struct ParseResult6f {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6f Parse(const std::string& src) {
  ParseResult6f result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

namespace {

// =============================================================================
// LRM section 6.6.7 -- User-defined nettypes
// =============================================================================
// §6.6.7: Basic nettype declaration with a simple built-in data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithIntType) {
  auto r = Parse(
      "module m;\n"
      "  nettype int mynet;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r);
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "mynet");
}

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

TEST(ParserSection6, NettypeDeclWithResolveFunc) {
  // nettype data_type nettype_identifier with tf_identifier ;
  auto r = Parse(
      "module t;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wTsum with Tsum;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ModuleItem* nt = nullptr;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kNettypeDecl) {
      nt = it;
      break;
    }
  }
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "wTsum");
  EXPECT_EQ(nt->nettype_resolve_func, "Tsum");
}

// §6.6.7: Nettype with logic data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithLogicType) {
  auto r = Parse(
      "module m;\n"
      "  nettype logic mylogic;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r);
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "mylogic");
}

TEST(ParserSection6, NettypeDeclAlias) {
  // nettype nettype_identifier nettype_identifier ;  (alias form)
  auto r = Parse(
      "module t;\n"
      "  typedef real TR[5];\n"
      "  nettype TR wTR;\n"
      "  nettype wTR nettypeid2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  int nettype_count = 0;
  for (auto* it : items) {
    if (it->kind == ModuleItemKind::kNettypeDecl) nettype_count++;
  }
  EXPECT_GE(nettype_count, 2);
}

// §6.6.7: Nettype with a packed vector type.
TEST(ParserSection6, Sec6_6_7_NettypeWithPackedVector) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype logic [7:0] byte_net;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype with a struct data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithStruct) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wT;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r, "wT");
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "wT");
}

struct ParseResult616 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult616 Parse(const std::string& src) {
  ParseResult616 result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

TEST(Parser, NettypeDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "mynet");
}

// §6.6.7: Nettype with resolution function — checks resolve func field.
TEST(ParserSection6, Sec6_6_7_NettypeWithResolveFuncName) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { real field1; bit field2; } T;\n"
      "  nettype T wTsum with Tsum;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r, "wTsum");
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->nettype_resolve_func, "Tsum");
}

// §6.6.7: Nettype alias — declaring a new name for an existing nettype.
TEST(ParserSection6, Sec6_6_7_NettypeAlias) {
  auto r = Parse(
      "module m;\n"
      "  typedef real TR[5];\n"
      "  nettype TR wTR;\n"
      "  nettype wTR alias_net;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r, "alias_net");
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "alias_net");
}

TEST(Parser, NettypeWithResolutionFunction) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet with resolve_fn;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "mynet");
  EXPECT_EQ(item->nettype_resolve_func, "resolve_fn");
}

// §6.6.7: Multiple nettypes in the same module.
TEST(ParserSection6, Sec6_6_7_MultipleNettypesInModule) {
  auto r = Parse(
      "module m;\n"
      "  typedef struct { real a; } A_t;\n"
      "  typedef struct { int b; } B_t;\n"
      "  nettype A_t netA;\n"
      "  nettype B_t netB;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNettypeDecl) count++;
  }
  EXPECT_EQ(count, 2);
}

TEST(ParserA213, DataDeclNettypeDeclaration) {
  // nettype_declaration alternative
  auto r = Parse("module m; nettype logic my_net; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
}

// §6.6.7: Nettype with real data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithRealType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype real real_net;\n"
              "endmodule\n"));
}

}  // namespace
