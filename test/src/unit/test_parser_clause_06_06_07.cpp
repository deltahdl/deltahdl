#include "elaborator/type_eval.h"
#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
static ModuleItem* FindNettypeDecl(ParseResult& r, std::string_view name = "") {
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
namespace {

TEST(NettypeParsing, NettypeWithIntType) {
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
TEST(NettypeParsing, NettypeDeclWithResolveFunc) {
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

TEST(NettypeParsing, NettypeWithStruct) {
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
TEST(NettypeParsing, NettypeDeclaration) {
  auto r = Parse(
      "module t;\n"
      "  nettype logic [7:0] mynet;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "mynet");
}

TEST(NettypeParsing, NettypeAlias) {
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

TEST(NettypeParsing, MultipleNettypesInModule) {
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

TEST(NettypeParsing, NettypeDeclWithScopedResolve) {
  auto r =
      Parse("module m; nettype logic my_net with pkg::resolve_fn; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->nettype_resolve_func, "resolve_fn");
}

TEST(NettypeParsing, NettypeInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef real myreal;\n"
      "  nettype myreal pkg_net;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->packages.size(), 1u);
}

TEST(NettypeParsing, NettypeWithArrayTypedef) {
  auto r = Parse(
      "module m;\n"
      "  typedef real TR[5];\n"
      "  nettype TR array_net;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r, "array_net");
  ASSERT_NE(nt, nullptr);
}

TEST(NettypeParsing, NettypeAliasForNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef real TR[5];\n"
              "  nettype TR wTR;\n"
              "  nettype wTR alias_net;\n"
              "  alias_net sig;\n"
              "endmodule\n"));
}

TEST(NettypeParsing, NettypeResolveFuncMultipleDrivers) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real val; } S;\n"
              "  function S resolve_S(input S drivers[]);\n"
              "    resolve_S = drivers[0];\n"
              "  endfunction\n"
              "  nettype S net_S with resolve_S;\n"
              "endmodule\n"));
}

TEST(NettypeParsing, DifferentResolveFuncs) {
  auto r = Parse(
      "module m;\n"
      "  typedef int IT;\n"
      "  nettype IT netA with resolve_a;\n"
      "  nettype IT netB with resolve_b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt_a = FindNettypeDecl(r, "netA");
  auto* nt_b = FindNettypeDecl(r, "netB");
  ASSERT_NE(nt_a, nullptr);
  ASSERT_NE(nt_b, nullptr);
  EXPECT_EQ(nt_a->nettype_resolve_func, "resolve_a");
  EXPECT_EQ(nt_b->nettype_resolve_func, "resolve_b");
}

TEST(NettypeParsing, NettypeNoResolveFunc) {
  auto r = Parse(
      "module m;\n"
      "  nettype int plain_net;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r, "plain_net");
  ASSERT_NE(nt, nullptr);
  EXPECT_TRUE(nt->nettype_resolve_func.empty());
}

// §6.6.7: an explicit data type is required for a user-defined nettype. A
// declaration carrying only a single identifier (a name with no preceding data
// type or source nettype) is not well formed and shall be rejected.
TEST(NettypeParsing, NettypeRequiresExplicitDataType) {
  EXPECT_FALSE(
      ParseOk("module m;\n"
              "  nettype mynet;\n"
              "endmodule\n"));
}

}  // namespace
