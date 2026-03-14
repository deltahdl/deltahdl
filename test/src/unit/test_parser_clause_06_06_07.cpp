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

TEST(DataTypeParsing, NettypeWithIntType) {
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
TEST(DataTypeParsing, NettypeDeclWithResolveFunc) {
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

TEST(DataTypeParsing, NettypeWithLogicType) {
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

TEST(DataTypeParsing, NettypeDeclAlias) {
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

TEST(DataTypeParsing, NettypeWithPackedVector) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype logic [7:0] byte_net;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeWithStruct) {
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

TEST(DataTypeParsing, NettypeWithResolveFuncName) {
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

TEST(DataTypeParsing, NettypeAlias) {
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

TEST(DataTypeParsing, MultipleNettypesInModule) {
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

TEST(TypeDeclParsing, DataDeclNettypeDeclaration) {
  auto r = Parse("module m; nettype logic my_net; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
}

TEST(DataTypeParsing, NettypeWithRealType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype real real_net;\n"
              "endmodule\n"));
}

TEST(TypeDeclParsing, NettypeDeclBasic) {
  auto r = Parse("module m; nettype real my_real_net; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->name, "my_real_net");
}

TEST(DataTypeParsing, NettypeWithShortrealType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype shortreal sr_net;\n"
              "endmodule\n"));
}

TEST(TypeDeclParsing, NettypeDeclWithResolve) {
  auto r = Parse("module m; nettype logic my_net with my_resolve; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->nettype_resolve_func, "my_resolve");
}

TEST(TypeDeclParsing, NettypeDeclWithScopedResolve) {
  auto r =
      Parse("module m; nettype logic my_net with pkg::resolve_fn; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNettypeDecl);
  EXPECT_EQ(item->nettype_resolve_func, "resolve_fn");
}

TEST(DataTypeParsing, NettypeInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef real myreal;\n"
      "  nettype myreal pkg_net;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->packages.size(), 1u);
}

TEST(DataTypeParsing, NettypeWithByteType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype byte byte_net;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeWithBitType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype bit bit_net;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeWithLongintType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype longint long_net;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeAsPortType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { logic [7:0] data; logic valid; } bus_t;\n"
              "  nettype bus_t bus_net;\n"
              "endmodule\n"
              "module top;\n"
              "  bus_t sig;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeWithPackedStruct) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } nibble_t;\n"
      "  nettype nibble_t nibble_net;\n"
      "endmodule\n"));
}

TEST(DataTypeParsing, NettypeWithArrayTypedef) {
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

TEST(DataTypeParsing, NettypeAliasForNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef real TR[5];\n"
              "  nettype TR wTR;\n"
              "  nettype wTR alias_net;\n"
              "  alias_net sig;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeResolveFuncMultipleDrivers) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real val; } S;\n"
              "  function S resolve_S(input S drivers[]);\n"
              "    resolve_S = drivers[0];\n"
              "  endfunction\n"
              "  nettype S net_S with resolve_S;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, DifferentResolveFuncs) {
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

TEST(DataTypeParsing, NettypeNoResolveFunc) {
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

TEST(DataTypeParsing, NettypeWithShortintType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype shortint si_net;\n"
              "endmodule\n"));
}

TEST(DataTypeParsing, NettypeWithWireDecls) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  nettype int custom_net;\n"
      "  tri t;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

TEST(DataTypeParsing, NettypeWithNamedType) {
  auto r = Parse(
      "module m;\n"
      "  typedef logic [31:0] word_t;\n"
      "  nettype word_t word_net;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* nt = FindNettypeDecl(r, "word_net");
  ASSERT_NE(nt, nullptr);
}

TEST(DataTypeParsing, NettypeWithResolveAndNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real field1; bit field2; } T;\n"
              "  nettype T wTsum with Tsum;\n"
              "  wTsum bus;\n"
              "endmodule\n"));
}

}  // namespace
