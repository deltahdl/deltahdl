#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

struct ParseResult6e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit *cu = nullptr;
  bool has_errors = false;
};

static ParseResult6e Parse(const std::string &src) {
  ParseResult6e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
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

static ModuleItem *FindNettypeDecl(ParseResult6e &r,
                                   std::string_view name = "") {
  if (!r.cu)
    return nullptr;
  for (auto *mod : r.cu->modules) {
    for (auto *item : mod->items) {
      if (item->kind == ModuleItemKind::kNettypeDecl) {
        if (name.empty() || item->name == name)
          return item;
      }
    }
  }
  return nullptr;
}

// =============================================================================
// LRM section 6.6.7 -- User-defined nettypes
// =============================================================================

// §6.6.7: Basic nettype declaration with a simple built-in data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithIntType) {
  auto r = Parse("module m;\n"
                 "  nettype int mynet;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r);
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "mynet");
}

// §6.6.7: Nettype with logic data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithLogicType) {
  auto r = Parse("module m;\n"
                 "  nettype logic mylogic;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r);
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "mylogic");
}

// §6.6.7: Nettype with a packed vector type.
TEST(ParserSection6, Sec6_6_7_NettypeWithPackedVector) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nettype logic [7:0] byte_net;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype with a struct data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithStruct) {
  auto r = Parse("module m;\n"
                 "  typedef struct { real field1; bit field2; } T;\n"
                 "  nettype T wT;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r, "wT");
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "wT");
}

// §6.6.7: Nettype with resolution function — checks resolve func field.
TEST(ParserSection6, Sec6_6_7_NettypeWithResolveFuncName) {
  auto r = Parse("module m;\n"
                 "  typedef struct { real field1; bit field2; } T;\n"
                 "  nettype T wTsum with Tsum;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r, "wTsum");
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->nettype_resolve_func, "Tsum");
}

// §6.6.7: Nettype alias — declaring a new name for an existing nettype.
TEST(ParserSection6, Sec6_6_7_NettypeAlias) {
  auto r = Parse("module m;\n"
                 "  typedef real TR[5];\n"
                 "  nettype TR wTR;\n"
                 "  nettype wTR alias_net;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r, "alias_net");
  ASSERT_NE(nt, nullptr);
  EXPECT_EQ(nt->name, "alias_net");
}

// §6.6.7: Multiple nettypes in the same module.
TEST(ParserSection6, Sec6_6_7_MultipleNettypesInModule) {
  auto r = Parse("module m;\n"
                 "  typedef struct { real a; } A_t;\n"
                 "  typedef struct { int b; } B_t;\n"
                 "  nettype A_t netA;\n"
                 "  nettype B_t netB;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto *item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNettypeDecl)
      count++;
  }
  EXPECT_EQ(count, 2);
}

// §6.6.7: Nettype with real data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithRealType) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nettype real real_net;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype with shortreal data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithShortrealType) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nettype shortreal sr_net;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype used to declare a net variable.
TEST(ParserSection6, Sec6_6_7_NettypeUsedForNetDecl) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  typedef struct { real field1; bit field2; } T;\n"
                      "  nettype T wT;\n"
                      "  wT my_signal;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype used with resolution function and net declaration.
TEST(ParserSection6, Sec6_6_7_NettypeWithResolveAndNetDecl) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  typedef struct { real field1; bit field2; } T;\n"
                      "  nettype T wTsum with Tsum;\n"
                      "  wTsum bus;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype in a package scope.
TEST(ParserSection6, Sec6_6_7_NettypeInPackage) {
  auto r = Parse("package pkg;\n"
                 "  typedef real myreal;\n"
                 "  nettype myreal pkg_net;\n"
                 "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->packages.size(), 1u);
}

// §6.6.7: Nettype with byte type.
TEST(ParserSection6, Sec6_6_7_NettypeWithByteType) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nettype byte byte_net;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype with bit type.
TEST(ParserSection6, Sec6_6_7_NettypeWithBitType) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nettype bit bit_net;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype with longint type.
TEST(ParserSection6, Sec6_6_7_NettypeWithLongintType) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nettype longint long_net;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype with typedef'd type used as port type.
TEST(ParserSection6, Sec6_6_7_NettypeAsPortType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { logic [7:0] data; logic valid; } bus_t;\n"
              "  nettype bus_t bus_net;\n"
              "endmodule\n"
              "module top;\n"
              "  bus_t sig;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype with packed struct type.
TEST(ParserSection6, Sec6_6_7_NettypeWithPackedStruct) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  typedef struct packed { logic [3:0] hi; logic [3:0] lo; } nibble_t;\n"
      "  nettype nibble_t nibble_net;\n"
      "endmodule\n"));
}

// §6.6.7: Nettype with array typedef.
TEST(ParserSection6, Sec6_6_7_NettypeWithArrayTypedef) {
  auto r = Parse("module m;\n"
                 "  typedef real TR[5];\n"
                 "  nettype TR array_net;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r, "array_net");
  ASSERT_NE(nt, nullptr);
}

// §6.6.7: Nettype alias used to declare nets.
TEST(ParserSection6, Sec6_6_7_NettypeAliasForNetDecl) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  typedef real TR[5];\n"
                      "  nettype TR wTR;\n"
                      "  nettype wTR alias_net;\n"
                      "  alias_net sig;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype with resolution function — multiple drivers scenario.
TEST(ParserSection6, Sec6_6_7_NettypeResolveFuncMultipleDrivers) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  typedef struct { real val; } S;\n"
                      "  function S resolve_S(input S drivers[]);\n"
                      "    resolve_S = drivers[0];\n"
                      "  endfunction\n"
                      "  nettype S net_S with resolve_S;\n"
                      "endmodule\n"));
}

// §6.6.7: Multiple nettypes with different resolution functions.
TEST(ParserSection6, Sec6_6_7_DifferentResolveFuncs) {
  auto r = Parse("module m;\n"
                 "  typedef int IT;\n"
                 "  nettype IT netA with resolve_a;\n"
                 "  nettype IT netB with resolve_b;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt_a = FindNettypeDecl(r, "netA");
  auto *nt_b = FindNettypeDecl(r, "netB");
  ASSERT_NE(nt_a, nullptr);
  ASSERT_NE(nt_b, nullptr);
  EXPECT_EQ(nt_a->nettype_resolve_func, "resolve_a");
  EXPECT_EQ(nt_b->nettype_resolve_func, "resolve_b");
}

// §6.6.7: Nettype with no resolution function — empty resolve func field.
TEST(ParserSection6, Sec6_6_7_NettypeNoResolveFunc) {
  auto r = Parse("module m;\n"
                 "  nettype int plain_net;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r, "plain_net");
  ASSERT_NE(nt, nullptr);
  EXPECT_TRUE(nt->nettype_resolve_func.empty());
}

// §6.6.7: Nettype with shortint type.
TEST(ParserSection6, Sec6_6_7_NettypeWithShortintType) {
  EXPECT_TRUE(ParseOk("module m;\n"
                      "  nettype shortint si_net;\n"
                      "endmodule\n"));
}

// §6.6.7: Nettype coexisting with wire and other net declarations.
TEST(ParserSection6, Sec6_6_7_NettypeWithWireDecls) {
  auto r = Parse("module m;\n"
                 "  wire [7:0] w;\n"
                 "  nettype int custom_net;\n"
                 "  tri t;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_GE(r.cu->modules[0]->items.size(), 3u);
}

// §6.6.7: Nettype with named type from typedef.
TEST(ParserSection6, Sec6_6_7_NettypeWithNamedType) {
  auto r = Parse("module m;\n"
                 "  typedef logic [31:0] word_t;\n"
                 "  nettype word_t word_net;\n"
                 "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *nt = FindNettypeDecl(r, "word_net");
  ASSERT_NE(nt, nullptr);
}
