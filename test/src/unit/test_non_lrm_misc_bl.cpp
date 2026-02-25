// Non-LRM tests

#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

// --- Test helpers ---
struct ParseResult {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

ParseResult Parse(const std::string& src) {
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

// =========================================================================
// §6.12: Realtime type — alias for real
// =========================================================================
TEST(ParserSection6, RealtimeWithInit) {
  // §6.12: realtime is equivalent to real for simulation.
  auto r = Parse(
      "module t;\n"
      "  realtime ts = 100.0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kRealtime);
  ASSERT_NE(item->init_expr, nullptr);
}

TEST(ParserSection6, RealInFunction) {
  // §6.12: real used as function return type.
  auto r = Parse(
      "module t;\n"
      "  function real compute();\n"
      "    return 1.5;\n"
      "  endfunction\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kFunctionDecl);
  EXPECT_EQ(item->return_type.kind, DataTypeKind::kReal);
}

// =========================================================================
// §6.16: String in block scope
// =========================================================================
TEST(ParserSection6, StringBlockDecl) {
  // §6.16: string declared inside an initial block.
  auto r = Parse(
      "module t;\n"
      "  initial begin\n"
      "    string msg;\n"
      "    msg = \"test\";\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kVarDecl);
  EXPECT_EQ(stmt->var_decl_type.kind, DataTypeKind::kString);
}

TEST(ParserSection6, StringFunctionArg) {
  // §6.16: string as a function argument type.
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  function void print_msg(string s);\n"
              "  endfunction\n"
              "endmodule\n"));
}

// =========================================================================
// §6.20: Constants — const variable
// =========================================================================
TEST(ParserSection6, ConstRealDecl) {
  // §6.20.6: const can qualify a real variable.
  auto r = Parse(
      "module t;\n"
      "  const real PI = 3.14159;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kReal);
  EXPECT_TRUE(item->data_type.is_const);
}

TEST(ParserSection6, ConstStringDecl) {
  // §6.20.6: const string declaration.
  auto r = Parse(
      "module t;\n"
      "  const string GREETING = \"Hi\";\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kString);
  EXPECT_TRUE(item->data_type.is_const);
}

// =========================================================================
// §6.22: Cast compatibility
// =========================================================================
TEST(ParserSection6, CastCompatibleRealToIntType) {
  // §6.22.4: real and int are cast compatible.
  DataType a;
  a.kind = DataTypeKind::kReal;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

TEST(ParserSection6, CastCompatibleEnumToInt) {
  // §6.22.4: enum and int are cast compatible.
  DataType a;
  a.kind = DataTypeKind::kEnum;
  DataType b;
  b.kind = DataTypeKind::kInt;
  EXPECT_TRUE(IsCastCompatible(a, b));
}

struct ParseResult6e {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult6e Parse(const std::string& src) {
  ParseResult6e result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

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

// §6.6.7: Nettype with real data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithRealType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype real real_net;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype with shortreal data type.
TEST(ParserSection6, Sec6_6_7_NettypeWithShortrealType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype shortreal sr_net;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype used to declare a net variable.
TEST(ParserSection6, Sec6_6_7_NettypeUsedForNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real field1; bit field2; } T;\n"
              "  nettype T wT;\n"
              "  wT my_signal;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype used with resolution function and net declaration.
TEST(ParserSection6, Sec6_6_7_NettypeWithResolveAndNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real field1; bit field2; } T;\n"
              "  nettype T wTsum with Tsum;\n"
              "  wTsum bus;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype in a package scope.
TEST(ParserSection6, Sec6_6_7_NettypeInPackage) {
  auto r = Parse(
      "package pkg;\n"
      "  typedef real myreal;\n"
      "  nettype myreal pkg_net;\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->packages.size(), 1u);
}

// §6.6.7: Nettype with byte type.
TEST(ParserSection6, Sec6_6_7_NettypeWithByteType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype byte byte_net;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype with bit type.
TEST(ParserSection6, Sec6_6_7_NettypeWithBitType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype bit bit_net;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype with longint type.
TEST(ParserSection6, Sec6_6_7_NettypeWithLongintType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
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

// §6.6.7: Nettype alias used to declare nets.
TEST(ParserSection6, Sec6_6_7_NettypeAliasForNetDecl) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef real TR[5];\n"
              "  nettype TR wTR;\n"
              "  nettype wTR alias_net;\n"
              "  alias_net sig;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype with resolution function — multiple drivers scenario.
TEST(ParserSection6, Sec6_6_7_NettypeResolveFuncMultipleDrivers) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  typedef struct { real val; } S;\n"
              "  function S resolve_S(input S drivers[]);\n"
              "    resolve_S = drivers[0];\n"
              "  endfunction\n"
              "  nettype S net_S with resolve_S;\n"
              "endmodule\n"));
}

// §6.6.7: Multiple nettypes with different resolution functions.
TEST(ParserSection6, Sec6_6_7_DifferentResolveFuncs) {
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

// §6.6.7: Nettype with no resolution function — empty resolve func field.
TEST(ParserSection6, Sec6_6_7_NettypeNoResolveFunc) {
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

// §6.6.7: Nettype with shortint type.
TEST(ParserSection6, Sec6_6_7_NettypeWithShortintType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  nettype shortint si_net;\n"
              "endmodule\n"));
}

// §6.6.7: Nettype coexisting with wire and other net declarations.
TEST(ParserSection6, Sec6_6_7_NettypeWithWireDecls) {
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

// §6.6.7: Nettype with named type from typedef.
TEST(ParserSection6, Sec6_6_7_NettypeWithNamedType) {
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

static ModuleItem* FirstItem(ParseResult6f& r) {
  if (!r.cu || r.cu->modules.empty()) return nullptr;
  auto& items = r.cu->modules[0]->items;
  return items.empty() ? nullptr : items[0];
}

// =============================================================================
// LRM section 6.7.1 -- Net declarations with built-in net types
// =============================================================================
// §6.7.1: Wire with multiple variable names produces separate items.
TEST(ParserSection6, Sec6_7_1_WireMultipleNames) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->name, "a");
  EXPECT_EQ(items[1]->name, "b");
  EXPECT_EQ(items[2]->name, "c");
}

// §6.7.1: Each item from a multi-name wire declaration is a kNetDecl.
TEST(ParserSection6, Sec6_7_1_WireMultipleNamesAllNetDecl) {
  auto r = Parse(
      "module t;\n"
      "  wire a, b, c;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kWire);
    EXPECT_TRUE(item->data_type.is_net);
  }
}

// §6.7.1: Wire with initializer (implicit continuous assignment).
TEST(ParserSection6, Sec6_7_1_WireWithInitializer) {
  auto r = Parse(
      "module t;\n"
      "  wire w = 1'b1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  ASSERT_NE(item->init_expr, nullptr);
}

// §6.7.1: Tri net with range.
TEST(ParserSection6, Sec6_7_1_TriWithRange) {
  auto r = Parse(
      "module t;\n"
      "  tri [7:0] t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_right->int_val, 0u);
}

// §6.7.1: Wand net declaration.
TEST(ParserSection6, Sec6_7_1_WandDecl) {
  auto r = Parse(
      "module t;\n"
      "  wand w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWand);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

// §6.7.1: Wor net declaration.
TEST(ParserSection6, Sec6_7_1_WorDecl) {
  auto r = Parse(
      "module t;\n"
      "  wor w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWor);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "w");
}

// §6.7.1: Triand net declaration.
TEST(ParserSection6, Sec6_7_1_TriandDecl) {
  auto r = Parse(
      "module t;\n"
      "  triand ta;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTriand);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Trior net declaration.
TEST(ParserSection6, Sec6_7_1_TriorDecl) {
  auto r = Parse(
      "module t;\n"
      "  trior to1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrior);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Tri0 net declaration.
TEST(ParserSection6, Sec6_7_1_Tri0Decl) {
  auto r = Parse(
      "module t;\n"
      "  tri0 t0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri0);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Tri1 net declaration.
TEST(ParserSection6, Sec6_7_1_Tri1Decl) {
  auto r = Parse(
      "module t;\n"
      "  tri1 t1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri1);
  EXPECT_TRUE(item->data_type.is_net);
}

// §6.7.1: Supply0 net declaration.
TEST(ParserSection6, Sec6_7_1_Supply0Decl) {
  auto r = Parse(
      "module t;\n"
      "  supply0 gnd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "gnd");
}

// §6.7.1: Supply1 net declaration.
TEST(ParserSection6, Sec6_7_1_Supply1Decl) {
  auto r = Parse(
      "module t;\n"
      "  supply1 vdd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kSupply1);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "vdd");
}

// §6.7.1: Uwire net declaration.
TEST(ParserSection6, Sec6_7_1_UwireDecl) {
  auto r = Parse(
      "module t;\n"
      "  uwire uw;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kUwire);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "uw");
}

// §6.7.1: Net with signed qualifier.
TEST(ParserSection6, Sec6_7_1_WireSignedQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire signed [7:0] s;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
}

// §6.7.1: Net with vectored qualifier.
TEST(ParserSection6, Sec6_7_1_WireVectoredQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire vectored [7:0] v;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_vectored);
  EXPECT_EQ(item->name, "v");
}

// §6.7.1: Net with scalared qualifier.
TEST(ParserSection6, Sec6_7_1_WireScalaredQualifier) {
  auto r = Parse(
      "module t;\n"
      "  wire scalared [7:0] sc;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_scalared);
  EXPECT_EQ(item->name, "sc");
}

// §6.7.1: Wire with explicit bit type.
TEST(ParserSection6, Sec6_7_1_WireWithBitType) {
  auto r = Parse(
      "module t;\n"
      "  wire bit [3:0] b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
  EXPECT_EQ(item->name, "b");
}

// §6.7.1: Net with single delay value.
TEST(ParserSection6, Sec6_7_1_WireWithDelay) {
  auto r = Parse(
      "module t;\n"
      "  wire #5 w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §6.7.1: Net with two delays (rise, fall).
TEST(ParserSection6, Sec6_7_1_WireTwoDelays) {
  auto r = Parse(
      "module t;\n"
      "  wire #(3, 5) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 3u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 5u);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// §6.7.1: Net with three delays (rise, fall, turnoff).
TEST(ParserSection6, Sec6_7_1_WireThreeDelays) {
  auto r = Parse(
      "module t;\n"
      "  wire #(2, 4, 6) w;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 2u);
  ASSERT_NE(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_fall->int_val, 4u);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay_decay->int_val, 6u);
}

// §6.7.1: Multiple net declarations of different types in the same module.
TEST(ParserSection6, Sec6_7_1_MixedNetTypesInModule) {
  auto r = Parse(
      "module t;\n"
      "  wire w;\n"
      "  tri t1;\n"
      "  wand wa;\n"
      "  supply0 gnd;\n"
      "  supply1 vdd;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 5u);
  EXPECT_EQ(items[0]->data_type.kind, DataTypeKind::kWire);
  EXPECT_EQ(items[1]->data_type.kind, DataTypeKind::kTri);
  EXPECT_EQ(items[2]->data_type.kind, DataTypeKind::kWand);
  EXPECT_EQ(items[3]->data_type.kind, DataTypeKind::kSupply0);
  EXPECT_EQ(items[4]->data_type.kind, DataTypeKind::kSupply1);
}

// §6.7.1: Net declaration with unpacked dimension.
TEST(ParserSection6, Sec6_7_1_WireUnpackedDim) {
  auto r = Parse(
      "module t;\n"
      "  wire w [0:3];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_EQ(item->name, "w");
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// §6.7.1: Wire with both packed and unpacked dimensions.
TEST(ParserSection6, Sec6_7_1_WirePackedAndUnpackedDims) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] mem [0:255];\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 7u);
  EXPECT_FALSE(item->unpacked_dims.empty());
}

// §6.7.1: Net with drive strength (strong0, pull1).
TEST(ParserSection6, Sec6_7_1_WireDriveStrength) {
  auto r = Parse(
      "module t;\n"
      "  wire (strong0, pull1) w = 1'b0;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  // 4=strong, 3=pull (parser encoding)
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 3u);
}

// §6.7.1: Trireg with charge strength (medium).
TEST(ParserSection6, Sec6_7_1_TriregChargeStrengthMedium) {
  auto r = Parse(
      "module t;\n"
      "  trireg (medium) m1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTrireg);
  EXPECT_EQ(item->data_type.charge_strength, 2);
}

// §6.7.1: Net coexisting with variable declarations in the same module.
TEST(ParserSection6, Sec6_7_1_NetCoexistsWithVarDecl) {
  auto r = Parse(
      "module t;\n"
      "  wire [7:0] net_w;\n"
      "  logic [7:0] var_v;\n"
      "  int count;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(items[0]->data_type.is_net);
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[1]->data_type.is_net);
  EXPECT_EQ(items[2]->kind, ModuleItemKind::kVarDecl);
  EXPECT_FALSE(items[2]->data_type.is_net);
}

// §6.7.1: Wire with range and multiple names.
TEST(ParserSection6, Sec6_7_1_WireRangeMultipleNames) {
  auto r = Parse(
      "module t;\n"
      "  wire [3:0] x, y, z;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 3u);
  for (auto* item : items) {
    EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
    ASSERT_NE(item->data_type.packed_dim_left, nullptr);
    EXPECT_EQ(item->data_type.packed_dim_left->int_val, 3u);
  }
  EXPECT_EQ(items[0]->name, "x");
  EXPECT_EQ(items[1]->name, "y");
  EXPECT_EQ(items[2]->name, "z");
}

// §6.7.1: Tri net with signed qualifier and range.
TEST(ParserSection6, Sec6_7_1_TriSignedWithRange) {
  auto r = Parse(
      "module t;\n"
      "  tri signed [15:0] ts;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kTri);
  EXPECT_TRUE(item->data_type.is_signed);
  EXPECT_TRUE(item->data_type.is_net);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 15u);
}

// §6.7.1: Wand with range.
TEST(ParserSection6, Sec6_7_1_WandWithRange) {
  auto r = Parse(
      "module t;\n"
      "  wand [31:0] bus;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FirstItem(r);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kWand);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.packed_dim_left->int_val, 31u);
  EXPECT_EQ(item->name, "bus");
}

// §6.7.1: Supply0 with range.
TEST(ParserSection6, Sec6_7_1_Supply0WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply0 [3:0] gnd_bus;\n"
              "endmodule\n"));
}

// §6.7.1: Supply1 with range.
TEST(ParserSection6, Sec6_7_1_Supply1WithRange) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  supply1 [3:0] vdd_bus;\n"
              "endmodule\n"));
}

}  // namespace
