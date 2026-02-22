#include <gtest/gtest.h>

#include <string>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "elaboration/elaborator.h"
#include "elaboration/rtlir.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

namespace {

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

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign *Elaborate(const std::string &src, ElabFixture &f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

}  // namespace

// =============================================================================
// A.2.5 Declaration ranges
// =============================================================================

// ---------------------------------------------------------------------------
// unpacked_dimension ::= [ constant_range ] | [ constant_expression ]
// ---------------------------------------------------------------------------

TEST(ParserA25, UnpackedDimConstantRange) {
  auto r = Parse("module m; logic x [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kBinary);
  EXPECT_EQ(item->unpacked_dims[0]->op, TokenKind::kColon);
}

TEST(ParserA25, UnpackedDimConstantExpression) {
  auto r = Parse("module m; logic x [8]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(item->name, "x");
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->kind, ExprKind::kIntegerLiteral);
}

TEST(ParserA25, UnpackedDimMultiple) {
  auto r = Parse("module m; logic x [3:0][7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 2u);
}

TEST(ParserA25, UnpackedDimElaboratesRange) {
  ElabFixture f;
  auto *design = Elaborate("module m; logic x [3:0]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].unpacked_size, 4u);
  EXPECT_EQ(mod->variables[0].unpacked_lo, 0u);
  EXPECT_TRUE(mod->variables[0].is_descending);
}

TEST(ParserA25, UnpackedDimElaboratesSize) {
  ElabFixture f;
  auto *design = Elaborate("module m; logic x [8]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
}

// ---------------------------------------------------------------------------
// packed_dimension ::= [ constant_range ] | unsized_dimension
// Note 24: unsized_dimension only legal in DPI import declarations.
// ---------------------------------------------------------------------------

TEST(ParserA25, PackedDimConstantRange) {
  auto r = Parse("module m; logic [7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kVarDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_NE(item->data_type.packed_dim_right, nullptr);
}

TEST(ParserA25, PackedDimMultiple) {
  auto r = Parse("module m; logic [3:0][7:0] x; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  EXPECT_EQ(item->data_type.extra_packed_dims.size(), 1u);
}

TEST(ParserA25, PackedDimElaboratesWidth) {
  ElabFixture f;
  auto *design = Elaborate("module m; logic [7:0] x; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].name, "x");
  EXPECT_EQ(mod->variables[0].width, 8u);
}

// ---------------------------------------------------------------------------
// associative_dimension ::= [ data_type ] | [ * ]
// ---------------------------------------------------------------------------

TEST(ParserA25, AssocDimWildcard) {
  auto r = Parse("module m; int aa [*]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "*");
}

TEST(ParserA25, AssocDimBuiltinType) {
  auto r = Parse("module m; int aa [string]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "string");
}

TEST(ParserA25, AssocDimIntType) {
  auto r = Parse("module m; logic [7:0] aa [int]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "int");
}

TEST(ParserA25, AssocDimByteType) {
  auto r = Parse("module m; int aa [byte]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0]->text, "byte");
}

TEST(ParserA25, AssocDimElaboratesWildcard) {
  ElabFixture f;
  auto *design = Elaborate("module m; int aa [*]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
}

TEST(ParserA25, AssocDimElaboratesStringIndex) {
  ElabFixture f;
  auto *design = Elaborate("module m; int aa [string]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
  EXPECT_TRUE(mod->variables[0].is_string_index);
}

TEST(ParserA25, AssocDimElaboratesIndexWidth) {
  ElabFixture f;
  auto *design = Elaborate("module m; int aa [byte]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_assoc);
  EXPECT_EQ(mod->variables[0].assoc_index_width, 8u);
}

// ---------------------------------------------------------------------------
// variable_dimension ::= unsized_dimension | unpacked_dimension
//                       | associative_dimension | queue_dimension
// (This is a union production; each alternative is tested above/below.)
// ---------------------------------------------------------------------------

TEST(ParserA25, VarDimAllFourAlternatives) {
  auto r = Parse(
      "module m;\n"
      "  int d [];       \n"
      "  int u [3:0];    \n"
      "  int a [string]; \n"
      "  int q [$];      \n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto &items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 4u);
  // unsized_dimension: nullptr sentinel
  ASSERT_EQ(items[0]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[0]->unpacked_dims[0], nullptr);
  // unpacked_dimension: range
  ASSERT_EQ(items[1]->unpacked_dims.size(), 1u);
  ASSERT_NE(items[1]->unpacked_dims[0], nullptr);
  EXPECT_EQ(items[1]->unpacked_dims[0]->kind, ExprKind::kBinary);
  // associative_dimension: string type
  ASSERT_EQ(items[2]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[2]->unpacked_dims[0]->text, "string");
  // queue_dimension: $
  ASSERT_EQ(items[3]->unpacked_dims.size(), 1u);
  EXPECT_EQ(items[3]->unpacked_dims[0]->text, "$");
}

// ---------------------------------------------------------------------------
// queue_dimension ::= [ $ [ : constant_expression ] ]
// ---------------------------------------------------------------------------

TEST(ParserA25, QueueDimUnbounded) {
  auto r = Parse("module m; int q [$]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  EXPECT_EQ(item->unpacked_dims[0]->rhs, nullptr);
}

TEST(ParserA25, QueueDimBounded) {
  auto r = Parse("module m; int q [$:100]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  ASSERT_NE(item->unpacked_dims[0], nullptr);
  EXPECT_EQ(item->unpacked_dims[0]->text, "$");
  ASSERT_NE(item->unpacked_dims[0]->rhs, nullptr);
}

TEST(ParserA25, QueueDimElaboratesUnbounded) {
  ElabFixture f;
  auto *design = Elaborate("module m; int q [$]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, -1);
}

TEST(ParserA25, QueueDimElaboratesBounded) {
  ElabFixture f;
  auto *design = Elaborate("module m; int q [$:255]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_queue);
  EXPECT_EQ(mod->variables[0].queue_max_size, 256);
}

// ---------------------------------------------------------------------------
// unsized_dimension ::= [ ]
// ---------------------------------------------------------------------------

TEST(ParserA25, UnsizedDimDynamicArray) {
  auto r = Parse("module m; int d []; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
  EXPECT_EQ(item->unpacked_dims[0], nullptr);
}

TEST(ParserA25, UnsizedDimElaboratesDynamic) {
  ElabFixture f;
  auto *design = Elaborate("module m; int d []; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_dynamic);
}

TEST(ParserA25, UnsizedDimWithInitInferSize) {
  ElabFixture f;
  auto *design = Elaborate("module m; int d [] = '{1,2,3}; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_TRUE(mod->variables[0].is_dynamic);
  EXPECT_EQ(mod->variables[0].unpacked_size, 3u);
}

// ---------------------------------------------------------------------------
// Combined / edge cases
// ---------------------------------------------------------------------------

TEST(ParserA25, PackedAndUnpackedDims) {
  auto r = Parse("module m; logic [7:0] mem [0:255]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserA25, PackedAndUnpackedElaboration) {
  ElabFixture f;
  auto *design = Elaborate("module m; logic [7:0] mem [0:3]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].width, 8u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 4u);
}

TEST(ParserA25, NetWithUnpackedDim) {
  auto r = Parse("module m; wire [7:0] bus [0:3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

TEST(ParserA25, PortWithPackedDim) {
  auto r = Parse("module m(input logic [15:0] data); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 1u);
  ASSERT_NE(r.cu->modules[0]->ports[0].data_type.packed_dim_left, nullptr);
}

TEST(ParserA25, AscendingUnpackedRange) {
  ElabFixture f;
  auto *design = Elaborate("module m; logic x [0:7]; endmodule\n", f);
  ASSERT_NE(design, nullptr);
  auto *mod = design->top_modules[0];
  ASSERT_GE(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].unpacked_size, 8u);
  EXPECT_FALSE(mod->variables[0].is_descending);
}
