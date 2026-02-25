// §6.7.1: Net declarations with built-in net types

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

// =============================================================================
// A.2 -- Overview tests
// =============================================================================
TEST(ParserAnnexA, A2NetDeclWire) {
  auto r = Parse("module m; wire [3:0] w; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_EQ(r.cu->modules[0]->items[0]->kind, ModuleItemKind::kNetDecl);
}

// --- net_declaration ---
// Form 1: net_type [strength] [vectored|scalared] data_type_or_implicit
//          [delay3] list_of_net_decl_assignments ;
// Form 2: nettype_identifier [delay_control] list_of_net_decl_assignments ;
// Form 3: interconnect implicit_data_type [#delay]
//          net_identifier {unpacked_dim} [, ...] ;
TEST(ParserA213, NetDeclWireBasic) {
  auto r = Parse("module m; wire [7:0] data; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_TRUE(item->data_type.is_net);
}

TEST(ParserA213, NetDeclWithDriveStrength) {
  auto r = Parse("module m; wire (strong0, weak1) w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  EXPECT_NE(item->drive_strength0, 0);
}

TEST(ParserA213, NetDeclWithDelay) {
  auto r = Parse("module m; wire #5 w; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_NE(item->net_delay, nullptr);
}

TEST(ParserA213, NetDeclMultipleAssign) {
  auto r = Parse("module m; wire a, b, c; endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 3);
}

// --- Drive strength on different net types ---
TEST(ParserA222, DriveStrengthOnTri) {
  // drive_strength works on tri nets (not just wire)
  auto r = Parse(
      "module m;\n"
      "  tri (strong0, strong1) t;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 4u);
  EXPECT_EQ(item->drive_strength1, 4u);
}

TEST(ParserA222, DriveStrengthOnWand) {
  // drive_strength works on wand nets
  auto r = Parse(
      "module m;\n"
      "  wand (pull0, pull1) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->drive_strength0, 3u);  // pull0
  EXPECT_EQ(item->drive_strength1, 3u);  // pull1
}

bool ParseOk(const std::string& src) {
  auto r = Parse(src);
  return r.cu && !r.has_errors;
}

// delay_value: ps_identifier — parameter/specparam identifier as delay.
TEST(ParserA223, DelayValuePsIdentifier) {
  auto r = Parse(
      "module m;\n"
      "  parameter delay_val = 5;\n"
      "  wire #delay_val w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  // items[0] is the parameter, items[1] is the wire
  auto* item = r.cu->modules[0]->items[1];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kIdentifier);
}

// ---------------------------------------------------------------------------
// delay3 ::= # delay_value
//          | # ( mintypmax_expression
//                [, mintypmax_expression [, mintypmax_expression]] )
// ---------------------------------------------------------------------------
// --- delay3 on net declarations ---
// delay3: single value on net declaration (# delay_value form).
TEST(ParserA223, Delay3NetSingleValue) {
  auto r = Parse(
      "module m;\n"
      "  wire #5 w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->int_val, 5u);
  EXPECT_EQ(item->net_delay_fall, nullptr);
  EXPECT_EQ(item->net_delay_decay, nullptr);
}

// delay3: mintypmax expression in parenthesized form.
TEST(ParserA223, Delay3NetMintypmax) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1:2:3) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
}

// --- list_of_net_decl_assignments ---
// net_decl_assignment { , net_decl_assignment }
TEST(ParserA23, ListOfNetDeclAssignmentsSingle) {
  auto r = Parse("module m; wire [7:0] data; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_EQ(count, 1);
}

TEST(ParserA23, ListOfNetDeclAssignmentsMultiple) {
  auto r = Parse("module m; wire a, b, c; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 3);
}

TEST(ParserA23, ListOfNetDeclAssignmentsWithUnpackedDim) {
  auto r = Parse("module m; wire a [3:0], b [7:0]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  int count = 0;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kNetDecl) count++;
  }
  EXPECT_GE(count, 2);
}

struct ElabFixture {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag{mgr};
};

RtlirDesign* Elaborate(const std::string& src, ElabFixture& f) {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto* cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  return elab.Elaborate(cu->modules.back()->name);
}

TEST(ParserA25, NetWithUnpackedDim) {
  auto r = Parse("module m; wire [7:0] bus [0:3]; endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kNetDecl);
  ASSERT_NE(item->data_type.packed_dim_left, nullptr);
  ASSERT_EQ(item->unpacked_dims.size(), 1u);
}

}  // namespace
