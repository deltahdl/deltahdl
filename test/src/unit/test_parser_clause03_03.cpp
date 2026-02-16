#include <gtest/gtest.h>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"
#include "preprocessor/preprocessor.h"

using namespace delta;

struct ParseResult303 {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult303 Parse(const std::string& src) {
  ParseResult303 result;
  DiagEngine diag(result.mgr);
  auto fid = result.mgr.AddFile("<test>", src);
  Preprocessor preproc(result.mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = result.mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(result.mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

static bool ParseOk(const std::string& src) {
  SourceManager mgr;
  Arena arena;
  DiagEngine diag(mgr);
  auto fid = mgr.AddFile("<test>", src);
  Preprocessor preproc(mgr, diag, {});
  auto pp = preproc.Preprocess(fid);
  auto pp_fid = mgr.AddFile("<preprocessed>", pp);
  Lexer lexer(mgr.FileContent(pp_fid), pp_fid, diag);
  Parser parser(lexer, arena, diag);
  parser.Parse();
  return !diag.HasErrors();
}

static ModuleItem* FindItemByKind(ParseResult303& r, ModuleItemKind kind) {
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

static bool HasItemOfKind(const std::vector<ModuleItem*>& items,
                          ModuleItemKind kind) {
  for (const auto* item : items)
    if (item->kind == kind) return true;
  return false;
}

static bool HasAlwaysOfKind(const std::vector<ModuleItem*>& items,
                            AlwaysKind kind) {
  for (const auto* item : items)
    if (item->kind == ModuleItemKind::kAlwaysBlock && item->always_kind == kind)
      return true;
  return false;
}

// =============================================================================
// LRM §3.3 — Modules
// =============================================================================

// §3.3: "The basic building block in SystemVerilog is the module, enclosed
//        between the keywords module and endmodule."
TEST(ParserClause03, Cl3_3_ModuleEndLabel) {
  auto r = Parse(
      "module m;\n"
      "endmodule : m\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "m");
}

// §3.3 LRM mux2to1 example (verbatim, with always_comb procedural block).
TEST(ParserClause03, Cl3_3_Mux2to1LrmExample) {
  auto r = Parse(
      "module mux2to1 (input wire a, b, sel,\n"
      "                output logic y);\n"
      "  always_comb begin\n"
      "    if (sel) y = a;\n"
      "    else     y = b;\n"
      "  end\n"
      "endmodule: mux2to1\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_EQ(r.cu->modules[0]->name, "mux2to1");
  ASSERT_EQ(r.cu->modules[0]->ports.size(), 4u);
  EXPECT_EQ(r.cu->modules[0]->ports[0].name, "a");
  EXPECT_EQ(r.cu->modules[0]->ports[3].name, "y");
  auto* blk = FindItemByKind(r, ModuleItemKind::kAlwaysBlock);
  ASSERT_NE(blk, nullptr);
  EXPECT_EQ(blk->always_kind, AlwaysKind::kAlwaysComb);
}

// §3.3: Data declarations, constants, user-defined types, class definitions
TEST(ParserClause03, Cl3_3_ModuleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  wire [7:0] w;\n"
      "  logic [15:0] v;\n"
      "  struct packed { logic [3:0] a; logic [3:0] b; } s;\n"
      "  union packed { logic [7:0] x; logic [7:0] y; } u;\n"
      "  parameter WIDTH = 8;\n"
      "  localparam DEPTH = 16;\n"
      "  typedef logic [7:0] byte_t;\n"
      "  class my_class; int val; endclass\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kParamDecl));
  EXPECT_TRUE(HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTypedef));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kClassDecl));
  EXPECT_GE(r.cu->modules[0]->items.size(), 7u);
}

// §3.3: "Subroutine definitions" and "Procedural blocks"
TEST(ParserClause03, Cl3_3_SubroutinesAndProceduralBlocks) {
  auto r = Parse(
      "module m;\n"
      "  logic clk, a, b;\n"
      "  function int add(int a, int b); return a + b; endfunction\n"
      "  task display_val(input int x); $display(\"%d\", x); endtask\n"
      "  initial a = 0;\n"
      "  final $display(\"done\");\n"
      "  always @(posedge clk) a <= b;\n"
      "  always_comb b = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFunctionDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kTaskDecl));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kInitialBlock));
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[0]->items, ModuleItemKind::kFinalBlock));
  EXPECT_TRUE(HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlways));
  EXPECT_TRUE(
      HasAlwaysOfKind(r.cu->modules[0]->items, AlwaysKind::kAlwaysComb));
}

// §3.3: "Generate blocks"
TEST(ParserClause03, Cl3_3_GenerateBlocks) {
  EXPECT_TRUE(
      ParseOk("module m #(parameter N = 4) ();\n"
              "  genvar i;\n"
              "  generate\n"
              "    for (i = 0; i < N; i = i + 1) begin : gen_loop\n"
              "      logic [7:0] data;\n"
              "    end\n"
              "  endgenerate\n"
              "endmodule\n"));
}

// §3.3: "Specify blocks"
TEST(ParserClause03, Cl3_3_SpecifyBlock) {
  EXPECT_TRUE(
      ParseOk("module m (input a, output y);\n"
              "  assign y = a;\n"
              "  specify\n"
              "    (a => y) = 1.5;\n"
              "  endspecify\n"
              "endmodule\n"));
}

// §3.3: "Continuous assignments"
TEST(ParserClause03, Cl3_3_ContinuousAssignment) {
  auto r = Parse(
      "module m;\n"
      "  logic a, b, y;\n"
      "  assign y = a & b;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* ca = FindItemByKind(r, ModuleItemKind::kContAssign);
  ASSERT_NE(ca, nullptr);
}

// §3.3: "Instantiations of other modules, programs, interfaces, checkers,
//        and primitives"
TEST(ParserClause03, Cl3_3_DesignElementInstantiations) {
  auto r = Parse(
      "module child; endmodule\n"
      "module top;\n"
      "  logic sig;\n"
      "  child c0();\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 2u);
  // "top" is modules[1]; check it has the instantiation.
  EXPECT_TRUE(
      HasItemOfKind(r.cu->modules[1]->items, ModuleItemKind::kModuleInst));
}
