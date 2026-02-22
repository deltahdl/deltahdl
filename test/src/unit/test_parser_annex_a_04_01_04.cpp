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

RtlirDesign *Elaborate(const std::string &src, ElabFixture &f,
                       std::string_view top = "") {
  auto fid = f.mgr.AddFile("<test>", src);
  Lexer lexer(f.mgr.FileContent(fid), fid, f.diag);
  Parser parser(lexer, f.arena, f.diag);
  auto *cu = parser.Parse();
  Elaborator elab(f.arena, f.diag, cu);
  auto name = top.empty() ? cu->modules.back()->name : top;
  return elab.Elaborate(name);
}

}  // namespace

// =============================================================================
// A.4.1.4 -- Checker instantiation
//
// checker_instantiation ::=
//   ps_checker_identifier name_of_instance
//     ( [ list_of_checker_port_connections ] ) ;
//
// list_of_checker_port_connections ::=
//   ordered_checker_port_connection { , ordered_checker_port_connection }
//   | named_checker_port_connection { , named_checker_port_connection }
//
// ordered_checker_port_connection ::=
//   { attribute_instance } [ property_actual_arg ]
//
// named_checker_port_connection ::=
//   { attribute_instance } . formal_port_identifier
//     [ ( [ property_actual_arg ] ) ]
//   | { attribute_instance } . *
// =============================================================================

// --- checker_instantiation: basic named port connections ---

TEST(ParserAnnexA0414, BasicCheckerInst) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic data);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(clk), .data(data)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- ordered_checker_port_connection ---

TEST(ParserAnnexA0414, CheckerInstOrderedPorts) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic b, input logic c);\n"
      "endchecker\n"
      "module m; my_chk u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

// --- named_checker_port_connection: .port_identifier(property_actual_arg) ---

TEST(ParserAnnexA0414, CheckerInstNamedPorts) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(clk), .rst(rst)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// --- named_checker_port_connection: .port_identifier (no parentheses) ---

TEST(ParserAnnexA0414, CheckerInstNamedPortNoParens) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

// --- named_checker_port_connection: .* (wildcard) ---

TEST(ParserAnnexA0414, CheckerInstWildcardPort) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

// --- list_of_checker_port_connections: empty ---

TEST(ParserAnnexA0414, CheckerInstEmptyPorts) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; my_chk u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

// --- name_of_instance: with unpacked_dimension (instance array) ---

TEST(ParserAnnexA0414, CheckerInstArray) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0 [3:0] (.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto *item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

// --- checker_instantiation: inside another checker ---

TEST(ParserAnnexA0414, CheckerInstInsideChecker) {
  auto r = Parse(
      "checker inner_chk(input logic sig);\n"
      "endchecker\n"
      "checker outer_chk;\n"
      "  logic sig;\n"
      "  inner_chk u0(.sig(sig));\n"
      "endchecker\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 2u);
  ASSERT_GE(r.cu->checkers[1]->items.size(), 2u);
  auto *inst = r.cu->checkers[1]->items[1];
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "inner_chk");
  EXPECT_EQ(inst->inst_name, "u0");
}

// =============================================================================
// Elaboration tests -- checker instantiation resolved through elaborator
// =============================================================================

// --- Elaborator resolves checker instantiation within a module ---

TEST(ParserAnnexA0414, ElaborationCheckerInstInModule) {
  ElabFixture f;
  auto *design = Elaborate(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module top;\n"
      "  logic clk, rst;\n"
      "  my_chk u0(.clk(clk), .rst(rst));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_EQ(design->top_modules.size(), 1u);
  auto *top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "my_chk");
  EXPECT_EQ(top->children[0].inst_name, "u0");
  EXPECT_NE(top->children[0].resolved, nullptr);
}

// --- Elaborator resolves checker instantiation with port bindings ---

TEST(ParserAnnexA0414, ElaborationCheckerInstPortBindings) {
  ElabFixture f;
  auto *design = Elaborate(
      "checker simple_chk(input logic data);\n"
      "endchecker\n"
      "module top;\n"
      "  logic d;\n"
      "  simple_chk u0(.data(d));\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto *top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_GE(top->children[0].port_bindings.size(), 1u);
  EXPECT_EQ(top->children[0].port_bindings[0].port_name, "data");
}

// --- Elaborator resolves checker inside checker ---

TEST(ParserAnnexA0414, ElaborationCheckerInsideChecker) {
  ElabFixture f;
  auto *design = Elaborate(
      "checker inner_chk(input logic sig);\n"
      "endchecker\n"
      "checker outer_chk;\n"
      "  logic sig;\n"
      "  inner_chk u0(.sig(sig));\n"
      "endchecker\n"
      "module top;\n"
      "  outer_chk oi();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  auto *top = design->top_modules[0];
  ASSERT_GE(top->children.size(), 1u);
  EXPECT_EQ(top->children[0].module_name, "outer_chk");
  auto *outer = top->children[0].resolved;
  ASSERT_NE(outer, nullptr);
  ASSERT_GE(outer->children.size(), 1u);
  EXPECT_EQ(outer->children[0].module_name, "inner_chk");
  EXPECT_NE(outer->children[0].resolved, nullptr);
}
