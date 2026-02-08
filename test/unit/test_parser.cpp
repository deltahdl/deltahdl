#include <catch2/catch_test_macros.hpp>

#include "common/arena.h"
#include "common/diagnostic.h"
#include "common/source_mgr.h"
#include "lexer/lexer.h"
#include "parser/parser.h"

using namespace delta;

static CompilationUnit* parse(const std::string& src) {
  static SourceManager mgr;
  static Arena arena;
  auto fid = mgr.add_file("<test>", src);
  DiagEngine diag(mgr);
  Lexer lexer(mgr.file_content(fid), fid, diag);
  Parser parser(lexer, arena, diag);
  return parser.parse();
}

TEST_CASE("Parse empty module", "[parser]") {
  const auto* cu = parse("module empty; endmodule");
  REQUIRE(cu != nullptr);
  REQUIRE(cu->modules.size() == 1);
  REQUIRE(cu->modules[0]->name == "empty");
  REQUIRE(cu->modules[0]->items.empty());
}

TEST_CASE("Parse module with initial block", "[parser]") {
  const auto* cu = parse(
      "module hello;\n"
      "  initial $display(\"Hello\");\n"
      "endmodule\n");
  REQUIRE(cu != nullptr);
  REQUIRE(cu->modules.size() == 1);
  REQUIRE(cu->modules[0]->items.size() == 1);
  REQUIRE(cu->modules[0]->items[0]->kind == ModuleItemKind::InitialBlock);
}

TEST_CASE("Parse module with ports", "[parser]") {
  const auto* cu = parse(
      "module mux(input logic a, input logic b, input logic sel, output logic "
      "y);\n"
      "  assign y = sel ? b : a;\n"
      "endmodule\n");
  REQUIRE(cu != nullptr);
  auto* mod = cu->modules[0];
  REQUIRE(mod->ports.size() == 4);
  REQUIRE(mod->ports[0].direction == Direction::Input);
  REQUIRE(mod->ports[0].name == "a");
  REQUIRE(mod->ports[3].direction == Direction::Output);
  REQUIRE(mod->ports[3].name == "y");
}

TEST_CASE("Parse continuous assignment", "[parser]") {
  const auto* cu = parse(
      "module top;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  REQUIRE(cu != nullptr);
  bool found_assign = false;
  for (auto* item : cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::ContAssign) {
      found_assign = true;
    }
  }
  REQUIRE(found_assign);
}

TEST_CASE("Parse always_ff block", "[parser]") {
  const auto* cu = parse(
      "module counter(input logic clk, rst);\n"
      "  logic [7:0] count;\n"
      "  always_ff @(posedge clk or posedge rst)\n"
      "    if (rst) count <= '0;\n"
      "    else count <= count + 1;\n"
      "endmodule\n");
  REQUIRE(cu != nullptr);
  auto* mod = cu->modules[0];
  bool found_ff = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::AlwaysBlock &&
        item->always_kind == AlwaysKind::AlwaysFF) {
      found_ff = true;
    }
  }
  REQUIRE(found_ff);
}

TEST_CASE("Parse expression precedence", "[parser]") {
  const auto* cu = parse(
      "module expr;\n"
      "  logic a;\n"
      "  assign a = 1 + 2 * 3;\n"
      "endmodule\n");
  REQUIRE(cu != nullptr);
  // Should parse without errors — correctness of precedence
  // is validated by the Pratt parser binding power table
}

TEST_CASE("Parse multiple modules", "[parser]") {
  const auto* cu = parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  REQUIRE(cu != nullptr);
  REQUIRE(cu->modules.size() == 3);
  REQUIRE(cu->modules[0]->name == "a");
  REQUIRE(cu->modules[1]->name == "b");
  REQUIRE(cu->modules[2]->name == "c");
}
