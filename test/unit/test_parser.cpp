#include <gtest/gtest.h>

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

TEST(Parser, EmptyModule) {
  const auto* cu = parse("module empty; endmodule");
  ASSERT_NE(cu, nullptr);
  ASSERT_EQ(cu->modules.size(), 1);
  EXPECT_EQ(cu->modules[0]->name, "empty");
  EXPECT_TRUE(cu->modules[0]->items.empty());
}

TEST(Parser, ModuleWithInitialBlock) {
  const auto* cu = parse(
      "module hello;\n"
      "  initial $display(\"Hello\");\n"
      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_EQ(cu->modules.size(), 1);
  ASSERT_EQ(cu->modules[0]->items.size(), 1);
  EXPECT_EQ(cu->modules[0]->items[0]->kind, ModuleItemKind::InitialBlock);
}

TEST(Parser, ModuleWithPorts) {
  const auto* cu = parse(
      "module mux(input logic a, input logic b, input logic sel, output logic "
      "y);\n"
      "  assign y = sel ? b : a;\n"
      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  auto* mod = cu->modules[0];
  ASSERT_EQ(mod->ports.size(), 4);
  EXPECT_EQ(mod->ports[0].direction, Direction::Input);
  EXPECT_EQ(mod->ports[0].name, "a");
  EXPECT_EQ(mod->ports[3].direction, Direction::Output);
  EXPECT_EQ(mod->ports[3].name, "y");
}

TEST(Parser, ContinuousAssignment) {
  const auto* cu = parse(
      "module top;\n"
      "  logic a, b;\n"
      "  assign a = b;\n"
      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  bool found_assign = false;
  for (auto* item : cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::ContAssign) {
      found_assign = true;
    }
  }
  EXPECT_TRUE(found_assign);
}

TEST(Parser, AlwaysFFBlock) {
  const auto* cu = parse(
      "module counter(input logic clk, rst);\n"
      "  logic [7:0] count;\n"
      "  always_ff @(posedge clk or posedge rst)\n"
      "    if (rst) count <= '0;\n"
      "    else count <= count + 1;\n"
      "endmodule\n");
  ASSERT_NE(cu, nullptr);
  auto* mod = cu->modules[0];
  bool found_ff = false;
  for (auto* item : mod->items) {
    if (item->kind == ModuleItemKind::AlwaysBlock &&
        item->always_kind == AlwaysKind::AlwaysFF) {
      found_ff = true;
    }
  }
  EXPECT_TRUE(found_ff);
}

TEST(Parser, ExpressionPrecedence) {
  const auto* cu = parse(
      "module expr;\n"
      "  logic a;\n"
      "  assign a = 1 + 2 * 3;\n"
      "endmodule\n");
  ASSERT_NE(cu, nullptr);
}

TEST(Parser, MultipleModules) {
  const auto* cu = parse(
      "module a; endmodule\n"
      "module b; endmodule\n"
      "module c; endmodule\n");
  ASSERT_NE(cu, nullptr);
  ASSERT_EQ(cu->modules.size(), 3);
  EXPECT_EQ(cu->modules[0]->name, "a");
  EXPECT_EQ(cu->modules[1]->name, "b");
  EXPECT_EQ(cu->modules[2]->name, "c");
}
