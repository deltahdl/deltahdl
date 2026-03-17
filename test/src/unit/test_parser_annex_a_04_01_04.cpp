#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(CheckerInstantiationGrammar, CheckerInstOrderedPorts) {
  auto r = Parse(
      "checker my_chk(input logic a, input logic b, input logic c);\n"
      "endchecker\n"
      "module m; my_chk u0(a, b, c); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_ports.size(), 3u);
}

TEST(CheckerInstantiationGrammar, CheckerInstNamedPorts) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(clk), .rst(rst)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

TEST(CheckerInstantiationGrammar, CheckerInstNamedPortNoParens) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk, .rst); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_EQ(item->inst_ports.size(), 2u);
  EXPECT_EQ(item->inst_ports[0].first, "clk");
  EXPECT_EQ(item->inst_ports[1].first, "rst");
}

TEST(CheckerInstantiationGrammar, BasicCheckerInst) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic data);\n"
      "endchecker\n"
      "module m; my_chk u0(.clk(clk), .data(data)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(CheckerInstantiationGrammar, CheckerInstWildcardPort) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_TRUE(item->inst_wildcard);
}

TEST(CheckerInstantiationGrammar, CheckerInstEmptyPorts) {
  auto r = Parse(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; my_chk u0(); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_TRUE(item->inst_ports.empty());
}

TEST(CheckerInstantiationGrammar, CheckerInstArray) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0 [3:0] (.clk(clk)); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_NE(item->inst_range_left, nullptr);
  EXPECT_NE(item->inst_range_right, nullptr);
}

TEST(CheckerInstantiationGrammar, CheckerInstInsideChecker) {
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
  auto* inst = r.cu->checkers[1]->items[1];
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "inner_chk");
  EXPECT_EQ(inst->inst_name, "u0");
}

TEST(CheckerInstantiationGrammar, CheckerInstantiatedInModule) {
  auto r = Parse(R"(
    checker my_checker(input logic clk, input logic data);
    endchecker

    module top;
      logic clk, data;
      my_checker chk_inst(.clk(clk), .data(data));
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  auto* inst = r.cu->modules[0]->items[0];
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "my_checker");
  EXPECT_EQ(inst->inst_name, "chk_inst");
}

TEST(CheckerInstantiationGrammar, CheckerInstantiationPositional) {
  auto r = Parse(R"(
    checker mutex(logic [31:0] sig, event clock, output bit failure);
      assert property (@clock $onehot0(sig))
        failure = 1'b0; else failure = 1'b1;
    endchecker
    module m(wire [31:0] bus, logic clk);
      logic res;
      mutex check_bus(bus, posedge clk, res);
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

TEST(CheckerInstantiationGrammar, CheckerInstantiationNamed) {
  auto r = Parse(R"(
    checker my_check(input logic clk, input logic data);
    endchecker
    module m;
      logic clk, data;
      my_check inst(.clk(clk), .data(data));
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.cu->modules[0]->items.empty());
}

TEST(CheckerInstantiationGrammar, CheckerInstantiationInAlwaysBlock) {
  auto r = Parse(R"(
    checker c1(event clk, logic [7:0] a, b);
      logic [7:0] sum;
      always_ff @(clk) begin
        sum <= a + 1'b1;
      end
    endchecker
    module m(input logic clk, logic [7:0] in1, in2);
      always @(posedge clk) begin
        c1 check_inside(posedge clk, in1, in2);
      end
    endmodule
  )");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->checkers.size(), 1u);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(CheckerInstantiationGrammar, CheckerInstMixedNamedAndWildcard) {
  auto r = Parse(
      "checker my_chk(input logic clk, input logic rst, input logic en);\n"
      "endchecker\n"
      "module m;\n"
      "  logic clk, rst, en;\n"
      "  my_chk u0(.clk(clk), .*);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_TRUE(item->inst_wildcard);
  EXPECT_FALSE(item->inst_ports.empty());
}

TEST(CheckerInstantiationGrammar, CheckerInstInGenerateBlock) {
  auto r = Parse(
      "checker my_chk(input logic sig);\n"
      "endchecker\n"
      "module m;\n"
      "  logic sig;\n"
      "  if (1) begin : gen\n"
      "    my_chk u0(.sig(sig));\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(CheckerInstantiationGrammar, PackageScopedCheckerInst) {
  auto r = Parse(
      "package pkg;\n"
      "  checker my_chk(input logic clk);\n"
      "  endchecker\n"
      "endpackage\n"
      "module m;\n"
      "  logic clk;\n"
      "  pkg::my_chk u0(.clk(clk));\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_scope, "pkg");
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_EQ(item->inst_name, "u0");
}

TEST(CheckerInstantiationGrammar, Error_MissingSemicolon) {
  EXPECT_FALSE(ParseOk(
      "checker my_chk;\n"
      "endchecker\n"
      "module m; my_chk u0() endmodule\n"));
}

}  // namespace
