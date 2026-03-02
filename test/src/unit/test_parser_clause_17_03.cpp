// §17.3: Checker instantiation

#include "fixture_parser.h"

using namespace delta;

namespace {

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
  auto* item = r.cu->modules[0]->items[0];
  EXPECT_EQ(item->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(item->inst_module, "my_chk");
  EXPECT_EQ(item->inst_name, "u0");
}

// --- named_checker_port_connection: .* (wildcard) ---
TEST(ParserAnnexA0414, CheckerInstWildcardPort) {
  auto r = Parse(
      "checker my_chk(input logic clk);\n"
      "endchecker\n"
      "module m; my_chk u0(.*); endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* item = r.cu->modules[0]->items[0];
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
  auto* inst = r.cu->checkers[1]->items[1];
  EXPECT_EQ(inst->kind, ModuleItemKind::kModuleInst);
  EXPECT_EQ(inst->inst_module, "inner_chk");
  EXPECT_EQ(inst->inst_name, "u0");
}

using CheckerParseTest = ProgramTestParse;

static const ModuleItem* FindItemOfKind(const std::vector<ModuleItem*>& items,
                                        ModuleItemKind kind) {
  for (const auto* item : items) {
    if (item->kind == kind) return item;
  }
  return nullptr;
}

// =============================================================================
// §17.6 Checker instantiation
// =============================================================================
TEST_F(CheckerParseTest, CheckerInstantiatedInModule) {
  auto* unit = Parse(R"(
    checker my_checker(input logic clk, input logic data);
    endchecker

    module top;
      logic clk, data;
      my_checker chk_inst(.clk(clk), .data(data));
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  const auto* inst =
      FindItemOfKind(unit->modules[0]->items, ModuleItemKind::kModuleInst);
  ASSERT_NE(inst, nullptr);
  EXPECT_EQ(inst->inst_module, "my_checker");
  EXPECT_EQ(inst->inst_name, "chk_inst");
}

struct ParseResult16c {
  SourceManager mgr;
  Arena arena;
  CompilationUnit* cu = nullptr;
  bool has_errors = false;
};

static ParseResult16c Parse(const std::string& src) {
  ParseResult16c result;
  auto fid = result.mgr.AddFile("<test>", src);
  DiagEngine diag(result.mgr);
  Lexer lexer(result.mgr.FileContent(fid), fid, diag);
  Parser parser(lexer, result.arena, diag);
  result.cu = parser.Parse();
  result.has_errors = diag.HasErrors();
  return result;
}

using VerifyParseTest = ProgramTestParse;

// =============================================================================
// §17.4 Checker instantiation
// =============================================================================
TEST_F(VerifyParseTest, CheckerInstantiationPositional) {
  auto* unit = Parse(R"(
    checker mutex(logic [31:0] sig, event clock, output bit failure);
      assert property (@clock $onehot0(sig))
        failure = 1'b0; else failure = 1'b1;
    endchecker
    module m(wire [31:0] bus, logic clk);
      logic res;
      mutex check_bus(bus, posedge clk, res);
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(unit->modules[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerInstantiationNamed) {
  auto* unit = Parse(R"(
    checker my_check(input logic clk, input logic data);
    endchecker
    module m;
      logic clk, data;
      my_check inst(.clk(clk), .data(data));
    endmodule
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
  EXPECT_FALSE(unit->modules[0]->items.empty());
}

TEST_F(VerifyParseTest, CheckerInstantiationInAlwaysBlock) {
  auto* unit = Parse(R"(
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
  ASSERT_EQ(unit->checkers.size(), 1u);
  ASSERT_EQ(unit->modules.size(), 1u);
}

TEST_F(VerifyParseTest, CheckerNestedWithClocking) {
  auto* unit = Parse(R"(
    checker c1(bit fclk, bit a, bit b);
      default clocking @(posedge fclk); endclocking
      checker c2(bit bclk, bit x, bit y);
        default clocking @(posedge bclk); endclocking
        rand bit m, n;
        u1: assume property (x != m);
        u2: assume property (y != n);
      endchecker
      rand bit q, r;
      c2 B1(fclk, q + r, r);
      always_ff @(posedge fclk)
        r <= a || q;
      u3: assume property (a != q);
    endchecker
  )");
  ASSERT_EQ(unit->checkers.size(), 1u);
  EXPECT_EQ(unit->checkers[0]->name, "c1");
  EXPECT_FALSE(unit->checkers[0]->items.empty());
}

}  // namespace
