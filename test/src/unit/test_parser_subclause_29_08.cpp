#include <gtest/gtest.h>

#include <vector>

#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"

using namespace delta;

namespace {

std::vector<ModuleItem*> FindUdpInstances(ParseResult& r) {
  std::vector<ModuleItem*> out;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kUdpInst) out.push_back(item);
  }
  return out;
}

const char* udp_def =
    "primitive my_udp(output y, input a, input b);\n"
    "  table\n"
    "    0 0 : 0;\n"
    "    1 1 : 1;\n"
    "  endtable\n"
    "endprimitive\n";

TEST(UdpInstantiation, ParsesAllInstantiationComponents) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp (strong0, strong1) #(2, 3) u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  auto* u = insts[0];
  EXPECT_EQ(u->inst_module, "my_udp");
  EXPECT_EQ(u->drive_strength0, 4u);
  EXPECT_EQ(u->drive_strength1, 4u);
  ASSERT_NE(u->gate_delay, nullptr);
  EXPECT_EQ(u->gate_delay->int_val, 2u);
  ASSERT_NE(u->gate_delay_fall, nullptr);
  EXPECT_EQ(u->gate_delay_fall->int_val, 3u);
  EXPECT_EQ(u->gate_inst_name, "u1");
  ASSERT_EQ(u->gate_terminals.size(), 3u);
}

TEST(UdpInstantiation, OptionalInstanceName) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_TRUE(insts[0]->gate_inst_name.empty());
  EXPECT_EQ(insts[0]->gate_terminals.size(), 3u);
}

TEST(UdpInstantiation, ArrayOfInstances) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp u1 [3:0] (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_NE(insts[0]->inst_range_left, nullptr);
  EXPECT_NE(insts[0]->inst_range_right, nullptr);
}

TEST(UdpInstantiation, MultipleInstancesInOneStatement) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp u1 (y, a, b), u2 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 2u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
  EXPECT_EQ(insts[1]->gate_inst_name, "u2");
}

TEST(UdpInstantiation, SharedStrengthAndDelayAcrossInstances) {
  auto r =
      Parse(std::string(udp_def) +
            "module top;\n"
            "  my_udp (strong0, weak1) #(2, 3) u1 (y, a, b), u2 (y, a, b);\n"
            "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 2u);
  for (auto* u : insts) {
    EXPECT_EQ(u->drive_strength0, 4u);
    EXPECT_EQ(u->drive_strength1, 2u);
    ASSERT_NE(u->gate_delay, nullptr);
    EXPECT_EQ(u->gate_delay->int_val, 2u);
    ASSERT_NE(u->gate_delay_fall, nullptr);
    EXPECT_EQ(u->gate_delay_fall->int_val, 3u);
  }
}

TEST(UdpInstantiation, SingleDelayForm) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp #5 u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->int_val, 5u);
  EXPECT_EQ(insts[0]->gate_delay_fall, nullptr);
}

TEST(UdpInstantiation, ParameterValuedDelay) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  parameter p3 = 12;\n"
                 "  my_udp #p3 u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->kind, ExprKind::kIdentifier);
  EXPECT_EQ(insts[0]->gate_delay->text, "p3");
  EXPECT_EQ(insts[0]->gate_delay_fall, nullptr);
}

TEST(UdpInstantiation, RejectsThreeDelays) {
  auto r = Parse(std::string(udp_def) +
                 "module top;\n"
                 "  my_udp #(1, 2, 3) u1 (y, a, b);\n"
                 "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "UDP instantiation shall have at most two delays", 8, "29.8"));
}

TEST(UdpInstantiation, UdpDeclaredLaterTakesADelayWithoutParentheses) {
  auto r = Parse(
      "module top;\n"
      "  my_udp #5 u1 (y, a, b);\n"
      "endmodule\n" +
      std::string(udp_def));
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  ASSERT_NE(insts[0]->gate_delay, nullptr);
  EXPECT_EQ(insts[0]->gate_delay->int_val, 5u);
  EXPECT_EQ(insts[0]->gate_inst_name, "u1");
}

TEST(UdpInstantiation, UdpDeclaredLaterTakesADriveStrength) {
  auto r = Parse(
      "module top;\n"
      "  my_udp (strong0, weak1) u1 (y, a, b);\n"
      "endmodule\n" +
      std::string(udp_def));
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_EQ(insts[0]->drive_strength0, 4u);
  EXPECT_EQ(insts[0]->drive_strength1, 2u);
}

TEST(UdpInstantiation, UdpDeclaredLaterTakesAnUnnamedInstance) {
  auto r = Parse(
      "module top;\n"
      "  my_udp (y, a, b);\n"
      "endmodule\n" +
      std::string(udp_def));
  EXPECT_FALSE(r.has_errors);
  auto insts = FindUdpInstances(r);
  ASSERT_EQ(insts.size(), 1u);
  EXPECT_TRUE(insts[0]->gate_inst_name.empty());
  ASSERT_EQ(insts[0]->gate_terminals.size(), 3u);
}

}  // namespace
