#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_expr.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"

using namespace delta;

namespace {

TEST(MinTypMaxDelayParsing, GateDelaySingleSlot) {
  EXPECT_TRUE(
      ParseOk("module t;\n"
              "  wire a, b, c;\n"
              "  and #(2:3:4) g1(c, a, b);\n"
              "endmodule\n"));
}

TEST(MinTypMaxDelayParsing, ContAssignTripleFields) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(10:20:30) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* delay = r.cu->modules[0]->items[2]->assign_delay;
  ASSERT_NE(delay, nullptr);
  ASSERT_EQ(delay->kind, ExprKind::kMinTypMax);
  ASSERT_NE(delay->lhs, nullptr);
  ASSERT_NE(delay->condition, nullptr);
  ASSERT_NE(delay->rhs, nullptr);
  EXPECT_EQ(delay->lhs->int_val, 10u);
  EXPECT_EQ(delay->condition->int_val, 20u);
  EXPECT_EQ(delay->rhs->int_val, 30u);
}

TEST(MinTypMaxDelayParsing, GateDelayTwoSlots) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  wire a, b, c;\n"
              "  and #(1:2:3, 4:5:6) g1(c, a, b);\n"
              "endmodule\n"));
}

TEST(MinTypMaxDelayParsing, ProceduralDelayControl) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    #(1:2:3) a = 1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kDelay);
  EXPECT_NE(stmt->delay, nullptr);
  EXPECT_EQ(stmt->delay->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, NetDelaySingleSlot) {
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

TEST(MinTypMaxDelayParsing, NetDelayThreeSlotTriples) {
  auto r = Parse(
      "module m;\n"
      "  wire #(1:2:3, 4:5:6, 7:8:9) w;\n"
      "endmodule");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[0];
  ASSERT_NE(item->net_delay, nullptr);
  ASSERT_NE(item->net_delay_fall, nullptr);
  ASSERT_NE(item->net_delay_decay, nullptr);
  EXPECT_EQ(item->net_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->net_delay_fall->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->net_delay_decay->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, ContAssignDelayTwoSlotTriples) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(1:2:3, 4:5:6) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = r.cu->modules[0]->items[2];
  ASSERT_NE(item->assign_delay, nullptr);
  ASSERT_NE(item->assign_delay_fall, nullptr);
  EXPECT_EQ(item->assign_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->assign_delay_fall->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, MinExceedsTypAndMaxAccepted) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(10:5:3) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* delay = r.cu->modules[0]->items[2]->assign_delay;
  ASSERT_NE(delay, nullptr);
  ASSERT_EQ(delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(delay->lhs->int_val, 10u);
  EXPECT_EQ(delay->condition->int_val, 5u);
  EXPECT_EQ(delay->rhs->int_val, 3u);
}

TEST(MinTypMaxDelayParsing, IdentifierExpressionsInTriple) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  parameter min_hi = 95, typ_hi = 100, max_hi = 105;\n"
              "  wire y, a;\n"
              "  assign #(min_hi : typ_hi : max_hi) y = a;\n"
              "endmodule\n"));
}

TEST(MinTypMaxDelayParsing, GateThreeSlotTurnOffTriple) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a, ctrl;\n"
      "  bufif0 #(5:7:9, 8:10:12, 15:18:21) g1(y, a, ctrl);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleItem* item = nullptr;
  for (auto* it : r.cu->modules[0]->items) {
    if (it->kind == ModuleItemKind::kGateInst) item = it;
  }
  ASSERT_NE(item, nullptr);
  ASSERT_NE(item->gate_delay, nullptr);
  ASSERT_NE(item->gate_delay_fall, nullptr);
  ASSERT_NE(item->gate_delay_decay, nullptr);
  EXPECT_EQ(item->gate_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->gate_delay_fall->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(item->gate_delay_decay->kind, ExprKind::kMinTypMax);
}

TEST(MinTypMaxDelayParsing, IncompleteMinTypMaxIsRejected) {
  auto r = Parse(
      "module m;\n"
      "  wire y, a;\n"
      "  assign #(1:2) y = a;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(ReportedError(r.diags, "expected ':', got ')'", 3, "11.11"));
}

TEST(MinTypMaxDelayParsing, UdpInstanceDelayTriples) {
  auto r = Parse(
      "primitive my_udp(output y, input a, input b);\n"
      "  table\n"
      "    0 0 : 0;\n"
      "    1 1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "module top;\n"
      "  my_udp #(2:3:4, 5:6:7) u1(y, a, b);\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ModuleItem* inst = nullptr;
  for (auto* item : r.cu->modules[0]->items) {
    if (item->kind == ModuleItemKind::kUdpInst) inst = item;
  }
  ASSERT_NE(inst, nullptr);
  ASSERT_NE(inst->gate_delay, nullptr);
  ASSERT_NE(inst->gate_delay_fall, nullptr);
  EXPECT_EQ(inst->gate_delay->kind, ExprKind::kMinTypMax);
  EXPECT_EQ(inst->gate_delay_fall->kind, ExprKind::kMinTypMax);
}

}  // namespace
