// §16.12.14: Abort properties

#include "fixture_parser.h"

using namespace delta;


namespace {

// property_expr ::= accept_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_AcceptOn) {
  EXPECT_TRUE(ParseOk(
      "module m;\n"
      "  assert property (@(posedge clk) accept_on(done) req |-> ack);\n"
      "endmodule\n"));
}

// property_expr ::= reject_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_RejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (@(posedge clk) reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sync_accept_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_SyncAcceptOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_accept_on(done) req |-> ack);\n"
              "endmodule\n"));
}

// property_expr ::= sync_reject_on ( expression_or_dist ) property_expr
TEST(ParserA210, PropertyExpr_SyncRejectOn) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  assert property (\n"
              "    @(posedge clk) sync_reject_on(err) req |-> ack);\n"
              "endmodule\n"));
}

}  // namespace
