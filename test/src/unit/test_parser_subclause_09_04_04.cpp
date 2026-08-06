#include "fixture_parser.h"
#include "helpers_parser_verify.h"

using namespace delta;
namespace {

TEST(ProcessParsing, WaitSequenceTriggered) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(abc.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ProcessParsing, WaitSequenceTriggeredOr) {
  auto r = Parse(
      "module m;\n"
      "  sequence s1;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  sequence s2;\n"
      "    @(negedge clk) c ##1 d;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(s1.triggered || s2.triggered);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

TEST(ProcessTimingAndControlParsing, WaitSequenceTriggeredWithAction) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence req_ack;\n"
              "    @(posedge clk) req ##[1:5] ack;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    wait(req_ack.triggered);\n"
              "    $display(\"handshake complete\");\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ProcessTimingAndControlParsing, WaitTriggeredInLoop) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  sequence s;\n"
              "    @(posedge clk) a ##1 b;\n"
              "  endsequence\n"
              "  initial begin\n"
              "    forever begin\n"
              "      wait(s.triggered);\n"
              "      count = count + 1;\n"
              "      @(posedge clk);\n"
              "    end\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ProcessParsing, WaitSequenceTriggeredWithDirectBody) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b ##1 c;\n"
      "  endsequence\n"
      "  initial\n"
      "    wait(abc.triggered) $display(\"matched\");\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
  EXPECT_NE(stmt->body, nullptr);
}

TEST(ProcessParsing, WaitSequenceTriggeredNullBody) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial\n"
      "    wait(abc.triggered) ;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* stmt = FirstInitialStmt(r);
  ASSERT_NE(stmt, nullptr);
  EXPECT_EQ(stmt->kind, StmtKind::kWait);
}

TEST(ProcessParsing, WaitSequenceTriggeredIfCheck) {
  auto r = Parse(
      "module m;\n"
      "  sequence abc;\n"
      "    @(posedge clk) a ##1 b;\n"
      "  endsequence\n"
      "  initial begin\n"
      "    wait(abc.triggered);\n"
      "    if (abc.triggered) $display(\"ok\");\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
}

}  // namespace
