#include <gtest/gtest.h>

#include <string>

#include "fixture_simulator.h"

namespace {

std::string OutputOf(const std::string& src) {
  SimFixture f;
  return RunCapture(src, f);
}

std::string MailboxRun(const std::string& declaration,
                       const std::string& steps) {
  return OutputOf("module t;\n" + declaration +
                  "  int a = 4, b, r1, r2;\n"
                  "  initial begin\n" +
                  steps + "  end\nendmodule\n");
}

TEST(MailboxPrototypeRun, TryPutPlacesTheValueOfAnOperatorExpression) {
  EXPECT_EQ(MailboxRun("  mailbox mb = new(1);\n",
                       "    r1 = mb.try_put(a + 1);\n"
                       "    r2 = mb.try_put(a * 2);\n"
                       "    mb.get(b);\n"
                       "    $write(\"%0d %0d %0d %0d\", r1, r2, b, "
                       "mb.num());\n"),
            "1 0 5 0");
}

TEST(MailboxPrototypeRun, ActualsAreBoundByTheNamesOfTheirFormals) {
  EXPECT_EQ(MailboxRun("  mailbox mb = new(.bound(2));\n",
                       "    mb.put(.message(a));\n"
                       "    r1 = mb.try_put(.message(6));\n"
                       "    r2 = mb.try_put(.message(7));\n"
                       "    $write(\"%0d%0d\", r1, r2);\n"
                       "    mb.peek(.message(b));\n"
                       "    $write(\" %0d\", b);\n"
                       "    mb.get(.message(b));\n"
                       "    $write(\" %0d\", b);\n"
                       "    r1 = mb.try_peek(.message(b));\n"
                       "    $write(\" %0d\", b);\n"
                       "    b = 0;\n"
                       "    r2 = mb.try_get(.message(b));\n"
                       "    $write(\" %0d %0d%0d\", b, r1, r2);\n"),
            "10 4 4 6 6 11");
}

TEST(MailboxPrototypeRun, AnEmptyOrNamedParameterListNamesTheSameClass) {
  EXPECT_EQ(MailboxRun("  mailbox #() mb = new;\n"
                       "  mailbox #(.T(int)) pm = new;\n",
                       "    mb.put(a);\n"
                       "    pm.put(9);\n"
                       "    mb.get(r1);\n"
                       "    pm.get(r2);\n"
                       "    $write(\"%0d %0d\", r1, r2);\n"),
            "4 9");
}

TEST(MailboxPrototypeRun, TheIntResultsAreThirtyTwoBits) {
  EXPECT_EQ(MailboxRun("  mailbox mb = new;\n",
                       "    $write(\"%0d \", $bits(mb.num()));\n"
                       "    $write(\"%0d \", $bits(mb.try_put(a)));\n"
                       "    $write(\"%0d \", $bits(mb.try_get(a)));\n"
                       "    $write(\"%0d\", $bits(mb.try_peek(a)));\n"),
            "32 32 32 32");
}

TEST(MailboxPrototypeRun, DISABLED_TheResultOfNumIsSigned) {
  EXPECT_EQ(MailboxRun("  mailbox mb = new;\n",
                       "    $write(\"%0d \", mb.num() - 1);\n"
                       "    $write(\"%0d \", mb.num() - 1 < 0);\n"
                       "    $write(\"%0d\", mb.num() < -1);\n"),
            "-1 1 0");
}

TEST(MailboxPrototypeRun, DISABLED_TheResultsOfTheTryMethodsAreSigned) {
  EXPECT_EQ(MailboxRun("  mailbox mb = new;\n",
                       "    $write(\"%0d \", mb.try_get(b) < -1);\n"
                       "    $write(\"%0d \", mb.try_peek(b) - 1 < 0);\n"
                       "    $write(\"%0d\", mb.try_put(a) - 2 < 0);\n"),
            "0 1 1");
}

TEST(MailboxPrototypeRun, AClassExtendsAMailboxNamedThroughStd) {
  EXPECT_EQ(OutputOf("module t;\n"
                     "  class LogMbx extends std::mailbox;\n"
                     "    int sent;\n"
                     "    function new(int b = 0); super.new(b); sent = 0;"
                     " endfunction\n"
                     "    function void send(int x); void'(try_put(x)); sent++;"
                     " endfunction\n"
                     "  endclass\n"
                     "  class P extends std::mailbox #(int); endclass\n"
                     "  LogMbx m;\n"
                     "  P p;\n"
                     "  int v, w;\n"
                     "  initial begin\n"
                     "    m = new;\n"
                     "    m.send(6);\n"
                     "    m.send(7);\n"
                     "    m.get(v);\n"
                     "    p = new;\n"
                     "    void'(p.try_put(9));\n"
                     "    p.get(w);\n"
                     "    $write(\"%0d %0d %0d %0d\", m.sent, v, w, p.num());\n"
                     "  end\n"
                     "endmodule\n"),
            "2 6 9 0");
}

TEST(MailboxPrototypeRun, AProgramsMailboxPassesItsMessages) {
  EXPECT_EQ(OutputOf("program t;\n"
                     "  mailbox mb = new(1);\n"
                     "  int v;\n"
                     "  initial begin\n"
                     "    mb.put(8);\n"
                     "    $write(\"%0d\", mb.try_put(9));\n"
                     "    mb.get(v);\n"
                     "    $write(\" %0d\", v);\n"
                     "  end\n"
                     "endprogram\n"),
            "0 8");
}

TEST(MailboxPrototypeRun, AUnitsMailboxPassesItsMessages) {
  EXPECT_EQ(OutputOf("mailbox unit_mb = new(1);\n"
                     "module t;\n"
                     "  int v;\n"
                     "  initial begin\n"
                     "    unit_mb.put(3);\n"
                     "    $write(\"%0d\", unit_mb.try_put(5));\n"
                     "    unit_mb.get(v);\n"
                     "    $write(\" %0d\", v);\n"
                     "  end\n"
                     "endmodule\n"),
            "0 3");
}

TEST(MailboxPrototypeRun, AFunctionsForkRunsTheTasksOfAMailbox) {
  EXPECT_EQ(MailboxRun("  mailbox mb = new;\n"
                       "  function automatic int pass();\n"
                       "    fork\n"
                       "      begin\n"
                       "        mb.put(12);\n"
                       "        mb.peek(r1);\n"
                       "        mb.get(r2);\n"
                       "      end\n"
                       "    join_none\n"
                       "    return mb.num();\n"
                       "  endfunction\n",
                       "    b = pass();\n"
                       "    #1;\n"
                       "    $write(\"%0d %0d %0d %0d\", b, r1, r2, "
                       "mb.num());\n"),
            "0 12 12 0");
}

}  // namespace
