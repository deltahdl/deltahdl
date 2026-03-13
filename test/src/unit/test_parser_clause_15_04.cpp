#include "fixture_parser.h"

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// §15.4 Mailboxes — Parser coverage
// ---------------------------------------------------------------------------

// §15.4.1 new()

TEST(MailboxParser, DeclarationUnbounded) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_GE(r.cu->modules[0]->items.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, NewBounded) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mbx;\n"
      "  initial begin\n"
      "    mbx = new(10);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, NewExpression) {
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.2–8 Method calls

TEST(MailboxParser, AllMethodCalls) {
  // §15.4: put, get, peek, num, try_get, try_peek, try_put.
  auto r = Parse(
      "module m;\n"
      "  int val;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(val);\n"
      "    mb.peek(val);\n"
      "    val = mb.num();\n"
      "    val = mb.try_get(val);\n"
      "    val = mb.try_peek(val);\n"
      "    val = mb.try_put(99);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, TryPutInConditional) {
  // §15.4.4: try_put returns int, usable in conditions.
  auto r = Parse(
      "module m;\n"
      "  initial begin\n"
      "    if (mb.try_put(42)) begin\n"
      "      $display(\"sent\");\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, TryGetInConditional) {
  // §15.4.6: try_get returns int, usable in conditions.
  auto r = Parse(
      "module m;\n"
      "  int val;\n"
      "  initial begin\n"
      "    if (mb.try_get(val)) begin\n"
      "      $display(\"received %0d\", val);\n"
      "    end\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

// §15.4.9 Parameterized mailboxes

TEST(MailboxParser, ParameterizedString) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(string) m_box;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  ASSERT_FALSE(r.cu->modules[0]->items.empty());
  EXPECT_EQ(r.cu->modules[0]->items[0]->name, "m_box");
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, ParameterizedNewString) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(string) sm;\n"
      "  initial begin\n"
      "    sm = new;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, ParameterizedNewBounded) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mbx;\n"
      "  initial begin\n"
      "    mbx = new(5);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, ParameterizedPutGet) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mbx;\n"
      "  initial begin\n"
      "    mbx = new();\n"
      "    mbx.put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, ParameterizedAllMethods) {
  // §15.4.9: Same methods as dynamic mailboxes.
  auto r = Parse(
      "module m;\n"
      "  mailbox #(int) mb = new();\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParser, MultipleDeclarations) {
  auto r = Parse(
      "module m;\n"
      "  mailbox m1 = new();\n"
      "  mailbox #(int) m2 = new(5);\n"
      "  initial begin\n"
      "    m1.put(1);\n"
      "    m2.put(2);\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
