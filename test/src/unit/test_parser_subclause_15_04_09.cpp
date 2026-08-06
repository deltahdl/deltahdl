#include "fixture_parser.h"

using namespace delta;

namespace {

TEST(MailboxParameterizedParser, ParameterizedDeclaration) {
  auto r = Parse(
      "module m;\n"
      "  mailbox #(string) m_box;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);

  auto& items = r.cu->modules[0]->items;
  ASSERT_FALSE(items.empty());
  EXPECT_EQ(items[0]->name, "m_box");
}

TEST(MailboxParameterizedParser, TypedefParameterizedMailbox) {
  auto r = Parse(
      "module m;\n"
      "  typedef mailbox #(string) s_mbox;\n"
      "  s_mbox sm;\n"
      "  initial begin\n"
      "    sm = new;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(MailboxParameterizedParser, UnparameterizedMailboxParses) {
  auto r = Parse(
      "module m;\n"
      "  mailbox mb;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

}  // namespace
