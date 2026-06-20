#include "fixture_elaborator.h"

using namespace delta;

namespace {

TEST(MailboxParameterizedElaborator, ParameterizedIntDeclaration) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
}

TEST(MailboxParameterizedElaborator, ParameterizedStringWithNew) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox #(string) mb = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(MailboxParameterizedElaborator, ParameterizedWithMethodCalls) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox #(int) mb;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "    mb.get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
