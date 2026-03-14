#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §15.4: mailbox declaration elaborates with class_type_name set.
TEST(MailboxElaborator, DeclarationSetsClassTypeName) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
}

// §15.4: multiple mailbox declarations each get correct class_type_name.
TEST(MailboxElaborator, MultipleMailboxDeclarations) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb1;\n"
      "  mailbox mb2;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 2u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
  EXPECT_EQ(mod->variables[1].class_type_name, "mailbox");
}

// §15.4: mailbox with initializer elaborates without error.
TEST(MailboxElaborator, DeclarationWithInitializer) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

// §15.4: mailbox does not require an explicit class declaration.
TEST(MailboxElaborator, BuiltInTypeWithoutClassDecl) {
  EXPECT_TRUE(ElabOk(
      "module m;\n"
      "  mailbox mb;\n"
      "endmodule\n"));
}

// §15.4: mailbox used in initial block with method calls elaborates.
TEST(MailboxElaborator, MethodCallsInInitialBlock) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb.put(42);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
