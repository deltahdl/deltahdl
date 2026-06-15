// IEEE 1800-2023 Annex G.4 (Std package -- Mailbox).
//
// Section G.4 presents the prototype of the built-in `mailbox` class that the
// std package provides; its semantics are owned by clause 15.4. The prototype
// is:
//
//   class mailbox #(type T = dynamic_singular_type);
//     function new(int bound = 0);
//     function int num();
//     task put( T message);
//     function int try_put( T message);
//     task get( ref T message );
//     function int try_get( ref T message );
//     task peek( ref T message );
//     function int try_peek( ref T message );
//   endclass
//
// These tests observe the elaborator providing that prototype out of the std
// package: `mailbox` resolves as a built-in class without any user
// `class mailbox` definition (Elaborator::RegisterCuScopeItems registers the
// std-package class name), and each prototype method elaborates at the call
// site, including the documented default new() argument omitted.

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// The std package supplies the class name; no user declaration is required.
TEST(MailboxStdPackageElaborator, BuiltInClassNeedsNoUserDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mbx;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
}

// new() with the bound argument omitted (prototype default 0).
TEST(MailboxStdPackageElaborator, NewWithDefaultBound) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mbx = new();\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
  EXPECT_NE(mod->variables[0].init_expr, nullptr);
}

// The full prototype surface: num / put / try_put / get / try_get / peek /
// try_peek each elaborate at the call site.
TEST(MailboxStdPackageElaborator, PrototypeMethodsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mbx = new();\n"
      "  int msg;\n"
      "  int got;\n"
      "  initial begin\n"
      "    got = mbx.num();\n"
      "    mbx.put(msg);\n"
      "    got = mbx.try_put(msg);\n"
      "    mbx.get(msg);\n"
      "    got = mbx.try_get(msg);\n"
      "    mbx.peek(msg);\n"
      "    got = mbx.try_peek(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// new() accepts an explicit bound, matching the `int bound` formal in the
// prototype constructor.
TEST(MailboxStdPackageElaborator, NewWithExplicitBound) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mbx = new(4);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
  auto* mod = design->top_modules[0];
  ASSERT_EQ(mod->variables.size(), 1u);
  EXPECT_EQ(mod->variables[0].class_type_name, "mailbox");
}

// The prototype's new() constructor also applies when the handle is built
// procedurally after declaration, then driven through the prototype methods.
TEST(MailboxStdPackageElaborator, DeferredConstructionAndUse) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mbx;\n"
      "  int msg;\n"
      "  initial begin\n"
      "    mbx = new(2);\n"
      "    mbx.put(msg);\n"
      "    mbx.get(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// num() and try_get() are `function int`: their value feeds an expression
// context (here an if-condition), and the elaborator accepts the
// value-returning prototype methods there.
TEST(MailboxStdPackageElaborator, ValueReturningMethodsUsableInExpression) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  mailbox mbx = new();\n"
      "  int msg;\n"
      "  initial begin\n"
      "    if (mbx.num() == 0) mbx.put(msg);\n"
      "    if (mbx.try_get(msg)) mbx.put(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
