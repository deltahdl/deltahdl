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

#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <string_view>
#include <vector>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

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

// §G.4: the prototype as src/elaborator/std_package.h writes it down -- the
// constructor new with its defaulted int bound, num taking nothing and
// returning int, the tasks put, get and peek and the int functions try_put,
// try_get and try_peek, each over one formal T message, by reference for the
// four that receive a message and by value for the two that send one -- over
// the type parameter T defaulting to dynamic_singular_type.
TEST(MailboxStdPackageElaborator, ThePrototypeIsWrittenDown) {
  const auto& prototype = MailboxPrototype();
  ASSERT_EQ(prototype.size(), 8u);
  EXPECT_EQ(prototype[0].name, "new");
  ASSERT_EQ(prototype[0].formals.size(), 1u);
  EXPECT_EQ(prototype[0].formals[0].name, "bound");
  EXPECT_TRUE(prototype[0].formals[0].has_default);
  EXPECT_EQ(prototype[1].name, "num");
  EXPECT_EQ(prototype[1].return_type, "int");
  EXPECT_TRUE(prototype[1].formals.empty());
  const std::vector<std::string_view> kNames{"put",     "try_put", "get",
                                             "try_get", "peek",    "try_peek"};
  for (std::size_t i = 0; i < 6; ++i) {
    const StdMethodPrototype& method = prototype[i + 2];
    EXPECT_EQ(method.name, kNames[i]);
    ASSERT_EQ(method.formals.size(), 1u);
    EXPECT_EQ(method.formals[0].type, "T");
    EXPECT_EQ(method.formals[0].name, "message");
    EXPECT_FALSE(method.formals[0].has_default);
    EXPECT_EQ(method.formals[0].by_reference, i >= 2);
    EXPECT_EQ(method.kind,
              i % 2 == 0 ? StdMethodKind::kTask : StdMethodKind::kFunction);
    EXPECT_EQ(method.return_type, i % 2 == 0 ? "void" : "int");
    EXPECT_EQ(LeastActualsOf(method), 1u);
    EXPECT_EQ(MostActualsOf(method), 1u);
  }
  EXPECT_EQ(&StdClassPrototype(StdPackageMember::kMailbox), &prototype);
  const std::optional<StdTypeParameter> kParameter =
      StdClassTypeParameterOf(StdPackageMember::kMailbox);
  ASSERT_TRUE(kParameter.has_value());
  const StdTypeParameter kT = kParameter.value_or(StdTypeParameter{});
  EXPECT_EQ(kT.name, "T");
  EXPECT_EQ(kT.default_type, "dynamic_singular_type");
  EXPECT_FALSE(kT.class_only);
  EXPECT_EQ(StdClassTypeParameterOf(StdPackageMember::kSemaphore),
            std::nullopt);
}

// §G.4: a call on a mailbox handle, parameterized or not, is checked against
// the prototype: a method it does not declare is rejected, as is put with no
// message, num with an argument and try_get with no destination, each under
// the subclause giving the prototype and at the call, while the prototype's
// own calls beside them are accepted.
TEST(MailboxStdPackageElaborator, CallsAreCheckedAgainstThePrototype) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  mailbox mbx;\n"
      "  mailbox #(int) pm;\n"
      "  int msg;\n"
      "  int got;\n"
      "  initial begin\n"
      "    mbx = new(4);\n"
      "    mbx.flush();\n"
      "    mbx.put();\n"
      "    got = mbx.num(1);\n"
      "    got = pm.try_get();\n"
      "    got = mbx.num();\n"
      "    pm.put(msg);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'mailbox' declares no method 'flush'", 8,
                            "G.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'put' of class 'mailbox' takes at least 1 "
                            "argument; 0 given",
                            9, "G.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'num' of class 'mailbox' takes at most 0 "
                            "arguments; 1 given",
                            10, "G.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'try_get' of class 'mailbox' takes at "
                            "least 1 argument; 0 given",
                            11, "G.4"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, 7u);
    EXPECT_NE(d.loc.line, 12u);
    EXPECT_NE(d.loc.line, 13u);
  }
}

}  // namespace
