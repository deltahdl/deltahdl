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

TEST(MailboxStdPackageElaborator, CallsWithoutParenthesesAreChecked) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  mailbox mb;\n"
      "  initial begin\n"
      "    mb = new;\n"
      "    mb.foo;\n"
      "    mb.get;\n"
      "    mb.num;\n"
      "    mb.get_randstate;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'mailbox' declares no method 'foo'", 5,
                            "G.4"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'get' of class 'mailbox' takes at least 1 "
                            "argument; 0 given",
                            6, "G.4"));
  EXPECT_EQ(f.diag.ErrorCount(), 2U);
}

}  // namespace
