#include <gtest/gtest.h>

#include <cstddef>
#include <optional>
#include <string>
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

std::string ModuleCalling(const std::string& call) {
  return "module m;\n  mailbox mb = new(4);\n  mailbox #(int) pm = new;\n"
         "  int n, v;\n  initial begin\n    " +
         call + "\n  end\nendmodule\n";
}

std::string ProgramCalling(const std::string& call) {
  return "program m;\n  mailbox mb = new(4);\n  int n, v;\n  initial begin\n"
         "    " +
         call + "\n  end\nendprogram\n";
}

std::string ClassCalling(const std::string& call) {
  return "class holder;\n  mailbox mb;\n  mailbox #(int) pm;\n"
         "  static mailbox sm;\n  int n, v;\n"
         "  function void act();\n    holder h = this;\n    " +
         call + "\n  endfunction\nendclass\nmodule m;\nendmodule\n";
}

std::string PackageCalling(const std::string& call) {
  return "package k;\n  mailbox own = new;\n  int n, v;\n"
         "  function automatic void act(mailbox mb, mailbox #(int) pm);\n"
         "    " +
         call + "\n  endfunction\nendpackage\nmodule m;\nendmodule\n";
}

std::string FunctionCalling(const std::string& call) {
  return "module m;\n  mailbox own = new;\n  int n, v;\n"
         "  function automatic void act(mailbox mb, mailbox #(int) pm);\n"
         "    " +
         call + "\n  endfunction\nendmodule\n";
}

std::string UnitCalling(const std::string& call) {
  return "mailbox mb = new;\nmodule m;\n  int n, v;\n  initial begin\n    " +
         call + "\n  end\nendmodule\n";
}

std::string ObjectCalling(const std::string& call) {
  return "class holder;\n  mailbox mb = new;\nendclass\nmodule m;\n"
         "  holder o = new;\n  int n, v;\n  initial begin\n    o." +
         call + "\n  end\nendmodule\n";
}

void ExpectErrorAt(const std::string& src, std::string_view at,
                   std::string_view message, std::string_view subclause) {
  ElabFixture f;
  ElabOk(src, f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), message, LineHolding(src, at),
                            subclause))
      << src;
}

const char* const kMessageMethods[] = {"put",     "try_put", "get",
                                       "try_get", "peek",    "try_peek"};

TEST(MailboxStdPackageElaborator, TheConstructorTakesOneBoundAtMost) {
  EXPECT_TRUE(ElabOk(ModuleCalling("mb = new; mb = new(); mb = new(2);")));
  ExpectErrorAt(ModuleCalling("mb = new(1, 2);"), "new(1, 2)",
                "constructor of class 'mailbox' takes at most 1 argument; 2 "
                "given",
                "G.4");
}

TEST(MailboxStdPackageElaborator, EachMessageMethodNeedsItsMessage) {
  for (const std::string kMethod : kMessageMethods) {
    EXPECT_TRUE(ElabOk(ModuleCalling("mb." + kMethod + "(v);"))) << kMethod;
    ExpectErrorAt(ModuleCalling("mb." + kMethod + "();"), "mb." + kMethod,
                  "method '" + kMethod +
                      "' of class 'mailbox' takes at least 1 argument; 0 given",
                  "G.4");
  }
}

TEST(MailboxStdPackageElaborator, EachMessageMethodTakesOneMessage) {
  for (const std::string kMethod : kMessageMethods) {
    ExpectErrorAt(ModuleCalling("pm." + kMethod + "(v, n);"), "pm." + kMethod,
                  "method '" + kMethod +
                      "' of class 'mailbox' takes at most 1 argument; 2 given",
                  "G.4");
  }
}

TEST(MailboxStdPackageElaborator, ActualsAreCountedInAProgram) {
  EXPECT_TRUE(ElabOk(ProgramCalling("n = mb.num();")));
  ExpectErrorAt(ProgramCalling("n = mb.num(1);"), "mb.num",
                "method 'num' of class 'mailbox' takes at most 0 arguments; 1 "
                "given",
                "G.4");
}

TEST(MailboxStdPackageElaborator, DISABLED_ActualsAreCountedInEveryScope) {
  EXPECT_TRUE(ElabOk(ClassCalling("n = mb.num();")));
  EXPECT_TRUE(ElabOk(PackageCalling("n = mb.num();")));
  EXPECT_TRUE(ElabOk(UnitCalling("n = mb.num();")));
  for (const auto& src :
       {ClassCalling("n = mb.num(1);"), PackageCalling("n = mb.num(1);"),
        UnitCalling("n = mb.num(1);"),
        ObjectCalling("mb.put(n + o.mb.num(1));")}) {
    ExpectErrorAt(src, "mb.num",
                  "method 'num' of class 'mailbox' takes at most 0 arguments; "
                  "1 given",
                  "G.4");
  }
  for (const auto& src :
       {ClassCalling("n = mb.try_get();"), PackageCalling("n = mb.try_get();"),
        UnitCalling("n = mb.try_get();")}) {
    ExpectErrorAt(src, "mb.try_get",
                  "method 'try_get' of class 'mailbox' takes at least 1 "
                  "argument; 0 given",
                  "G.4");
  }
  ExpectErrorAt(FunctionCalling("n = mb.try_put(1, 2);"), "mb.try_put",
                "method 'try_put' of class 'mailbox' takes at most 1 argument; "
                "2 given",
                "G.4");
}

TEST(MailboxStdPackageElaborator, DISABLED_ConstructionsAreCountedInAClass) {
  EXPECT_TRUE(ElabOk(ClassCalling("mb = new(2);")));
  for (const auto& src :
       {ClassCalling("mb = new(1, 2);"), PackageCalling("mb = new(1, 2);")}) {
    ExpectErrorAt(src, "new(1, 2)",
                  "constructor of class 'mailbox' takes at most 1 argument; 2 "
                  "given",
                  "G.4");
  }
}

TEST(MailboxStdPackageElaborator, AProgramAndAUnitDeclareMailboxes) {
  EXPECT_TRUE(ElabOk(ProgramCalling("mb.put(1); mb.get(v);")));
  EXPECT_TRUE(ElabOk(UnitCalling("mb.put(1); mb.get(v);")));
}

TEST(MailboxStdPackageElaborator, AnEmptyOrNamedParameterListIsAccepted) {
  EXPECT_TRUE(
      ElabOk("module m;\n"
             "  mailbox #() dynamic_one = new;\n"
             "  mailbox #(.T(int)) named_one = new;\n"
             "  std::mailbox #(.T(string)) scoped_one = new;\n"
             "endmodule\n"));
}

TEST(MailboxStdPackageElaborator, DISABLED_ASecondParameterValueIsRejected) {
  for (const std::string kType :
       {"mailbox #(int, int)", "std::mailbox #(int, int)",
        "mailbox #(.T(int), .U(int))"}) {
    ElabFixture f;
    ElabOk("module m;\n  " + kType + " mb;\nendmodule\n", f);
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(), "'mailbox'", 2, "G.4"))
        << kType;
  }
}

TEST(MailboxStdPackageElaborator, DISABLED_AParameterValueThatIsNoTypeIsError) {
  for (const std::string kType :
       {"mailbox #(5)", "std::mailbox #(5)", "mailbox #(.T(5))"}) {
    ElabFixture f;
    ElabOk("module m;\n  " + kType + " mb;\nendmodule\n", f);
    EXPECT_TRUE(
        ReportedError(f.diag.Diagnostics(), "type parameter 'T'", 2, "G.4"))
        << kType;
  }
}

TEST(MailboxStdPackageElaborator, ActualsBoundToTheirFormalsNamesAreAccepted) {
  EXPECT_TRUE(ElabOk(ModuleCalling("mb = new(.bound(3));")));
  for (const std::string kMethod : kMessageMethods) {
    EXPECT_TRUE(ElabOk(ModuleCalling("mb." + kMethod + "(.message(v));")))
        << kMethod;
  }
}

TEST(MailboxStdPackageElaborator, DISABLED_ActualsBoundToOtherNamesAreErrors) {
  ExpectErrorAt(ModuleCalling("mb = new(.size(3));"), ".size",
                "no parameter 'size' in", "G.4");
  for (const std::string kMethod : kMessageMethods) {
    ExpectErrorAt(ModuleCalling("mb." + kMethod + "(.msg(v));"), ".msg",
                  "no parameter 'msg' in", "G.4");
  }
}

TEST(MailboxStdPackageElaborator, DISABLED_ATaskOfTheMailboxIsNoOperand) {
  for (const std::string kMethod : {"put", "get", "peek"}) {
    EXPECT_TRUE(ElabOk(ModuleCalling("n = mb.try_" + kMethod + "(v);")));
    for (const auto& call :
         {"n = mb." + kMethod + "(v);", "if (mb." + kMethod + "(v)) n = 1;"}) {
      ExpectErrorAt(ModuleCalling(call), "mb." + kMethod,
                    "task '" + kMethod +
                        "' is enabled from a statement and cannot be an "
                        "operand of an expression",
                    "13.3");
    }
  }
}

TEST(MailboxStdPackageElaborator, AFunctionCallsTheFunctionsOfAMailbox) {
  for (const char* call :
       {"n = mb.num();", "n = mb.try_put(v);", "n = mb.try_get(v);",
        "n = mb.try_peek(v);", "n = pm.try_get(v);", "n = pm.try_peek(v);"}) {
    EXPECT_TRUE(ElabOk(FunctionCalling(call))) << call;
    EXPECT_TRUE(ElabOk(ClassCalling(call))) << call;
    EXPECT_TRUE(ElabOk(PackageCalling(call))) << call;
  }
}

TEST(MailboxStdPackageElaborator, AForkInAFunctionEnablesTheTasksOfAMailbox) {
  for (const std::string kMethod : {"put", "get", "peek"}) {
    const std::string kFork = "fork own." + kMethod + "(v); join_none";
    EXPECT_TRUE(ElabOk(FunctionCalling(kFork))) << kMethod;
    EXPECT_TRUE(ElabOk(PackageCalling(kFork))) << kMethod;
    EXPECT_TRUE(ElabOk(ClassCalling("fork mb." + kMethod + "(v); join_none")))
        << kMethod;
  }
}

TEST(MailboxStdPackageElaborator, DISABLED_AFunctionEnablesNoTaskOfAMailbox) {
  for (const std::string kMethod : {"put", "get", "peek"}) {
    const std::string kEnable = "." + kMethod + "(v);";
    for (const std::string kHandle : {"mb", "pm", "own"}) {
      ExpectErrorAt(FunctionCalling(kHandle + kEnable), kHandle + kEnable,
                    "function cannot enable a task", "13.4");
      ExpectErrorAt(PackageCalling(kHandle + kEnable), kHandle + kEnable,
                    "function cannot enable a task", "13.4");
    }
    for (const std::string kHandle : {"mb", "pm", "this.mb", "h.mb", "sm"}) {
      ExpectErrorAt(ClassCalling(kHandle + kEnable), kHandle + kEnable,
                    "function cannot enable a task", "13.4");
    }
  }
}

TEST(MailboxStdPackageElaborator, AnUndeclaredMethodIsRejectedInAProgram) {
  ExpectErrorAt(ProgramCalling("mb.zap();"), "mb.zap",
                "class 'mailbox' declares no method 'zap'", "G.4");
}

TEST(MailboxStdPackageElaborator,
     DISABLED_AnUndeclaredMethodIsRejectedInEveryScope) {
  for (const auto& src :
       {ClassCalling("mb.zap();"), ClassCalling("this.mb.zap();"),
        PackageCalling("mb.zap();"), UnitCalling("mb.zap();"),
        ObjectCalling("mb.zap();")}) {
    ExpectErrorAt(src, "mb.zap", "class 'mailbox' declares no method 'zap'",
                  "G.4");
  }
}

TEST(MailboxStdPackageElaborator,
     DISABLED_AnUndeclaredMethodOfADerivedClassIsRejected) {
  const std::string kDerived =
      "class mb2 extends mailbox;\n"
      "  function void extra(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  mb2 h;\n";
  EXPECT_TRUE(ElabOk(kDerived +
                     "  initial begin h.extra(); h.put(1); end\nendmodule\n"));
  ExpectErrorAt(kDerived + "  initial h.zap();\nendmodule\n", "h.zap",
                "declares no method 'zap'", "G.4");
}

TEST(MailboxStdPackageElaborator, AMemberOfAnIntResultIsRejected) {
  for (const std::string kMethod : {"try_put", "try_get", "try_peek"}) {
    EXPECT_TRUE(ElabOk(ModuleCalling("void'(mb." + kMethod + "(v));")));
    ExpectErrorAt(ModuleCalling("void'(mb." + kMethod + "(v).foo());"), ".foo",
                  "'foo' is not a built-in method of the integral or real "
                  "value that '" +
                      kMethod + "()' returns",
                  "23.7");
  }
}

}  // namespace
