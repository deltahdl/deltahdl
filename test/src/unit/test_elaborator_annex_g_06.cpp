#include <gtest/gtest.h>

#include <cstddef>
#include <string_view>
#include <vector>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ProcessStdPackageElaborator, BuiltInClassNeedsNoUserDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProcessStdPackageElaborator, PrototypeMethodsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string st;\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
      "    p.status();\n"
      "    p.kill();\n"
      "    p.await();\n"
      "    p.suspend();\n"
      "    p.resume();\n"
      "    p.srandom(7);\n"
      "    st = p.get_randstate();\n"
      "    p.set_randstate(st);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProcessStdPackageElaborator, StateEnumMembersElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
      "    if (p.status() == process::FINISHED) ;\n"
      "    if (p.status() == process::RUNNING) ;\n"
      "    if (p.status() == process::WAITING) ;\n"
      "    if (p.status() == process::SUSPENDED) ;\n"
      "    if (p.status() == process::KILLED) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProcessStdPackageElaborator, FinalPrototypeCannotBeExtended) {
  ElabFixture f;
  ElabOk(
      "class C extends process;\n"
      "endclass\n"
      "module m;\n"
      "  C c;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot extend a class declared ':final'", 1,
                            "8.13"));
}

TEST(ProcessStdPackageElaborator, PrototypeHasNoNewConstructor) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    process p;\n"
      "    p = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct a process object with 'new'", 4,
                            "9.7"));
}

TEST(ProcessStdPackageElaborator, HandlePassedToSubroutine) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic do_work(process p);\n"
      "    p.kill();\n"
      "  endtask\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
      "    do_work(p);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(ProcessStdPackageElaborator, ThePrototypeIsWrittenDown) {
  const auto& prototype = ProcessPrototype();
  ASSERT_EQ(prototype.size(), 9u);
  const std::vector<std::string_view> kNames{
      "self",   "status",  "kill",          "await",        "suspend",
      "resume", "srandom", "get_randstate", "set_randstate"};
  for (std::size_t i = 0; i < kNames.size(); ++i) {
    EXPECT_EQ(prototype[i].name, kNames[i]);
    EXPECT_EQ(prototype[i].is_static, i == 0);
    EXPECT_EQ(prototype[i].kind,
              i == 3 ? StdMethodKind::kTask : StdMethodKind::kFunction);
    EXPECT_EQ(MostActualsOf(prototype[i]), (i == 6 || i == 8) ? 1u : 0u);
    EXPECT_EQ(LeastActualsOf(prototype[i]), MostActualsOf(prototype[i]));
  }
  EXPECT_EQ(prototype[0].return_type, "process");
  EXPECT_EQ(prototype[1].return_type, "state");
  EXPECT_EQ(prototype[6].formals[0].type, "int");
  EXPECT_EQ(prototype[6].formals[0].name, "seed");
  EXPECT_EQ(prototype[7].return_type, "string");
  EXPECT_EQ(prototype[8].formals[0].type, "string");
  EXPECT_EQ(prototype[8].formals[0].name, "state");
  EXPECT_EQ(&StdClassPrototype(StdPackageMember::kProcess), &prototype);
  EXPECT_TRUE(StdClassIsFinal(StdPackageMember::kProcess));
  EXPECT_FALSE(StdClassIsFinal(StdPackageMember::kSemaphore));
  EXPECT_FALSE(StdClassHasConstructor(StdPackageMember::kProcess));
  EXPECT_TRUE(StdClassHasConstructor(StdPackageMember::kSemaphore));
  EXPECT_TRUE(StdClassHasConstructor(StdPackageMember::kMailbox));
  const std::vector<std::string_view> kStates{"FINISHED", "RUNNING", "WAITING",
                                              "SUSPENDED", "KILLED"};
  EXPECT_EQ(ProcessStateEnumMembers(), kStates);
}

TEST(ProcessStdPackageElaborator, CallsAreCheckedAgainstThePrototype) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  string st;\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
      "    p.kill(1);\n"
      "    p.srandom();\n"
      "    p.restart();\n"
      "    p.status();\n"
      "    p.srandom(3);\n"
      "    p.set_randstate(st);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'kill' of class 'process' takes at most 0 "
                            "arguments; 1 given",
                            5, "G.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'srandom' of class 'process' takes at "
                            "least 1 argument; 0 given",
                            6, "G.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'process' declares no method 'restart'", 7,
                            "G.6"));
  for (const auto& d : f.diag.Diagnostics()) {
    EXPECT_NE(d.loc.line, 8u);
    EXPECT_NE(d.loc.line, 9u);
    EXPECT_NE(d.loc.line, 10u);
  }
}

TEST(ProcessStdPackageElaborator, CallsWithoutParenthesesAreChecked) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    static process p = process::self();\n"
      "    p.baz;\n"
      "    p.srandom;\n"
      "    p.kill;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "class 'process' declares no method 'baz'", 4,
                            "G.6"));
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "method 'srandom' of class 'process' takes at "
                            "least 1 argument; 0 given",
                            5, "G.6"));
  EXPECT_EQ(f.diag.ErrorCount(), 2U);
}

}  // namespace
