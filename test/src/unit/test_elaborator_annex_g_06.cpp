// IEEE 1800-2023 Annex G.6 (Std package -- Process).
//
// Section G.6 presents the prototype of the built-in `process` class that the
// std package provides; its semantics are owned by clause 9.7. The prototype
// is:
//
//   class :final process;
//     typedef enum {FINISHED, RUNNING, WAITING, SUSPENDED, KILLED} state;
//     static function process self();
//     function state status();
//     function void kill();
//     task await();
//     function void suspend();
//     function void resume();
//     function void srandom(int seed);
//     function string get_randstate();
//     function void set_randstate(string state);
//   endclass
//
// These tests observe the elaborator providing that prototype out of the std
// package: `process` resolves as a built-in class without any user
// `class process` definition (Elaborator::RegisterCuScopeItems registers the
// std-package class name), the static self() yields a handle, the prototype
// methods elaborate at their call sites, and two prototype-derived rules hold
// -- the class is declared `:final` (it cannot be extended) and it has no
// new() constructor (it cannot be built with `new`).

#include <cstddef>
#include <string_view>
#include <vector>

#include "elaborator/std_package.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// The std package supplies the class name; no user declaration is required.
TEST(ProcessStdPackageElaborator, BuiltInClassNeedsNoUserDefinition) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// The full prototype surface: status / kill / await / suspend / resume /
// srandom / get_randstate / set_randstate each elaborate at the call site.
TEST(ProcessStdPackageElaborator, PrototypeMethodsElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string st;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
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

// Each member of the prototype's state enum elaborates as a scope member of
// the built-in type, compared against the value-returning status() result.
TEST(ProcessStdPackageElaborator, StateEnumMembersElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
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

// The prototype is `class :final process;`: extending it is rejected.
TEST(ProcessStdPackageElaborator, FinalPrototypeCannotBeExtended) {
  // The report names §8.13, the rule against extending a class declared
  // ':final', rather than G.6 or §9.7. G.6 is what declares the prototype
  // final; §8.13 is the rule that declaration then breaks.
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

// The prototype declares no new() constructor: a handle is taken from self(),
// never built with `new`.
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

// G.6-1 + G.6-5 edge: a handle obtained from self() is passed across a
// subroutine boundary and a prototype method (kill) is invoked on the formal,
// so the built-in type resolves as an argument type and the method elaborates
// at the callee site.
TEST(ProcessStdPackageElaborator, HandlePassedToSubroutine) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  task automatic do_work(process p);\n"
      "    p.kill();\n"
      "  endtask\n"
      "  initial begin\n"
      "    process p = process::self();\n"
      "    do_work(p);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §G.6: the prototype as src/elaborator/std_package.h writes it down -- the
// nine methods, self static and returning process, status returning state,
// await the one task, srandom over int seed, get_randstate returning string
// and set_randstate over string state, the others void and taking nothing;
// the class :final; no constructor; and the nested enum state of FINISHED,
// RUNNING, WAITING, SUSPENDED and KILLED.
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

// §G.6: a call on a process handle is checked against the prototype: kill
// with an argument, srandom with none and a method the prototype does not
// declare are each rejected under §G.6 at the call, while status, srandom
// with a seed and set_randstate with a state beside them are accepted.
TEST(ProcessStdPackageElaborator, CallsAreCheckedAgainstThePrototype) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  string st;\n"
      "  initial begin\n"
      "    process p = process::self();\n"
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

}  // namespace
