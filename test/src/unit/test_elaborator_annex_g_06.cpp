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

#include "fixture_elaborator.h"

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
  EXPECT_FALSE(
      ElabOk("class C extends process;\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// The prototype declares no new() constructor: a handle is taken from self(),
// never built with `new`.
TEST(ProcessStdPackageElaborator, PrototypeHasNoNewConstructor) {
  EXPECT_FALSE(
      ElabOk("module m;\n"
             "  initial begin\n"
             "    process p;\n"
             "    p = new;\n"
             "  end\n"
             "endmodule\n"));
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

}  // namespace
