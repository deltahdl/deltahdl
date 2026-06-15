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
// Unlike the mailbox/semaphore prototypes, `process` has no new() constructor:
// a handle is obtained from the static self(). These tests observe the parser
// recognizing the std-package type name (Parser::known_types_ seeds "process")
// so declarations, the static self() call, the state-enum scope members, and
// the full prototype method surface parse without any user `class process`.

#include "fixture_parser.h"

using namespace delta;

namespace {

// `process` is a known std-package type name on its own.
TEST(ProcessStdPackageParser, BareDeclarationOfBuiltInType) {
  auto r = Parse(
      "module m;\n"
      "  process p;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// The prototype's handle is obtained from the static self(), parsed through
// the class scope-resolution operator rather than from new().
TEST(ProcessStdPackageParser, StaticSelfYieldsHandle) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p;\n"
              "    p = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

// The full prototype call surface parses: status / kill / await / suspend /
// resume / srandom / get_randstate / set_randstate.
TEST(ProcessStdPackageParser, PrototypeMethodsParse) {
  auto r = Parse(
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
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
}

// Each member of the prototype's state enum parses as a scope member of the
// built-in type.
TEST(ProcessStdPackageParser, StateEnumMembersParse) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process p = process::self();\n"
              "    if (p.status() == process::FINISHED) ;\n"
              "    if (p.status() == process::RUNNING) ;\n"
              "    if (p.status() == process::WAITING) ;\n"
              "    if (p.status() == process::SUSPENDED) ;\n"
              "    if (p.status() == process::KILLED) ;\n"
              "  end\n"
              "endmodule\n"));
}

// G.6-4 edge: the prototype names the enum typedef `state`. Naming it through
// the scope-resolution operator yields a usable type for a declaration -- the
// parser records the std-package scope and the nested type name.
TEST(ProcessStdPackageParser, ScopedStateTypeNameParses) {
  auto r = Parse(
      "module m;\n"
      "  process::state st;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  EXPECT_FALSE(r.has_errors);
  auto& items = r.cu->modules[0]->items;
  ASSERT_GE(items.size(), 1u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->data_type.scope_name, "process");
  EXPECT_EQ(items[0]->data_type.type_name, "state");
}

// G.6-1 edge: the std-package type name is recognized in a subroutine formal
// port list, so a process handle can be declared as an argument type.
TEST(ProcessStdPackageParser, ProcessAsSubroutineFormalType) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  task automatic do_work(process p);\n"
              "    p.kill();\n"
              "  endtask\n"
              "endmodule\n"));
}

// G.6-1 edge: the type name is recognized as the element type of an array
// declaration, and an element is assigned a handle from the static self().
TEST(ProcessStdPackageParser, ProcessArrayDeclaration) {
  EXPECT_TRUE(
      ParseOk("module m;\n"
              "  initial begin\n"
              "    process job[3];\n"
              "    job[0] = process::self();\n"
              "  end\n"
              "endmodule\n"));
}

}  // namespace
