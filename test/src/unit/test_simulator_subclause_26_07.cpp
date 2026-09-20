#include <gtest/gtest.h>

#include "fixture_simulator.h"
#include "helpers_scheduler.h"

using namespace delta;

namespace {

// §26.7 (Syntax 26-5): a name of the built-in package may be written behind
// `std::`, so `std::process::self()` is §9.7's `process::self()` and answers
// the handle of the calling process rather than null. The two handles name
// one process, so they compare equal.
TEST(StdBuiltInPackageSim, StdQualifiedProcessSelfNamesTheRunningProcess) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] non_null, same;\n"
      "  initial begin\n"
      "    std::process p = std::process::self();\n"
      "    process q = process::self();\n"
      "    non_null = (p != null) ? 1 : 0;\n"
      "    same = (p == q) ? 1 : 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"non_null", 1u}, {"same", 1u}});
}

// §9.7 through §26.7: the handle `std::process::self()` answers is the calling
// process, so its status() is RUNNING (1) and not the zero state a null handle
// reports; the enum literals reached as `std::process::RUNNING` and
// `std::process::KILLED` are §9.7's 1 and 4.
TEST(StdBuiltInPackageSim, StdQualifiedProcessHandleStatusAndStateLiterals) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] st, lits;\n"
      "  initial begin\n"
      "    std::process p = std::process::self();\n"
      "    st = p.status();\n"
      "    lits = std::process::RUNNING + 10 * std::process::KILLED;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"st", 1u}, {"lits", 41u}});
}

// §9.7 through §26.7: a child's `std::process::self()` handle is the child, so
// the parent's kill() through it stops the child before its delayed write; a
// null handle would kill nothing and the write would land.
TEST(StdBuiltInPackageSim, StdQualifiedProcessSelfHandleKillsTheChild) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  logic [31:0] x;\n"
      "  initial begin\n"
      "    std::process p;\n"
      "    x = 7;\n"
      "    fork\n"
      "      begin\n"
      "        p = std::process::self();\n"
      "        #10 x = 99;\n"
      "      end\n"
      "    join_none\n"
      "    #1;\n"
      "    p.kill();\n"
      "    #20;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  ASSERT_FALSE(f.has_errors);
  LowerRunAndCheck(f, design, {{"x", 7u}});
}

}  // namespace
