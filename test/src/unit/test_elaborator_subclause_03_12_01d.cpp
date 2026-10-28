#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "common/diagnostic.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// A source whose hierarchical name `path`, written at `line`, ends in a name
// only the compilation-unit scope declares.
struct UnitReachedByPath {
  const char* src;
  const char* path;
  const char* name;
  uint32_t line;
};

// §3.12.1 (printed page 57): no hierarchical reference reaches an identifier
// the compilation-unit scope declares. A path from $root, a path headed by a
// top-level instance's name or by the name of a module above the reference
// (§23.8), each written in a module's procedural block, continuous assignment
// or function, in a program, or in a task or function of the unit, ends at an
// instance that declares no `g` of its own, and so names nothing.
TEST(UnitScopeHierarchicalNames, PathEndingAtAUnitName) {
  const UnitReachedByPath kCases[] = {
      {"int g;\n"
       "module top;\n"
       "  int y;\n"
       "  initial y = $root.g;\n"
       "endmodule\n",
       "$root.g", "g", 4},
      {"int g;\n"
       "module top;\n"
       "  int y;\n"
       "  initial y = top.g;\n"
       "endmodule\n",
       "top.g", "g", 4},
      {"int g;\n"
       "module top;\n"
       "  int y;\n"
       "  initial y = $root.top.g;\n"
       "endmodule\n",
       "$root.top.g", "g", 4},
      {"int g;\n"
       "module top;\n"
       "  wire [31:0] w;\n"
       "  assign w = top.g;\n"
       "endmodule\n",
       "top.g", "g", 4},
      {"int g;\n"
       "module top;\n"
       "  function int f();\n"
       "    return top.g;\n"
       "  endfunction\n"
       "endmodule\n",
       "top.g", "g", 4},
      {"int g;\n"
       "module child;\n"
       "  int y;\n"
       "  initial y = top.g;\n"
       "endmodule\n"
       "module top;\n"
       "  child c();\n"
       "endmodule\n",
       "top.g", "g", 4},
      {"int g;\n"
       "module child;\n"
       "endmodule\n"
       "module top;\n"
       "  child c();\n"
       "  int y;\n"
       "  initial y = $root.top.c.g;\n"
       "endmodule\n",
       "$root.top.c.g", "g", 7},
      {"int g;\n"
       "module other;\n"
       "endmodule\n"
       "module top;\n"
       "  int y;\n"
       "  initial y = other.g;\n"
       "endmodule\n",
       "other.g", "g", 6},
      {"int g;\n"
       "program top;\n"
       "  int y;\n"
       "  initial y = top.g;\n"
       "endprogram\n",
       "top.g", "g", 4},
      {"int g;\n"
       "function int f();\n"
       "  return top.g;\n"
       "endfunction\n"
       "module top;\n"
       "endmodule\n",
       "top.g", "g", 3},
  };
  for (const UnitReachedByPath& c : kCases) {
    ElabFixture f;
    EXPECT_FALSE(ElabOk(c.src, f)) << c.src;
    EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                              std::string("hierarchical name '") + c.path +
                                  "' is unresolved: '" + c.name +
                                  "' is declared in the compilation-unit scope",
                              c.line, "3.12.1"))
        << c.src;
  }
}

// The nearest allowed forms: each path ending at an instance that declares a
// `g` of its own, which is what the path reaches whatever the unit declares,
// and a name headed by a variable of the referencing module, which is read
// from that variable rather than from the top-level instance of its name.
TEST(UnitScopeHierarchicalNames, PathEndingAtAnInstancesOwnName) {
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "module child;\n"
             "  int g;\n"
             "  int y;\n"
             "  initial y = top.g + $root.top.g;\n"
             "endmodule\n"
             "module top;\n"
             "  int g;\n"
             "  int y;\n"
             "  wire [31:0] w;\n"
             "  child c();\n"
             "  assign w = top.g;\n"
             "  initial y = $root.top.g + $root.top.c.g + other.g;\n"
             "  initial y = $unit::g + g;\n"
             "endmodule\n"
             "module other;\n"
             "  int g;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "program top;\n"
             "  int g;\n"
             "  int y;\n"
             "  initial y = top.g;\n"
             "endprogram\n"));
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "function int f();\n"
             "  return top.g;\n"
             "endfunction\n"
             "module top;\n"
             "  int g;\n"
             "endmodule\n"));
  EXPECT_TRUE(
      ElabOk("int g;\n"
             "module other;\n"
             "endmodule\n"
             "module top;\n"
             "  struct { int g; } other;\n"
             "  int y;\n"
             "  initial y = other.g;\n"
             "endmodule\n"));
}

// A module instantiated twice writes its path once, and it is reported once.
TEST(UnitScopeHierarchicalNames, PathInAModuleInstantiatedTwiceReportedOnce) {
  ElabFixture f;
  EXPECT_FALSE(
      ElabOk("int g;\n"
             "module child;\n"
             "  int y;\n"
             "  initial y = top.g;\n"
             "endmodule\n"
             "module top;\n"
             "  child c1();\n"
             "  child c2();\n"
             "endmodule\n",
             f));
  int reports = 0;
  for (const Diagnostic& d : f.diag.Diagnostics()) {
    if (d.subclause == "3.12.1") ++reports;
  }
  EXPECT_EQ(reports, 1);
}

}  // namespace
