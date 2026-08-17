#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast.h"

using namespace delta;

namespace {

// §3.2 decides what AppendCellDeclarations moves, because §33.2.1 makes a
// library "a named collection of cells" and a cell "a design element (see
// 3.2)". §3.2 names seven: "a SystemVerilog module (see Clause 23), program
// (see Clause 24), interface (see Clause 25), checker (see Clause 17), package
// (see Clause 26), primitive (see Clause 28) or configuration (see Clause 33)".
//
// All seven are declared in one source here rather than one kind per case, so a
// merge that drops a kind is caught whichever kind it drops. The checker is the
// one it dropped when this was written, and it is the one §33.2.1's own list of
// examples omits.
TEST(AppendCellDeclarations, EveryDesignElementKindReachesTheTarget) {
  auto src = Parse(
      "module m;\n"
      "endmodule\n"
      "program p;\n"
      "endprogram\n"
      "interface i;\n"
      "endinterface\n"
      "checker chk;\n"
      "  logic flag = 0;\n"
      "endchecker\n"
      "package pk;\n"
      "endpackage\n"
      "primitive u(output o, input a);\n"
      "  table\n"
      "    0 : 0;\n"
      "    1 : 1;\n"
      "  endtable\n"
      "endprimitive\n"
      "config cfg;\n"
      "  design m;\n"
      "endconfig\n");
  ASSERT_NE(src.cu, nullptr);
  ASSERT_FALSE(src.has_errors);

  CompilationUnit target;
  AppendCellDeclarations(target, *src.cu);

  EXPECT_EQ(target.modules.size(), 1u);
  EXPECT_EQ(target.programs.size(), 1u);
  EXPECT_EQ(target.interfaces.size(), 1u);
  EXPECT_EQ(target.checkers.size(), 1u);
  EXPECT_EQ(target.packages.size(), 1u);
  EXPECT_EQ(target.udps.size(), 1u);
  EXPECT_EQ(target.configs.size(), 1u);
}

// The name as well as the count, for the one kind §33.2.1's examples leave out.
// A count of 1 is reached by a merge that appended a null as readily as by one
// that carried the declaration, and only the name separates them.
TEST(AppendCellDeclarations, CheckerReachesTheTargetUnderItsOwnName) {
  auto src = Parse(
      "checker chk;\n"
      "  logic flag = 0;\n"
      "endchecker\n");
  ASSERT_NE(src.cu, nullptr);
  ASSERT_FALSE(src.has_errors);

  CompilationUnit target;
  AppendCellDeclarations(target, *src.cu);

  ASSERT_EQ(target.checkers.size(), 1u);
  ASSERT_NE(target.checkers[0], nullptr);
  EXPECT_EQ(target.checkers[0]->name, "chk");
}

// The boundary the two cases above need. §3.12.1 rules that "items defined in
// the compilation-unit scope cannot be accessed by name from outside the
// compilation unit", so what a source declares outside every design element
// stays with the unit that parsed it.
//
// Without this, widening the merge to every list CompilationUnit holds would
// satisfy the two cases above while carrying a compilation-unit class and
// typedef across a boundary §3.12.1 closes. The two assertions on `src.cu`
// are what make the emptiness of the target mean something: they show the
// source declared both, so an empty target is a merge that left them rather
// than a source that never had them.
TEST(AppendCellDeclarations, CompilationUnitScopeDeclarationsStayBehind) {
  auto src = Parse(
      "typedef int cu_t;\n"
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n");
  ASSERT_NE(src.cu, nullptr);
  ASSERT_FALSE(src.has_errors);
  ASSERT_FALSE(src.cu->classes.empty());
  ASSERT_FALSE(src.cu->cu_items.empty());

  CompilationUnit target;
  AppendCellDeclarations(target, *src.cu);

  EXPECT_EQ(target.modules.size(), 1u);
  EXPECT_TRUE(target.classes.empty());
  EXPECT_TRUE(target.cu_items.empty());
}

// A run reaches this function once per source description, so what an earlier
// description contributed has to survive the next call. A merge that assigned
// rather than appended would leave the unit holding only the last description's
// cells, and every case above would still pass because each merges into a
// target that starts empty.
TEST(AppendCellDeclarations, TargetKeepsWhatItAlreadyHeld) {
  auto first = Parse(
      "module one;\n"
      "endmodule\n");
  auto second = Parse(
      "module two;\n"
      "endmodule\n");
  ASSERT_NE(first.cu, nullptr);
  ASSERT_NE(second.cu, nullptr);

  CompilationUnit target;
  AppendCellDeclarations(target, *first.cu);
  AppendCellDeclarations(target, *second.cu);

  ASSERT_EQ(target.modules.size(), 2u);
  EXPECT_EQ(target.modules[0]->name, "one");
  EXPECT_EQ(target.modules[1]->name, "two");
}

}  // namespace
