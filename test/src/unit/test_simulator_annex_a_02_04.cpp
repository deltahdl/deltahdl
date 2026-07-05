#include "helpers_scheduler.h"

using namespace delta;

// §A.2.4 end-to-end coverage. The declaration-assignment productions of §A.2.4
// are syntactic, but the value each one binds is produced by the full pipeline:
// a variable_decl_assignment initializer, a dynamic_array_new, and a class_new
// each yield a real runtime object. These tests build that input from real
// source syntax (declaration initializers, dynamic arrays, class handles) and
// run it, observing the bound value the production actually produced rather
// than merely that it parsed.

namespace {

// variable_decl_assignment, first alternative: `variable_identifier
// { variable_dimension } [ = expression ]`. The declaration initializer takes
// effect at time zero, so the scalar carries the initialized value at runtime.
TEST(DeclarationAssignmentSim, VarDeclInitializerAppliesAtRuntime) {
  auto v = RunAndGet(
      "module t;\n"
      "  int x = 5;\n"
      "  int result;\n"
      "  initial result = x;\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 5u);
}

// variable_decl_assignment, second alternative: a dynamic-array identifier with
// `= dynamic_array_new`. The `new [ expression ]` size form allocates the
// array; its size is observable at runtime.
TEST(DeclarationAssignmentSim, VarDeclDynamicArrayNewSizeInitializer) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = new[4];\n"
      "  int result;\n"
      "  initial result = d.size();\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 4u);
}

// A dynamic array created with a `'{...}` assignment-pattern initializer, then
// a reduction method observed on it — the §7 dynamic-array dependency built
// from real syntax and driven through simulation. Sum of {4,5,6} is 15.
TEST(DeclarationAssignmentSim, VarDeclDynamicArrayReductionOverBraceInit) {
  auto v = RunAndGet(
      "module t;\n"
      "  int d[] = '{4, 5, 6};\n"
      "  int result;\n"
      "  initial result = d.sum() with (item);\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 15u);
}

// dynamic_array_new copy form: `new [ expression ] ( expression )`. The source
// array is itself a real dynamic array; the new array copies its leading
// elements and default-fills the rest. size()==3 and d[1] tracks src[1]==8.
TEST(DeclarationAssignmentSim, VarDeclDynamicArrayNewCopyInitializer) {
  auto v = RunAndGet(
      "module t;\n"
      "  int src[] = '{7, 8};\n"
      "  int d[] = new[3](src);\n"
      "  int result;\n"
      "  initial result = d.size() * 100 + d[1];\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 308u);
}

// variable_decl_assignment, third alternative: `class_variable_identifier
// [ = class_new ]`. The bare `new` runs the constructor; the constructed
// object's property is observable through the handle.
TEST(DeclarationAssignmentSim, VarDeclClassNewInitializerConstructsObject) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(); v = 42; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new;\n"
      "    result = c.v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

// class_new with a `( list_of_arguments )`: the constructor argument reaches
// the object's property. new(21) with `v = a * 2` yields 42.
TEST(DeclarationAssignmentSim, VarDeclClassNewWithArgsInitializer) {
  auto v = RunAndGet(
      "class C;\n"
      "  int v;\n"
      "  function new(int a); v = a * 2; endfunction\n"
      "endclass\n"
      "module t;\n"
      "  int result;\n"
      "  initial begin\n"
      "    C c = new(21);\n"
      "    result = c.v;\n"
      "  end\n"
      "endmodule\n",
      "result");
  EXPECT_EQ(v, 42u);
}

}  // namespace
