// End-to-end (parse -> elaborate -> lower -> run) coverage for the §A.8.2
// "Subroutine calls" productions. Every §A.8.2 rule is pure syntax carried by
// the parser, but several of the productions describe calls whose behavior only
// becomes observable once the call is executed against an input that was itself
// produced by a dependency subclause (a function declared per §13.4, a dynamic
// array built with a §A.8.1 concatenation initializer). These tests build that
// input from real source syntax and observe the produced result, confirming the
// call production the parser emitted is wired all the way through the pipeline.
// (The constant_function_call production folds during elaboration; its
// literal/parameter/localparam argument forms are observed at that stage in
// test_elaborator_annex_a_08_02.cpp.)

#include "helpers_scheduler.h"

using namespace delta;

namespace {

// tf_call / function_subroutine_call: a user function declared with real §13.4
// syntax is called with positional arguments and its return value observed.
TEST(SubroutineCallSim, FunctionCallWithPositionalArgsReturnsValue) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  function int add(int a, int b); return a + b; endfunction\n"
                "  int r;\n"
                "  initial r = add(20, 22);\n"
                "endmodule\n",
                "r"),
      42u);
}

// list_of_arguments, named form: `.identifier(expression)` binds by name, so
// the arguments may be supplied out of declaration order. Using a
// non-commutative body (a - b) proves the binding is by name and not by
// position.
TEST(SubroutineCallSim, NamedArgumentsBindByName) {
  EXPECT_EQ(
      RunAndGet("module t;\n"
                "  function int sub(int a, int b); return a - b; endfunction\n"
                "  int r;\n"
                "  initial r = sub(.b(3), .a(10));\n"
                "endmodule\n",
                "r"),
      7u);
}

// list_of_arguments, mixed positional-then-named form: leading positional
// arguments followed by a trailing named argument.
TEST(SubroutineCallSim, MixedPositionalAndNamedArguments) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  function int f3(int a, int b, int c);\n"
                      "    return a * 100 + b * 10 + c;\n"
                      "  endfunction\n"
                      "  int r;\n"
                      "  initial r = f3(1, 2, .c(3));\n"
                      "endmodule\n",
                      "r"),
            123u);
}

// array_manipulation_call with array_method_name = method_identifier ("sum"),
// over a dynamic array built with a §A.8.1 concatenation initializer.
TEST(SubroutineCallSim, ArrayReductionSumOverInitializedArray) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {10, 20, 30};\n"
                      "  int r;\n"
                      "  initial r = arr.sum();\n"
                      "endmodule\n",
                      "r"),
            60u);
}

// array_method_name keyword form "and": the reduction keyword is a distinct
// alternative of array_method_name (not an ordinary method_identifier).
TEST(SubroutineCallSim, ArrayReductionAndKeyword) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {7, 6};\n"
                      "  int r;\n"
                      "  initial r = arr.and;\n"
                      "endmodule\n",
                      "r"),
            6u);  // 7 & 6 == 6
}

// array_method_name keyword form "or".
TEST(SubroutineCallSim, ArrayReductionOrKeyword) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {1, 2};\n"
                      "  int r;\n"
                      "  initial r = arr.or;\n"
                      "endmodule\n",
                      "r"),
            3u);  // 1 | 2 == 3
}

// array_method_name keyword form "xor".
TEST(SubroutineCallSim, ArrayReductionXorKeyword) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {6, 3};\n"
                      "  int r;\n"
                      "  initial r = arr.xor;\n"
                      "endmodule\n",
                      "r"),
            5u);  // 6 ^ 3 == 5
}

// array_manipulation_call's optional `with ( expression )` clause: the
// reduction folds the with-expression evaluated per element, over a dynamic
// array built from real initializer syntax.
TEST(SubroutineCallSim, ArrayReductionWithClause) {
  EXPECT_EQ(RunAndGet("module t;\n"
                      "  int arr[] = {1, 2, 3, 4};\n"
                      "  int r;\n"
                      "  initial r = arr.sum() with (item * 2);\n"
                      "endmodule\n",
                      "r"),
            20u);  // 2*(1+2+3+4) == 20
}

}  // namespace
