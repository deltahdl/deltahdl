#include <gtest/gtest.h>

#include <string>

#include "builders_ast.h"
#include "common/types.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"
#include "simulator/lowerer.h"
#include "simulator/variable.h"

using namespace delta;

namespace {

// §20.6.2: $bits returns a value whose type is integer; the simulator
// constructs the result as a 32-bit Logic4Vec irrespective of how wide the
// argument is.
TEST(UtilitySystemTaskTest, BitsResultIsInteger) {
  SimFixture f;
  auto* var = f.ctx.CreateVariable("v", 7);
  var->value = MakeLogic4VecVal(f.arena, 7, 0);
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeId(f.arena, "v")});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.width, 32u);
  EXPECT_EQ(result.ToUint64(), 7u);
}

// §20.6.2: $bits returns 0 when its argument is a dynamically sized
// expression that is currently empty. Built from real source: an unelaborated
// queue declared with no initializer holds zero elements, so its live
// bit-stream size is 0.
TEST(PrimarySim, BitsOfCurrentlyEmptyQueueReturnsZero) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int q[$];\n"
      "  int n;\n"
      "  initial n = $bits(q);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 0u);
}

// §20.6.2: for a non-empty dynamically sized expression, $bits reports the
// live bit-stream size — the element count times the per-element width. Three
// 32-bit ints in a queue give 96. The queue is populated from a real
// assignment-pattern initializer (§7.10.1), not hand-built.
TEST(PrimarySim, BitsOfNonEmptyQueueReportsLiveBitStreamSize) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int q[$] = '{10, 20, 30};\n"
      "  int n;\n"
      "  initial n = $bits(q);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 96u);
}

// §20.6.2 (NC2): a 4-state value counts as 1 bit. A 32-bit logic vector — even
// holding all-x content — reports a bit-stream size of exactly 32, matching
// its declared width, though the runtime may use wider storage for the x/z
// encoding. Built from real source and driven through the full pipeline.
TEST(PrimarySim, BitsOf4StateVectorEqualsDeclaredWidth) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  logic [31:0] v;\n"
      "  int n;\n"
      "  initial begin\n"
      "    v = 32'bx;\n"
      "    n = $bits(v);\n"
      "  end\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 32u);
}

// §20.6.2 NC6: the packed struct {logic valid; bit [8:1] data;} has total
// bit-stream width 9 (1 + 8). $bits on either the typedef or a variable of
// that type shall report exactly that width.
TEST(PrimarySim, BitsOfPackedStructTypedefMatchesMemberSum) {
  SimFixture f;
  auto* design = ElaborateSrc(
      "module t;\n"
      "  typedef struct packed { logic valid; bit [8:1] data; } MyType;\n"
      "  int w_type;\n"
      "  int w_var;\n"
      "  MyType m;\n"
      "  initial begin\n"
      "    w_type = $bits(MyType);\n"
      "    w_var = $bits(m);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  Lowerer lowerer(f.ctx, f.arena, f.diag);
  lowerer.Lower(design);
  f.scheduler.Run();
  auto* w_type = f.ctx.FindVariable("w_type");
  auto* w_var = f.ctx.FindVariable("w_var");
  ASSERT_NE(w_type, nullptr);
  ASSERT_NE(w_var, nullptr);
  EXPECT_EQ(w_type->value.ToUint64(), 9u);
  EXPECT_EQ(w_var->value.ToUint64(), 9u);
}

// §20.6.2 (NC1 data_type form): $bits(data_type) accepts a ranged built-in
// type and reports that packed vector's bit-stream size — 8 for logic [7:0].
// This is a distinct argument form from a bare keyword or a struct typedef.
TEST(PrimarySim, BitsOfRangedDataTypeArg) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int n;\n"
      "  initial n = $bits(logic [7:0]);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 8u);
}

// §20.6.2: the dynamically sized-expression rule also holds for a dynamic
// array (§7.5), a different source construct from a queue. Sized with a real
// new[3] initializer, its live bit-stream size is 3 * 32 = 96 — driven through
// the full pipeline, not hand-built.
TEST(PrimarySim, BitsOfDynamicArrayFromNewReportsLiveBitStreamSize) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  int d[] = new[3];\n"
      "  int n;\n"
      "  initial n = $bits(d);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 96u);
}

// §20.6.2 (NC5): because $bits folds to an elaboration-time constant on a
// fixed-size argument, it may define a parameter/localparam value — a code path
// distinct from a packed-dimension range. Here a localparam takes its value
// from $bits and then sizes a vector; reading $bits of that vector back at run
// time observes the constant that flowed through the parameter (16).
TEST(PrimarySim, BitsResultUsableAsLocalparamValue) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  localparam int W = $bits(16'h0);\n"
      "  logic [W-1:0] v;\n"
      "  int n;\n"
      "  initial n = $bits(v);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 16u);
}

// §20.6.2: "the $bits system function returns the number of bits required to
// hold an expression as a bit stream", and the 0 it also defines is reserved
// for "a dynamically sized expression that is currently empty", which
// BitsOfCurrentlyEmptyQueueReturnsZero above covers. `byte` is fixed-size, so
// §6.11 Table 6-8's eight bits is the only answer here.
//
// The declaration takes its type through a class scope prefix, and the class is
// written inside the module. That resolution happens in the elaborator, but
// EvalBits in src/simulator/eval_systask.cpp answers from the run-time value's
// own width, so a width that survives elaboration can still be lost between
// Lowerer::LowerVar and the read. This is the assertion that spans both.
TEST(PrimarySim, BitsOfAModuleLocalClassScopedTypedefVariable) {
  SimFixture f;
  auto* n = RunAndFindVar(
      "module t;\n"
      "  class Cfg;\n"
      "    typedef byte my_type;\n"
      "  endclass\n"
      "  Cfg::my_type v;\n"
      "  int n;\n"
      "  initial n = $bits(v);\n"
      "endmodule\n",
      f, "n");
  ASSERT_NE(n, nullptr);
  EXPECT_EQ(n->value.ToUint64(), 8u);
}

// §20.6.2 (printed page 629): $bits answers "the number of bits required to
// hold an expression as a bit stream", which for a fixed-size unpacked array
// is every element's: 16 for `logic [7:0] m [0:1]` and for the net array
// `wire [7:0] w [0:1]`, 48 for `logic [7:0] md [2][3]`, 24 for its row
// md[1], 128 for `int a [4]`. Read at run time the name was one element's
// worth, and each answered its element's 8 or 32.
TEST(PrimarySim, BitsOfFixedSizeUnpackedArraysCountEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  logic [7:0] m [0:1];\n"
                       "  wire [7:0] w [0:1];\n"
                       "  logic [7:0] md [2][3];\n"
                       "  int a [4];\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(m), "
                       "$bits(w), $bits(md), $bits(md[1]), $bits(a));\n"
                       "endmodule\n",
                       f),
            "16 16 48 24 128\n");
}

// §20.6.2 with §23.6: the same holds for an instance's array named through a
// hierarchical reference -- 32 for u.mem, `logic [7:0] mem[2:5]`, 24 and 12
// for u.m2, `logic [3:0] m2[2][3]`, and its row u.m2[1] -- and an instance's
// queue counts its live elements, 96 for three ints. Each answered its
// element's 8, 4 or 32.
TEST(PrimarySim, BitsOfHierarchicallyNamedArraysCountEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module sub;\n"
                       "  logic [7:0] mem[2:5];\n"
                       "  logic [3:0] m2[2][3];\n"
                       "  int q[$] = '{1, 2, 3};\n"
                       "endmodule\n"
                       "module t;\n"
                       "  sub u();\n"
                       "  initial $display(\"%0d %0d %0d %0d\", $bits(u.mem), "
                       "$bits(u.m2), $bits(u.m2[1]), $bits(u.q));\n"
                       "endmodule\n",
                       f),
            "32 24 12 96\n");
}

// §20.6.2 with §8.5: a class object's unpacked array property is sized the
// same way -- 24 for `logic [7:0] data[1:3]` through a handle and bare in a
// method, and 64 for a dynamic `int d[]` holding the two elements its new[]
// gave it. Read as an expression each answered one element's 32 or 8.
TEST(PrimarySim, BitsOfClassArrayPropertiesCountEveryElement) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  class C;\n"
                       "    logic [7:0] data[1:3];\n"
                       "    int d[];\n"
                       "    function int own; return $bits(data); endfunction\n"
                       "  endclass\n"
                       "  C m = new;\n"
                       "  initial begin\n"
                       "    m.d = new[2];\n"
                       "    $display(\"%0d %0d %0d\", $bits(m.data), m.own(), "
                       "$bits(m.d));\n"
                       "  end\n"
                       "endmodule\n",
                       f),
            "24 24 64\n");
}

// §20.6.2 with §8.23 and §26.3: a data type named through its class or package
// is sized as the type it stands for -- 8 for class C's `typedef byte T`, as a
// variable of it and a module typedef renaming it are, 16 for package p's
// `typedef shortint T`, and 4 for the typedef of a class nested in a class.
TEST(PrimarySim, BitsOfClassAndPackageScopedTypedefs) {
  SimFixture f;
  EXPECT_EQ(RunCapture("package p;\n"
                       "  typedef shortint T;\n"
                       "endpackage\n"
                       "module t;\n"
                       "  class C;\n"
                       "    typedef byte T;\n"
                       "    class N;\n"
                       "      typedef bit [3:0] T;\n"
                       "    endclass\n"
                       "  endclass\n"
                       "  typedef C::T U;\n"
                       "  C::T x;\n"
                       "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(x), "
                       "$bits(U), $bits(C::T), $bits(p::T), $bits(C::N::T));\n"
                       "endmodule\n",
                       f),
            "8 8 8 16 4\n");
}

// §20.6.2 with §7.4.4: a typedef that declares a fixed-size unpacked array
// holds every element's bits -- `Bits [36:1]` 36, `B8 [8:1]` 8, a two-
// dimensional `byte M [2][3]` 48, and `Bits BB [2]`, an array of it defined in
// stages, 72 -- as a variable declared with the name does.
TEST(PrimarySim, BitsOfAnUnpackedArrayTypedefName) {
  SimFixture f;
  std::string out = RunCapture(
      "module t;\n"
      "  typedef bit Bits [36:1];\n"
      "  typedef bit B8 [8:1];\n"
      "  typedef byte M [2][3];\n"
      "  typedef Bits BB [2];\n"
      "  Bits b;\n"
      "  initial $display(\"%0d %0d %0d %0d %0d\", $bits(Bits), $bits(b),\n"
      "                   $bits(B8), $bits(M), $bits(BB));\n"
      "endmodule\n",
      f);
  EXPECT_EQ(out, "36 36 8 48 72\n");
}

// §20.6.2: $bits of a data type named at run time is the type's width: an
// integer type keyword's and a typedef's whose range a parameter sizes.
TEST(BitsSim, ATypeNameAtRunTimeIsItsWidth) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module top;\n"
                       "  parameter W = 10;\n"
                       "  typedef logic [W-1:0] word_t;\n"
                       "  word_t arr[3];\n"
                       "  initial $display(\"%0d %0d %0d %0d\", $bits(word_t), "
                       "$bits(arr), $bits(int), $bits(byte));\n"
                       "endmodule\n",
                       f),
            "10 30 32 8\n");
}

// §20.6.2: $bits determines its result without evaluating the expression it
// encloses, so a call is sized by the function's return type and not made.
TEST(BitsSim, ACallIsSizedWithoutBeingMade) {
  SimFixture f;
  EXPECT_EQ(RunCapture("module t;\n"
                       "  int calls = 0;\n"
                       "  function int f();\n"
                       "    calls++;\n"
                       "    return 5;\n"
                       "  endfunction\n"
                       "  function logic [11:0] g();\n"
                       "    calls++;\n"
                       "    return 0;\n"
                       "  endfunction\n"
                       "  initial $display(\"%0d %0d %0d\", $bits(f()), "
                       "$bits(g()), calls);\n"
                       "endmodule\n",
                       f),
            "32 12 0\n");
}

}  // namespace
