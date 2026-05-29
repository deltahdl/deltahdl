#include "builders_ast.h"
#include "fixture_elaborator.h"
#include "fixture_evaluator.h"
#include "fixture_simulator.h"
#include "simulator/evaluation.h"

using namespace delta;

namespace {

TEST(ConstEval, BitsExpr) {
  EvalFixture f;

  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(8'hFF)", f)), 8);
  EXPECT_EQ(ConstEvalInt(ParseExprFrom("$bits(16'h0)", f)), 16);
}

TEST(SubroutineCallExprElaboration, SystemTfCallBitsElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] v;\n"
      "  logic [31:0] x;\n"
      "  initial x = $bits(v);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(UtilitySystemTaskTest, BitsOf32BitValue) {
  SimFixture f;
  auto* expr = MakeSysCall(f.arena, "$bits", {MakeInt(f.arena, 42)});
  auto result = EvalExpr(expr, f.ctx, f.arena);
  EXPECT_EQ(result.ToUint64(), 32u);
}

// §20.6.2: applying $bits directly to a dynamically sized type identifier
// (queue typedef here) has no defined extent and shall be an error.
TEST(BitsCallRestrictions, BitsOnQueueTypedefIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  int n;\n"
      "  initial n = $bits(qt);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.6.2: the same query on a fixed-size type identifier is legal.
TEST(BitsCallRestrictions, BitsOnFixedTypedefIsLegal) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef logic [3:0] ft;\n"
      "  int n;\n"
      "  initial n = $bits(ft);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.6.2: $bits shall not enclose a function whose return type is a
// dynamically sized data type.
TEST(BitsCallRestrictions, BitsEnclosingDynamicReturnFuncIsError) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  typedef byte qt[$];\n"
      "  function qt mkq(); return mkq; endfunction\n"
      "  int n;\n"
      "  initial n = $bits(mkq());\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.6.2 (with §8.26 satisfied): $bits shall not be applied to an object
// whose type is an interface class.
TEST(BitsCallRestrictions, BitsOnInterfaceClassObjectIsError) {
  ElabFixture f;
  Elaborate(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC h;\n"
      "  int n;\n"
      "  initial n = $bits(h);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}
