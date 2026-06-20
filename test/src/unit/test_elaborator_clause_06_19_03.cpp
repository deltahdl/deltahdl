#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "lexer/token.h"

using namespace delta;

namespace {

TEST(Elaboration, EnumStrictTypeCheck_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumMemberAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = c;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumCastAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = e'(2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(Elaboration, EnumNonblockingIntAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  always @(*) begin\n"
      "    val <= 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumExprAssignNoCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int x;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = x + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.19.3: a compound assignment writes the arithmetic result back into the
// enum variable, which is an arbitrary-expression assignment and therefore
// requires an explicit cast — without one the strong-typing rule is violated.
TEST(Elaboration, EnumCompoundAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val += 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.19.3: an increment likewise stores an integral result into the enum
// variable without a cast, so the strong-typing rule rejects it.
TEST(Elaboration, EnumIncrement_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val++;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumLocalVarInitInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumModuleLevelInitInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

TEST(Elaboration, EnumModuleLevelInitMember_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val = c;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3: enumeration values can still be used as constants in expressions and
// the result assigned to a variable of a compatible integral type. The strong
// typing only constrains the enum side, never the read-out into an integral.
TEST(Elaboration, EnumValueAssignedToInt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int y;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = c;\n"
      "    y = val;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3: enumerated variables are auto-cast into integral values, so an enum
// term may appear inside an arithmetic expression whose result feeds an
// integral target without any explicit cast.
TEST(Elaboration, EnumAutoCastInIntExpr_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int y;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = b;\n"
      "    y = val + 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3: enumerated variables are type-checked in arguments — passing a bare
// integral value to an enum-typed formal requires an explicit cast, just as a
// direct assignment would.
TEST(Elaboration, EnumArgIntWithoutCast_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  function automatic int g(e p);\n"
      "    return 0;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = g(1);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §6.19.3: an enum member passed by name to an enum-typed formal is well-typed.
TEST(Elaboration, EnumArgMember_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  function automatic int g(e p);\n"
      "    return 0;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = g(c);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3: an explicit cast supplies a legal value for an enum-typed formal.
TEST(Elaboration, EnumArgCast_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  function automatic int g(e p);\n"
      "    return 0;\n"
      "  endfunction\n"
      "  int y;\n"
      "  initial begin\n"
      "    y = g(e'(1));\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3: the strong-typing prohibition carves out an exception for an enum
// that is a member of a union — such a member may take a direct out-of-set
// value without an explicit cast, unlike a standalone enum variable (cf.
// EnumStrictTypeCheck_Error, which rejects the same assignment).
TEST(Elaboration, EnumUnionMemberDirectIntAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  typedef union { e f; int i; } u_t;\n"
      "  u_t u;\n"
      "  initial begin\n"
      "    u.f = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3: enumerated variables are type-checked with relational operators by
// being auto-cast to their integral value, so comparing an enum against a plain
// integer (cf. the `if (1 == c)` example) is well-typed and not an error.
TEST(Elaboration, EnumRelationalCompareWithInt_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  int y;\n"
      "  initial begin\n"
      "    e val;\n"
      "    val = c;\n"
      "    if (1 == val) y = 0;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

}  // namespace
