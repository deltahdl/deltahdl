#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"

// §6.22.3 "Assignment compatible" is a definitional subclause: it carries no
// BNF production and no "shall". It defines the category of
// assignment-compatible types as all equivalent types (see §6.22.2) plus all
// nonequivalent types that have implicit casting rules defined between them
// (§6.24), and gives three illustrating facts: all integral types are mutually
// assignment compatible, conversion can lose data by truncation or rounding,
// and compatibility can be one-directional (an enum value flows into an
// integral without a cast, but not the reverse). The whole classification is an
// elaborator-stage predicate, IsAssignmentCompatible in type_eval.cpp, so this
// clause's coverage lives at the elaborator stage. The runtime data-loss note
// is observed separately in the simulator canonical file.

using namespace delta;

namespace {

// ---------------------------------------------------------------------------
// Full-pipeline observation: production code applies IsAssignmentCompatible.
// A value-returning function's return statement is checked against its return
// type with IsAssignmentCompatible (elaborator_validate_funcchecks.cpp). This
// drives real source through parse+elaborate and observes the rule accepting a
// compatible return and rejecting an incompatible one -- the only difference
// between the two modules is the declared return type.
// ---------------------------------------------------------------------------

TEST(AssignmentCompatibleElaboration, FunctionReturnAcceptsIntegralValue) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function int f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration, FunctionReturnRejectsIncompatibleValue) {
  ElabFixture f;
  // A string return type is not assignment compatible with an integral literal
  // (no equivalence and no implicit casting rule), so IsAssignmentCompatible
  // returns false and the return statement is rejected.
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function string f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

// End-to-end input form: a real operand into an integral target. A real and an
// integral type have an implicit numeric conversion, so the return is accepted;
// this drives the real<->integral branch from real source rather than a
// hand-built type.
TEST(AssignmentCompatibleElaboration,
     FunctionReturnAcceptsRealValueIntoIntegral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function int f();\n"
      "    return 3.5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// End-to-end input form: an integral operand into a real target -- the other
// direction of the real<->integral implicit conversion.
TEST(AssignmentCompatibleElaboration,
     FunctionReturnAcceptsIntegralValueIntoReal) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function real f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// End-to-end NEGATIVE input form: a string operand into an integral target.
// A string is nonequivalent to an integral type and has no implicit casting
// rule, so the return is rejected. This is the reverse direction of the
// integral-into-string rejection above and exercises the residual (return
// false) branch from real source.
TEST(AssignmentCompatibleElaboration,
     FunctionReturnRejectsStringValueIntoIntegral) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function int f();\n"
      "    return \"nope\";\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_TRUE(f.diag.HasErrors());
}

// End-to-end input form built from dependency §6.22.2 syntax: the return type
// is a sized signed packed vector (bit signed [31:0]), which §6.22.2 governs
// and which the §6.22 head treats as interchangeable with int. Assigning an
// integral literal to it is accepted -- the operand type is produced by real
// declaration syntax, not hand-built, and production applies the rule.
TEST(AssignmentCompatibleElaboration,
     FunctionReturnAcceptsSizedSignedVectorType) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  function bit signed [31:0] f();\n"
      "    return 5;\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// Full-pipeline accept paths: assignment-compatible declarations elaborate
// clean. int <-> bit signed [31:0] interchange is the §6.22 head example.
// ---------------------------------------------------------------------------

TEST(AssignmentCompatibleElaboration, AssignRealToInt) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  real r;\n"
      "  int i;\n"
      "  initial i = r;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

TEST(AssignmentCompatibleElaboration, IntAndBitSignedAreInterchangeable) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top;\n"
      "  int x;\n"
      "  bit signed [31:0] y;\n"
      "  initial begin\n"
      "    x = y;\n"
      "    y = x;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// ---------------------------------------------------------------------------
// Classification matrix. IsAssignmentCompatible is a pure elaborator-stage
// predicate over two data types; these exercise the type-pair cases that a
// single accepting/rejecting source site cannot all reach at once.
// ---------------------------------------------------------------------------

// C1: all equivalent types are assignment compatible (equivalent branch, which
// consumes §6.22.2). logic and reg are equivalent.
TEST(AssignmentCompatibleElaboration, EquivalentTypesAreCompatible) {
  DataType a;
  a.kind = DataTypeKind::kLogic;
  DataType b;
  b.kind = DataTypeKind::kReg;
  EXPECT_TRUE(TypesEquivalent(a, b));
  EXPECT_TRUE(IsAssignmentCompatible(a, b));
}

// C2: all integral types are assignment compatible in both directions.
TEST(AssignmentCompatibleElaboration, IntegralCompatibilityIsSymmetric) {
  DataType i;
  i.kind = DataTypeKind::kInt;
  i.is_signed = true;
  DataType l;
  l.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(i, l));
  EXPECT_TRUE(IsAssignmentCompatible(l, i));

  DataType byte_t;
  byte_t.kind = DataTypeKind::kByte;
  DataType shortint_t;
  shortint_t.kind = DataTypeKind::kShortint;
  EXPECT_TRUE(IsAssignmentCompatible(byte_t, shortint_t));
  EXPECT_TRUE(IsAssignmentCompatible(shortint_t, byte_t));
}

// C2/C1: real and integral types have implicit numeric conversion, both ways;
// the real family is mutually compatible.
TEST(AssignmentCompatibleElaboration, RealAndIntegralNumericConversion) {
  DataType real_t;
  real_t.kind = DataTypeKind::kReal;
  DataType logic_t;
  logic_t.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(real_t, logic_t));
  EXPECT_TRUE(IsAssignmentCompatible(logic_t, real_t));

  DataType shortreal_t;
  shortreal_t.kind = DataTypeKind::kShortreal;
  DataType realtime_t;
  realtime_t.kind = DataTypeKind::kRealtime;
  EXPECT_TRUE(IsAssignmentCompatible(real_t, shortreal_t));
  EXPECT_TRUE(IsAssignmentCompatible(realtime_t, shortreal_t));
}

// C5: compatibility can be one-directional. An enum value is assignment
// compatible with an integral type, but an integral value is not assignment
// compatible with an enum (it needs an explicit cast).
TEST(AssignmentCompatibleElaboration, EnumToIntegralIsOneDirectional) {
  DataType enum_t;
  enum_t.kind = DataTypeKind::kEnum;
  DataType int_t;
  int_t.kind = DataTypeKind::kInt;
  int_t.is_signed = true;
  DataType logic_t;
  logic_t.kind = DataTypeKind::kLogic;
  EXPECT_TRUE(IsAssignmentCompatible(enum_t, int_t));
  EXPECT_TRUE(IsAssignmentCompatible(enum_t, logic_t));
  EXPECT_FALSE(IsAssignmentCompatible(int_t, enum_t));
  EXPECT_FALSE(IsAssignmentCompatible(logic_t, enum_t));
}

// C1 residual: nonequivalent types with no implicit casting rule between them
// are not assignment compatible.
TEST(AssignmentCompatibleElaboration, UnrelatedTypesAreNotCompatible) {
  DataType int_t;
  int_t.kind = DataTypeKind::kInt;

  DataType string_t;
  string_t.kind = DataTypeKind::kString;
  EXPECT_FALSE(IsAssignmentCompatible(string_t, int_t));

  DataType chandle_t;
  chandle_t.kind = DataTypeKind::kChandle;
  EXPECT_FALSE(IsAssignmentCompatible(chandle_t, int_t));

  DataType event_t;
  event_t.kind = DataTypeKind::kEvent;
  EXPECT_FALSE(IsAssignmentCompatible(event_t, int_t));
}

}  // namespace
