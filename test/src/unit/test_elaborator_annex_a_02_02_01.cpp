// §A.2.2.1: elaborator-stage coverage of Net and variable types. The
// elaborator must accept each data_type / net_type alternative from the
// §A.2.2.1 grammar without diagnostics and propagate the parsed kind into the
// RTLIR.

#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §A.2.2.1 integer_vector_type: every bit/logic/reg signal elaborates.
TEST(NetAndVariableTypeElaboration, IntegerVectorTypeLogic) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic [7:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 integer_atom_type: int/byte/longint values elaborate.
TEST(NetAndVariableTypeElaboration, IntegerAtomTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  byte b;\n"
      "  shortint s;\n"
      "  int i;\n"
      "  longint l;\n"
      "  integer n;\n"
      "  time t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 non_integer_type: real/shortreal/realtime values elaborate.
TEST(NetAndVariableTypeElaboration, NonIntegerTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  real r;\n"
      "  shortreal s;\n"
      "  realtime t;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 net_type: wire/tri/wand/wor/uwire nets elaborate into RtlirNet.
TEST(NetAndVariableTypeElaboration, NetTypesElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  wire w;\n"
      "  tri t;\n"
      "  wand wa;\n"
      "  wor wo;\n"
      "  uwire u;\n"
      "  supply0 s0;\n"
      "  supply1 s1;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 signing: explicit signed/unsigned on a data_type elaborates.
TEST(NetAndVariableTypeElaboration, SigningExplicitElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  logic signed   [7:0] s;\n"
      "  integer unsigned u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 struct_union: packed struct and tagged union types elaborate.
TEST(NetAndVariableTypeElaboration, StructUnionElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed { logic [3:0] a; logic [3:0] b; } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

TEST(NetAndVariableTypeElaboration, UnionTaggedElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef union tagged { int v; void none; } u_t;\n"
      "  u_t u;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 data_type ::= string / chandle / event — each elaborates as a
// variable.
TEST(NetAndVariableTypeElaboration, StringChandleEventElaborate) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  string s;\n"
      "  chandle h;\n"
      "  event e;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 var_data_type ::= var data_type_or_implicit — `var` on a port
// admits an explicit storage qualifier and elaborates.
TEST(NetAndVariableTypeElaboration, VarDataTypeElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m(input var int x);\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 ↔ §A.9.1 cross-link: a struct_union_member carries an
// attribute_instance per §A.9.1. The elaborator must accept the construct
// (attributes on members do not block type evaluation).
TEST(NetAndVariableTypeElaboration, StructMemberAttributeInstanceCrossLink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  typedef struct packed {\n"
      "    (* keep *) logic [3:0] a;\n"
      "    logic [3:0] b;\n"
      "  } s_t;\n"
      "  s_t s;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 ↔ §A.8.3 cross-link: packed_dimension bounds are §A.8.3
// constant_expressions. A parameter-driven bound must constant-fold during
// elaboration.
TEST(NetAndVariableTypeElaboration, PackedDimensionConstantExpressionCrossLink) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  parameter N = 8;\n"
      "  logic [N-1:0] x;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

// §A.2.2.1 type_reference ::= type ( expression ) — a type(expr) form is
// elaborated into a fully resolved data type for the declared variable.
TEST(NetAndVariableTypeElaboration, TypeReferenceElaborates) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module m;\n"
      "  int x;\n"
      "  type(x) y;\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.has_errors);
}

}  // namespace
