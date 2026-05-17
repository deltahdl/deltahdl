#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §10.8 item (a): "A continuous or procedural assignment." A procedural
// assignment is the canonical assignment-like context; the elaborator must
// accept an unprefixed structure literal whose type is determined by the LHS
// (per §5.10's cross-reference to §10.8).
TEST(AssignmentLikeContext, ProceduralAssignmentTypesStructLiteralFromLHS) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t s;\n"
             "  initial s = '{8'h11, 8'h22};\n"
             "endmodule\n"));
}

// §10.8 item (a): A continuous assignment is likewise assignment-like and
// types an unprefixed structure literal RHS from the LHS net's data type.
TEST(AssignmentLikeContext, ContinuousAssignmentTypesStructLiteralFromLHS) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  ab_t s;\n"
             "  assign s = '{8'h11, 8'h22};\n"
             "endmodule\n"));
}

// §10.8 item (b): "A parameter value assignment in a module ..." with an
// explicitly typed parameter is an assignment-like context — the parameter's
// declared type supplies the implicit type for an unprefixed structure
// literal default.
TEST(AssignmentLikeContext, ExplicitTypedParameterDefaultIsAssignmentLike) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  parameter ab_t P = '{8'h11, 8'h22};\n"
             "endmodule\n"));
}

// §10.8 item (d): "A port connection to an input or output port of a
// module ..." The instantiation's port connection types its RHS like an
// assignment — a structure literal connecting to a typed input port picks
// up the port's type without an explicit prefix.
TEST(AssignmentLikeContext, InputPortConnectionTypesStructLiteralFromPort) {
  EXPECT_TRUE(
      ElabOk("module inner(input struct packed {\n"
             "  logic [7:0] a; logic [7:0] b;\n"
             "} p);\n"
             "endmodule\n"
             "module t;\n"
             "  inner u(.p('{8'h11, 8'h22}));\n"
             "endmodule\n"));
}

// §10.8 item (e): "The passing of a value to a subroutine input, output, or
// inout argument." A struct-typed task input is an assignment-like context
// for the structure literal actual at the call site. §10.8 cross-links to
// §13.3 here — the task's formal supplies the LHS type.
TEST(AssignmentLikeContext, SubroutineInputArgTypesStructLiteralFromFormal) {
  EXPECT_TRUE(
      ElabOk("module t;\n"
             "  typedef struct packed { logic [7:0] a; logic [7:0] b; } ab_t;\n"
             "  task consume(input ab_t s);\n"
             "  endtask\n"
             "  initial consume('{8'h11, 8'h22});\n"
             "endmodule\n"));
}

// §10.8 exclusion: "A port connection to an inout or ref port of a module,
// interface, or program" is NOT an assignment-like context. An inout port
// must be connected to a net (not a variable) — there is no implicit
// assignment-like coercion that would copy a variable's value into the
// inout port, so the elaborator rejects the variable-to-inout connection
// rather than silently treating it as an assignment.
TEST(AssignmentLikeContext, InoutPortVariableConnectionRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(inout wire [7:0] p);\n"
      "endmodule\n"
      "module top;\n"
      "  logic [7:0] v;\n"
      "  sub u(.p(v));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

// §10.8 exclusion: "The passing of a value to a subroutine ref port" is NOT
// an assignment-like context. A ref port requires a variable; a net actual
// would have to be assignment-coerced into the formal, but §10.8 forbids
// that classification — so the elaborator rejects net-to-ref-port binding.
TEST(AssignmentLikeContext, RefPortNetBindingRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module sub(ref logic [7:0] p);\n"
      "endmodule\n"
      "module top;\n"
      "  wire [7:0] w;\n"
      "  sub u(.p(w));\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.diag.HasErrors());
}

}  // namespace
