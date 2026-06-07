#include "fixture_elaborator.h"

using namespace delta;

namespace {

// §20.16: the output terms of a PLA modeling system task shall only be
// variables. A single variable output term elaborates cleanly.
TEST(PlaOutputTerms, VariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic b;\n"
      "  initial $async$and$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: a net used as the output term violates the shall and is rejected.
TEST(PlaOutputTerms, NetOutputIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$and$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16: a concatenation of variable output terms is permitted.
TEST(PlaOutputTerms, ConcatenatedVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a1, a2;\n"
      "  logic b1, b2, b3;\n"
      "  initial $sync$or$plane(mem, {a1, a2}, {b1, b2, b3});\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: a concatenation of output terms that includes a net is rejected,
// because every output term must be a variable.
TEST(PlaOutputTerms, ConcatenatedOutputWithNetIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic b1;\n"
      "  wire b2;\n"
      "  initial $async$nor$array(mem, a, {b1, b2});\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

// §20.16: the restriction applies only to output terms. An input term may be a
// net, so a net input paired with a variable output elaborates cleanly.
TEST(PlaOutputTerms, NetInputWithVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire a;\n"
      "  logic b;\n"
      "  initial $sync$nand$plane(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16, Table 20-12: the output-terms restriction applies only to the
// enumerated PLA tasks. A name whose logic component is not one of
// and/or/nand/nor is not a PLA task, so a net in its third argument does not
// trigger the rule. This pins the boundary of which names are recognized.
TEST(PlaOutputTerms, NonTableNameIsNotSubjectToTheRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$xor$array(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16, Table 20-12: a name carrying more than the three
// array_type/logic/format components is not one of the enumerated tasks, so the
// output-terms rule does not apply even with a net in the output position.
TEST(PlaOutputTerms, NameWithExtraComponentIsNotSubjectToTheRule) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire b;\n"
      "  initial $async$and$array$extra(mem, a, b);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: an output term may be a select of a variable, which remains a
// variable reference and is accepted.
TEST(PlaOutputTerms, BitSelectOfVariableOutputIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  logic [3:0] b;\n"
      "  initial $sync$or$array(mem, a, b[0]);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16: a select of a net still references a net, not a variable, so using it
// as an output term violates the shall and is rejected.
TEST(PlaOutputTerms, BitSelectOfNetOutputIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  logic a;\n"
      "  wire [3:0] b;\n"
      "  initial $async$and$array(mem, a, b[0]);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(f.has_errors);
}

}  // namespace
