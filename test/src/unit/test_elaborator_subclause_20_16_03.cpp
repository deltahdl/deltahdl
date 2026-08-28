#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

// §20.16.3: "PLA input terms, output terms, and memory shall be specified in
// ascending order." The LRM's own examples declare the memory as
// `logic [1:n] mem[1:m]`, with both the width (packed) and depth (unpacked)
// ranges ascending; such a call elaborates cleanly.
TEST(PlaAscendingOrder, AscendingMemoryAndTermsAreAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: a memory whose packed (width) range descends violates the
// ascending-order requirement.
TEST(PlaAscendingOrder, DescendingMemoryWidthIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task shall be "
                            "declared in ascending order",
                            5, "20.16.3"));
}

// §20.16.3: the depth (unpacked) range of the memory is equally subject to the
// rule; a descending unpacked dimension is rejected.
TEST(PlaAscendingOrder, DescendingMemoryDepthIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [3:1];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task shall be "
                            "declared in ascending order",
                            5, "20.16.3"));
}

// §20.16.3: a descending input-terms vector violates the rule.
TEST(PlaAscendingOrder, DescendingInputTermsAreRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [7:1] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the input terms of a PLA modeling system task "
                            "shall be specified in ascending order",
                            5, "20.16.3"));
}

// §20.16.3: a descending output-terms vector violates the rule.
TEST(PlaAscendingOrder, DescendingOutputTermsAreRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [3:1] breg;\n"
      "  initial $sync$or$plane(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output terms of a PLA modeling system task "
                            "shall be specified in ascending order",
                            5, "20.16.3"));
}

// §20.16.3: an equal-bound (one-bit) range is its own ascending and descending
// form; treating it as ascending keeps a scalar-width term legal. This pins the
// boundary of the left <= right test.
TEST(PlaAscendingOrder, EqualBoundRangeIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire [1:1] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: terms given as a concatenation of scalars carry no declared range,
// so the structural check leaves them alone — the ascending-order requirement
// on the listing order is the modeler's responsibility, not a range violation.
TEST(PlaAscendingOrder, ConcatenatedScalarTermsAreNotRangeChecked) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] mem [1:3];\n"
      "  wire a1, a2, a3, a4, a5, a6, a7;\n"
      "  logic b1, b2, b3;\n"
      "  initial $async$and$array(mem, {a1,a2,a3,a4,a5,a6,a7}, {b1,b2,b3});\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: the declared range bounds are §11.2.1 constant expressions, so a
// bound may be a parameter rather than an integer literal — the LRM's own
// example declares the memory with symbolic bounds. A parameter-valued packed
// range that folds to a descending direction must be caught the same way a
// literal descending range is; folding the bound in the module parameter scope
// is a different code path from a literal.
TEST(PlaAscendingOrder, DescendingMemoryWidthViaParameterIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  logic [P:1] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task shall be "
                            "declared in ascending order",
                            6, "20.16.3"));
}

// §20.16.3: the accepting path for the same parameter input form — a
// parameter-valued packed range that folds ascending elaborates cleanly.
TEST(PlaAscendingOrder, AscendingMemoryWidthViaParameterIsAccepted) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  parameter P = 7;\n"
      "  logic [1:P] mem [1:3];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3: a localparam is the other §11.2.1 constant form that a range bound
// admits. A localparam-valued unpacked (depth) bound that folds descending is
// rejected just like a literal one.
TEST(PlaAscendingOrder, DescendingMemoryDepthViaLocalparamIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  localparam Q = 3;\n"
      "  logic [1:7] mem [Q:1];\n"
      "  wire [1:7] awire;\n"
      "  logic [1:3] breg;\n"
      "  initial $async$and$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task shall be "
                            "declared in ascending order",
                            6, "20.16.3"));
}

// §20.16.3, scoped against §20.16's task table: the ascending-order rule
// applies only to recognized PLA tasks. A descending memory passed to a name
// that is not one of the enumerated tasks raises no ascending-order error.
TEST(PlaAscendingOrder, NonPlaTaskNameIsNotRangeChecked) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] mem [1:3];\n"
      "  wire [7:1] awire;\n"
      "  logic [3:1] breg;\n"
      "  initial $async$xor$array(mem, awire, breg);\n"
      "endmodule\n",
      f);
  EXPECT_FALSE(f.has_errors);
}

// §20.16.3 states its rule over the memory and term arguments of a PLA
// modeling system task -- "PLA input terms, output terms, and memory shall be
// specified in ascending order" -- and names no position the call may stand
// in. Each of the four cases below writes the call in one such position, and
// each is a position CheckPlaAscendingStmt in
// src/elaborator/elaborator_validate_queries.cpp reached only once it took its
// list of nested statements from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Every one of them elaborated
// clean beforehand, with a descending range left where the clause requires an
// ascending one.
//
// Stmt::for_steps is the fifth position that list added and it carries no case
// here, for the reason the same conversion records in
// test/src/unit/test_elaborator_subclause_20_16.cpp: a PLA task returns no
// value and the one form Syntax 20-16 defines ends in a semicolon, while none
// of A.6.8's three for_step_assignment forms takes one.
//
// The three arguments the clause names are spread across the cases so that no
// two of them assert the same report.

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm.
// The parser keeps the pass arm in Stmt::assert_pass_stmt.
TEST(PlaAscendingOrder, DescendingMemoryInAnAssertionPassStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [7:1] amem [1:3];\n"
      "  wire [1:7] ain;\n"
      "  logic [1:3] aout;\n"
      "  logic ready;\n"
      "  initial assert (ready) $sync$nand$array(amem, ain, aout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task shall be "
                            "declared in ascending order",
                            6, "20.16.3"));
}

// §16.3's else arm of the same action block, kept in Stmt::assert_fail_stmt.
// The memory and the output terms here are ascending, so the input terms are
// the only argument that can carry the report.
TEST(PlaAscendingOrder,
     DescendingInputTermsInAnAssertionFailStatementIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] bmem [1:3];\n"
      "  wire [7:1] bterm;\n"
      "  logic [1:3] bout;\n"
      "  logic done;\n"
      "  initial assert (done) else $async$nor$plane(bmem, bterm, bout);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the input terms of a PLA modeling system task "
                            "shall be specified in ascending order",
                            6, "20.16.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, so a
// randcase holds a statement per item, kept in Stmt::randcase_items. The
// output terms are declared descending and are variables, so §20.16's separate
// requirement that they not be nets is satisfied and cannot account for the
// report.
TEST(PlaAscendingOrder, DescendingOutputTermsInARandcaseItemIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] cmem [1:3];\n"
      "  wire [1:7] cterm;\n"
      "  logic [3:1] cout;\n"
      "  initial randcase 1: $sync$and$plane(cmem, cterm, cout); endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the output terms of a PLA modeling system task "
                            "shall be specified in ascending order",
                            5, "20.16.3"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements, kept in RsProd::code_stmts and reached through
// Stmt::rs_productions. The memory's packed range is ascending and its
// unpacked one is not, which is the second of the two ranges §20.16.3 reads
// off a memory declaration.
TEST(PlaAscendingOrder,
     DescendingMemoryDepthInARandsequenceCodeBlockIsRejected) {
  ElabFixture f;
  Elaborate(
      "module m;\n"
      "  logic [1:7] dmem [3:1];\n"
      "  wire [1:7] dterm;\n"
      "  logic [1:3] dout;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { $async$or$array(dmem, dterm, dout); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "the memory of a PLA modeling system task shall be "
                            "declared in ascending order",
                            7, "20.16.3"));
}

}  // namespace
