// §25.9 "Virtual interfaces": the statement positions its operation rules
// reach. Every case here writes the same illegal addition of two virtual
// interfaces that AdditionOperator_Error in
// test_elaborator_subclause_25_09a.cpp writes at the top level of an initial
// block, and varies only the statement position it stands in.
//
// §25.9 states which operations a virtual interface admits and names no
// statement those rules are suspended in, so every child-statement link Stmt
// declares is a position the rule reaches.
// Elaborator::WalkStmtsForVirtualInterfaceOps in
// src/elaborator/elaborator_validate_datatype_ops.cpp had written out six of
// the thirteen links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h states, so the addition
// elaborated clean in any of the other seven. The walk now takes its list from
// ForEachChildStmt, and the cases below are one per newly reached position:
// A.6.3's par_block (Stmt::fork_stmts), A.6.8's for_initialization and
// for_step (Stmt::for_inits, Stmt::for_steps), A.6.10's action_block
// (Stmt::assert_pass_stmt, Stmt::assert_fail_stmt), §18.16's randcase_item
// (Stmt::randcase_items), and A.6.12's rs_code_block (Stmt::rs_productions).
//
// The cases for which operations §25.9 admits at all, and for the declarations
// that may name a virtual interface, are in
// test_elaborator_subclause_25_09a.cpp, which the 1000-line cap in
// .github/workflows/deltahdl.yml separated this file from.

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(VirtualInterfaceElaboration, AdditionOperatorInForkArm_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial fork\n"
      "    c = a + b;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInForInitialization_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  int i;\n"
      "  initial for (c = a + b; i < 1; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInForStep_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 1; c = a + b) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInAssertionPassStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial assert (1) c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInAssertionFailStmt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial assert (1) else c = a + b;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 4,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration, AdditionOperatorInRandcaseItem_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial randcase\n"
      "    1 : c = a + b;\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 5,
                            "25.9"));
}

TEST(VirtualInterfaceElaboration,
     AdditionOperatorInRandsequenceCodeBlock_Error) {
  ElabFixture f;
  ElaborateSrc(
      "interface simple_bus; endinterface\n"
      "module top;\n"
      "  virtual simple_bus a, b, c;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { c = a + b; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "operator is not allowed on virtual interface", 6,
                            "25.9"));
}

}  // namespace
