#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(Elaboration, AssocArgSameTypeOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  int aa[string];\n"
             "  function automatic int f(int x[string]);\n"
             "    return x[\"a\"];\n"
             "  endfunction\n"
             "  initial begin\n"
             "    aa[\"a\"] = 1;\n"
             "    f(aa);\n"
             "  end\n"
             "endmodule\n"));
}

TEST(Elaboration, AssocArgIndexTypeMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array index type mismatch in argument",
                            7, "7.9.10"));
}

TEST(Elaboration, FixedArrayToAssocArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int fa[4];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(fa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

TEST(Elaboration, DynamicArrayToAssocArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int da[];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(da);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

TEST(Elaboration, AssocArgToFixedArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(int x[4]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

TEST(Elaboration, AssocArgToDynamicArrayRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(int x[]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

TEST(Elaboration, AssocArgElementTypeMismatchRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 7, "7.9.10"));
}

TEST(Elaboration, AssocArgIntIndexOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  int aa[int];\n"
             "  function automatic int f(int x[int]);\n"
             "    return x[0];\n"
             "  endfunction\n"
             "  initial begin\n"
             "    f(aa);\n"
             "  end\n"
             "endmodule\n"));
}

// Compatible-type acceptance is not limited to an int element: a packed-vector
// element that matches between actual and formal (same width, same
// 4-state-ness) binds cleanly. Exercises the element-equivalence accept path
// for a non-int value type.
TEST(Elaboration, AssocArgPackedElementSameTypeOk) {
  EXPECT_TRUE(
      ElabOk("module top;\n"
             "  logic [7:0] aa[int];\n"
             "  function automatic logic [7:0] f(logic [7:0] x[int]);\n"
             "    return x[0];\n"
             "  endfunction\n"
             "  initial begin\n"
             "    aa[0] = 8'hAB;\n"
             "    f(aa);\n"
             "  end\n"
             "endmodule\n"));
}

// A queue is another array kind: it cannot be passed where an associative
// formal is expected, just like the fixed-size and dynamic cases.
TEST(Elaboration, QueueToAssocArgRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int q[$];\n"
      "  function automatic int g(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    g(q);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

// The reverse also holds: an associative array cannot be passed where a queue
// formal (another array kind) is expected.
TEST(Elaboration, AssocArgToQueueRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int g(int x[$]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    g(aa);\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array cannot be passed to or from a "
                            "non-associative array parameter",
                            7, "7.9.10"));
}

// The index-type compatibility rule still applies when the actual reaches the
// formal through a named argument binding rather than a positional one: a
// string-indexed actual bound by name to an int-indexed formal is rejected.
TEST(Elaboration, AssocArgIndexMismatchViaNamedBindingRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[string];\n"
      "  function automatic int f(int x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    f(.x(aa));\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "associative array index type mismatch in argument",
                            7, "7.9.10"));
}

// §7.9.10 governs the actual bound to an array formal and says nothing about
// the statement the call stands in, so every position a statement holds a
// statement in is a position the report is made at. WalkStmtForArrayArgTypes
// in src/elaborator/elaborator_validate_class_array_assign.cpp had written out
// eight of the thirteen child-statement links Stmt declares, and now takes the
// list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. The cases below cover one
// newly reached position each, all of them using the element-type mismatch of
// AssocArgElementTypeMismatchRejected above so that only the position varies.

// A.6.3 gives `par_block ::= fork [ : block_identifier ] {
// block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser keeps in Stmt::fork_stmts.
TEST(Elaboration, AssocArgElementTypeMismatchInForkArmRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial fork\n"
      "    f(aa);\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 7, "7.9.10"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(Elaboration, AssocArgElementTypeMismatchInAssertionPassStmtRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial assert (1) f(aa);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 6, "7.9.10"));
}

TEST(Elaboration, AssocArgElementTypeMismatchInAssertionFailStmtRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial assert (1) else f(aa);\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 6, "7.9.10"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, kept in
// Stmt::randcase_items.
TEST(Elaboration, AssocArgElementTypeMismatchInRandcaseItemRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial randcase\n"
      "    1 : f(aa);\n"
      "  endcase\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 7, "7.9.10"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(Elaboration, AssocArgElementTypeMismatchInRandsequenceCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { f(aa); };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 8, "7.9.10"));
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second statement list
// under Stmt::rs_productions, reached by a different member from
// RsProd::code_stmts, so the case above does not answer for it.
TEST(Elaboration,
     AssocArgElementTypeMismatchInRandsequenceWeightCodeBlockRejected) {
  ElabFixture f;
  ElaborateSrc(
      "module top;\n"
      "  int aa[int];\n"
      "  int i;\n"
      "  function automatic int f(logic [7:0] x[int]);\n"
      "    return x[0];\n"
      "  endfunction\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : alt := 1 { f(aa); };\n"
      "      alt : { i = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "associative array element type mismatch in argument", 9, "7.9.10"));
}

}  // namespace
