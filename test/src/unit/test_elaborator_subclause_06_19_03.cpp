#include "common/types.h"
#include "elaborator/sensitivity.h"
#include "elaborator/type_eval.h"
#include "fixture_elaborator.h"
#include "helpers_reported_error.h"
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

// §6.19.3: the strong-typing rule holds in every procedural block, not only in
// `initial` and `always`. An integer assigned to an enum variable inside an
// `always_comb` block is rejected exactly as EnumStrictTypeCheck_Error's
// `initial` form is.
TEST(Elaboration, EnumAlwaysCombIntAssign_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  always_comb val = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 4,
                            "6.19.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "compound assignment to enum variable without cast",
                            5, "6.19.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "increment/decrement of enum variable without cast",
                            5, "6.19.3"));
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
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 4,
                            "6.19.3"));
}

TEST(Elaboration, EnumModuleLevelInitInt_Error) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 3,
                            "6.19.3"));
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
  EXPECT_TRUE(ReportedError(
      f.diag.Diagnostics(),
      "integer value passed to enum argument without cast", 8, "6.19.3"));
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

// §6.19.3: assigning a same-type enumerated variable to another is a well-typed
// assignment and needs no cast — the strong-typing rule constrains only values
// drawn from outside the enumeration, not another value of the very same type.
// This exercises the enum-variable operand form, distinct from the enum
// named-constant operand covered by EnumMemberAssign_Ok.
TEST(Elaboration, EnumSameTypeVarAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e src;\n"
      "    e dst;\n"
      "    src = b;\n"
      "    dst = src;\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3: casting is the sanctioned route for placing a value of a different
// type, or an out-of-set value, into an enum variable. Built from the §6.24.2
// dynamic-cast dependency ($cast), the same integral value that a direct
// assignment rejects (cf. EnumStrictTypeCheck_Error) reaches the enum without a
// strong-typing diagnostic, distinct from the §6.24.1 static-cast form covered
// by EnumCastAssign_Ok.
TEST(Elaboration, EnumDynamicCastAssign_Ok) {
  ElabFixture f;
  auto* design = ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    e val;\n"
      "    $cast(val, 2);\n"
      "  end\n"
      "endmodule\n",
      f);
  ASSERT_NE(design, nullptr);
  EXPECT_FALSE(f.diag.HasErrors());
}

// §6.19.3 is stated of the assignment and names no statement it is suspended
// in, so Elaborator::WalkStmtsForEnumAssign in
// src/elaborator/elaborator_validate_types.cpp descends every link
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h names. The
// cases below cover the seven links the walk used to omit. Each link that can
// hold a declaration takes a pair, because the walk both reports the offending
// assignment and collects the enum variables a statement declares into
// Elaborator::enum_var_names_: the first case declares the variable outside the
// link and assigns inside it, which exercises the report, and the second
// declares it inside the link, which exercises the collection.

// §9.3.2 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, so a fork arm
// holds both halves of this pair. Parser::ParseBlockVarDecls in
// src/parser/parser_stmt_block.cpp puts the declarations in Stmt::fork_stmts
// beside the statements.
TEST(Elaboration, EnumIntAssignInAForkArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    fork\n"
      "      val = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInAForkArmIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    fork\n"
      "      e val;\n"
      "      val = 1;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...`, so a
// for header assigns to any variable in scope, an enum variable among them.
//
// The other form A.6.8 admits there, `for_variable_declaration ::= [ var ]
// data_type variable_identifier = expression { , ... }`, takes no case of its
// own: Parser::ParseForLocalDeclInits in src/parser/parser_stmt.cpp records the
// declared type in Stmt::for_init_types and pushes the initialization into
// Stmt::for_inits as a plain assignment statement, so no statement in the link
// satisfies StmtDeclaresEnumVar and the collecting half of the walk has nothing
// there to reach whatever it descends.
TEST(Elaboration, EnumIntAssignInAForInitializationIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (val = 1; i < 2; i = i + 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, so a for step assigns to
// an enum variable the same way. None of the three declares a name, so this
// link takes the assignment case alone: no conforming source puts a
// declaration in a for step for the collecting half of the walk to find.
TEST(Elaboration, EnumIntAssignInAForStepIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  int i;\n"
      "  initial begin\n"
      "    for (i = 0; i < 2; val = 1) ;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

// §16.3 and A.6.10 give `action_block ::= statement_or_null | [ statement ]
// else statement_or_null`, so an immediate assertion holds a statement in each
// arm, kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. A
// declaration is not a statement_or_null, so the collecting case of each pair
// writes the declaration in a begin-end block the arm holds, which is reached
// through that arm and through no other link.
TEST(Elaboration, EnumIntAssignInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    assert (1) val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    assert (1) begin\n"
      "      e val;\n"
      "      val = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumIntAssignInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    assert (1) else val = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    assert (1) else begin\n"
      "      e val;\n"
      "      val = 1;\n"
      "    end\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §6.19.3 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(Elaboration, EnumIntAssignInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : val = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInARandcaseItemIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : begin\n"
      "        e val;\n"
      "        val = 1;\n"
      "      end\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 7,
                            "6.19.3"));
}

// §18.17 and A.6.12 give `rs_code_block ::= { { data_declaration }
// { statement_or_null } }`, so a randsequence production's code block holds
// both halves of this pair directly. Parser::ParseRsCodeBlockStmts in
// src/parser/parser_verify.cpp puts them in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(Elaboration, EnumIntAssignInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  e val;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { val = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 6,
                            "6.19.3"));
}

TEST(Elaboration, EnumDeclaredAndAssignedInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElaborateSrc(
      "module top();\n"
      "  typedef enum {a, b, c, d} e;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { e val; val = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "integer assigned to enum variable without cast", 5,
                            "6.19.3"));
}

}  // namespace
