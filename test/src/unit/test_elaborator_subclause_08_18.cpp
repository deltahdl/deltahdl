#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(DataHidingElaboration, PublicMemberAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.x = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.secret = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration, ProtectedMemberAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  protected int hidden;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.hidden = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access protected member from outside", 8,
                            "8.18"));
}

TEST(DataHidingElaboration, LocalMethodAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local function int get_id();\n"
      "    return 0;\n"
      "  endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.get_id();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            10, "8.18"));
}

TEST(DataHidingElaboration, PublicMethodAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  function void show(); endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Packet p;\n"
             "    p = new;\n"
             "    p.show();\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ProtectedMethodAccessError) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  protected function void secret(); endfunction\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.secret();\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access protected member from outside", 8,
                            "8.18"));
}

TEST(DataHidingElaboration, ConstructorLocalAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  local function new();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, ConstructorProtectedAllowed) {
  EXPECT_TRUE(
      ElabOk("class C;\n"
             "  protected function new(int x);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  C c;\n"
             "endmodule\n"));
}

// §8.18: local members are not visible within subclasses.
// A base-class local accessed through a derived handle is still rejected.
TEST(DataHidingElaboration, LocalNotVisibleViaDerivedHandle) {
  ElabFixture f;
  ElabOk(
      "class Base;\n"
      "  local int secret;\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Derived d;\n"
      "    d = new;\n"
      "    d.secret = 1;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            10, "8.18"));
}

// §8.18: a protected member has all the characteristics of a local member
// except that it is inherited / visible to subclasses. A subclass method
// may reference an inherited protected property.
TEST(DataHidingElaboration, ProtectedAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected int hidden;\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int read_hidden();\n"
             "    return hidden;\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.18: the visible-to-subclasses characteristic of a protected member applies
// to methods as well as properties. A subclass method may call an inherited
// protected method — the method form of the preceding property test.
TEST(DataHidingElaboration, ProtectedMethodAccessibleInSubclassMethod) {
  EXPECT_TRUE(
      ElabOk("class Base;\n"
             "  protected function int secret();\n"
             "    return 7;\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "  function int reveal();\n"
             "    return secret();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Derived d;\n"
             "endmodule\n"));
}

// §8.18: within a class, a local property of the same class may be
// referenced even if it is in a different instance of the same class.
TEST(DataHidingElaboration, SameClassInstanceLocalAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

// §8.18: a protected member has all the characteristics of a local member
// (differing only in being inheritable). The same-class cross-instance
// reference permitted for a local property is therefore equally permitted for a
// protected one: a method may read a protected property of another instance of
// its own class.
TEST(DataHidingElaboration, SameClassInstanceProtectedAccessOk) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  protected int i;\n"
             "  function int compare(Packet other);\n"
             "    return (this.i == other.i);\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "endmodule\n"));
}

// The twelve cases below cover the child-statement links of Stmt that the
// §8.18 walk in src/elaborator/elaborator_validate_classes.cpp reaches for the
// first time now that WalkStmtsForVisibility and CollectBlockClassVarDecls both
// take their list from ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h. Each had written out six of
// the thirteen links, so an access in a link the walk was missing was never
// examined, and a handle declared in a link the collection was missing was
// never recorded with the class it was declared as.
//
// Each link a declaration can stand in takes a pair. The rejected case writes
// the access through the module-scope handle `p`, which the walk has to reach.
// The accepted case redeclares `p` in the same link as a handle to a class
// whose `secret` is public, so the access is legal and §8.18 has nothing to
// report.
//
// The accepted case guards that outcome rather than isolating the collection.
// Elaborator::ValidateClassHandleOps in
// src/elaborator/elaborator_validate_class_handles.cpp already descends all
// thirteen links, it stands earlier in the ordered series
// Elaborator::ValidateModuleConstraints runs, and it records every block-local
// handle in Elaborator::class_var_types_ -- the map CollectBlockClassVarDecls
// is seeded from -- so the redeclaration reaches the §8.18 pass whatever the
// collection itself reaches. No case here can therefore separate the two
// walks, and the collection is converted because §8.18 is one rule and reading
// its two halves off two different lists is what put the reporter and the
// collector out of step to begin with.

// §8.18 states that a local member is unreachable from outside its class and
// puts no condition on the statement the access is written in. A.6.3 gives
// `par_block ::= fork [ : block_identifier ] { block_item_declaration } {
// statement_or_null } join_keyword`, so a fork arm holds both halves of this
// pair directly: the assignment here, and the declaration in the case below it,
// which Parser::ParseBlockVarDecls in src/parser/parser_stmt_block.cpp puts in
// Stmt::fork_stmts beside the statements.
TEST(DataHidingElaboration, LocalMemberAccessInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial fork\n"
      "    p.secret = 1;\n"
      "  join\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

TEST(DataHidingElaboration, HandleRedeclaredInAForkArmChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial fork\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  join\n"
             "endmodule\n"));
}

// A.6.8 gives `for_initialization ::= list_of_variable_assignments | ...` and
// `variable_assignment ::= variable_lvalue = expression`, and A.8.5 makes a
// member select a variable_lvalue, so a for header assigns through a class
// handle. The loop's control variable is declared above the loop, which leaves
// the header's assignment as the only access in the source.
//
// The link takes the rejected case alone. A for_variable_declaration is not a
// data_declaration and Parser::ParseForLocalDeclInits in
// src/parser/parser_stmt.cpp records it in Stmt::for_init_types beside the
// assignment, so no declaration statement ever stands in Stmt::for_inits for
// CollectBlockClassVarDecls to read.
TEST(DataHidingElaboration, LocalMemberAccessInAForInitializationIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  int i;\n"
      "  initial for (p.secret = 0; i < 2; i = i + 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

// A.6.8 gives `for_step_assignment ::= operator_assignment |
// inc_or_dec_expression | function_subroutine_call`, so a for step writes
// through a class handle the same way. None of the three declares a name, so
// this link takes the rejected case alone.
TEST(DataHidingElaboration, LocalMemberAccessInAForStepIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  int i;\n"
      "  initial for (i = 0; i < 2; p.secret = 1) ;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            7, "8.18"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// which Parser::ParseAssertStmt in src/parser/parser_assert.cpp puts in
// Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. A declaration is not a
// statement_or_null, so the accepted case of each pair writes its declaration
// inside a begin-end block the arm holds.
TEST(DataHidingElaboration, LocalMemberAccessInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial assert (1) p.secret = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            6, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInAnAssertionPassStmtChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial assert (1) begin\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(DataHidingElaboration, LocalMemberAccessInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial assert (1) else p.secret = 1;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            6, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInAnAssertionFailStmtChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial assert (1) else begin\n"
             "    Open p;\n"
             "    p.secret = 1;\n"
             "  end\n"
             "endmodule\n"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.18 is a rule about the source, so it holds whether the weighted
// draw would select the item or not, and the declaration again needs the
// begin-end block a statement_or_null admits.
TEST(DataHidingElaboration, LocalMemberAccessInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : p.secret = 1;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInARandcaseItemChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    randcase\n"
             "      1 : begin\n"
             "        Open p;\n"
             "        p.secret = 1;\n"
             "      end\n"
             "    endcase\n"
             "  end\n"
             "endmodule\n"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds both halves of this pair
// directly. Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// them in RsProd::code_stmts, which Stmt::rs_productions reaches and no other
// member of Stmt does.
TEST(DataHidingElaboration,
     LocalMemberAccessInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "class Packet;\n"
      "  local int secret;\n"
      "endclass\n"
      "module m;\n"
      "  Packet p;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { p.secret = 1; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot access local member from outside its class",
                            8, "8.18"));
}

TEST(DataHidingElaboration,
     HandleRedeclaredInARandsequenceCodeBlockChangesTheClassChecked) {
  EXPECT_TRUE(
      ElabOk("class Packet;\n"
             "  local int secret;\n"
             "endclass\n"
             "class Open;\n"
             "  int secret;\n"
             "endclass\n"
             "module m;\n"
             "  Packet p;\n"
             "  initial begin\n"
             "    randsequence(main)\n"
             "      main : { Open p; p.secret = 1; };\n"
             "    endsequence\n"
             "  end\n"
             "endmodule\n"));
}

}  // namespace
