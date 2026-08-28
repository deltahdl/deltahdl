#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(InterfaceClassCastingAndRefAssignment, InterfaceRefAssignOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

TEST(InterfaceClassCastingAndRefAssignment, AssignImplHandleToIfaceVarOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo implements PutImp;\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo fifo_obj;\n"
             "    PutImp put_ref;\n"
             "    fifo_obj = new;\n"
             "    put_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     AssignImplHandleToMultipleIfaceVarsOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "interface class GetImp;\n"
             "  pure virtual function void get();\n"
             "endclass\n"
             "class Fifo implements PutImp, GetImp;\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "  virtual function void get();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo fifo_obj;\n"
             "    PutImp put_ref;\n"
             "    GetImp get_ref;\n"
             "    fifo_obj = new;\n"
             "    put_ref = fifo_obj;\n"
             "    get_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassNewError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    IC ic;\n"
      "    ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

// §8.26.5: assigning an object handle to an interface-class variable the object
// implements is legal when written as a declaration initializer too -- the
// exact syntactic form the LRM example uses (`PutImp put_ref = fifo_obj;`),
// which is distinct from the procedural-assignment form covered above.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignImplHandleToIfaceVarDeclInitOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp;\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo implements PutImp;\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo fifo_obj = new;\n"
             "    PutImp put_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: assigning an object handle to an interface-class variable is legal
// only when the object's class implements that interface. Class C does not
// implement IC, so the handle assignment is not assignment compatible and must
// be rejected at elaboration.
//
// The report that rejects it is the general class-handle assignment
// compatibility check in CheckClassHandleAssignCompatibility
// (src/elaborator/elaborator_validate_class_handles.cpp), which passes
// Subclause("8.4") — §8.4 is where the standard states that a handle may only
// be assigned from an assignment-compatible type, and §8.26.5 is what makes an
// implementing class compatible with the interface. The subclause asserted is
// the one the emission site passes.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignUnimplementedHandleToIfaceVarError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C c_obj;\n"
      "    IC ic_ref;\n"
      "    c_obj = new;\n"
      "    ic_ref = c_obj;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "class handle assignment requires assignment compatible "
                    "types",
                    11, "8.4"));
}

// §8.26.5: an object of an interface class type shall not be constructed. The
// construction here is written as a block-local declaration initializer
// (`IC ic = new;`) rather than a procedural assignment, and must be rejected
// just the same.
TEST(InterfaceClassCastingAndRefAssignment, InterfaceClassNewDeclInitError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    IC ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 6,
                            "8.26.5"));
}

// §8.26.5: the interface-class construction prohibition also applies when the
// declaration initializer appears at module scope (`IC ic = new;` as a module
// item) rather than inside a procedural block.
TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewModuleScopeDeclInitError) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic = new;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 5,
                            "8.26.5"));
}

// §8.26.5: the construction prohibition is specific to interface classes; a
// declaration initializer that constructs a concrete class implementing the
// interface is legal and must still elaborate. This guards the new decl-init
// check against over-rejecting ordinary class construction.
TEST(InterfaceClassCastingAndRefAssignment, ConcreteClassNewDeclInitOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class C implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    C c = new;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: the object-handle-to-interface-variable assignment is legal when the
// interface class is parameterized and the object's class implements the same
// specialization -- the exact shape of the LRM's own example
// (`PutImp#(int) put_ref = fifo_obj;`). The interface class and the
// implementing class both carry a type parameter, so this exercises the
// assignment-compatibility check across parameterized types, a distinct input
// form from the non-parameterized cases above.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignParamImplHandleToParamIfaceVarOk) {
  EXPECT_TRUE(
      ElabOk("interface class PutImp #(type T = logic);\n"
             "  pure virtual function void put();\n"
             "endclass\n"
             "class Fifo #(type T = int) implements PutImp #(T);\n"
             "  virtual function void put();\n"
             "  endfunction\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Fifo #(int) fifo_obj;\n"
             "    PutImp #(int) put_ref;\n"
             "    fifo_obj = new;\n"
             "    put_ref = fifo_obj;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: a class implements an interface class when it does so through a
// superclass as well as directly. Assigning a derived-class object handle to a
// variable of an interface class implemented by the base class is legal, so the
// assignment-compatibility check must accept it -- an input form where the
// implements relationship is produced by inheritance rather than a direct
// implements clause on the object's own class.
TEST(InterfaceClassCastingAndRefAssignment,
     AssignInheritedImplHandleToIfaceVarOk) {
  EXPECT_TRUE(
      ElabOk("interface class IC;\n"
             "  pure virtual function void foo();\n"
             "endclass\n"
             "class Base implements IC;\n"
             "  virtual function void foo();\n"
             "  endfunction\n"
             "endclass\n"
             "class Derived extends Base;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    Derived d;\n"
             "    IC ic;\n"
             "    d = new;\n"
             "    ic = d;\n"
             "  end\n"
             "endmodule\n"));
}

// §8.26.5: the prohibition on constructing an interface-class object applies to
// a parameterized interface class the same as a plain one -- constructing a
// specialization such as `PutImp#(int)` with 'new' must still be rejected.
TEST(InterfaceClassCastingAndRefAssignment, ParamInterfaceClassNewError) {
  ElabFixture f;
  ElabOk(
      "interface class PutImp #(type T = logic);\n"
      "  pure virtual function void put();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    PutImp #(int) p;\n"
      "    p = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

// The seven cases below, and the note that closes them, carry §8.26.5's
// construction prohibition into each statement link
// Elaborator::WalkStmtsForClassHandleOps in
// src/elaborator/elaborator_validate_class_handles.cpp did not read before
// #3319. That walk wrote out six of the thirteen links ForEachChildStmt in
// src/elaborator/elaborator_validate_internal.h names, so a `new` on an
// interface class handle one level down -- in a fork arm, an assertion action
// block, a randcase item or a randsequence code block -- reached neither
// CheckNewOnUnconstructibleHandle nor CheckNewOnInterfaceDeclInit.
//
// The two checks take separate cases because they answer different sources:
// the first reads a procedural assignment (`ic = new;`), the second a
// declaration initializer (`IC ic = new;`), and A.6.3 and A.6.12 are the only
// two of the seven links that admit a declaration at all.
//
// Each report stands at the offending statement, which is where both checks
// anchor it, so every case names the line its own `new` is written on.

// A.6.3 gives `par_block ::= fork [ : block_identifier ]
// { block_item_declaration } { statement_or_null } join_keyword`, whose
// statements the parser puts in Stmt::fork_stmts.

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    fork\n"
      "      ic = new;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 8,
                            "8.26.5"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// one below it cover one arm each.
TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInAnAssertionPassStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    assert (1) ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInAnAssertionFailStmtIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    assert (1) else ic = new;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.26.5 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInARandcaseItemIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    randcase\n"
      "      1 : ic = new;\n"
      "    endcase\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 8,
                            "8.26.5"));
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, which Parser::ParseRsCodeBlockStmts in src/parser/parser_verify.cpp puts
// in RsProd::code_stmts, reached through Stmt::rs_productions and through no
// other member of Stmt. RsRule::weight_code is the second statement position
// under that one link, and ForEachRandsequenceRuleStmt visits both.
TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  IC ic;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { ic = new; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 8,
                            "8.26.5"));
}

// The declaration form in the two links that admit a declaration. A.6.3's
// par_block holds a block_item_declaration before its statements, which
// Parser::ParseBlockVarDecls in src/parser/parser_stmt_block.cpp puts in
// Stmt::fork_stmts beside them, so CheckNewOnInterfaceDeclInit reads it there
// or nowhere.
TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewDeclInitInAForkArmIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    fork\n"
      "      IC ic2 = new;\n"
      "    join\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

// A.6.12's rs_code_block admits a data_declaration ahead of its statements,
// the second and last of the seven links that admits one.
TEST(InterfaceClassCastingAndRefAssignment,
     InterfaceClassNewDeclInitInARandsequenceCodeBlockIsReported) {
  ElabFixture f;
  ElabOk(
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    randsequence(main)\n"
      "      main : { IC ic2 = new; };\n"
      "    endsequence\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "cannot construct object of interface class", 7,
                            "8.26.5"));
}

// Stmt::for_inits and Stmt::for_steps get no case for either check, and no
// conforming source can give them one. A.6.8 gives `for_initialization ::=
// list_of_variable_assignments | for_variable_declaration` and
// `for_step_assignment ::= operator_assignment | inc_or_dec_expression |
// function_subroutine_call`, and every one of those forms writes `= expression`
// or a call. A.6.2 makes `class_new` an alternative of blocking_assignment
// rather than an expression -- `[ implicit_class_handle . | class_scope |
// package_scope ] hierarchical_variable_identifier select = class_new` -- and
// A.2.4 admits it in a variable_decl_assignment, so `new` reaches neither
// position. The links are still descended, because the list is descended
// whole, and the §8.4 cases in test_elaborator_subclause_08_04.cpp cover them
// with an operation those productions do admit.

}  // namespace
