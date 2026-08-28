#include <string>

#include "fixture_elaborator.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassConstraintElaboration, WeakReferenceDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) wr;\n"
             "  end\n"
             "endmodule\n"));
}

TEST(ClassConstraintElaboration, WeakReferenceAsMemberOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "class holder;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endclass\n"
             "module m;\n"
             "endmodule\n"));
}

// The declaration position decides which of the four sites enforcing this rule
// fires, and all four cite §8.30.1. That is the subclause carrying the sentence
// they enforce -- "The parameter type T shall be a class type; all other types
// shall result in a compiler error" -- while §8.30 "Weak references" is the
// heading above it and states no rule. Two of the four cited §8.30 until #3058,
// so the same breach named a different clause depending on where the
// declaration stood. Asserting one subclause across all five cases is what a
// single site drifting again would break.
TEST(ClassConstraintElaboration, WeakReferenceNonClassTypeError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(int) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "weak_reference type parameter shall be a class "
                            "type",
                            3, "8.30.1"));
}

TEST(ClassConstraintElaboration, WeakReferenceAsFunctionArgOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  function void f(weak_reference #(my_obj) wr);\n"
             "  endfunction\n"
             "endmodule\n"));
}

// A weak_reference incorporated into another object as a class property is held
// to the same class-type restriction: a non-class parameter is a compiler error
// at the member-declaration site too.
TEST(ClassConstraintElaboration, WeakReferenceNonClassMemberError) {
  ElabFixture f;
  ElabOk(
      "class holder;\n"
      "  weak_reference #(int) wr;\n"
      "endclass\n"
      "module m;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "weak_reference type parameter shall be a class "
                            "type",
                            2, "8.30.1"));
}

// The class-type restriction applies wherever weak_reference#(T) is declared,
// including a subroutine argument. A non-class parameter on a function port is
// a compiler error just as it is on a variable declaration.
TEST(ClassConstraintElaboration, WeakReferenceNonClassFunctionArgError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  function void f(weak_reference #(int) wr);\n"
      "  endfunction\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "weak_reference type parameter shall be a class "
                            "type",
                            2, "8.30.1"));
}

// A weak_reference declared directly as a module item (not inside a procedural
// block) is checked by a separate elaborator path than a block-local variable.
// A class parameter is accepted there just as it is for a procedural local.
TEST(ClassConstraintElaboration, WeakReferenceModuleItemDeclOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "module m;\n"
             "  weak_reference #(my_obj) wr;\n"
             "endmodule\n"));
}

// The module-item declaration path enforces the same restriction: a non-class
// parameter at module scope is a compiler error, exercising the module-level
// validator rather than the procedural-block one covered above.
TEST(ClassConstraintElaboration, WeakReferenceModuleItemNonClassError) {
  ElabFixture f;
  ElabOk(
      "module m;\n"
      "  weak_reference #(int) wr;\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "weak_reference type parameter shall be a class "
                            "type",
                            2, "8.30.1"));
}

// The Overview's own example forward-declares the referent class with
// `typedef class my_obj;` before naming it as the weak_reference parameter. A
// forward-declared class is still a class type, so this exact form elaborates.
TEST(ClassConstraintElaboration, WeakReferenceForwardTypedefClassOk) {
  EXPECT_TRUE(
      ElabOk("typedef class my_obj;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_obj) weak_obj;\n"
             "  end\n"
             "endmodule\n"
             "class my_obj;\n"
             "  int x;\n"
             "endclass\n"));
}

// A typedef alias of a class denotes the same class type, so a
// weak_reference parameterized on the alias names a class type and shall be
// accepted just as the class name itself is. The parameter check follows the
// typedef through to the underlying class rather than demanding the raw class
// name at the use site.
TEST(ClassConstraintElaboration, WeakReferenceTypedefAliasOfClassOk) {
  EXPECT_TRUE(
      ElabOk("class my_obj;\n"
             "  int x;\n"
             "endclass\n"
             "typedef my_obj my_alias;\n"
             "module m;\n"
             "  initial begin\n"
             "    weak_reference #(my_alias) wr;\n"
             "  end\n"
             "endmodule\n"));
}

// The closest rejected neighbor of the accepting path: a parameter that names a
// user-defined type which is NOT a class (here a typedef enum). Unlike a
// built-in keyword such as `int`, the argument is a named type, so the check
// must resolve the name through the typedef table, find a non-class type, and
// still report the compiler error the rule requires.
TEST(ClassConstraintElaboration, WeakReferenceTypedefNonClassError) {
  ElabFixture f;
  ElabOk(
      "typedef enum {A, B} col_t;\n"
      "module m;\n"
      "  initial begin\n"
      "    weak_reference #(col_t) wr;\n"
      "  end\n"
      "endmodule\n",
      f);
  EXPECT_TRUE(ReportedError(f.diag.Diagnostics(),
                            "weak_reference type parameter shall be a class "
                            "type",
                            4, "8.30.1"));
}

// §8.30.1 rules that "The parameter type T shall be a class type; all other
// types shall result in a compiler error", and puts no condition on the
// statement the declaration stands in. ValidateLocalWeakRefDecls in
// src/elaborator/elaborator_scope_rules.cpp is the site that answers for a
// declaration inside a procedural block, and it had written out nine of the
// thirteen child-statement links Stmt declares. It now takes the list from
// ForEachChildStmt in src/elaborator/elaborator_validate_internal.h, and the
// five cases below cover one newly reached position each. A randsequence
// production keeps statements in RsProd::code_stmts and in RsRule::weight_code,
// which ForEachRandsequenceRuleStmt reaches by different members, so each is
// its own position.
//
// `stmt` is written at line 4 and may run to several lines, so the line the
// report stands at is read back out of the source rather than counted. Each
// case writes the declaration inside a begin-end block, so what the position
// under test decides is whether the walk reaches that block at all.
void ExpectNonClassWeakRefIn(const std::string& stmt) {
  ElabFixture f;
  std::string src =
      "module m;\n  logic ok;\n  initial\n    " + stmt + "\nendmodule\n";
  ElaborateSrc(src, f);
  EXPECT_TRUE(
      ReportedError(f.diag.Diagnostics(),
                    "weak_reference type parameter shall be a class type",
                    LineHolding(src, "weak_reference #(int) wr;"), "8.30.1"));
}

// §16.3 gives `action_block ::= statement_or_null | [ statement ] else
// statement_or_null`, so an immediate assertion holds a statement in each arm,
// kept in Stmt::assert_pass_stmt and Stmt::assert_fail_stmt. This case and the
// next cover one arm each.
TEST(ClassConstraintElaboration, WeakReferenceNonClassInAnAssertionPassStmt) {
  ExpectNonClassWeakRefIn("assert (ok) begin weak_reference #(int) wr; end");
}

TEST(ClassConstraintElaboration, WeakReferenceNonClassInAnAssertionFailStmt) {
  ExpectNonClassWeakRefIn(
      "assert (ok) else begin weak_reference #(int) wr; end");
}

// §18.16 gives `randcase_item ::= expression : statement_or_null`, whose
// statement the parser keeps in the second member of a Stmt::randcase_items
// entry. §8.30.1 is a rule about the source, so it holds whether the weighted
// draw would select the item or not.
TEST(ClassConstraintElaboration, WeakReferenceNonClassInARandcaseItem) {
  ExpectNonClassWeakRefIn(
      "randcase 1: begin weak_reference #(int) wr; end endcase");
}

// A.6.12 gives `rs_code_block ::= { { data_declaration } { statement_or_null }
// }`, so a randsequence production's code block holds ordinary procedural
// statements. They are kept in RsProd::code_stmts, reached through
// Stmt::rs_productions and through no other member of Stmt.
TEST(ClassConstraintElaboration,
     WeakReferenceNonClassInARandsequenceCodeBlock) {
  ExpectNonClassWeakRefIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : { begin weak_reference #(int) wr; end };\n"
      "      endsequence\n"
      "    end");
}

// §18.17.1 lets a weight specification be followed by a code block of its own,
// which the parser keeps in RsRule::weight_code. It is a second list under
// Stmt::rs_productions, so a walk reaches it without reaching
// RsProd::code_stmts and the case above does not answer for it.
TEST(ClassConstraintElaboration,
     WeakReferenceNonClassInARandsequenceWeightCodeBlock) {
  ExpectNonClassWeakRefIn(
      "begin\n"
      "      randsequence(main)\n"
      "        main : alt := 1 { begin weak_reference #(int) wr; end };\n"
      "        alt : { ok = 1; };\n"
      "      endsequence\n"
      "    end");
}

}  // namespace
