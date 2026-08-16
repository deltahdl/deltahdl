#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;

namespace {

TEST(ClassAssignRenameParsing, HandleAssignment) {
  EXPECT_TRUE(
      ParseOk("class Packet;\n"
              "  int data;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Packet p1, p2;\n"
              "    p1 = new;\n"
              "    p2 = p1;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassAssignRenameParsing, ShallowCopyNewIdentifier) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C c1, c2;\n"
      "    c1 = new;\n"
      "    c2 = new c1;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
}

TEST(ClassAssignRenameParsing, PropertyInitInClassBody) {
  auto r = Parse(
      "class baseA;\n"
      "  integer j = 5;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
}

TEST(ClassAssignRenameParsing, ClassContainingClassProperty) {
  EXPECT_TRUE(
      ParseOk("class baseA;\n"
              "  integer j = 5;\n"
              "endclass\n"
              "class B;\n"
              "  integer i = 1;\n"
              "  baseA a;\n"
              "endclass\n"));
}

TEST(ClassAssignRenameParsing, ShallowCopyInDeclaration) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "endclass\n"
              "module m;\n"
              "  C c1;\n"
              "  initial begin C c2 = new c1; end\n"
              "endmodule\n"));
}

// A.2.4's `new expression` takes any expression as the copy source, and
// footnote 23 on class_new asks only that it "evaluate to an object handle".
// §8.11 (printed page 187) makes `this` one: "The this keyword denotes a
// predefined object handle that refers to the object that was used to invoke
// the subroutine that this is used within." A non-static class method is one of
// the five contexts that clause admits `this` in, so this source is legal and
// copies the object the method was invoked on.
//
// The case fails on a run that reads the copy source only when it begins with
// an identifier. `this` is then left standing where the statement terminator
// belongs, and the §12.3 report that draws says the source is missing a
// semicolon -- which, written, would make it `p2 = new;` followed by a bare
// `this`, so the copy asked for is silently not the copy given.
TEST(ClassAssignRenameParsing, ShallowCopyFromThisAccepted) {
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int x;\n"
              "  function C dup();\n"
              "    C p2;\n"
              "    p2 = new this;\n"
              "    return p2;\n"
              "  endfunction\n"
              "endclass\n"));
}

// Reads the copy source back off the `new` expression, because acceptance alone
// does not say `this` was taken as one. A run that consumed the keyword and
// discarded it would report nothing and pass
// ClassAssignRenameParsing.ShallowCopyFromThisAccepted, and the design would
// get `p2 = new;` -- a fresh object where a copy was written.
// Parser::ParseMemberAccessChain in src/parser/expr_parser.cpp gives a bare
// `this` an ExprKind::kIdentifier node whose text is "this", which is what the
// copy source has to be.
TEST(ClassAssignRenameParsing, ShallowCopyFromThisStoresCopySource) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  function C dup();\n"
      "    C p2;\n"
      "    p2 = new this;\n"
      "    return p2;\n"
      "  endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  const Expr* copy_src = nullptr;
  for (const auto* member : r.cu->classes[0]->members) {
    if (member->kind != ClassMemberKind::kMethod || member->method == nullptr) {
      continue;
    }
    for (const auto* stmt : member->method->func_body_stmts) {
      if (stmt->kind == StmtKind::kBlockingAssign && stmt->rhs != nullptr &&
          stmt->rhs->kind == ExprKind::kCall && stmt->rhs->text == "new") {
        copy_src = stmt->rhs->lhs;
      }
    }
  }
  ASSERT_NE(copy_src, nullptr);
  EXPECT_EQ(copy_src->kind, ExprKind::kIdentifier);
  EXPECT_EQ(copy_src->text, "this");
}

TEST(ClassAssignRenameParsing, DeepChainedMemberAccess) {
  EXPECT_TRUE(
      ParseOk("class Node;\n"
              "  int val;\n"
              "  Node next;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    Node p;\n"
              "    p = new;\n"
              "    p.next = new;\n"
              "    p.next.next = new;\n"
              "    p.next.next.val = 99;\n"
              "  end\n"
              "endmodule\n"));
}

// §8.12 (printed page 188): "It shall be illegal to use a typed constructor
// call for a shallow copy (see 8.8)." A.2.4 gives class_new the alternatives
// `[ class_scope ] new [ ( list_of_arguments ) ]` and `new expression`, so the
// copy source belongs to the alternative carrying no class scope. The plain
// `c2 = new c1;` form is accepted by
// ClassAssignRenameParsing.ShallowCopyNewIdentifier, which isolates the `C::`
// prefix as the difference.
TEST(ClassAssignRenameParsing, TypedConstructorShallowCopyRejected) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C c1, c2;\n"
      "    c1 = new;\n"
      "    c2 = C::new c1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a typed constructor call cannot take a shallow-copy source", 8,
      "8.12"));
}

// §8.12 bans the typed constructor call for every shallow copy, not only for
// one whose source is an identifier, so widening what `new` takes as a copy
// source has to widen what a class scope over it is reported for. The case
// fails on a run that admits `this` after a bare `new` and not after `C::new`:
// the class scope is then silently accepted, which is what
// ClassAssignRenameParsing.TypedConstructorShallowCopyRejected states it must
// not be for the identifier form.
TEST(ClassAssignRenameParsing, TypedConstructorShallowCopyFromThisRejected) {
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "  function C dup();\n"
      "    C p2;\n"
      "    p2 = C::new this;\n"
      "    return p2;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a typed constructor call cannot take a shallow-copy source", 5,
      "8.12"));
}

TEST(ClassAssignRenameParsing,
     TypedConstructorShallowCopyReportsExactlyOneError) {
  // Parser::MakeMemberAccess consumes the copy source, so the statement still
  // finds its semicolon. `c1` used to stand where the terminator belongs and
  // Parser::ParseAssignmentOrExprStmt reported it a second time under §12.3.
  auto r = Parse(
      "class C;\n"
      "  int x;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    C c1, c2;\n"
      "    c1 = new;\n"
      "    c2 = C::new c1;\n"
      "  end\n"
      "endmodule\n");
  uint32_t errors = 0;
  for (const auto& d : r.diags) {
    if (d.severity == DiagSeverity::kError) errors++;
  }
  EXPECT_EQ(errors, 1U);
}

TEST(ClassAssignRenameParsing,
     TypedConstructorShallowCopyInDeclarationRejected) {
  // A declaration initializer reaches the expression parser from
  // Parser::ParseBlockVarDecls rather than from
  // Parser::ParseAssignmentOrExprStmt, so the assignment form above does not
  // answer for it. ClassAssignRenameParsing.ShallowCopyInDeclaration accepts
  // the same declaration written without the class scope.
  auto r = Parse(
      "class C;\n"
      "endclass\n"
      "module m;\n"
      "  C c1;\n"
      "  initial begin\n"
      "    C c2 = C::new c1;\n"
      "  end\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a typed constructor call cannot take a shallow-copy source", 6,
      "8.12"));
}

TEST(ClassAssignRenameParsing, TypedConstructorCallWithArgumentAccepted) {
  // §8.8 (printed page 186): "Arguments may be passed to a typed constructor
  // call if appropriate, just as for an ordinary constructor." Without this
  // case the §8.12 report above is satisfied by refusing every class-scoped
  // `new`, since the copy source is the only thing that makes one illegal.
  EXPECT_TRUE(
      ParseOk("class C;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  C c2;\n"
              "  initial c2 = C::new(1);\n"
              "endmodule\n"));
}

}  // namespace
