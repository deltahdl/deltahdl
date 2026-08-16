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
