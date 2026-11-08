#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"
#include "parser/ast_expr.h"
#include "parser/ast_stmt.h"

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
