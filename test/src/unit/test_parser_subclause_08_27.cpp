#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_reported_error.h"

using namespace delta;
namespace {

TEST(ClassParsing, ForwardTypedefClassSelfRef) {
  auto r = Parse(
      "typedef class Node;\n"
      "class Node;\n"
      "  Node next;\n"
      "  int data;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_GE(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "Node");
}

TEST(ClassParsing, TypedefClassMutualReference) {
  auto r = Parse(
      "typedef class C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "class C2;\n"
      "  C1 c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_EQ(r.cu->classes[0]->name, "C1");
  EXPECT_EQ(r.cu->classes[1]->name, "C2");
}

TEST(ClassParsing, TypedefInterfaceClass) {
  auto r = Parse(
      "typedef interface class IC;\n"
      "interface class IC;\n"
      "  pure virtual function void foo();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_TRUE(r.cu->classes[0]->is_interface);
}

TEST(ClassParsing, BareForwardTypedefWithoutClassKeyword) {
  auto r = Parse(
      "typedef C2;\n"
      "class C1;\n"
      "  C2 c;\n"
      "endclass\n"
      "class C2;\n"
      "  C1 c;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 2u);
}

TEST(ClassParsing, ForwardTypedefParameterizedClass) {
  auto r = Parse(
      "typedef class C;\n"
      "module top;\n"
      "  C#(1, real) v2;\n"
      "  C#(.p(2), .T(real)) v3;\n"
      "endmodule\n"
      "class C #(parameter p = 2, type T = int);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_GE(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->name, "C");
}

TEST(ClassParsing, ClassNamedAsATypeBeforeItsDeclarationIsRefused) {
  {
    auto r = Parse(
        "class C1;\n"
        "  C2 c;\n"
        "endclass\n"
        "class C2; endclass\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "expected ';', got identifier", 2, "8.5"))
        << "p1";
  }
  {
    auto r = Parse(
        "module m;\n"
        "  class M1;\n"
        "    M2 x;\n"
        "  endclass\n"
        "  class M2; endclass\n"
        "endmodule\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "expected ';', got identifier", 3, "8.5"))
        << "p2";
  }
  {
    auto r = Parse(
        "package pk;\n"
        "  class P1;\n"
        "    P2 x;\n"
        "  endclass\n"
        "  class P2; endclass\n"
        "endpackage\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "expected ';', got identifier", 3, "8.5"))
        << "p3";
  }
  {
    auto r = Parse(
        "class R1;\n"
        "  function C3 f(); return null; endfunction\n"
        "endclass\n"
        "class C3; endclass\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "expected ';', got identifier", 2, "13.4"))
        << "p4";
  }
  {
    auto r = Parse(
        "class R2;\n"
        "  function void f(C3 a); endfunction\n"
        "endclass\n"
        "class C3; endclass\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "expected ')', got identifier", 2, "13.3"))
        << "p5";
  }
  {
    auto r = Parse(
        "class R3;\n"
        "  function void f();\n"
        "    C3 l;\n"
        "  endfunction\n"
        "endclass\n"
        "class C3; endclass\n");
    EXPECT_TRUE(
        ReportedError(r.diags, "expected ';', got identifier", 3, "12.3"))
        << "p6";
  }
}

}  // namespace
