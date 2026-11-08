#include <gtest/gtest.h>

#include <cstdint>

#include "common/diagnostic.h"
#include "fixture_parser.h"
#include "helpers_reported_error.h"
#include "parser/ast_class.h"

using namespace delta;
namespace {

TEST(AbstractClassParsing, VirtualClass) {
  auto r = Parse("virtual class base; endclass");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
}

TEST(PureVirtualMethodParsing, PureVirtualFunction) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 1u);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_virtual);
  EXPECT_TRUE(m->is_pure_virtual);
  EXPECT_EQ(m->kind, ClassMemberKind::kMethod);
}

TEST(PureVirtualMethodParsing, PureVirtualFunctionPrototype) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function int compute(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_pure_virtual);
}

TEST(PureVirtualMethodParsing, PureVirtualTaskPrototype) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual task do_work(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_pure_virtual);
}

TEST(AbstractClassParsing, NonPureVirtualNotFlagged) {
  auto r = Parse(
      "class Base;\n"
      "  virtual function void display(); endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_virtual);
  EXPECT_FALSE(m->is_pure_virtual);
}

TEST(AbstractClassParsing, AbstractExtendsAbstract) {
  auto r = Parse(
      "virtual class Shape;\n"
      "  pure virtual function int area();\n"
      "endclass\n"
      "virtual class Shape2D extends Shape;\n"
      "  pure virtual function int perimeter();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  EXPECT_TRUE(r.cu->classes[0]->is_virtual);
  EXPECT_TRUE(r.cu->classes[1]->is_virtual);
  EXPECT_TRUE(r.cu->classes[1]->members[0]->is_pure_virtual);
}

TEST(AbstractClassParsing, ConcreteOverridesPureVirtual) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "endclass\n"
      "class Derived extends Base;\n"
      "  virtual function void display(); endfunction\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes.size(), 2u);
  auto* derived_m = r.cu->classes[1]->members[0];
  EXPECT_TRUE(derived_m->is_virtual);
  EXPECT_FALSE(derived_m->is_pure_virtual);
}

TEST(PureVirtualMethodParsing, PureVirtualAndExtern) {
  auto r = Parse(
      "class C;\n"
      "  pure virtual function void pv_fn();\n"
      "  pure virtual task pv_task();\n"
      "  extern function void ext_fn();\n"
      "  extern static task ext_task();\n"
      "endclass\n");
  ASSERT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto& members = r.cu->classes[0]->members;
  ASSERT_EQ(members.size(), 4u);
  EXPECT_EQ(members[0]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[1]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[2]->kind, ClassMemberKind::kMethod);
  EXPECT_EQ(members[3]->kind, ClassMemberKind::kMethod);
  EXPECT_TRUE(members[0]->is_virtual);
  EXPECT_TRUE(members[1]->is_virtual);
  EXPECT_EQ(members[2]->method->name, "ext_fn");
  EXPECT_TRUE(members[3]->is_static);
}

TEST(PureVirtualMethodParsing, PureVirtualMethodHasNoBody) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  auto* m = r.cu->classes[0]->members[0];
  EXPECT_TRUE(m->is_pure_virtual);
  EXPECT_TRUE(m->method->func_body_stmts.empty());
}

TEST(AbstractClassParsing, NonAbstractClassNotFlaggedVirtual) {
  auto r = Parse("class C; endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.cu->classes[0]->is_virtual);
}

TEST(AbstractClassParsing, MultiplePureVirtualMethods) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function int compute();\n"
      "  pure virtual task run(input int x);\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  ASSERT_EQ(r.cu->classes[0]->members.size(), 2u);
  EXPECT_TRUE(r.cu->classes[0]->members[0]->is_pure_virtual);
  EXPECT_TRUE(r.cu->classes[0]->members[1]->is_pure_virtual);
}

TEST(PureVirtualMethodParsing, PureVirtualWithBodyRejected) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "    return;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a pure virtual method shall not have a body", 2, "8.21"));
}

TEST(PureVirtualMethodParsing, PureVirtualWithBodyReportsExactlyOneError) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "    return;\n"
      "  endfunction\n"
      "endclass\n");
  uint32_t errors = 0;
  for (const auto& d : r.diags) {
    if (d.severity == DiagSeverity::kError) errors++;
  }
  EXPECT_EQ(errors, 1U);
}

TEST(PureVirtualMethodParsing, PureVirtualTaskWithBodyRejected) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual task run();\n"
      "    return;\n"
      "  endtask\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a pure virtual method shall not have a body", 2, "8.21"));
}

TEST(PureVirtualMethodParsing, PureVirtualWithEmptyBodyRejected) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a pure virtual method shall not have a body", 2, "8.21"));
}

TEST(PureVirtualMethodParsing, PureVirtualWithDeclarationBodyAddsNoProperty) {
  auto r = Parse(
      "virtual class Base;\n"
      "  pure virtual function void display();\n"
      "    int x = 1;\n"
      "  endfunction\n"
      "endclass\n");
  EXPECT_TRUE(ReportedError(
      r.diags, "a pure virtual method shall not have a body", 2, "8.21"));
  ASSERT_EQ(r.cu->classes.size(), 1u);
  EXPECT_EQ(r.cu->classes[0]->members.size(), 1u);
}

}  // namespace
