#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "parser/ast_class.h"
#include "parser/ast_module.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(ObjectPropertyParsing, PropertyAccessDotNotation) {
  auto r = Parse(
      "class Packet;\n"
      "  int command;\n"
      "  int address;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int var1;\n"
      "    Packet p;\n"
      "    p = new;\n"
      "    p.command = 1;\n"
      "    p.address = 2;\n"
      "    var1 = p.command;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  auto* mod = r.cu->modules.back();
  ASSERT_NE(mod, nullptr);

  ASSERT_EQ(r.cu->classes.size(), 1u);
  auto* cls = r.cu->classes[0];
  EXPECT_EQ(cls->name, "Packet");
  ASSERT_GE(cls->members.size(), 2u);
  EXPECT_EQ(cls->members[0]->name, "command");
  EXPECT_EQ(cls->members[1]->name, "address");
}

TEST(ObjectPropertyParsing, ParameterAccessViaInstance) {
  ParseOk(
      "class vector #(parameter width = 7, type T = int);\n"
      "  T data;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    automatic int w;\n"
      "    vector #(3) v;\n"
      "    v = new;\n"
      "    w = v.width;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ObjectPropertyParsing, EnumAccessViaInstance) {
  ParseOk(
      "class Packet;\n"
      "  typedef enum {ERR_OVERFLOW = 10, ERR_UNDERFLOW = 1123} PCKT_TYPE;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    automatic int x;\n"
      "    p = new;\n"
      "    x = p.ERR_OVERFLOW;\n"
      "  end\n"
      "endmodule\n");
}

TEST(ObjectPropertyParsing, PropertyReadAndWrite) {
  ParseOk(
      "class Packet;\n"
      "  bit [3:0] command;\n"
      "  bit [40:0] address;\n"
      "  integer time_requested;\n"
      "  const integer buffer_size = 100;\n"
      "endclass\n"
      "module m;\n"
      "  initial begin\n"
      "    Packet p;\n"
      "    automatic int var1;\n"
      "    automatic integer packet_time;\n"
      "    p = new;\n"
      "    p.command = 4'd0;\n"
      "    p.address = 41'b0;\n"
      "    packet_time = p.time_requested;\n"
      "    var1 = p.buffer_size;\n"
      "  end\n"
      "endmodule\n");
}

// §8.5 puts no restriction on the data type of a class property, §26.3
// references a package's declaration through the package scope resolution
// operator, and A.2.2.1 lets a data_type be a type_identifier behind a
// package_scope (printed pages 183, 808 and 1182 of IEEE 1800-2023). The
// parser reads an identifier as a named type only where it knows the name as a
// type, and a package name never is one, so `pk::sev_t s = pk::MED;` in a class
// body was reported at the `::` where a `;` was expected. The property keeps
// both halves of the scoped name and its initializer.
TEST(ObjectPropertyParsing, PackageScopedTypeDeclaresAProperty) {
  auto r = Parse(
      "package pk;\n"
      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
      "endpackage\n"
      "class C;\n"
      "  pk::sev_t s = pk::MED;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  const auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 1u);
  const auto* s = cls->members[0];
  EXPECT_EQ(s->kind, ClassMemberKind::kProperty);
  EXPECT_EQ(s->name, "s");
  EXPECT_EQ(s->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(s->data_type.scope_name, "pk");
  EXPECT_EQ(s->data_type.type_name, "sev_t");
  EXPECT_NE(s->init_expr, nullptr);
}

// A.2.7's function_data_type_or_implicit takes the same data_type, so a
// method's return type spells a package-scoped type the same way. The method
// is a member whose return type keeps the scope and the name, and the parse
// after it is undisturbed: the property declared next is still read.
TEST(ObjectPropertyParsing, PackageScopedTypeReturnedByAMethod) {
  auto r = Parse(
      "package pk;\n"
      "  typedef enum {LOW, MED = 2, HIGH} sev_t;\n"
      "endpackage\n"
      "class C;\n"
      "  function pk::sev_t nxt(); return pk::HIGH; endfunction\n"
      "  int after;\n"
      "endclass\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->classes.size(), 1u);
  const auto* cls = r.cu->classes[0];
  ASSERT_EQ(cls->members.size(), 2u);
  const auto* nxt = cls->members[0];
  EXPECT_EQ(nxt->kind, ClassMemberKind::kMethod);
  ASSERT_NE(nxt->method, nullptr);
  EXPECT_EQ(nxt->method->name, "nxt");
  EXPECT_TRUE(nxt->method->method_class.empty());
  EXPECT_EQ(nxt->method->return_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(nxt->method->return_type.scope_name, "pk");
  EXPECT_EQ(nxt->method->return_type.type_name, "sev_t");
  EXPECT_EQ(cls->members[1]->name, "after");
}

// §8.24's out-of-block declaration of a constructor names the class before
// `::new`, and one of a method names it before `::name(`; neither spells a
// type, so a class this parse does not know still opens the method's name
// rather than a scoped return type.
TEST(ObjectPropertyParsing, ScopedMethodNameIsNotAReturnType) {
  auto r = Parse(
      "package pkg;\n"
      "  function Other::new(); endfunction\n"
      "  function Other::go(); endfunction\n"
      "endpackage\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->packages.size(), 1u);
  const auto* pkg = r.cu->packages[0];
  ASSERT_EQ(pkg->items.size(), 2u);
  EXPECT_EQ(pkg->items[0]->method_class, "Other");
  EXPECT_EQ(pkg->items[0]->name, "new");
  EXPECT_EQ(pkg->items[1]->method_class, "Other");
  EXPECT_EQ(pkg->items[1]->name, "go");
}

}  // namespace
