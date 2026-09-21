#include <gtest/gtest.h>

#include "fixture_parser.h"
#include "helpers_parser_verify.h"
#include "helpers_reported_error.h"
#include "parser/ast_design.h"
#include "parser/ast_module.h"
#include "parser/ast_stmt.h"
#include "parser/ast_type.h"

using namespace delta;

namespace {

TEST(ClassParsing, WeakReferenceDecl) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  initial begin\n"
              "    weak_reference #(my_obj) wr;\n"
              "  end\n"
              "endmodule\n"));
}

TEST(ClassParsing, WeakReferenceAsMember) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "class holder;\n"
              "  weak_reference #(my_obj) wr;\n"
              "endclass\n"));
}

TEST(ClassParsing, WeakReferenceAsFunctionArg) {
  EXPECT_TRUE(
      ParseOk("class my_obj;\n"
              "  int x;\n"
              "endclass\n"
              "module m;\n"
              "  function void f(weak_reference #(my_obj) wr);\n"
              "  endfunction\n"
              "endmodule\n"));
}

// §8.30.1 (printed page 217 of IEEE 1800-2023) has a variable declared of
// type weak_reference#(T), and §8.30.2's example (printed 218) declares two of
// them at module scope with the `#` written against the class name. §6.8
// continues a data_declaration with a list of declarators, so the two names
// share one declared type, each carrying the class name and its one type
// argument.
TEST(ClassParsing, WeakReferenceModuleScopeDeclaratorList) {
  auto r = Parse(
      "class obj;\n"
      "  int v = 9;\n"
      "endclass\n"
      "module t;\n"
      "  weak_reference#(obj) wref1, wref2;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  ASSERT_EQ(r.cu->modules.size(), 1u);
  const auto& items = r.cu->modules[0]->items;
  ASSERT_EQ(items.size(), 2u);
  EXPECT_EQ(items[0]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[0]->name, "wref1");
  EXPECT_EQ(items[1]->kind, ModuleItemKind::kVarDecl);
  EXPECT_EQ(items[1]->name, "wref2");
  for (const auto* item : items) {
    EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
    EXPECT_EQ(item->data_type.scope_name, "");
    EXPECT_EQ(item->data_type.type_name, "weak_reference");
    ASSERT_EQ(item->data_type.type_params.size(), 1u);
    EXPECT_EQ(item->data_type.type_params[0].type_name, "obj");
  }
}

// §8.30.1 (printed 218) puts the weak_reference class in the built-in std
// package of §26.7 (printed 816), and §26.3 reaches a package's declaration
// through the package scope resolution operator, so `std::weak_reference#(obj)`
// at module scope declares a variable of the same class as the bare name, with
// the package recorded as its scope.
TEST(ClassParsing, WeakReferenceStdScopedAtModuleScope) {
  auto r = Parse(
      "class obj;\n"
      "  int v = 9;\n"
      "endclass\n"
      "module t;\n"
      "  std::weak_reference#(obj) wref1;\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* item = FindItemByKind(r, ModuleItemKind::kVarDecl);
  ASSERT_NE(item, nullptr);
  EXPECT_EQ(item->name, "wref1");
  EXPECT_EQ(item->data_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(item->data_type.scope_name, "std");
  EXPECT_EQ(item->data_type.type_name, "weak_reference");
  ASSERT_EQ(item->data_type.type_params.size(), 1u);
  EXPECT_EQ(item->data_type.type_params[0].type_name, "obj");
}

// The same package-scoped form as a block item: A.2.8 admits a data_declaration
// among the block items of a sequential block, and A.2.2.1 lets its data_type
// be a type_identifier behind a package_scope.
TEST(ClassParsing, WeakReferenceStdScopedInProceduralBlock) {
  auto r = Parse(
      "class obj;\n"
      "  int v = 9;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    std::weak_reference#(obj) wref1;\n"
      "    wref1 = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 2u);
  const auto* decl = body->stmts[0];
  EXPECT_EQ(decl->kind, StmtKind::kVarDecl);
  EXPECT_EQ(decl->var_name, "wref1");
  EXPECT_EQ(decl->var_decl_type.kind, DataTypeKind::kNamed);
  EXPECT_EQ(decl->var_decl_type.scope_name, "std");
  EXPECT_EQ(decl->var_decl_type.type_name, "weak_reference");
  ASSERT_EQ(decl->var_decl_type.type_params.size(), 1u);
  EXPECT_EQ(decl->var_decl_type.type_params[0].type_name, "obj");
}

// The bare class name with the `#` written against it, as §8.30.2's example
// spells it, declares a block item the same way the spaced form does.
TEST(ClassParsing, WeakReferenceTightHashInProceduralBlock) {
  auto r = Parse(
      "class obj;\n"
      "  int v = 9;\n"
      "endclass\n"
      "module t;\n"
      "  initial begin\n"
      "    weak_reference#(obj) w;\n"
      "    w = null;\n"
      "  end\n"
      "endmodule\n");
  ASSERT_NE(r.cu, nullptr);
  EXPECT_FALSE(r.has_errors);
  auto* body = FirstInitialBody(r);
  ASSERT_NE(body, nullptr);
  ASSERT_EQ(body->kind, StmtKind::kBlock);
  ASSERT_EQ(body->stmts.size(), 2u);
  const auto* decl = body->stmts[0];
  EXPECT_EQ(decl->kind, StmtKind::kVarDecl);
  EXPECT_EQ(decl->var_name, "w");
  EXPECT_EQ(decl->var_decl_type.scope_name, "");
  EXPECT_EQ(decl->var_decl_type.type_name, "weak_reference");
  ASSERT_EQ(decl->var_decl_type.type_params.size(), 1u);
  EXPECT_EQ(decl->var_decl_type.type_params[0].type_name, "obj");
}

// §8.30.2's example names its two references weak1 and weak2, but §5.6
// (printed 74) forbids a keyword as a user-defined identifier and Table B.1
// (printed 1220) reserves weak1 as one of the drive strengths of A.1.11, so
// the example as written is not a declaration: §6.8 puts a variable name
// after the type, and the keyword is reported there, whichever way the class
// is named. §5.6.1 has an escaped keyword read as an identifier, and the
// declaration then goes through.
TEST(ClassParsing, WeakReferenceReservedWeak1IsNotADeclarator) {
  auto bare = Parse(
      "class obj;\n"
      "  int v = 9;\n"
      "endclass\n"
      "module t;\n"
      "  weak_reference#(obj) weak1, weak2;\n"
      "endmodule\n");
  EXPECT_TRUE(
      ReportedError(bare.diags, "expected identifier, got 'weak1'", 5, "6.8"));
  auto scoped = Parse(
      "class obj;\n"
      "  int v = 9;\n"
      "endclass\n"
      "module t;\n"
      "  std::weak_reference#(obj) weak1;\n"
      "endmodule\n");
  EXPECT_TRUE(ReportedError(scoped.diags, "expected identifier, got 'weak1'", 5,
                            "6.8"));
  EXPECT_TRUE(
      ParseOk("class obj;\n"
              "  int v = 9;\n"
              "endclass\n"
              "module t;\n"
              "  weak_reference#(obj) \\weak1 , weak2;\n"
              "endmodule\n"));
}

}  // namespace
